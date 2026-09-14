package garden.xeno.symbolum.logic

import scala.annotation.tailrec
import garden.xeno.symbolum.kernel.*

/**
 * Equality-preserving transformations, each returning the theorem that justifies it.
 *
 * Nothing here is trusted. Every function returns a value of the kernel's theorem type, which
 * means every step it took went through an inference rule; a mistake in this file produces a
 * theorem about something other than what was asked for, or no theorem at all, and never a false
 * one.
 *
 * This is where the derived rules get their plumbing: a definition is unfolded by applying the
 * defining equation to arguments and reducing the result, and both halves of that are here.
 */
object Conv {

  /* ------------------------------------------------------------ small steps */

  /**
   * `|- t = t`, with the leaves shared.
   *
   * [[Kernel.refl]] with one thing added and nothing changed. Where `t` is an atom (a constant, a
   * free variable or a bound index) the theorem is built once and handed out again. Every caller
   * above the kernel should reach for this rather than for the rule, and the reason is a
   * measurement rather than a preference.
   *
   * == What it is worth, counted on 2026-09-11 ==
   *
   * Over the 112 lemmas the standard chain derives: 575834 proof nodes, of which **58.1% are a
   * sequent already derived elsewhere in the same proof as a separate object**, and reflexivity is
   * 51% of those duplicates. `|- = = =` alone exists 31366 times, because [[sym]] built a fresh one
   * on every call; `|- v = v` 19233 times, `|- ! = !` 9019, `|- SUC = SUC` 5312. Sharing the atoms
   * removes **134532 nodes, 23.4% of every proof in the library**, and nothing else about any of
   * them changes: same conclusion, same empty hypothesis list, same `Derivation.Reflexivity` node.
   *
   * A memo over **every** term would have removed 29.0% rather than 23.4%. It is not here because
   * the population is the difference between the two: 4287 distinct atoms against 26791 distinct
   * terms, and a cache keyed by arbitrary terms is unbounded in the size of what anyone proves and
   * pays an O(size) hash on every lookup. Atoms are bounded by the signature and by the variables
   * in play, and hash in constant time.
   *
   * == Why this is not a change to what a proof is ==
   *
   * `Derivation`'s own docstring says a proof is a graph shared by reference and that a step used
   * twice is one object. Until this, that was true of everything except the leaves, where it was
   * false 134532 times. `Derivation.size` counts by identity deliberately, so the figures it
   * reports move when this lands: they move because the work stopped being done, which is the
   * direction that number is supposed to move in.
   *
   * Sharing across theories is not a question either, and it is worth saying why rather than
   * leaving it to be rediscovered. A cached leaf is `|- t = t`, which holds whatever `t` denotes,
   * so two theories that declare a constant of the same name and type and mean different things by
   * it get a theorem that is true in both. That the two constants compare equal at all is the
   * defect `docs/adr/0008` leaves open for declared constants; this table neither causes it nor
   * widens it, because `Kernel.refl` would have produced an equal theorem in either theory anyway
   * and a theorem's identity here is its sequent.
   *
   * == The bound, and what happens at it ==
   *
   * [[Atoms]] entries. Past it the cache stops growing and the rule is called directly, so the
   * behaviour is identical and only the saving stops. A cap rather than no cap because a session
   * that generates fresh variables forever would otherwise retain one theorem per variable; the
   * number is twice what the whole standard library needs, measured above.
   */
  def refl(term: Term): Kernel.Thm = term match {
    case App(_, _) | Abs(_, _) => Kernel.refl(term)
    case atom =>
      // `Option` at the boundary, because the map is a Java one and its two misses are both a
      // `null`: absent from `get`, and won-the-race from `putIfAbsent`. Reading them as `null`
      // inside Scala is how one of them eventually gets tested with `==` and the other forgotten.
      Option(atoms.get(atom)).getOrElse {
        val built = Kernel.refl(atom)
        if (atoms.size < Atoms) Option(atoms.putIfAbsent(atom, built)).getOrElse(built)
        else built
      }
  }

  /**
   * How many atoms the reflexivity cache holds.
   *
   * Measured: the standard chain's 112 lemmas reach 4287 distinct atoms in all. Twice that, so that
   * a development half as large again as everything here still shares all of its leaves, and a
   * runaway supply of fresh variables still stops at a bounded table.
   */
  val Atoms: Int = 8192

  private val atoms: java.util.concurrent.ConcurrentHashMap[Term, Kernel.Thm] =
    new java.util.concurrent.ConcurrentHashMap[Term, Kernel.Thm]()

  /** `G |- a = b` gives `G |- b = a`. */
  def sym(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Term.destEq(theorem.conclusion) match {
      case None => Left(NotOfForm("an equation", theorem.conclusion))
      case Some((lhs, _)) =>
        val equality = refl(Term.equalityAt(Term.typeOf(lhs)))
        // One theorem and not two: the same `|- lhs = lhs` is wanted on both sides, and building it
        // twice was two nodes where the proof has one.
        val left = refl(lhs)
        for {
          applied <- LogicError.lift(Kernel.mkComb(equality, theorem))
          both <- LogicError.lift(Kernel.mkComb(applied, left))
          result <- LogicError.lift(Kernel.eqMp(both, left))
        } yield result
    }

  /** `G |- x = y` gives `G |- f x = f y`. */
  def apTerm(fn: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    LogicError.lift(Kernel.mkComb(refl(fn), theorem))

  /** `G |- f = g` gives `G |- f x = g x`. */
  def apThm(theorem: Kernel.Thm, argument: Term): Either[LogicError, Kernel.Thm] =
    LogicError.lift(Kernel.mkComb(theorem, refl(argument)))

  /** Chain two equations. */
  def trans(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    LogicError.lift(Kernel.trans(left, right))

  /**
   * `G |- R a b`, `|- a = a'` and `|- b = b'` give `G |- R a' b'`.
   *
   * Congruence on whatever relation the theorem is about, read off the theorem rather than looked
   * up, so that the same three lines serve any binary relation. Here rather than in [[Rewrite]]
   * because both sides are known and there is nothing to search for: rewriting with an equation
   * whose right side contains its left, which is what transporting backwards means, would run the
   * rewriter to its limit.
   */
  def rewriteSides(
    left: Kernel.Thm,
    right: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    theorem.conclusion match {
      case App(App(relation, _), _) =>
        for {
          onLeft <- LogicError.lift(Kernel.mkComb(refl(relation), left))
          onBoth <- LogicError.lift(Kernel.mkComb(onLeft, right))
          result <- LogicError.lift(Kernel.eqMp(onBoth, theorem))
        } yield result

      case other => Left(NotOfForm("a relation between two terms", other))
    }

  /** `G |- R a b` and `|- b = b'` give `G |- R a b'`. */
  def rewriteRight(
    theorem: Kernel.Thm,
    equation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    theorem.conclusion match {
      case App(App(_, left), _) => rewriteSides(refl(left), equation, theorem)
      case other => Left(NotOfForm("a relation between two terms", other))
    }

  /* --------------------------------------------------------- beta normal form */

  /**
   * `|- t = t'`, where `t'` is the beta normal form of `t`.
   *
   * The recursion terminates without a step limit, and the reason is not that the inputs happen
   * to be small: every well-typed term of the simply typed lambda calculus is strongly
   * normalising, and the kernel's constructors build no other kind. A fuel parameter here would
   * be a branch no well-typed term can reach, which is worse than none: it would have to be
   * tested, and it could not be.
   *
   * If that assumption is ever wrong, this loops rather than returning an error, and the fault is
   * in the kernel's typing rather than here.
   */
  def betaNormalise(term: Term): Either[LogicError, Kernel.Thm] = term match {
    case Abs(binderType, _) =>
      val variable = freshVariable("v", binderType, Term.freeVariables(term))
      for {
        redex <- LogicError.lift(Term.app(term, variable))
        opened <- Term.betaReduce(redex).toRight(NotOfForm("a redex", redex))
        inner <- betaNormalise(opened)
        // Closing over the variable the body was opened with rebuilds the original binder, so the
        // left side of this is the term that came in, not a copy of it.
        result <- LogicError.lift(Kernel.abs(variable, inner))
      } yield result

    case App(fn, argument) =>
      for {
        fnEq <- betaNormalise(fn)
        argumentEq <- betaNormalise(argument)
        combined <- LogicError.lift(Kernel.mkComb(fnEq, argumentEq))
        result <- contractHead(combined)
      } yield result

    case _ => Right(refl(term))
  }

  /** If the right side of `theorem` is a redex, contract it and normalise what comes out. */
  private def contractHead(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Term.destEq(theorem.conclusion) match {
      case Some((_, right @ App(Abs(_, _), _))) =>
        for {
          step <- LogicError.lift(Kernel.beta(right))
          contracted <- trans(theorem, step)
          reduced <- Term.destEq(step.conclusion)
            .map(_._2)
            .toRight(NotOfForm("an equation", step.conclusion))
          rest <- betaNormalise(reduced)
          result <- trans(contracted, rest)
        } yield result

      case _ => Right(theorem)
    }

  /**
   * `G |- l = r` gives `G |- l' = r'`, both sides in beta normal form.
   *
   * Used where both sides are the result of applying something to both halves of an equation over
   * variables, as in the projection schemas in [[Rules]]. On a term a caller supplied, [[betaSides]]
   * is the one to use: this reduces everything, including whatever the caller wrote.
   */
  def normaliseSides(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Term.destEq(theorem.conclusion) match {
      case None => Left(NotOfForm("an equation", theorem.conclusion))
      case Some((left, right)) =>
        for {
          leftNormal <- betaNormalise(left)
          rightNormal <- betaNormalise(right)
          reversed <- sym(leftNormal)
          joined <- trans(reversed, theorem)
          result <- trans(joined, rightNormal)
        } yield result
    }

  /* ------------------------------------------------------- single contractions */

  /** `|- t = t'`, with `t` contracted once at its root if it is a redex and left alone otherwise. */
  def betaRoot(term: Term): Either[LogicError, Kernel.Thm] =
    Term.betaReduce(term) match {
      case Some(_) => LogicError.lift(Kernel.beta(term))
      case None => Right(refl(term))
    }

  /**
   * `G |- l = r` gives `G |- l' = r'`, each side contracted once at its root.
   *
   * For a rule that has applied both sides of an equation between two lambdas to an argument: the
   * two redexes it built are contracted and nothing else is, so an argument that contains a redex
   * of its own goes through as it was written.
   */
  def betaSides(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Term.destEq(theorem.conclusion) match {
      case None => Left(NotOfForm("an equation", theorem.conclusion))
      case Some((left, right)) =>
        for {
          leftStep <- betaRoot(left)
          rightStep <- betaRoot(right)
          reversed <- sym(leftStep)
          joined <- trans(reversed, theorem)
          result <- trans(joined, rightStep)
        } yield result
    }

  /** `G |- l = r` gives `G |- l = r'`, the right side contracted once at its root. */
  private def betaRhs(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Term.destEq(theorem.conclusion) match {
      case None => Left(NotOfForm("an equation", theorem.conclusion))
      case Some((_, right)) => betaRoot(right).flatMap(trans(theorem, _))
    }

  /**
   * `|- c a1 ... an = body`, from the equation defining `c` and the arguments it is applied to.
   *
   * Each argument is applied to both sides and the application that makes on the right is
   * contracted, so the body that comes out is the definition with the arguments substituted rather
   * than a term with the substitution still pending. Only that application is contracted: an
   * argument is put into the body exactly as it was given, redexes and all. The first version
   * normalised the whole right side, which rewrote the caller's arguments and left the left side
   * stating something the right no longer matched.
   */
  def unfold(definition: Kernel.Thm, arguments: List[Term]): Either[LogicError, Kernel.Thm] =
    arguments.foldLeft(Right(definition): Either[LogicError, Kernel.Thm]) { (acc, argument) =>
      for {
        current <- acc
        applied <- apThm(current, argument)
        reduced <- betaRhs(applied)
      } yield reduced
    }

  /* ------------------------------------------------------------------ naming */

  /** A variable of the given type whose name is free in nothing in `avoid`. */
  def freshVariable(base: String, ty: Type, avoid: Set[FVar]): FVar = {
    val used = avoid.map(_.name)

    @tailrec
    def pick(index: Int): String = {
      val candidate = if (index == 0) base else s"$base$index"
      if (!used.contains(candidate)) candidate else pick(index + 1)
    }

    Term.variable(pick(0), ty)
  }
}
