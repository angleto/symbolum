package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Steps over the naturals and over propositions that the derivations beside `Complex` share:
 * `RuleThirty` and `Gilbreath`. Each is a line or two over `ComplexKit` and decides nothing a
 * reader has to trust; what comes out is a theorem the kernel built or a refusal.
 *
 * `numLin` settles a comparison of naturals by carrying it to the reals, where `Linarith` reads it,
 * with every image of a natural known to be non-negative. `tauto` hands a goal to the propositional
 * procedure after opening each equation between propositions into two implications, since the
 * procedure reads such an equation as an atom. `deciding` and `byCases` replace a `COND` by its
 * branch wherever literals decide its condition, and split on propositions until they do.
 * `belowBound` proves two sums equal from their terms below the bound.
 *
 * Two facts these steps rest on are proved here once per instance: `eqImpTheorem`, which is
 * `(a = b) = ((a ==> b) /\ (b ==> a))` for propositions, and `notLeTheorem`, which is `n < m` from
 * `~(m <= n)`.
 */
private[theories] final class NumberSteps(val kit: ComplexKit, val semiring: Semiring) {
  import kit.*

  type R[A] = Either[LogicError, A]

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)

  /** A number variable as text the parser reads back as the same variable. */
  def v(name: String): String = s"($name:num)"

  lazy val eqImpTheorem: R[Kernel.Thm] = eqImp
  lazy val notLeTheorem: R[Kernel.Thm] = notLe

  def num(text: String): R[Kernel.Thm] = prop(text).flatMap(semiring.prove)

  def assumed(text: String): R[(Term, Kernel.Thm)] =
    for {
      term <- prop(text)
      held <- LogicError.lift(Kernel.assume(term))
    } yield (term, held)

  /** `l = r` when beta-normalising both sides meets. */
  def byBeta(goal: Term): R[Kernel.Thm] =
    for {
      sides <- Term.destEq(goal).toRight(NotOfForm("an equation", goal))
      left <- Conv.betaNormalise(sides._1)
      right <- Conv.betaNormalise(sides._2)
      back <- Conv.sym(right)
      out <- Conv.trans(left, back)
    } yield out

  /* ------------------------------------------------------------ propositional */

  /**
   * `(a = b) = ((a ==> b) /\ (b ==> a))` for propositions: the propositional procedure reads an
   * equation between propositions as an atom, so a goal about one goes to it through this.
   */
  def eqImp: R[Kernel.Thm] = {
    val a = Term.variable("a", Type.Bool)
    val b = Term.variable("b", Type.Bool)
    for {
      eqT <- prop("(a:bool) = (b:bool)")
      impT <- prop("((a:bool) ==> (b:bool)) /\\ (b ==> a)")
      e <- LogicError.lift(Kernel.assume(eqT))
      aa <- LogicError.lift(Kernel.assume(a))
      bb <- LogicError.lift(Kernel.assume(b))
      ab <- LogicError.lift(Kernel.eqMp(e, aa))
      ba <- Conv.sym(e).flatMap(s => LogicError.lift(Kernel.eqMp(s, bb)))
      forward <- for { i1 <- rules.disch(a, ab); i2 <- rules.disch(b, ba); out <- conj(i1, i2) } yield out
      h <- LogicError.lift(Kernel.assume(impT))
      parts <- split(h)
      b1 <- rules.mp(parts(0), aa)
      a1 <- rules.mp(parts(1), bb)
      back = Kernel.deductAntisym(a1, b1)
      out <- gen(Kernel.deductAntisym(back, forward), a, b)
    } yield out
  }

  lazy val propositional: Propositional = Propositional.over(classical, logic)

  /** `goal` from `premises` by the propositional procedure, equations between propositions opened. */
  def tauto(premises: Seq[Kernel.Thm], goal: Term): R[Kernel.Thm] =
    for {
      rule <- eqImpTheorem
      opened <- premises.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, q) =>
        for { done <- acc; o <- rw(rule, q) } yield done :+ o
      }
      out <- rewriting(Seq(rule), goal) { g =>
        for {
          implication <- opened.foldRight[R[Term]](Right(g))((q, acc) => acc.flatMap(logic.mkImp(q.conclusion, _)))
          proved <- propositional.prove(implication)
          out <- mp(proved, opened*)
        } yield out
      }
    } yield out

  /* ------------------------------------------------------------ order over num */

  def instance(text: String, binds: (String, Term)*): R[Term] =
    for {
      template <- prop(text)
      out <- substitute(binds.map { case (name, term) => Term.variable(name, Numbers) -> term }.toMap, template)
    } yield out

  def comparison(term: Term): Option[(String, Term, Term)] = term match {
    case App(App(Const(name, _), a), b) if name == Peano.StrictOrder || name == Peano.NonStrictOrder => Some((name, a, b))
    case _ => None
  }

  lazy val embedding: R[Vector[Kernel.Thm]] =
    Vector("NUM_REAL_ADD", "NUM_REAL_MUL", "NUM_REAL_SUC", "NUM_REAL_ZERO", "NUM_REAL_ONE", "NUM_REAL_BIT0", "NUM_REAL_BIT1")
      .foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((acc, n) => for { done <- acc; f <- fact(n) } yield done :+ f)

  /** `thm` with the embedding pushed through every operation and numeral, to a fixed point: a numeral opens in several passes. */
  def embedded(thm: Kernel.Thm, eqs: Vector[Kernel.Thm]): R[Kernel.Thm] =
    eqs.foldLeft[R[Kernel.Thm]](Right(thm))((acc, e) => acc.flatMap(th => rw(e, th))).flatMap { once =>
      if (once.conclusion == thm.conclusion) Right(once) else embedded(once, eqs)
    }

  /** A fact over the naturals carried to the reals: `a < b` as `real a + 1 <= real b`. */
  def lifted(thm: Kernel.Thm): R[Vector[Kernel.Thm]] =
    logic.destConj(thm.conclusion) match {
      case Some(_) =>
        for {
          l <- rules.conjElim1(thm).flatMap(lifted)
          r <- rules.conjElim2(thm).flatMap(lifted)
        } yield l ++ r
      case None =>
        comparison(thm.conclusion) match {
          case Some((name, a, b)) =>
            val (lemma, text) =
              if (name == Peano.StrictOrder) ("NUM_REAL_LT", "(a:num) < (b:num) ==> real_of_num a + 1 <= real_of_num b")
              else ("NUM_REAL_LE", "(a:num) <= (b:num) ==> real_of_num a <= real_of_num b")
            for {
              target <- instance(text, "a" -> a, "b" -> b)
              implication <- fact(lemma).flatMap(rules.specToReduced(_, target))
              out <- mp(implication, thm)
            } yield Vector(out)
          case None =>
            Term.destEq(thm.conclusion) match {
              case Some((a, _)) if Term.typeOf(a) == Numbers =>
                for {
                  realOf <- LogicError.lift(theory.constant(Peano.EmbeddingName, Type.fun(Numbers, Reals)))
                  out <- Conv.apTerm(realOf, thm)
                } yield Vector(out)
              case _ if onReals(thm.conclusion) => Right(Vector(thm))
              case _ => Left(NotOfForm("a comparison of naturals", thm.conclusion))
            }
        }
    }

  /** A comparison or an equation between reals, passed to `Linarith` as it is. */
  def onReals(term: Term): Boolean = term match {
    case App(App(Const(name, _), _), _) if name == Real.NonStrictOrder || name == Real.Order => true
    case _ => Term.destEq(term).exists(e => Term.typeOf(e._1) == Reals)
  }

  /** A comparison of naturals, or a conjunction of them, from comparisons of naturals, by `Linarith` over their images. */
  def numLin(facts: Seq[Kernel.Thm], goal: Term): R[Kernel.Thm] =
    logic.destConj(goal) match {
      case Some((l, r)) => for { a <- numLin(facts, l); b <- numLin(facts, r); out <- conj(a, b) } yield out
      case None if Term.destEq(goal).exists(e => Term.typeOf(e._1) == Numbers) =>
        val (a, b) = Term.destEq(goal).get
        for {
          up <- instance("(a:num) <= (b:num)", "a" -> a, "b" -> b).flatMap(numLin(facts, _))
          down <- instance("(b:num) <= (a:num)", "a" -> a, "b" -> b).flatMap(numLin(facts, _))
          anti <- instance("(a:num) <= (b:num) /\\ b <= a ==> a = b", "a" -> a, "b" -> b)
            .flatMap(tg => fact("NUM_LE_ANTISYM").flatMap(rules.specToReduced(_, tg)))
          out <- conj(up, down).flatMap(mp(anti, _))
        } yield out
      case None =>
        for {
          parts <- comparison(goal).toRight(NotOfForm("a comparison of naturals", goal))
          (name, a, b) = parts
          eqs <- embedding
          reals <- facts.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((acc, f) =>
            for { done <- acc; l <- lifted(f); e <- l.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((a2, g) =>
              for { d <- a2; h <- embedded(g, eqs) } yield d :+ h) } yield done ++ e)
          out <-
            if (name == Peano.StrictOrder)
              for {
                target <- instance("real_of_num (SUC (a:num)) <= real_of_num (b:num)", "a" -> a, "b" -> b)
                onReals <- onImages(eqs, reals, target)
                back <- instance("real_of_num (SUC (a:num)) <= real_of_num (b:num) ==> SUC a <= b", "a" -> a, "b" -> b)
                  .flatMap(tg => fact("NUM_REAL_LE_BACK").flatMap(rules.specToReduced(_, tg)))
                le <- mp(back, onReals)
                below <- instance("(a:num) < SUC a", "a" -> a).flatMap(tg => fact("NUM_LT_SUC").flatMap(rules.specToReduced(_, tg)))
                chain <- instance("(a:num) < SUC a /\\ SUC a <= (b:num) ==> a < b", "a" -> a, "b" -> b)
                  .flatMap(tg => fact("NUM_LT_LE_TRANS").flatMap(rules.specToReduced(_, tg)))
                both <- conj(below, le)
                out <- mp(chain, both)
              } yield out
            else
              for {
                target <- instance("real_of_num (a:num) <= real_of_num (b:num)", "a" -> a, "b" -> b)
                onReals <- onImages(eqs, reals, target)
                back <- instance("real_of_num (a:num) <= real_of_num (b:num) ==> a <= b", "a" -> a, "b" -> b)
                  .flatMap(tg => fact("NUM_REAL_LE_BACK").flatMap(rules.specToReduced(_, tg)))
                out <- mp(back, onReals)
              } yield out
        } yield out
    }

  /** `goal` over the reals by `Linarith`, after the embedding, with every image of a natural known to be non-negative. */
  def onImages(eqs: Vector[Kernel.Thm], facts: Vector[Kernel.Thm], goal: Term): R[Kernel.Thm] =
    rewriting(eqs, goal) { g =>
      val atoms = (facts.map(_.conclusion) :+ g).flatMap(images).distinct
      for {
        nonneg <- atoms.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((acc, w) =>
          for {
            done <- acc
            f <- instance("(0:real) <= real_of_num (a:num)", "a" -> w).flatMap(tg => fact("NUM_REAL_NONNEG").flatMap(rules.specToReduced(_, tg)))
          } yield done :+ f)
        out <- linT(facts ++ nonneg, g)
      } yield out
    }

  /** Every argument of the embedding of the naturals in `term`. */
  def images(term: Term): Vector[Term] = term match {
    case App(Const(name, _), a) if name == Peano.EmbeddingName => Vector(a)
    case App(f, a) => images(f) ++ images(a)
    case Abs(_, _) => Vector.empty
    case _ => Vector.empty
  }

  def numLinText(facts: Seq[Kernel.Thm], goal: String): R[Kernel.Thm] = prop(goal).flatMap(numLin(facts, _))

  /* ------------------------------------------------------------ the step in signs */

  def atReals(thm: Kernel.Thm): Kernel.Thm = Kernel.instType(Map(Classical.TypeVariable -> Reals), thm)

  /* ------------------------------------------------------------ bits */

  def two: R[Kernel.Thm] = numLinText(Seq.empty, "(0:num) < 2")

  /** `goal` when rewriting left exactly `held`. */
  def landsOn(held: Kernel.Thm)(goal: Term): R[Kernel.Thm] =
    if (goal == held.conclusion) Right(held) else Left(NotOfForm("the fact the rewriting was to reach", goal))

  /** `~(0 = 1)` over the naturals. */
  def zeroNotOne: R[Kernel.Thm] =
    for {
      held <- assumed("(0:num) = SUC 0")
      (eqT, eq) = held
      absurd <- for {
        flipped <- Conv.sym(eq)
        not <- at(fact("NUM_SUC_NOT_ZERO"), "~(SUC 0 = 0)")
        out <- rules.notElim(not, flipped)
      } yield out
      refuted <- rules.notIntro(eqT, absurd)
      out <- fact("NUM_ONE_SUC").flatMap(Conv.sym).flatMap(rw(_, refuted))
    } yield out

  /** `b = 0 \/ b = 1` from `b < 2`. */
  def binary(b: String, lt: Kernel.Thm): R[Kernel.Thm] =
    for {
      lt2 <- numLinText(Seq(lt), s"$b < SUC (SUC 0)")
      split_ <- at(fact("NUM_LT_SUC_CASES"), s"$b < SUC (SUC 0) ==> $b < SUC 0 \\/ $b = SUC 0").flatMap(mp(_, lt2))
      left <- for {
        h <- assumed(s"$b < SUC 0")
        z <- numLinText(Seq(h._2), s"$b = 0")
        d <- prop(s"$b = 1").flatMap(rules.disjIntro1(_, z))
      } yield d
      right <- for {
        h <- assumed(s"$b = SUC 0")
        e <- fact("NUM_ONE_SUC").flatMap(Conv.sym).flatMap(rw(_, h._2))
        d <- prop(s"$b = 0").flatMap(rules.disjIntro2(_, e))
      } yield d
      out <- rules.disjElim(split_, left, right)
    } yield out

  /* ------------------------------------------------------------ deciding conditionals */

  /** Every locally closed `COND b x y` in `term`, outside binders. */
  def conditionals(term: Term): Vector[Term] = term match {
    case c @ App(App(App(Const(name, _), b), x), y) if name == Classical.Conditional =>
      (if (Term.isLocallyClosed(c)) Vector(c) else Vector.empty) ++ conditionals(b) ++ conditionals(x) ++ conditionals(y)
    case App(f, a) => conditionals(f) ++ conditionals(a)
    case _ => Vector.empty
  }

  /** `COND b x y = x` or `= y`, when `literals` decide `b`; `None` when they do not. */
  def condValue(cond: Term, literals: Seq[Kernel.Thm]): R[Option[Kernel.Thm]] = cond match {
    case App(App(App(_, b), x), y) =>
      val ty = Term.typeOf(x)
      def at_(name: String, premise: Term, holds: Kernel.Thm, value: Term): R[Kernel.Thm] =
        for {
          eq <- LogicError.lift(Term.eq(cond, value))
          target <- logic.mkImp(premise, eq)
          out <- fact(name).map(Kernel.instType(Map(Classical.TypeVariable -> ty), _)).flatMap(rules.specToReduced(_, target)).flatMap(mp(_, holds))
        } yield out
      val reflexive = Term.destEq(b).collect { case (l, r) if l == r => Kernel.refl(l) }
      reflexive.orElse(tauto(literals, b).toOption) match {
        case Some(holds) => at_("COND_TRUE", b, holds, x).map(Some(_))
        case None =>
          logic.mkNot(b).flatMap { nb =>
            tauto(literals, nb) match {
              case Right(refuted) => at_("COND_FALSE", nb, refuted, y).map(Some(_))
              case Left(_) => Right(None)
            }
          }
      }
    case other => Left(NotOfForm("a conditional", other))
  }

  /** `goal` with every conditional `literals` decide replaced by its branch, then closed by `close`. */
  def deciding(literals: Seq[Kernel.Thm])(close: Term => R[Kernel.Thm])(goal: Term): R[Kernel.Thm] =
    conditionals(goal).distinct.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, c) =>
      for { done <- acc; v <- condValue(c, literals) } yield done ++ v.toVector
    }.flatMap { values =>
      if (values.isEmpty) close(goal) else rewriting(values, goal)(deciding(literals)(close))
    }

  /** `goal` in every case of the propositions `atoms`, each closed by `close` from the literals of its case. */
  def byCases(atoms: List[Term], literals: Vector[Kernel.Thm] = Vector.empty)(close: Vector[Kernel.Thm] => Term => R[Kernel.Thm])(goal: Term): R[Kernel.Thm] =
    atoms match {
      case Nil => close(literals)(goal)
      case p :: rest =>
        for {
          np <- logic.mkNot(p)
          yes <- LogicError.lift(Kernel.assume(p)).flatMap(h => byCases(rest, literals :+ h)(close)(goal))
          no <- LogicError.lift(Kernel.assume(np)).flatMap(h => byCases(rest, literals :+ h)(close)(goal))
          out <- classical.cases(p, yes, no)
        } yield out
    }

  /** An identity over the reals after beta and the embedding of the naturals. */
  def arithmetic(goal: Term): R[Kernel.Thm] =
    for {
      eqs <- embedding
      out <- rewriting(eqs, goal)(g => betaThen(g)(driver.identity))
    } yield out

  def betaThen(goal: Term)(close: Term => R[Kernel.Thm]): R[Kernel.Thm] =
    for {
      e <- Conv.betaNormalise(goal)
      g <- Term.destEq(e.conclusion).map(_._2).toRight(NotOfForm("an equation", e.conclusion))
      proved <- close(g)
      back <- Conv.sym(e)
      out <- LogicError.lift(Kernel.eqMp(back, proved))
    } yield out

  /**
   * `Sum F bound = Sum G bound` for `sum` the term `Sum F bound`, from `F s = G s` at every `s` below
   * `bound`: `facts` gives what is known at such an `s`, the conditionals they decide are decided, and
   * the rest is an identity.
   */
  def belowBound(sum: Term, target: String, bound: String)(
    facts: (String, Kernel.Thm) => R[(Seq[Kernel.Thm], Seq[Kernel.Thm], List[Term])]
  ): R[Kernel.Thm] =
    sum match {
      case App(App(_, lhsFn), _) =>
        val sv = Term.variable("sb", Numbers)
        for {
          rhsFn <- term(target, Type.fun(Numbers, Reals))
          held <- assumed(s"(sb:num) < $bound")
          (bT, b) = held
          known <- facts("(sb:num)", b)
          (rewrites, literals, splits) = known
          left <- LogicError.lift(Term.app(lhsFn, sv))
          right <- LogicError.lift(Term.app(rhsFn, sv))
          pointGoal <- LogicError.lift(Term.eq(left, right))
          normal <- Conv.betaNormalise(pointGoal)
          normalGoal <- Term.destEq(normal.conclusion).map(_._2).toRight(NotOfForm("an equation", normal.conclusion))
          pointwise <- rewriting(rewrites, normalGoal)(byCases(splits, literals.toVector)(lits => orAbsurd(lits)(deciding(lits)(arithmetic))))
          general <- rules.disch(bT, pointwise).flatMap(gen(_, sv))
          sumR <- term(s"Sum ($target) ($bound)", Reals)
          eq <- LogicError.lift(Term.eq(sum, sumR))
          target_ <- logic.mkImp(general.conclusion, eq)
          congruent <- fact("SUM_CONGRUENCE_BELOW").flatMap(rules.specToReduced(_, target_))
          out <- mp(congruent, general)
        } yield out
      case other => Left(NotOfForm("a sum", other))
    }

  /** `goal` by `close`, or from literals that cannot all hold. */
  def orAbsurd(literals: Seq[Kernel.Thm])(close: Term => R[Kernel.Thm])(goal: Term): R[Kernel.Thm] =
    close(goal).left.flatMap { refusal =>
      (for {
        falsity <- prop("F")
        contra <- tauto(literals, falsity)
        out <- rules.falsityElim(goal, contra)
      } yield out).left.map(_ => refusal)
    }

  def numClose(goal: Term): R[Kernel.Thm] = byBeta(goal).orElse(semiring.prove(goal))

  /** `(0 = 1) = F` over the naturals. */
  def zeroOneFalse: R[Kernel.Thm] =
    for {
      eqT <- prop("(0:num) = 1")
      falsity <- prop("F")
      apart <- zeroNotOne
      fromFalse <- LogicError.lift(Kernel.assume(falsity)).flatMap(rules.falsityElim(eqT, _))
      toFalse <- LogicError.lift(Kernel.assume(eqT)).flatMap(rules.notElim(apart, _))
    } yield Kernel.deductAntisym(fromFalse, toFalse)

  /** `(1 = 1) = T`. */
  def oneOneTrue: R[Kernel.Thm] = nm("1").flatMap(one => rules.eqTruthIntro(Kernel.refl(one)))

  /** The conclusion of an implication, past its antecedents. */
  def goalConclusion(t: Term): Term = logic.destImp(t).map(e => goalConclusion(e._2)).getOrElse(t)

  /** `thm` with every conditional in it that `literals` decide replaced by its branch. */
  def decidedIn(thm: Kernel.Thm, literals: Seq[Kernel.Thm]): R[Kernel.Thm] =
    conditionals(thm.conclusion).distinct.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, c) =>
      for { done <- acc; v <- condValue(c, literals) } yield done ++ v.toVector
    }.flatMap { values =>
      if (values.isEmpty) Right(thm)
      else values.foldLeft[R[Kernel.Thm]](Right(thm))((acc, e) => acc.flatMap(rw(e, _))).flatMap(decidedIn(_, literals))
    }

  /** `n < m` from `~(m <= n)`. */
  def notLe: R[Kernel.Thm] = {
    val (mv, nv) = (Term.variable("m", Numbers), Term.variable("n", Numbers))
    for {
      held <- assumed("~((m:num) <= (n:num))")
      (hT, h) = held
      total <- at(fact("NUM_LT_TOTAL"), "(n:num) < (m:num) \\/ n = m \\/ m < n")
      wanted <- prop("(n:num) < (m:num)")
      lt <- assumed("(n:num) < (m:num)")
      eqCase <- for {
        e <- assumed("(n:num) = (m:num)")
        le <- numLinText(Seq(e._2), "(m:num) <= (n:num)")
        out <- rules.notElim(h, le).flatMap(rules.falsityElim(wanted, _))
      } yield out
      gtCase <- for {
        g <- assumed("(m:num) < (n:num)")
        le <- numLinText(Seq(g._2), "(m:num) <= (n:num)")
        out <- rules.notElim(h, le).flatMap(rules.falsityElim(wanted, _))
      } yield out
      rest <- prop("(n:num) = (m:num) \\/ (m:num) < n")
      inner <- rules.disjElim(LogicError.lift(Kernel.assume(rest)).toOption.get, eqCase, gtCase)
      out <- rules.disjElim(total, lt._2, inner).flatMap(rules.disch(hT, _)).flatMap(gen(_, mv, nv))
    } yield out
  }

  /** `0 < m` from `~(m = 0)`. */
  def positiveOf(nonzero: Kernel.Thm, M: String): R[Kernel.Thm] =
    for {
      held <- assumed(s"$M <= 0")
      zero <- at(fact("NUM_LE_ZERO"), s"$M <= 0 ==> $M = 0").flatMap(mp(_, held._2))
      contra <- rules.notElim(nonzero, zero)
      refuted <- rules.notIntro(held._1, contra)
      out <- notLeTheorem.flatMap(at(_, s"~($M <= 0) ==> 0 < $M")).flatMap(mp(_, refuted))
    } yield out

  /** `!a b. H ==> C` for a goal of that shape, the hypothesis assumed. */
  def underHypsAll(goal: Term, a: FVar, b: FVar)(body: (Kernel.Thm, Term) => R[Kernel.Thm]): R[Kernel.Thm] =
    for {
      stripped <- rules.specAll(LogicError.lift(Kernel.assume(goal)).toOption.get, List(a, b)).map(_.conclusion)
      parts <- logic.destImp(stripped).toRight(NotOfForm("an implication", stripped))
      h <- LogicError.lift(Kernel.assume(parts._1))
      proved <- body(h, parts._2)
      out <- rules.disch(parts._1, proved).flatMap(gen(_, a, b))
    } yield out
}
