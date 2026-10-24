package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Steps over the naturals and over propositions that the derivations beside `Complex` share:
 * `RuleThirty`, `RuleFamily`, `Gilbreath` and `Triangular`. Each is a line or two over `ComplexKit` and decides nothing a
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
 * `~(m <= n)`. Six more are about remainders modulo a power of two and the bits they hold, which
 * `RuleThirty` and `Triangular` both need: `modSplitTheorem` and `modEqSplitTheorem` split a
 * remainder modulo `2^(k + 1)` into the one modulo `2^k` and bit `k`, `bitAboveTheorem` and
 * `bitTopTheorem` read bit `k` below and just above `2^k`, and `modOneTheorem` and
 * `modModTheorem` are the remainder modulo 1 and the remainder of a remainder. Eight are about
 * halving, which `RuleThirty` and `RuleFamily` both need: `modTwoShiftTheorem`, `modDoubleTheorem`
 * and `divModShiftTheorem` move a remainder through `2 m + e`, `bitHalveTheorem`, `divOneTheorem`
 * and `bitLowTheorem` read a bit of a half, `condBelowTwoTheorem` bounds a bit written with `COND`,
 * and `belowPowerTheorem` is `m < 2^m`.
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

  /* ------------------------------------------------------------ remainders modulo a power of two */

  /** Bit `j` of `y`. */
  def bitText(j: String, y: String): String = s"NUM_MOD (NUM_DIV ($y) (NUM_POW 2 ($j))) 2 = 1"

  lazy val modSplitTheorem: R[Kernel.Thm] = modSplit
  lazy val modEqSplitTheorem: R[Kernel.Thm] = modEqSplit
  lazy val bitAboveTheorem: R[Kernel.Thm] = bitAbove
  lazy val bitTopTheorem: R[Kernel.Thm] = bitTop
  lazy val modOneTheorem: R[Kernel.Thm] = modOne
  lazy val modModTheorem: R[Kernel.Thm] = modMod

  /** The remainder modulo `2^(SUC k)` is the remainder modulo `2^k` plus bit `k` in its place. */
  def modSplit: R[Kernel.Thm] = {
    val yv = Term.variable("y", Numbers); val kv = Term.variable("k", Numbers)
    val M = "NUM_POW 2 (k:num)"; val Q = s"NUM_DIV (y:num) ($M)"; val Rr = s"NUM_MOD (y:num) ($M)"
    val B = s"NUM_MOD ($Q) 2"; val Q2 = s"NUM_DIV ($Q) 2"; val P2 = "NUM_POW 2 (SUC (k:num))"
    for {
      dm1 <- at(fact("NUM_DIV_MOD"), s"$M * $Q + $Rr = y")
      dm2 <- at(fact("NUM_DIV_MOD"), s"2 * $Q2 + $B = $Q")
      positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $M").flatMap(mp(_, t2)))
      rLt <- at(fact("NUM_MOD_LT"), s"0 < $M ==> $Rr < $M").flatMap(mp(_, positive))
      bLt <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> $B < 2").flatMap(mp(_, t2)))
      powSuc <- at(fact("NUM_POW_SUC"), s"$P2 = $M * 2")
      regroup <- num(s"$M * (2 * $Q2 + $B) + $Rr = $M * 2 * $Q2 + ($Rr + $M * $B)")
      split_ <- rw(dm2, regroup).flatMap(rw(dm1, _)).flatMap(e => Conv.sym(powSuc).flatMap(rw(_, e)))
      goalT <- prop(s"$Rr + $M * $B < $P2")
      mulZero <- at(fact("NUM_MUL_ZERO"), s"$M * 0 = 0")
      mulOne <- num(s"$M * 1 = $M")
      bound <- for {
        either <- binary(B, bLt)
        zero <- for {
          h <- assumed(s"$B = 0")
          out <- rewriting(Seq(h._2, mulZero), goalT)(numLin(Seq(rLt, powSuc), _))
        } yield out
        unit <- for {
          h <- assumed(s"$B = 1")
          out <- rewriting(Seq(h._2, mulOne), goalT)(numLin(Seq(rLt, powSuc), _))
        } yield out
        out <- rules.disjElim(either, zero, unit)
      } yield out
      unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
        s"y = $P2 * $Q2 + ($Rr + $M * $B) /\\ $Rr + $M * $B < $P2 ==> $Q2 = NUM_DIV y ($P2) /\\ $Rr + $M * $B = NUM_MOD y ($P2)")
      out <- conj(split_, bound).flatMap(mp(unique, _)).flatMap(rules.conjElim2).flatMap(Conv.sym).flatMap(gen(_, yv, kv))
    } yield out
  }

  /** Two numbers agree modulo `2^(SUC k)` exactly when they agree modulo `2^k` and at bit `k`. */
  def modEqSplit: R[Kernel.Thm] = {
    val (yv, nv, kv) = (Term.variable("y", Numbers), Term.variable("n", Numbers), Term.variable("k", Numbers))
    val M = "NUM_POW 2 (k:num)"; val P2 = "NUM_POW 2 (SUC (k:num))"
    def Rr(z: String) = s"NUM_MOD ($z:num) ($M)"
    def B(z: String) = s"NUM_MOD (NUM_DIV ($z:num) ($M)) 2"
    val E = s"NUM_MOD (y:num) ($P2) = NUM_MOD (n:num) ($P2)"
    val C = s"${Rr("y")} = ${Rr("n")} /\\ ((${B("y")} = 1) = (${B("n")} = 1))"
    for {
      sy <- at(modSplitTheorem, s"NUM_MOD (y:num) ($P2) = ${Rr("y")} + $M * ${B("y")}")
      sn <- at(modSplitTheorem, s"NUM_MOD (n:num) ($P2) = ${Rr("n")} + $M * ${B("n")}")
      positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $M").flatMap(mp(_, t2)))
      lowY <- at(fact("NUM_MOD_LT"), s"0 < $M ==> ${Rr("y")} < $M").flatMap(mp(_, positive))
      lowN <- at(fact("NUM_MOD_LT"), s"0 < $M ==> ${Rr("n")} < $M").flatMap(mp(_, positive))
      bY <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> ${B("y")} < 2").flatMap(mp(_, t2)))
      bN <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> ${B("n")} < 2").flatMap(mp(_, t2)))
      forward <- for {
        h <- assumed(E)
        sums <- rw(sy, h._2).flatMap(rw(sn, _))
        swapY <- num(s"${Rr("y")} + $M * ${B("y")} = $M * ${B("y")} + ${Rr("y")}")
        swapN <- num(s"${Rr("n")} + $M * ${B("n")} = $M * ${B("n")} + ${Rr("n")}")
        ordered <- rw(swapY, sums).flatMap(rw(swapN, _))
        unique <- at(fact("NUM_DIVISION_UNIQUE"),
          s"$M * ${B("y")} + ${Rr("y")} = $M * ${B("n")} + ${Rr("n")} /\\ ${Rr("y")} < $M /\\ ${Rr("n")} < $M ==> " +
            s"${B("y")} = ${B("n")} /\\ ${Rr("y")} = ${Rr("n")}")
        parts <- conjs(ordered, lowY, lowN).flatMap(mp(unique, _)).flatMap(split)
        bits <- prop(s"(${B("y")} = 1) = (${B("n")} = 1)").flatMap(g => rewriting(Seq(parts(0)), g)(byBeta))
        out <- conj(parts(1), bits)
      } yield out
      backward <- for {
        h <- assumed(C)
        parts <- split(h._2)
        goal <- prop(E)
        zeroOne <- zeroNotOne
        equalBits <- for {
          ey <- binary(B("y"), bY)
          en <- binary(B("n"), bN)
          wanted <- prop(s"${B("y")} = ${B("n")}")
          same = (a: Kernel.Thm, b: Kernel.Thm) => rewriting(Seq(a, b), wanted)(byBeta)
          mixed = (a: Kernel.Thm, b: Kernel.Thm) =>
            for {
              iff <- rw(a, parts(1)).flatMap(rw(b, _))
              one <- nm("1").map(Conv.refl)
              zeroIsOne <- LogicError.lift(Kernel.eqMp(iff, one)).orElse(Conv.sym(iff).flatMap(s => LogicError.lift(Kernel.eqMp(s, one))))
              contra <- rules.notElim(zeroOne, zeroIsOne)
              out <- rules.falsityElim(wanted, contra)
            } yield out
          out <- for {
            y0 <- assumed(s"${B("y")} = 0"); y1 <- assumed(s"${B("y")} = 1")
            n0 <- assumed(s"${B("n")} = 0"); n1 <- assumed(s"${B("n")} = 1")
            c00 <- same(y0._2, n0._2); c01 <- mixed(y0._2, n1._2)
            c10 <- mixed(y1._2, n0._2); c11 <- same(y1._2, n1._2)
            whenY0 <- rules.disjElim(en, c00, c01)
            whenY1 <- rules.disjElim(en, c10, c11)
            out <- rules.disjElim(ey, whenY0, whenY1)
          } yield out
        } yield out
        out <- rewriting(Seq(sy, sn, parts(0), equalBits), goal)(byBeta)
      } yield out
      out <- gen(Kernel.deductAntisym(backward, forward), yv, nv, kv)
    } yield out
  }

  /** Below `2^k`, bit `k` is off. */
  def bitAbove: R[Kernel.Thm] = {
    val kv = Term.variable("k", Numbers)
    val c = Term.variable("c", Numbers)
    for {
      held <- assumed("(c:num) < NUM_POW 2 (k:num)")
      (belowT, below) = held
      zero <- at(fact("NUM_DIV_MOD_BELOW"), "(c:num) < NUM_POW 2 (k:num) ==> NUM_DIV c (NUM_POW 2 k) = 0 /\\ NUM_MOD c (NUM_POW 2 k) = c")
        .flatMap(mp(_, below)).flatMap(rules.conjElim1)
      modZero <- two.flatMap(t2 => at(fact("NUM_DIV_MOD_BELOW"), "(0:num) < 2 ==> NUM_DIV 0 2 = 0 /\\ NUM_MOD 0 2 = 0").flatMap(mp(_, t2)))
        .flatMap(rules.conjElim2)
      apart <- zeroNotOne
      goal <- prop(s"~(${bitText("k:num", "c:num")})")
      closed <- rewriting(Seq(zero, modZero), goal)(landsOn(apart))
      out <- rules.disch(belowT, closed).flatMap(gen(_, kv, c))
    } yield out
  }

  /** `2^k + c` has bit `k` on, for `c` below `2^k`. */
  def bitTop: R[Kernel.Thm] = {
    val kv = Term.variable("k", Numbers)
    val c = Term.variable("c", Numbers)
    for {
      held <- assumed("(c:num) < NUM_POW 2 (k:num)")
      (belowT, below) = held
      step <- at(fact("NUM_DIV_MOD_STEP"),
        "(c:num) < NUM_POW 2 (k:num) ==> NUM_DIV (NUM_POW 2 k + c) (NUM_POW 2 k) = SUC 0 /\\ NUM_MOD (NUM_POW 2 k + c) (NUM_POW 2 k) = c")
        .flatMap(mp(_, below)).flatMap(rules.conjElim1)
      oneBelow <- numLinText(Seq.empty, "SUC 0 < 2")
      modOne <- at(fact("NUM_DIV_MOD_BELOW"), "SUC 0 < 2 ==> NUM_DIV (SUC 0) 2 = 0 /\\ NUM_MOD (SUC 0) 2 = SUC 0")
        .flatMap(mp(_, oneBelow)).flatMap(rules.conjElim2)
      one <- fact("NUM_ONE_SUC").flatMap(Conv.sym)
      goal <- prop(bitText("k:num", "NUM_POW 2 (k:num) + (c:num)"))
      closed <- rewriting(Seq(step, modOne), goal)(landsOn(one))
      out <- rules.disch(belowT, closed).flatMap(gen(_, kv, c))
    } yield out
  }

  /** `NUM_MOD x 1 = 0`. */
  def modOne: R[Kernel.Thm] =
    for {
      unit <- numLinText(Seq.empty, "(0:num) < SUC 0")
      lt <- at(fact("NUM_MOD_LT"), "(0:num) < SUC 0 ==> NUM_MOD (x:num) (SUC 0) < SUC 0").flatMap(mp(_, unit))
      out <- numLinText(Seq(lt), "NUM_MOD (x:num) (SUC 0) = 0").flatMap(gen(_, Term.variable("x", Numbers)))
    } yield out

  /** A residue modulo `2^k` is its own residue. */
  def modMod: R[Kernel.Thm] = {
    val (nv, kv) = (Term.variable("n", Numbers), Term.variable("k", Numbers))
    val M = "NUM_POW 2 (k:num)"; val Rr = s"NUM_MOD (n:num) ($M)"
    for {
      positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $M").flatMap(mp(_, t2)))
      lt <- at(fact("NUM_MOD_LT"), s"0 < $M ==> $Rr < $M").flatMap(mp(_, positive))
      out <- at(fact("NUM_DIV_MOD_BELOW"), s"$Rr < $M ==> NUM_DIV ($Rr) ($M) = 0 /\\ NUM_MOD ($Rr) ($M) = $Rr")
        .flatMap(mp(_, lt)).flatMap(rules.conjElim2).flatMap(gen(_, nv, kv))
    } yield out
  }

  /* ------------------------------------------------------------ halving, bits and the low remainder */

  lazy val modTwoShiftTheorem: R[Kernel.Thm] = modTwoShift
  lazy val bitHalveTheorem: R[Kernel.Thm] = bitHalve
  lazy val condBelowTwoTheorem: R[Kernel.Thm] = condBelowTwo
  lazy val modDoubleTheorem: R[Kernel.Thm] = modDouble
  lazy val divModShiftTheorem: R[Kernel.Thm] = divModShift
  lazy val belowPowerTheorem: R[Kernel.Thm] = belowPower
  lazy val divOneTheorem: R[Kernel.Thm] = divOne
  lazy val bitLowTheorem: R[Kernel.Thm] = bitLow

  /** `NUM_MOD (2 * a + q) 2 = NUM_MOD q 2`. */
  def modTwoShift: R[Kernel.Thm] = {
    val a = Term.variable("a", Numbers)
    val q = Term.variable("q", Numbers)
    for {
      dm <- at(fact("NUM_DIV_MOD"), "2 * NUM_DIV (q:num) 2 + NUM_MOD q 2 = q")
      regroup <- num("2 * (a:num) + (2 * NUM_DIV (q:num) 2 + NUM_MOD q 2) = 2 * (a + NUM_DIV q 2) + NUM_MOD q 2")
      split_ <- rw(dm, regroup)
      below <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), "(0:num) < 2 ==> NUM_MOD (q:num) 2 < 2").flatMap(mp(_, t2)))
      unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
        "2 * (a:num) + (q:num) = 2 * (a + NUM_DIV q 2) + NUM_MOD q 2 /\\ NUM_MOD q 2 < 2 ==> " +
          "a + NUM_DIV q 2 = NUM_DIV (2 * a + q) 2 /\\ NUM_MOD q 2 = NUM_MOD (2 * a + q) 2")
      parts <- conj(split_, below).flatMap(mp(unique, _)).flatMap(split)
      out <- Conv.sym(parts(1)).flatMap(gen(_, a, q))
    } yield out
  }

  /** Halving moves every bit down by one: `bit (SUC q) (2 m + e) = bit q m` for `e < 2`. */
  def bitHalve: R[Kernel.Thm] = {
    val (qv, mv, ev) = (Term.variable("q", Numbers), Term.variable("m", Numbers), Term.variable("e", Numbers))
    val P = "NUM_POW 2 (q:num)"
    val D = s"NUM_DIV (m:num) ($P)"; val M = s"NUM_MOD (m:num) ($P)"
    val n = "2 * (m:num) + (e:num)"
    for {
      held <- assumed("(e:num) < 2")
      (smallT, small) = held
      dm <- at(fact("NUM_DIV_MOD"), s"$P * $D + $M = m")
      positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $P").flatMap(mp(_, t2)))
      below <- at(fact("NUM_MOD_LT"), s"0 < $P ==> $M < $P").flatMap(mp(_, positive))
      powSuc <- at(fact("NUM_POW_SUC"), "NUM_POW 2 (SUC (q:num)) = NUM_POW 2 q * 2").flatMap(Conv.sym)
      regroup <- num(s"2 * ($P * $D + $M) + (e:num) = $P * 2 * $D + (2 * $M + e)")
      split_ <- rw(dm, regroup).flatMap(rw(powSuc, _))
      remainder <- numLinText(Seq(below, small), s"2 * $M + (e:num) < $P * 2").flatMap(rw(powSuc, _))
      unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
        s"$n = NUM_POW 2 (SUC q) * $D + (2 * $M + e) /\\ 2 * $M + e < NUM_POW 2 (SUC q) ==> " +
          s"$D = NUM_DIV ($n) (NUM_POW 2 (SUC q)) /\\ 2 * $M + e = NUM_MOD ($n) (NUM_POW 2 (SUC q))")
      quotient <- conj(split_, remainder).flatMap(mp(unique, _)).flatMap(rules.conjElim1).flatMap(Conv.sym)
      goal <- prop(s"(${bitText("SUC (q:num)", n)}) = (${bitText("q:num", "m:num")})")
      closed <- rewriting(Seq(quotient), goal)(byBeta)
      out <- rules.disch(smallT, closed).flatMap(gen(_, qv, mv, ev))
    } yield out
  }

  /** `COND b 1 0 < 2` over the naturals. */
  def condBelowTwo: R[Kernel.Thm] = {
    val b = Term.variable("b", Type.Bool)
    for {
      goal <- prop("COND (b:bool) 1 0 < (2:num)")
      out <- byCases(List(b))(lits => deciding(lits)(numLin(Seq.empty, _)))(goal).flatMap(gen(_, b))
    } yield out
  }

  /** `NUM_MOD (2 m + e) (2^(SUC k)) = 2 (NUM_MOD m (2^k)) + e` for `e < 2`. */
  def modDouble: R[Kernel.Thm] = {
    val (kv, mv, ev) = (Term.variable("k", Numbers), Term.variable("m", Numbers), Term.variable("e", Numbers))
    val P = "NUM_POW 2 (k:num)"; val P2 = "NUM_POW 2 (SUC (k:num))"
    val D = s"NUM_DIV (m:num) ($P)"; val Mm = s"NUM_MOD (m:num) ($P)"
    val n = "2 * (m:num) + (e:num)"
    for {
      held <- assumed("(e:num) < 2")
      (smallT, small) = held
      dm <- at(fact("NUM_DIV_MOD"), s"$P * $D + $Mm = m")
      positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $P").flatMap(mp(_, t2)))
      below <- at(fact("NUM_MOD_LT"), s"0 < $P ==> $Mm < $P").flatMap(mp(_, positive))
      powSuc <- at(fact("NUM_POW_SUC"), s"$P2 = $P * 2")
      regroup <- num(s"2 * ($P * $D + $Mm) + (e:num) = $P * 2 * $D + (2 * $Mm + e)")
      split_ <- rw(dm, regroup).flatMap(e => Conv.sym(powSuc).flatMap(rw(_, e)))
      bound <- numLinText(Seq(below, small, powSuc), s"2 * $Mm + (e:num) < $P2")
      unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
        s"$n = $P2 * $D + (2 * $Mm + e) /\\ 2 * $Mm + e < $P2 ==> $D = NUM_DIV ($n) ($P2) /\\ 2 * $Mm + e = NUM_MOD ($n) ($P2)")
      out <- conj(split_, bound).flatMap(mp(unique, _)).flatMap(rules.conjElim2).flatMap(Conv.sym)
        .flatMap(rules.disch(smallT, _)).flatMap(gen(_, kv, mv, ev))
    } yield out
  }

  /** Halving a residue modulo `2^(SUC k)` gives the residue of the half modulo `2^k`, and the low bit survives. */
  def divModShift: R[Kernel.Thm] = {
    val (nv, kv) = (Term.variable("n", Numbers), Term.variable("k", Numbers))
    val N = "(n:num)"; val P = "NUM_POW 2 (k:num)"; val P2 = "NUM_POW 2 (SUC (k:num))"
    val D = s"NUM_DIV $N 2"; val E = s"NUM_MOD $N 2"; val X = s"NUM_MOD $N ($P2)"
    for {
      dm <- at(fact("NUM_DIV_MOD"), s"2 * $D + $E = $N")
      lt <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> $E < 2").flatMap(mp(_, t2)))
      doubled <- at(modDoubleTheorem, s"$E < 2 ==> NUM_MOD (2 * $D + $E) ($P2) = 2 * NUM_MOD ($D) ($P) + $E").flatMap(mp(_, lt))
        .flatMap(rw(dm, _))
      unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
        s"$X = 2 * NUM_MOD ($D) ($P) + $E /\\ $E < 2 ==> NUM_MOD ($D) ($P) = NUM_DIV ($X) 2 /\\ $E = NUM_MOD ($X) 2")
      parts <- conj(doubled, lt).flatMap(mp(unique, _)).flatMap(split)
      a <- Conv.sym(parts(0)); b <- Conv.sym(parts(1))
      out <- conj(a, b).flatMap(gen(_, nv, kv))
    } yield out
  }

  /** `m < 2^m`. */
  def belowPower: R[Kernel.Thm] = {
    val mv = Term.variable("m", Numbers)
    for {
      body <- prop("(m:num) < NUM_POW 2 m")
      out <- induct(mv, body)(
        _ =>
          for {
            p0 <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
            out <- prop("(0:num) < NUM_POW 2 0").flatMap(numLin(Seq(p0), _))
          } yield out,
        (kk, hyp, _) => {
          val M = v(kk.name)
          for {
            ps <- at(fact("NUM_POW_SUC"), s"NUM_POW 2 (SUC $M) = NUM_POW 2 $M * 2")
            out <- prop(s"SUC $M < NUM_POW 2 (SUC $M)").flatMap(numLin(Seq(hyp, ps), _))
          } yield out
        }
      )
    } yield out
  }

  /** `NUM_DIV x 1 = x`. */
  def divOne: R[Kernel.Thm] =
    for {
      unit <- numLinText(Seq.empty, "(0:num) < SUC 0")
      eq <- numLinText(Seq.empty, "(x:num) = SUC 0 * x + 0")
      u <- at(fact("NUM_DIV_MOD_UNIQUE"), "(x:num) = SUC 0 * x + 0 /\\ 0 < SUC 0 ==> x = NUM_DIV x (SUC 0) /\\ 0 = NUM_MOD x (SUC 0)")
      out <- conj(eq, unit).flatMap(mp(u, _)).flatMap(rules.conjElim1).flatMap(Conv.sym).flatMap(gen(_, Term.variable("x", Numbers)))
    } yield out

  /** Bit 0 is the remainder by 2, and bit `SUC j` is bit `j` of the half. */
  def bitLow: R[Kernel.Thm] = {
    val (jv, xv) = (Term.variable("j", Numbers), Term.variable("x", Numbers))
    val X = "(x:num)"; val J = "(j:num)"
    for {
      powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
      zeroGoal <- prop(s"(${bitText("0", X)}) = (NUM_MOD $X 2 = 1)")
      divOne <- divOneTheorem
      zero <- rewriting(Seq(powZero, divOne), zeroGoal)(byBeta)
      dm <- at(fact("NUM_DIV_MOD"), s"2 * NUM_DIV $X 2 + NUM_MOD $X 2 = $X")
      lt <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> NUM_MOD $X 2 < 2").flatMap(mp(_, t2)))
      half <- at(bitHalveTheorem, s"NUM_MOD $X 2 < 2 ==> ((${bitText(s"SUC $J", s"2 * NUM_DIV $X 2 + NUM_MOD $X 2")}) = (${bitText(J, s"NUM_DIV $X 2")}))")
        .flatMap(mp(_, lt)).flatMap(rw(dm, _))
      halfAll <- gen(half, jv)
      out <- conj(zero, halfAll).flatMap(gen(_, xv))
    } yield out
  }
}
