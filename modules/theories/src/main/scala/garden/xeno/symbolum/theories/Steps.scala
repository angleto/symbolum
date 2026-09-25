package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The steps a hand derivation over `num` is made of, shared by the files that write one.
 *
 * `Euler` and `EuclidAlgorithm` both needed the same dozen moves: take an implication or an
 * equation apart, split on a proposition, read a conditional off under its test, close an
 * arithmetic identity with SEMIRING after rewriting both sides with ground equations. Written twice
 * they were two copies free to drift, so they are here, over the `Kit` `Freshman` already defines.
 * Nothing in this file can construct a theorem the kernel would not: each function is a sequence of
 * derived rules, and a caller that misuses one gets a refusal rather than a wrong theorem.
 *
 * `equate` is the one to read before reaching for it. It rewrites each side with the equations it
 * is given, then turns `SUC 0` into the numeral `1`, because SEMIRING reads a numeral and treats
 * `SUC 0` as an atom, and only then asks SEMIRING. The two passes are separate so that an equation
 * about `NUM_SUM f (SUC 0)` fires before its argument is renamed.
 */
private[theories] object Steps {
  type R[A] = Either[LogicError, A]
  type Kit = Freshman.Kit


  def imp(kit: Kit, t: Term): R[(Term, Term)] = kit.logic.destImp(t).toRight(NotOfForm("an implication", t))
  def disj(kit: Kit, t: Term): R[(Term, Term)] = kit.logic.destDisj(t).toRight(NotOfForm("a disjunction", t))
  def conj(kit: Kit, t: Term): R[(Term, Term)] = kit.logic.destConj(t).toRight(NotOfForm("a conjunction", t))
  def assume(t: Term): R[Kernel.Thm] = LogicError.lift(Kernel.assume(t))
  def eqTerm(a: Term, b: Term): R[Term] = LogicError.lift(Term.eq(a, b))
  def app(f: Term, args: Term*): R[Term] = LogicError.lift(Term.appAll(f, args.toList))
  def sides(t: Term): R[(Term, Term)] = Term.destEq(t).toRight(NotOfForm("an equation", t))

  /** Discharge in reverse, so `dischAll(List(a, b), th)` is `a ==> b ==> c`. */
  def dischAll(kit: Kit, hyps: List[Term], th: Kernel.Thm): R[Kernel.Thm] =
    hyps.reverse.foldLeft[R[Kernel.Thm]](Right(th))((acc, h) => acc.flatMap(kit.rules.disch(h, _)))

  def fresh(name: String, ty: Type, avoid: Kernel.Thm*): FVar =
    Conv.freshVariable(name, ty, avoid.flatMap(t => (t.conclusion +: t.hypotheses.toVector).flatMap(Term.freeVariables)).toSet)

  /** `left = right` by rewriting each side with ground equations, `SUC 0` to `1`, and SEMIRING. */
  def equate(kit: Kit, left: Term, right: Term, leftEqs: Vector[Kernel.Thm], rightEqs: Vector[Kernel.Thm]): R[Kernel.Thm] =
    for {
      toNumeral <- kit.fact("NUM_ONE_SUC").flatMap(Conv.sym)
      numeralRules <- Rewrite.Rule.all(kit.logic, Vector(toNumeral))
      leftRules <- Rewrite.Rule.all(kit.logic, leftEqs)
      rightRules <- Rewrite.Rule.all(kit.logic, rightEqs)
      leftMoved <- Rewrite.rewrite(leftRules, left)
      rightMoved <- Rewrite.rewrite(rightRules, right)
      leftTerm <- Limit.rightOf(leftMoved)
      rightTerm <- Limit.rightOf(rightMoved)
      leftNumeral <- Rewrite.rewrite(numeralRules, leftTerm)
      rightNumeral <- Rewrite.rewrite(numeralRules, rightTerm)
      leftFinal <- Limit.rightOf(leftNumeral)
      rightFinal <- Limit.rightOf(rightNumeral)
      middle <- eqTerm(leftFinal, rightFinal).flatMap(kit.semiring.prove)
      leftAll <- Conv.trans(leftMoved, leftNumeral)
      rightAll <- Conv.trans(rightMoved, rightNumeral)
      joined <- Conv.trans(leftAll, middle)
      back <- Conv.sym(rightAll)
      result <- Conv.trans(joined, back)
    } yield result

  /** `a = d` from `a = b`, `b = c`, `c = d`, in order. */
  def transAll(steps: Kernel.Thm*): R[Kernel.Thm] =
    steps.tail.foldLeft[R[Kernel.Thm]](Right(steps.head))((acc, s) => acc.flatMap(Conv.trans(_, s)))

  /** `lambda a = lambda b`, beta-reduced, from `a = b`. */
  def cong(lambda: Term, eq: Kernel.Thm): R[Kernel.Thm] = Conv.apTerm(lambda, eq).flatMap(Conv.betaSides)

  def ltSuc(kit: Kit, n: Term): R[Kernel.Thm] = kit.use("NUM_LT_SUC", List(n))

  def succ(kit: Kit, n: Term): R[Term] = kit.term("SUC", Type.fun(kit.numbers, kit.numbers)).flatMap(app(_, n))

  /** `x < SUC n` from `x < n`. */
  def belowSuc(kit: Kit, x: Term, n: Term, lt: Kernel.Thm): R[Kernel.Thm] =
    for {
      sn <- succ(kit, n)
      up <- ltSuc(kit, n)
      both <- kit.rules.conjIntro(lt, up)
      r <- kit.use("NUM_LT_TRANS", List(x, n, sn), both)
    } yield r

  /** `~(y = x)` from `x < y`. */
  def neqOfLt(kit: Kit, x: Term, y: Term, lt: Kernel.Thm): R[Kernel.Thm] =
    for {
      e <- eqTerm(y, x)
      h <- assume(e)
      back <- Conv.sym(h)
      yy <- Limit.rewriteInProposition(back, lt)
      irr <- kit.use("NUM_LT_IRREFL", List(y))
      f <- kit.rules.notElim(irr, yy)
      r <- kit.rules.notIntro(e, f)
    } yield r

  /** `x < n` from `x < SUC n` and `~(x = n)`. */
  def belowOfNeq(kit: Kit, x: Term, n: Term, lt: Kernel.Thm, neq: Kernel.Thm): R[Kernel.Thm] =
    for {
      cases <- kit.use("NUM_LT_SUC_CASES", List(n, x), lt)
      p_below <- disj(kit, cases.conclusion)
      (below, same) = p_below
      b <- assume(below)
      s <- assume(same)
      f <- kit.rules.notElim(neq, s)
      out <- kit.rules.falsityElim(below, f)
      r <- kit.rules.disjElim(cases, b, out)
    } yield r

  /** `COND c a b = a` or `= b`, from `c` or `~c`. */
  def condTrue(kit: Kit, c: Term, a: Term, b: Term, holds: Kernel.Thm): R[Kernel.Thm] =
    kit.fact("COND_TRUE").map(Kernel.instType(Map(Classical.TypeVariable -> Term.typeOf(a)), _))
      .flatMap(kit.applyTo(_, List(c, a, b), holds))
  def condFalse(kit: Kit, c: Term, a: Term, b: Term, fails: Kernel.Thm): R[Kernel.Thm] =
    kit.fact("COND_FALSE").map(Kernel.instType(Map(Classical.TypeVariable -> Term.typeOf(a)), _))
      .flatMap(kit.applyTo(_, List(c, a, b), fails))

  /** Case split on `p`: `whenTrue` gets `p` assumed, `whenFalse` gets `~p`. */
  def split(kit: Kit, p: Term)(whenTrue: Kernel.Thm => R[Kernel.Thm], whenFalse: Kernel.Thm => R[Kernel.Thm]): R[Kernel.Thm] =
    for {
      middle <- kit.use("EXCLUDED_MIDDLE", List(p))
      notP <- kit.logic.mkNot(p)
      hp <- assume(p)
      hn <- assume(notP)
      t <- whenTrue(hp)
      f <- whenFalse(hn)
      r <- kit.rules.disjElim(middle, t, f)
    } yield r

  /** The body of a universal at one argument, as a term. */
  def open(kit: Kit, quantified: Term, x: Term): R[Term] =
    assume(quantified).flatMap(kit.rules.spec(x, _)).flatMap(Limit.normalised).map(_.conclusion)

  /** A predicate applied to `x` and beta-reduced, as a term. */
  def instantiate(predicate: Term, x: Term): R[Term] =
    app(predicate, x).flatMap(Conv.betaNormalise).flatMap(Limit.rightOf)

  /** `COND c a b` taken apart. */
  def conditional(t: Term): R[(Term, Term, Term)] = t match {
    case App(App(App(_, test), yes), no) => Right((test, yes, no))
    case other => Left(NotOfForm("a conditional", other))
  }

  /** `P rhs` from `P lhs` and `lhs = rhs`, for `P` a lambda. */
  def transport(lambda: Term, eq: Kernel.Thm, thm: Kernel.Thm): R[Kernel.Thm] =
    cong(lambda, eq).flatMap(e => LogicError.lift(Kernel.eqMp(e, thm)))

  def zero(kit: Kit): R[Term] = kit.term("0", kit.numbers)
  def one(kit: Kit): R[Term] = kit.term("SUC 0", kit.numbers)
  def mul(kit: Kit, x: Term, y: Term): R[Term] =
    kit.term("NUM_MUL", Type.fun(kit.numbers, Type.fun(kit.numbers, kit.numbers))).flatMap(app(_, x, y))

  /** `0 < n` from `~(n = 0)`, through `NUM_CASES`. */
  def positive(kit: Kit, n: Term, nonZero: Kernel.Thm): R[Kernel.Thm] =
    for {
      cases <- kit.use("NUM_CASES", List(n))
      p <- disj(kit, cases.conclusion)
      (isZero, isSuc) = p
      z <- zero(kit)
      target <- kit.term("NUM_LT", Type.fun(kit.numbers, Type.fun(kit.numbers, Type.Bool))).flatMap(app(_, z, n))
      zeroCase <- for {
        h <- assume(isZero)
        absurd <- kit.rules.notElim(nonZero, h)
        r <- kit.rules.falsityElim(target, absurd)
      } yield r
      mPred <- kit.logic.destExistsPredicate(isSuc).toRight(NotOfForm("an existential", isSuc))
      m = fresh("m", kit.numbers, nonZero)
      mBodyT <- instantiate(mPred, m)
      hm <- assume(mBodyT)
      atSuc <- kit.use("NUM_ZERO_LT_SUC", List(m))
      back <- Conv.sym(hm)
      moved <- Limit.rewriteInProposition(back, atSuc)
      hs <- assume(isSuc)
      sucCase <- kit.rules.existsElim(hs, m, moved)
      r <- kit.rules.disjElim(cases, zeroCase, sucCase)
    } yield r
}
