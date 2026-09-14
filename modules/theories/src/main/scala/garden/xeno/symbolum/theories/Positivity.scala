package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * That a numeral is above zero, and therefore that it is not zero.
 *
 * The five order axioms are relational: each says how `<` survives an operation, and none of them
 * says that any particular number is below any other. So `0 < 1` is something to prove rather than
 * something the theory hands over, and every fact about a numeral's sign is downstream of it.
 *
 * == Why this is its own module and not part of [[Order]] ==
 *
 * Because the ring normal form needs one fact from it, and [[Order]] is built on top of the ring.
 *
 * A rational coefficient is a numeral over a numeral, and `x / 2 + x / 2 = x` is not an identity of
 * a commutative ring: unfolded it is `x * inv 2 + x * inv 2 = x`, and the step it needs is
 * `2 * inv 2 = 1`, which is `MUL_INVERSE` under `~(2 = 0)`. In a field of characteristic two the
 * statement is false, so no normal form can reach it and no rearrangement avoids the side
 * condition. What discharges the condition is the order, and nothing below it.
 *
 * That put the requirement and its supplier on opposite sides of the chain
 * `Arithmetic -> Polynomial -> Ring -> Order`. The cut is here because it is clean: `0 < 1` needs
 * three ring identities over `1` and `-1`, which the expanding normalisation in [[Arithmetic]]
 * settles in a few passes, and the climb to `0 < n` and the step to `~(n = 0)` need no ring at all.
 * What genuinely wants the collecting normal form is [[Order.less]], comparing two arbitrary
 * numerals, and that is not needed here. So this file sits above [[Arithmetic]] and below
 * [[Polynomial]], [[Order]] holds these three facts by citing them rather than by deriving them a
 * second time, and the dependencies still point one way.
 *
 * == Why the cost follows the digits ==
 *
 * [[Positivity.positive]] recurses on the bits rather than counting up, because `BIT0 k` is `k + k`
 * and `BIT1 k` is `(k + k) + 1` by definition and a sum of positives is positive. So `0 < 1000000`
 * costs twenty steps and not a million, which is the same distinction the collecting ring normal
 * form is built on: the length of a numeral, not its value.
 */
final class Positivity private (
  val arithmetic: Arithmetic,
  val facts: Map[String, Kernel.Thm]
) {

  val reals: RealTheory = arithmetic.reals

  private val rules = reals.logic.rules

  /** The fact named, as a theorem with no hypotheses. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** `|- 0 < 1` */
  def zeroLessOne: Either[LogicError, Kernel.Thm] = fact(Positivity.ZeroLessOne)

  /** `|- !x y. 0 < x ==> 0 < y ==> 0 < x + y` */
  def addPositive: Either[LogicError, Kernel.Thm] = fact(Positivity.AddPositive)

  /** `|- !x. 0 < x ==> ~(x = 0)` */
  def nonZero: Either[LogicError, Kernel.Thm] = fact(Positivity.NonZero)

  /**
   * `|- 0 < n`, for a numeral above zero.
   *
   * Zero and below are refused rather than attempted: `0 < 0` is false, and there is no numeral
   * below zero to be handed one.
   */
  def positive(value: BigInt): Either[LogicError, Kernel.Thm] =
    if (value > 0) positiveNumeral(value)
    else reals.term(value.toString).flatMap(found => Left(NotOfForm("a numeral above zero", found)))

  /**
   * `|- ~(n = 0)`, for a numeral above zero, with nothing assumed.
   *
   * This is the fact the ring normal form buys the whole module for. It is a theorem rather than a
   * hypothesis precisely because `n` is a numeral: [[Field]] meets the same side condition on a
   * symbolic denominator, cannot settle it, and carries it to the caller in the sequent, which is
   * the right answer there and would be the wrong one here. A tactic that returns
   * `~(2 = 0) |- x / 2 + x / 2 = x` has told the reader nothing they could not have worked out,
   * and has made a conditional theorem out of an unconditional one.
   */
  def numeralNonZero(value: BigInt): Either[LogicError, Kernel.Thm] =
    for {
      above <- positive(value)
      lemma <- nonZero
      numeral <- Numeral.of(reals, value)
      instance <- rules.spec(numeral, lemma)
      result <- rules.mp(instance, above)
    } yield result

  /**
   * `|- 0 < n` for `n` above zero, by recursion on the bits of `n`.
   *
   * `1` is the base and the only place an axiom-level argument happens. Above it, the numeral is
   * `BIT0 k` or `BIT1 k` for the numeral `k` below it, both of which unfold into sums of things
   * already known positive, and the unfolding is a definition read backwards rather than a search.
   */
  private def positiveNumeral(value: BigInt): Either[LogicError, Kernel.Thm] =
    if (value == 1) zeroLessOne
    else
      for {
        half <- Numeral.of(reals, value / 2)
        below <- positiveNumeral(value / 2)
        doubled <- addPositives(below, below)
        result <-
          if (value % 2 == 0)
            // `k + k` is `BIT0 k`, which is the numeral for twice `k`.
            Numeral.doubling(reals, half).flatMap(Conv.rewriteRight(doubled, _))
          else
            for {
              unit <- zeroLessOne
              odd <- addPositives(doubled, unit)
              unfolded <- Numeral.successorOfDouble(reals, half)
              folded <- Conv.sym(unfolded)
              shifted <- Conv.rewriteRight(odd, folded)
            } yield shifted
      } yield result

  /** `|- 0 < a` and `|- 0 < b` give `|- 0 < a + b`. */
  private def addPositives(
    left: Kernel.Thm,
    right: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      lemma <- addPositive
      leftSide <- Positivity.destLess(reals, left.conclusion).map(_._2)
      rightSide <- Positivity.destLess(reals, right.conclusion).map(_._2)
      instance <- rules.specAll(lemma, List(leftSide, rightSide))
      afterFirst <- rules.mp(instance, left)
      result <- rules.mp(afterFirst, right)
    } yield result
}

object Positivity {

  /** `|- 0 < 1` */
  val ZeroLessOne: String = "ZERO_LT_ONE"

  /** `|- !x y. 0 < x ==> 0 < y ==> 0 < x + y` */
  val AddPositive: String = "ADD_POSITIVE"

  /** `|- !x. 0 < x ==> ~(x = 0)` */
  val NonZero: String = "POSITIVE_NOT_ZERO"

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val relation: Type = Type.fun(real, Type.fun(real, Type.Bool))

  /** Built once over the standard arithmetic. */
  lazy val standard: Positivity =
    construct(Arithmetic.standard).fold(
      error =>
        throw new IllegalStateException(s"the positivity facts do not build: ${error.message}"),
      identity
    )

  /**
   * The three facts, over a theory whose arithmetic has already been proved.
   *
   * Each derivation takes what it rests on as an argument rather than fetching it, which is what
   * makes it readable on its own: the signature says what it depends on, and a lemma that grew a
   * dependency cannot hide it in a lookup.
   */
  def construct(arithmetic: Arithmetic): Either[LogicError, Positivity] = {
    val reals = arithmetic.reals

    for {
      zeroLeft <- arithmetic.lemma(Arithmetic.ZeroOnTheLeft)
      unit <- zeroLessOne(arithmetic)
      sum <- sumOfPositives(reals, zeroLeft)
      notZero <- nonZero(reals)
    } yield new Positivity(
      arithmetic,
      Map(ZeroLessOne -> unit, AddPositive -> sum, NonZero -> notZero)
    )
  }

  /**
   * `|- 0 < 1`, by cases on trichotomy at `0` and `1`.
   *
   * Every branch reaches the goal, and the middle one is the only one that reaches it by
   * contradiction:
   *
   *  - `0 < 1` is the goal;
   *  - `0 = 1` contradicts `ONE_NOT_ZERO`, so the branch closes by ex falso;
   *  - `1 < 0` gives `0 < -1` by adding `-1` to both sides, then `0 < -1 * -1` because the order
   *    is closed under products of positives, and `-1 * -1` is `1`.
   *
   * The third branch is worth reading twice. It does not rule the case out, it proves the goal
   * inside it: a field where `1 < 0` is a field where `-1` is positive, and the square of a
   * positive is positive, so `1` is positive there too. What that branch actually shows is that
   * the case is empty, but the derivation never has to say so.
   *
   * The three ring identities it needs are over `1` and `-1`, so they are settled by the expanding
   * normalisation, which is what [[Arithmetic]] carries. Nothing here wants the collecting form,
   * and asking for it is what would put this above [[Ring]] instead of below it.
   */
  def zeroLessOne(arithmetic: Arithmetic): Either[LogicError, Kernel.Thm] = {
    val reals = arithmetic.reals
    val logic = reals.logic
    val rules = logic.rules

    def term(text: String): Either[LogicError, Term] = reals.term(text)
    def proposition(text: String): Either[LogicError, Term] = reals.proposition(text)
    def identity(text: String): Either[LogicError, Kernel.Thm] =
      proposition(text).flatMap(Rewrite.proveEquation(logic, arithmetic.normalisation, _))

    for {
      zero <- term("0")
      one <- term("1")
      minusOne <- term("-1")
      goal <- proposition("0 < 1")

      trichotomy <- reals
        .axiom("LT_TOTAL")
        .flatMap(rules.spec(zero, _))
        .flatMap(rules.spec(one, _))

      // The first branch assumes what is being proved, which is what a case analysis on a
      // disjunction containing the goal looks like.
      first <- LogicError.lift(Kernel.assume(goal))

      // The second contradicts the one axiom that separates the two numerals.
      equated <- proposition("0 = 1").flatMap(term => LogicError.lift(Kernel.assume(term)))
      reversed <- Conv.sym(equated)
      distinct <- reals.axiom("ONE_NOT_ZERO")
      absurd <- rules.notElim(distinct, reversed)
      second <- rules.falsityElim(goal, absurd)

      // The third adds `-1` to both sides, squares, and lands on the goal.
      below <- proposition("1 < 0").flatMap(term => LogicError.lift(Kernel.assume(term)))
      addition <- reals
        .axiom("LT_ADD")
        .flatMap(rules.spec(one, _))
        .flatMap(rules.spec(zero, _))
        .flatMap(rules.spec(minusOne, _))
      shifted <- rules.mp(addition, below)
      cancels <- identity("1 + -1 = 0")
      absorbs <- identity("0 + -1 = -1")
      negative <- Conv.rewriteSides(cancels, absorbs, shifted)
      product <- reals
        .axiom("LT_MUL")
        .flatMap(rules.spec(minusOne, _))
        .flatMap(rules.spec(minusOne, _))
      squared <- rules.conjIntro(negative, negative).flatMap(rules.mp(product, _))
      square <- identity("-1 * -1 = 1")
      third <- Conv.rewriteSides(Conv.refl(zero), square, squared)

      // Trichotomy nests to the right, so the two eliminations do too.
      tail <- proposition("0 = 1 \\/ 1 < 0").flatMap(term => LogicError.lift(Kernel.assume(term)))
      fromTail <- rules.disjElim(tail, second, third)
      result <- rules.disjElim(trichotomy, first, fromTail)
    } yield result
  }

  /**
   * `|- !x y. 0 < x ==> 0 < y ==> 0 < x + y`.
   *
   * From the axiom, `0 < x` gives `y < x + y`; with `0 < y` and transitivity that is `0 < x + y`.
   *
   * It lives here rather than in [[Linarith]], where it was written, because it is a fact about the
   * order and both the tactic and [[Positivity.positive]] need it: the recursion on the bits of a
   * numeral is this lemma applied once per bit.
   */
  def sumOfPositives(reals: RealTheory, zeroLeft: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      ltAdd <- reals.axiom("LT_ADD")
      ltTransitive <- reals.axiom("LT_TRANSITIVE")

      zero <- reals.term("0")
      sum <- reals.term("x:real + y:real")
      firstPremise <- reals.proposition("0 < x:real")
      secondPremise <- reals.proposition("0 < y:real")
      firstAssumed <- LogicError.lift(Kernel.assume(firstPremise))
      secondAssumed <- LogicError.lift(Kernel.assume(secondPremise))

      instance <- rules.specAll(ltAdd, List(zero, x, y))
      applied <- rules.mp(instance, firstAssumed)

      zeroAtY <- rules.spec(y, zeroLeft)
      rules0 <- Rewrite.Rule.all(reals.logic, Vector(zeroAtY))
      shifted <- Rewrite.inTheorem(rules0, applied)

      transitivity <- rules.specAll(ltTransitive, List(zero, y, sum))
      both <- rules.conjIntro(secondAssumed, shifted)
      result <- rules.mp(transitivity, both)

      innerDischarged <- rules.disch(secondPremise, result)
      outerDischarged <- rules.disch(firstPremise, innerDischarged)
      general <- rules.genAll(outerDischarged, List(x, y))
    } yield general
  }

  /**
   * `|- !x. 0 < x ==> ~(x = 0)`.
   *
   * The side condition `MUL_INVERSE` is stated with, which is why [[Order.inversePositive]] can use
   * that axiom at all, and which is what [[Positivity.numeralNonZero]] discharges for a numeral.
   * Assuming the equation rewrites `0 < x` into `0 < 0`, and irreflexivity refuses it.
   */
  def nonZero(reals: RealTheory): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)

    for {
      irreflexive <- reals.axiom("LT_IRREFLEXIVE")
      zero <- reals.term("0")

      positive <- reals.proposition("0 < x:real")
      assumed <- LogicError.lift(Kernel.assume(positive))
      equation <- reals.proposition("x:real = 0")
      equated <- LogicError.lift(Kernel.assume(equation))

      rules0 <- Rewrite.Rule.all(reals.logic, Vector(equated))
      atZero <- Rewrite.inTheorem(rules0, assumed)

      never <- rules.spec(zero, irreflexive)
      absurd <- rules.notElim(never, atZero)
      negated <- rules.notIntro(equation, absurd)

      discharged <- rules.disch(positive, negated)
      general <- rules.gen(x, discharged)
    } yield general
  }

  /* ----------------------------------------------------------------- helpers */

  /** The two sides of `a < b`. */
  def destLess(reals: Signature, term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(Const(Real.Order, _), left), right) => Right((left, right))
    case other => Left(NotOfForm("a strict inequality", other))
  }

  /** The `<` constant. */
  def lessThanConstant(reals: Signature): Either[LogicError, Term] =
    LogicError.lift(reals.theory.constant(Real.Order, relation))
}
