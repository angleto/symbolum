package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What a sequence of reals converges to, which is the first analysis this repository has.
 *
 * `converges s l` is the epsilon-N statement and nothing more: past some index every term of `s` is
 * within every positive distance of `l`. `lim s` is the value, named by choice the way `NUM_GCD`
 * and `max` are, and pinned by [[Unique]]: where a sequence converges at all, `lim` is what it
 * converges to, and where it does not the term denotes and nothing here says what.
 *
 * == Why this is the missing piece and not one of several ==
 *
 * The reals have carried `COMPLETENESS` since the beginning and until 2026-09-13 nothing read it;
 * `Peano.NUM_ARCHIMEDES` was the first thing to spend it. What the axiom is **for** is convergence,
 * and convergence could not be said here at all: `docs/proving.md` has listed the transcendental
 * functions as the fourth thing to add since it was written, and the reason given each time is that
 * they need sequences. This is the sequences.
 *
 * [[Transcendental]] is the consumer it was written for and the two landed together, which is
 * `docs/adr/0007`'s rule about an axiom arriving in the commit whose derivation needs it, read for
 * a definition instead: a limit operator with no limit taken is a constant nobody has checked.
 *
 * == It costs no axiom, and one thing it does not do ==
 *
 * Both constants are definitions. `lim` reaches `select`, which the chain already pays for, so what
 * a development over this must believe is what it was before; `LimitSpec` asserts that as an
 * equality rather than as a ceiling, the way `CodingSpec` does.
 *
 * **Nothing here proves that a sequence converges.** Every fact below takes convergence as a
 * hypothesis and moves it, with one exception: [[Constant]], where the sequence does not move at
 * all. This is the vocabulary and the bookkeeping rather than an instrument for establishing the
 * thing. What establishes it in general is the monotone convergence theorem, which is the next
 * piece of this development and is where `COMPLETENESS` is spent a second time; until it lands, a
 * caller that wants a limit hands one over or has a sequence that is eventually constant.
 *
 * That pair, [[Constant]] with [[Eventually]], is more than it looks: it settles every sequence
 * that stops moving, which is what a power series at zero is, and it is the whole of what
 * [[Transcendental]] can reach today.
 *
 * == The epsilon principle is here rather than in `Order`, and that is an argument worth making ==
 *
 * [[BelowEveryPositive]] is a fact about the order on the reals and mentions neither constant of
 * this file, so `Order` is where a reader would look for it. It is here because it is what a limit
 * argument spends and nothing below has ever wanted it: three links down it would sit where nothing
 * cites it. If a second consumer appears below this, it moves, and the citation moves with it.
 */
final class Limit private (
  val magnitude: Magnitude,
  val peano: Peano,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = magnitude.classical.logic
    .over(theory)
    .fold(
      error => throw new IllegalStateException(s"the logic does not extend: ${error.message}"),
      identity
    )

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** `|- !x. 0 <= x ==> (!e. 0 < e ==> x < e) ==> x = 0`, the epsilon principle. */
  def belowEveryPositive: Either[LogicError, Kernel.Thm] = fact(Limit.BelowEveryPositive)

  /** `|- !c. converges (\n. c) c` */
  def constantSequence: Either[LogicError, Kernel.Thm] = fact(Limit.Constant)

  /** `|- !s a b. converges s a ==> converges s b ==> a = b` */
  def unique: Either[LogicError, Kernel.Thm] = fact(Limit.Unique)

  /** `|- !s l. converges s l ==> lim s = l` */
  def valueOfConverges: Either[LogicError, Kernel.Thm] = fact(Limit.ValueOfConverges)

  /** `|- !s t l N. (!n. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l` */
  def eventually: Either[LogicError, Kernel.Thm] = fact(Limit.Eventually)

  /** `|- !s. (!n. s n <= s (SUC n)) ==> !m n. NUM_LE m n ==> s m <= s n` */
  def monotoneBelow: Either[LogicError, Kernel.Thm] = fact(Limit.MonotoneBelow)

  /** `|- !s. (!n. s n <= s (SUC n)) ==> (?b. !n. s n <= b) ==> ?l. converges s l` */
  def monotoneConverges: Either[LogicError, Kernel.Thm] = fact(Limit.MonotoneConverges)

  /**
   * `|- !f g. (!n. 0 <= f n) ==> (!n. f n <= g n) ==> (?b. !n. Sum g n <= b)
   * ==> ?l. converges (Sum f) l`
   */
  def comparison: Either[LogicError, Kernel.Thm] = fact(Limit.Comparison)

  /** `|- !s t a b. converges s a ==> converges t b ==> converges (\n. s n + t n) (a + b)` */
  def added: Either[LogicError, Kernel.Thm] = fact(Limit.Added)

  /** `|- !s a. converges s a ==> converges (\n. -(s n)) (-a)` */
  def negated: Either[LogicError, Kernel.Thm] = fact(Limit.Negated)
}

object Limit {

  /** `converges s l` says the sequence `s` converges to `l`. */
  val Converges: String = "converges"

  /** `lim s` is what `s` converges to, where it converges to anything. */
  val Value: String = "lim"

  /**
   * The epsilon-N definition, as the text a person checks it by.
   *
   * Written out in the concrete syntax rather than assembled, for the reason `docs/adr/0004` gives
   * for the sixteen axioms: what a reader has to check is that this says "past some index, within
   * every positive distance", and a reader checks a sentence rather than a sequence of builder
   * calls.
   *
   * `NUM_LE N n` rather than `NUM_LT`, and the distance is strict. Both are the usual conventions
   * and neither is load-bearing: the same sequences converge either way, since an index can be
   * stepped and a tolerance can be halved. What **is** load-bearing is that the tolerance is a real
   * and not a natural, which is what makes this convergence in the reals.
   */
  val ConvergesBody: String =
    "\\s:num -> real. \\l:real. !e:real. 0 < e ==> ?N:num. !n:num. NUM_LE N n ==> abs (s n - l) < e"

  /**
   * The value, which is choice applied to the predicate above and nothing else.
   *
   * The same construction as `NUM_GCD`, `NUM_FLOOR` and `max`: a term that denotes at every
   * argument and about which nothing is provable except where something satisfies the predicate.
   * [[Unique]] is what makes that exception the whole of the interesting case: a sequence has at
   * most one limit, so `lim s` is not merely *a* limit of `s` but *the* one.
   */
  val ValueBody: String = "\\s:num -> real. select (\\l:real. converges s l)"

  /** `|- !x. 0 <= x ==> (!e. 0 < e ==> x < e) ==> x = 0` */
  val BelowEveryPositive: String = "LE_BELOW_EVERY_POSITIVE"

  /** `|- !c. converges (\n. c) c` */
  val Constant: String = "CONVERGES_CONSTANT"

  /** `|- !s a b. converges s a ==> converges s b ==> a = b` */
  val Unique: String = "CONVERGES_UNIQUE"

  /** `|- !s l. converges s l ==> lim s = l` */
  val ValueOfConverges: String = "LIM_OF_CONVERGES"

  /** `|- !s t l N. (!n. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l` */
  val Eventually: String = "CONVERGES_EVENTUALLY"

  /**
   * `|- !s. (!n. s n <= s (SUC n)) ==> !m n. NUM_LE m n ==> s m <= s n`
   *
   * A step at a time gives a step to anywhere, which is the induction nobody states and everybody
   * uses. It is published beside the theorem below rather than folded into it because it is about
   * the order and not about convergence: a caller with an increasing sequence and no interest in
   * its limit wants this one.
   */
  val MonotoneBelow: String = "MONOTONE_LE"

  /**
   * `|- !s. (!n. s n <= s (SUC n)) ==> (?b. !n. s n <= b) ==> ?l. converges s l`
   *
   * The monotone convergence theorem, and the first thing in this repository to **prove** that a
   * sequence converges rather than to take a convergence as a hypothesis. It is where
   * `COMPLETENESS` is spent the second time, `Peano.NUM_ARCHIMEDES` having been the first.
   */
  val MonotoneConverges: String = "MONOTONE_CONVERGES"

  /**
   * The comparison test: a non-negative series under a bounded one converges.
   *
   * The first thing here that obtains the convergence of a **series** rather than of a sequence,
   * and it is [[MonotoneConverges]] spent on the one sequence a series always has. `docs/adr/0017`
   * and `docs/proving.md` both put it first among what the analysis still owes, and what it buys
   * immediately is that `exp 1 > 2` stops being statable-and-unproved.
   */
  val Comparison: String = "SUM_COMPARISON"

  /**
   * `|- !s t a b. converges s a ==> converges t b ==> converges (\n. s n + t n) (a + b)`
   *
   * The limit of a sum is the sum of the limits, and it is the first fact in this development that
   * relates **two** convergent sequences to each other. Everything above it takes one sequence and
   * says something about it alone: that a constant converges, that a limit is unique, that an
   * increasing bounded sequence has one. A development that cannot add two limits cannot state the
   * Cauchy product, so this is the piece the analysis was actually short of, and `docs/adr/0017`
   * does not name it because the thing it names, `SUM_SWAP`, is a different gap.
   *
   * The proof is the epsilon argument [[Unique]] already contains, run forwards instead of into a
   * contradiction: halve the tolerance, take the two indices the halves give, and answer at a
   * single index above both. `Peano.NUM_LE_ADD` is what "above both" is here and a maximum is not,
   * for the reason [[Unique]] gives: `num` has no maximum, and the sum of two indices is above each
   * of them for nothing.
   *
   * == Why the triangle inequality is not used, although this is where a reader expects it ==
   *
   * `Magnitude.ABS_TRIANGLE` says `abs (x + y) <= abs x + abs y`, and the textbook step is that
   * inequality applied to `(s n - a) + (t n - b)`. Using it would mean first rewriting
   * `s n + t n - (a + b)` into that sum **under `abs`**, which is a rewrite of a subterm the
   * congruence here reaches only through [[rewriteInProposition]], and then a second step to put
   * the two halves together. What replaces it costs one `Order.ABS_CASES` split and two `Linarith`
   * calls: in each branch `abs` is gone, and what is left is linear over the eight atoms. The
   * inequality is not avoided, it is **decided**, which is what having a fragment decider is for.
   */
  val Added: String = "CONVERGES_ADD"

  /**
   * `|- !s a. converges s a ==> converges (\n. -(s n)) (-a)`
   *
   * Negation of a sequence, and it is here rather than as the scalar multiple `c = -1` for a reason
   * that is about the proof and not about generality. `converges (\n. c * s n) (c * a)` divides the
   * tolerance by `abs c` and therefore has to split on `c = 0` before it can divide at all; the
   * negation divides by nothing, keeps the same index, and is three lines of `Linarith` over the
   * same two bounds [[Added]] uses. So the additive group of limits is complete at this cut and the
   * scalar multiple is left, deliberately, to whoever needs it with its case split.
   */
  val Negated: String = "CONVERGES_NEG"

  /** Everything this development proves, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    BelowEveryPositive -> "!x:real. 0 <= x ==> (!e:real. 0 < e ==> x < e) ==> x = 0",
    Constant -> "!c:real. converges (\\n:num. c) c",
    Unique -> "!s:num -> real. !a:real. !b:real. converges s a ==> converges s b ==> a = b",
    ValueOfConverges -> "!s:num -> real. !l:real. converges s l ==> lim s = l",
    Eventually ->
      ("!s:num -> real. !t:num -> real. !l:real. !N:num. " +
        "(!n:num. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l"),
    MonotoneBelow ->
      ("!s:num -> real. (!n:num. s n <= s (SUC n)) ==> " +
        "!m:num. !n:num. NUM_LE m n ==> s m <= s n"),
    MonotoneConverges ->
      ("!s:num -> real. (!n:num. s n <= s (SUC n)) ==> (?b:real. !n:num. s n <= b) ==> " +
        "?l:real. converges s l"),
    Comparison ->
      ("!f:num -> real. !g:num -> real. (!n:num. 0 <= f n) ==> (!n:num. f n <= g n) ==> " +
        "(?b:real. !n:num. Sum g n <= b) ==> ?l:real. converges (Sum f) l"),
    Added ->
      ("!s:num -> real. !t:num -> real. !a:real. !b:real. " +
        "converges s a ==> converges t b ==> converges (\\n:num. s n + t n) (a + b)"),
    Negated ->
      "!s:num -> real. !a:real. converges s a ==> converges (\\n:num. -(s n)) (-a)"
  )

  private val values: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val sequences: Type = Type.fun(numbers, values)

  /** The standard development, which is the chain's own and not a second one beside it. */
  lazy val standard: Limit = Chain.standard.limit

  /**
   * The development over a magnitude and a Peano arithmetic that are in one signature.
   *
   * `base` is the theory to extend rather than `magnitude.theory`, for the reason `Rotation` gives:
   * a constant declared into a side branch is unreachable from every link above it, so what this
   * extends is whatever the chain has reached by the time it gets here.
   */
  def construct(
    magnitude: Magnitude,
    peano: Peano,
    series: Series,
    reals: RealTheory,
    induct: Induct,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Limit] = {
    val classical = magnitude.classical

    for {
      convergesBody <- Parser.term(base, notation, ConvergesBody)
      definedConverges <- LogicError.lift(Kernel.defineConstant(base, Converges, convergesBody))
      (afterConverges, convergesDefinition) = definedConverges

      valueBody <- Parser.term(afterConverges, notation, ValueBody)
      definedValue <- LogicError.lift(Kernel.defineConstant(afterConverges, Value, valueBody))
      (theory, valueDefinition) = definedValue

      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(magnitude.order)

      irreflexive <- reals.axiom("LT_IRREFLEXIVE")
      completeness <- reals.axiom("COMPLETENESS")
      leCases <- magnitude.order.leCases
      leOfEq <- magnitude.order.leOfEq
      notForall <- classical.fact(Classical.NotForall)
      doubleNegation <- classical.fact(Classical.DoubleNegation)
      weakFromNegated <- magnitude.order.fact(Order.LeOfNotLt)
      addAtZero <- peano.fact(Peano.AddAtZero)
      addAtSuccessor <- peano.fact(Peano.AddAtSuccessor)
      orderDefinition <- peano.definition(Peano.NonStrictOrder)
      absCases <- magnitude.absCases
      absAbove <- magnitude.absAbove
      absAboveNegation <- magnitude.absAboveNegation
      absNonNegative <- magnitude.absNonNegative
      absZero <- magnitude.absZero
      atMostSum <- peano.fact(Peano.AtMostSum)
      transitive <- peano.fact(Peano.Transitive)
      addCommutative <- peano.fact(Peano.AddCommutative)

      // `Series` is built at `Chain.scala:307` and this at 388, so the dependency runs the way the
      // chain already runs and costs a parameter rather than a reordering. The comparison test is
      // here and not in `Transcendental`, which has both halves already: that file's first sentence
      // says it is the transcendental functions, and a general fact about series under it would
      // make that sentence false.
      sumAtSuccessor <- series.fact(Series.AtSuccessor)
      sumMonotone <- series.fact(Series.Monotone)

      bounds = Bounds(absCases, absAbove, absAboveNegation, absNonNegative, absZero)
      indices = Indices(atMostSum, transitive, addCommutative)

      epsilon <- belowEveryPositive(logic, linarith, theory, notation, irreflexive, leCases)
      constant <- constantSequence(logic, linarith, theory, notation, convergesDefinition, absCases)
      unique <- uniqueLimit(
        logic, linarith, theory, notation, convergesDefinition, bounds, indices, epsilon)
      value <- valueOfConverges(logic, classical, theory, notation, valueDefinition, unique)
      eventually <- eventuallyEqual(
        logic, theory, notation, convergesDefinition, indices)

      monotoneBelow <- monotoneOrder(
        logic, linarith, theory, notation, induct, leOfEq, orderDefinition, addAtZero,
        addAtSuccessor)

      monotoneConverges <- monotoneConvergence(
        logic, linarith, theory, notation, convergesDefinition, completeness, notForall,
        doubleNegation, irreflexive, weakFromNegated, bounds, monotoneBelow)

      comparisonTest <- comparison(
        logic, linarith, theory, notation, sumAtSuccessor, sumMonotone, monotoneConverges)

      addedLimits <- convergesAdd(
        logic, linarith, theory, notation, convergesDefinition, bounds, indices)
      negatedLimit <- convergesNegated(
        logic, linarith, theory, notation, convergesDefinition, bounds)
    } yield new Limit(
      magnitude,
      peano,
      theory,
      notation,
      Map(Converges -> convergesDefinition, Value -> valueDefinition),
      Map(
        BelowEveryPositive -> epsilon,
        Constant -> constant,
        Unique -> unique,
        ValueOfConverges -> value,
        Eventually -> eventually,
        MonotoneBelow -> monotoneBelow,
        MonotoneConverges -> monotoneConverges,
        Comparison -> comparisonTest,
        Added -> addedLimits,
        Negated -> negatedLimit
      )
    )
  }

  /**
   * The comparison test, from the three facts it is made of and nothing else.
   *
   * == Why it is short ==
   *
   * Every piece was already published and the work is putting them in one order. `SUM_SUC` says a
   * partial sum grows by the term just added, so non-negative terms make the partial sums an
   * increasing sequence; `SUM_MONOTONE` says termwise domination carries to the partial sums; and
   * [[MonotoneConverges]] closes an increasing sequence bounded above. The series is never
   * mentioned as a series: what converges is the sequence `Sum f`, which is what a series **is**
   * here, and that is why no new constant and no axiom are needed.
   *
   * == The hypothesis is stronger than the argument strictly needs, and that is deliberate ==
   *
   * `!n. 0 <= f n` asks for non-negativity at **every** index, where the mathematics needs it only
   * from the point the tail starts. The reason is [[MonotoneConverges]]: it asks for
   * `!n. s n <= s (SUC n)` everywhere, so a weaker hypothesis here would need a convergence rule
   * for an eventually increasing sequence, which this development has not got. [[Eventually]] is
   * not that rule: it carries a limit across two sequences that agree past an index, which is
   * eventual **equality** and not eventual monotonicity.
   *
   * So the weaker form is a piece of work rather than a better phrasing of this one, and it is
   * named here so that a reader meeting the strong hypothesis knows it was measured against the
   * rule above rather than written down without looking.
   */
  private def comparison(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    sumAtSuccessor: Kernel.Thm,
    sumMonotone: Kernel.Thm,
    monotoneConverges: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val f = Term.variable("f", sequences)
    val g = Term.variable("g", sequences)
    val n = Term.variable("n", numbers)
    val b = Term.variable("b", values)

    def proposition(text: String): Either[LogicError, Term] =
      Parser.proposition(theory, notation, text)

    for {
      nonNegative <- proposition("!n:num. 0 <= (f:num -> real) n")
      dominated <- proposition("!n:num. (f:num -> real) n <= (g:num -> real) n")
      boundedAbove <- proposition("?b:real. !n:num. Sum (g:num -> real) n <= b")

      assumedNonNegative <- LogicError.lift(Kernel.assume(nonNegative))
      assumedDominated <- LogicError.lift(Kernel.assume(dominated))
      assumedBounded <- LogicError.lift(Kernel.assume(boundedAbove))

      /* ---- the partial sums increase, which is `SUM_SUC` read with a non-negative term ---- */

      sumF <- Parser.term(theory, notation, "Sum (f:num -> real)")
      atSuccessor <- rules.specAll(sumAtSuccessor, List(f, n))
      termNonNegative <- rules.spec(n, assumedNonNegative)

      // `Sum f n <= Sum f n + f n` is a linear consequence of `0 <= f n`, and the equation above
      // turns the right side into `Sum f (SUC n)`. Linarith decides the first and the rewriting
      // does the second, which is why neither half is a hand derivation.
      growsBody <- proposition(
        "0 <= (f:num -> real) n:num ==> Sum f n <= Sum f n + f n")
      grows <- linarith.prove(growsBody)
      growsAt <- rules.mp(grows, termNonNegative)
      // Reversed, because `SUM_SUC` reads `Sum f (SUC n) = Sum f n + f n` and what has to move is
      // the right side into the left: the linear step above produces `Sum f n + f n` and
      // `MONOTONE_CONVERGES` asks for `Sum f (SUC n)`.
      folded <- Conv.sym(atSuccessor)
      increasingAt <- Rewrite.Rule
        .of(logic, folded)
        .flatMap(rule => Rewrite.inTheorem(Vector(rule), growsAt))
      increasing <- rules.gen(n, increasingAt)

      /* ---- and they are bounded, because they lie under `g`'s ---- */

      belowG <- rules.specAll(sumMonotone, List(f, g))
      dominatedSums <- rules.mp(belowG, assumedDominated)

      bound <- proposition("!n:num. Sum (g:num -> real) n <= b:real")
      assumedBound <- LogicError.lift(Kernel.assume(bound))

      // A CONJUNCTION and not two arrows, because of the `conjIntro` below and for no other
      // reason. This comment said the conjunction was the shape `Linarith.prove` documents and
      // that a curried goal comes back wrong, and **that is false**: `Linarith.split` peels every
      // antecedent, not one, and `CurriedGoalSpec` has pinned the two forms as the same goal since
      // the day a version that peeled exactly one was repaired. What refused the curried attempt
      // was `Rules.mp`, downstream, against an antecedent this assembly does not build -- a
      // constraint of the three lines below rather than of the prover. The distinction is worth
      // the paragraph: a wrong figure gets rechecked by whoever trips on it, and a wrong
      // constraint gets **obeyed**, so nobody ever discovers it was unnecessary.
      transitivityGoal <- proposition(
        "Sum (f:num -> real) n:num <= Sum (g:num -> real) n /\\ Sum g n <= b:real ==> " +
          "Sum f n <= b")
      transitivity <- linarith.prove(transitivityGoal)
      underG <- rules.spec(n, dominatedSums)
      underB <- rules.spec(n, assumedBound)
      both <- rules.conjIntro(underG, underB)
      belowBoundAt <- rules.mp(transitivity, both)
      belowBound <- rules.gen(n, belowBoundAt)

      // The witness is discharged here rather than carried: what `MONOTONE_CONVERGES` wants is the
      // existential, and rebuilding it after the case keeps `b` out of the conclusion.
      boundedF <- proposition("?b:real. !n:num. Sum (f:num -> real) n <= b")
      witnessed <- logic
        .destExistsPredicate(boundedF)
        .toRight(NotOfForm("an existential quantification", boundedF))
      packed <- rules.existsIntro(witnessed, b, belowBound)
      existsBound <- rules.existsElim(assumedBounded, b, packed)

      /* ---- and that is exactly what the monotone rule asks for ---- */

      atSums <- rules.spec(sumF, monotoneConverges)
      converging <- rules.mp(atSums, increasing).flatMap(rules.mp(_, existsBound))

      dischargedBounded <- rules.disch(boundedAbove, converging)
      dischargedDominated <- rules.disch(dominated, dischargedBounded)
      dischargedNonNegative <- rules.disch(nonNegative, dischargedDominated)
      result <- rules.genAll(dischargedNonNegative, List(f, g))
    } yield result
  }

  /**
   * What a derivation about `abs` needs, so that each one names what it uses.
   *
   * A record rather than a tuple for the reason `Magnitude.SignPieces` gives: a positional read of
   * five theorems of the same type is how a derivation gets assembled out of the wrong pieces.
   */
  private final case class Bounds(
    cases: Kernel.Thm,
    above: Kernel.Thm,
    aboveNegation: Kernel.Thm,
    nonNegative: Kernel.Thm,
    zero: Kernel.Thm
  )

  /** What a derivation that puts two indices together needs: a sum is above each summand. */
  private final case class Indices(
    atMostSum: Kernel.Thm,
    transitive: Kernel.Thm,
    commutative: Kernel.Thm
  )

  /**
   * `|- !x. 0 <= x ==> (!e. 0 < e ==> x < e) ==> x = 0`, and it is classical in nothing.
   *
   * The textbook proof argues by contradiction from the excluded middle. That is not needed and the
   * route here says why: `Order.LE_CASES` turns `0 <= x` into `0 < x \/ 0 = x`, and the first
   * disjunct is refuted **directly** by instantiating the hypothesis at `e := x`, which gives
   * `x < x` against the irreflexivity axiom. What comes out is a disjunction elimination rather
   * than a contradiction, so **this derivation** reaches no classical axiom, which `LimitSpec`
   * asserts rather than this sentence claiming it.
   *
   * It is the only one in the file of which that is true, and the reason is worth knowing before
   * reading the rest: everything else here touches `abs`, which is defined through `select`, so the
   * choice axiom arrives with the first `Magnitude` fact whatever route the proof takes. What the
   * route buys is not a cheaper foundation, it is that nothing here **decides** anything by the
   * excluded middle.
   *
   * The instantiation at `e := x` is the whole content, and it is the step somebody rediscovers
   * every time they meet this lemma: the hypothesis is about **every** positive tolerance, so it is
   * about the number itself.
   */
  private def belowEveryPositive(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    irreflexive: Kernel.Thm,
    leCases: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", values)

    for {
      nonNegative <- Parser.proposition(theory, notation, "0 <= x:real")
      assumedNonNegative <- LogicError.lift(Kernel.assume(nonNegative))

      everyPositive <- Parser.proposition(theory, notation, "!e:real. 0 < e ==> x:real < e")
      assumedEvery <- LogicError.lift(Kernel.assume(everyPositive))

      target <- Parser.proposition(theory, notation, "x:real = 0")
      zero <- Parser.term(theory, notation, "0:real", values)

      split <- rules.specAll(leCases, List(zero, x)).flatMap(rules.mp(_, assumedNonNegative))

      strict <- Parser.proposition(theory, notation, "0 < x:real")
      fromStrict <- for {
        assumed <- LogicError.lift(Kernel.assume(strict))
        atItself <- rules.spec(x, assumedEvery).flatMap(rules.mp(_, assumed))
        never <- rules.spec(x, irreflexive)
        clash <- rules.notElim(never, atItself)
        anything <- rules.falsityElim(target, clash)
      } yield anything

      equated <- Parser.proposition(theory, notation, "0 = x:real")
      fromEquated <- for {
        assumed <- LogicError.lift(Kernel.assume(equated))
        turn <- linarith.prove("!a:real. 0 = a ==> a = 0")
        applied <- rules.spec(x, turn).flatMap(rules.mp(_, assumed))
      } yield applied

      settled <- rules.disjElim(split, fromStrict, fromEquated)
      result <- rules
        .disch(everyPositive, settled)
        .flatMap(rules.disch(nonNegative, _))
        .flatMap(rules.gen(x, _))
    } yield result
  }

  /**
   * `|- !c. converges (\n. c) c`, the one sequence whose limit needs no analysis.
   *
   * Every index answers, so the witness is `0` and the distance is `abs (c - c)`. That the distance
   * is zero is `Magnitude.ABS_CASES` and one linear step in each branch, which is cheaper than it
   * looks: the two branches differ only in the sign of a difference that vanishes either way.
   *
   * It is not decoration. [[Eventually]] turns it into every sequence that is eventually constant,
   * and that pair is what [[Transcendental]] evaluates a power series at zero with, without any
   * convergence theorem at all.
   */
  private def constantSequence(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    absCases: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val c = Term.variable("c", values)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)

    for {
      sequence <- Parser.term(theory, notation, "\\n:num. c:real", sequences)
      unfolded <- Conv.unfold(convergesDefinition, List(sequence, c))
      opened <- normaliseRight(unfolded)
      body <- rightOf(opened)

      difference <- Parser.term(theory, notation, "c:real - c:real", values)
      distance <- Parser.term(theory, notation, "abs (c:real - c:real)", values)
      split <- rules.spec(difference, absCases)

      plain <- Parser.proposition(theory, notation, "abs (c:real - c:real) = c - c")
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        cancels <- linarith.prove("!a:real. a - a = 0")
        result <- rules.spec(c, cancels).flatMap(Conv.trans(assumed, _))
      } yield result

      negated <- Parser.proposition(theory, notation, "abs (c:real - c:real) = -(c - c)")
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negated))
        cancels <- linarith.prove("!a:real. -(a - a) = 0")
        result <- rules.spec(c, cancels).flatMap(Conv.trans(assumed, _))
      } yield result

      vanishes <- rules.disjElim(split, fromPlain, fromNegated)

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      small <- linarith.prove("!a:real. !e:real. a = 0 ==> 0 < e ==> a < e")
      close <- rules
        .specAll(small, List(distance, e))
        .flatMap(rules.mp(_, vanishes))
        .flatMap(rules.mp(_, assumedPositive))

      guard <- Parser.proposition(theory, notation, "NUM_LE 0 n:num")
      guarded <- rules.disch(guard, close).flatMap(rules.gen(n, _))

      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> abs (c:real - c:real) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      first <- Parser.term(theory, notation, "0:num", numbers)
      witnessed <- rules.existsIntro(predicate, first, guarded)

      whole <- rules.disch(positive, witnessed).flatMap(rules.gen(e, _))
      _ <- sameStatement(notation, whole, body)

      folded <- Conv.sym(opened).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))
      result <- rules.gen(c, folded)
    } yield result
  }

  /**
   * `|- !s a b. converges s a ==> converges s b ==> a = b`: a sequence has at most one limit.
   *
   * The argument is the standard one, and the two places it could have been harder are both closed
   * by something this chain already has. Halving the tolerance is `Linarith`'s, since a numeral
   * denominator is a rational coefficient to it and `0 < e ==> 0 < e / 2` is inside the fragment it
   * decides. Putting the two indices together is `Peano.NUM_LE_ADD`: their sum is above each of
   * them, so no maximum on `num` is needed, and there is none.
   *
   * What is left is one case split on the sign of `a - b`, because the distance between the two
   * limits has to be compared with the tolerance and `abs` is not linear. Each branch is a single
   * `Linarith` step over five hypotheses, which is the triangle inequality written out rather than
   * `Magnitude.ABS_TRIANGLE` applied: the two bounds it would be assembled from are already in
   * hand, and putting them together with the case hypothesis is what the procedure is for.
   *
   * The conclusion is reached through [[BelowEveryPositive]] rather than by contradiction, and what
   * that is worth is stated where that lemma is: not a cheaper foundation, since `abs` costs choice
   * either way, but no step that decides a question by the excluded middle.
   */
  private def uniqueLimit(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds,
    indices: Indices,
    epsilon: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val a = Term.variable("a", values)
    val b = Term.variable("b", values)
    val e = Term.variable("e", values)
    val m = Term.variable("m", numbers)
    val k = Term.variable("k", numbers)

    for {
      toA <- Parser.proposition(theory, notation, "converges (s:num -> real) (a:real)")
      toB <- Parser.proposition(theory, notation, "converges (s:num -> real) (b:real)")
      assumedA <- LogicError.lift(Kernel.assume(toA))
      assumedB <- LogicError.lift(Kernel.assume(toB))

      unfoldedA <- Conv.unfold(convergesDefinition, List(s, a)).flatMap(normaliseRight)
      unfoldedB <- Conv.unfold(convergesDefinition, List(s, b)).flatMap(normaliseRight)
      bodyA <- LogicError.lift(Kernel.eqMp(unfoldedA, assumedA))
      bodyB <- LogicError.lift(Kernel.eqMp(unfoldedB, assumedB))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      half <- Parser.term(theory, notation, "e:real / 2", values)
      halfPositive <- linarith
        .prove("!e:real. 0 < e ==> 0 < e / 2")
        .flatMap(rules.spec(e, _))
        .flatMap(rules.mp(_, assumedPositive))

      nearA <- rules.spec(half, bodyA).flatMap(rules.mp(_, halfPositive))
      nearB <- rules.spec(half, bodyB).flatMap(rules.mp(_, halfPositive))

      // Inside the two witnesses, at the one index that answers both.
      insideA <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (a:real)) < e:real / 2"
      )
      insideB <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE k:num n ==> abs ((s:num -> real) n - (b:real)) < e:real / 2"
      )
      assumedInsideA <- LogicError.lift(Kernel.assume(insideA))
      assumedInsideB <- LogicError.lift(Kernel.assume(insideB))

      index <- Parser.term(theory, notation, "NUM_ADD m:num k:num", numbers)
      aboveM <- rules.specAll(indices.atMostSum, List(m, k))
      aboveK <- for {
        other <- rules.specAll(indices.atMostSum, List(k, m))
        swap <- rules.specAll(indices.commutative, List(k, m))
        carried <- rewriteWith(swap, other)
      } yield carried

      closeA <- rules.spec(index, assumedInsideA).flatMap(rules.mp(_, aboveM))
      closeB <- rules.spec(index, assumedInsideB).flatMap(rules.mp(_, aboveK))

      // The term at the index that answers both, and the two distances, read rather than built:
      // what a reader checks against the case split below is a sentence.
      atIndex <- Parser.term(theory, notation, "(s:num -> real) (NUM_ADD m:num k:num)", values)
      gapA <- Parser.term(
        theory, notation, "(s:num -> real) (NUM_ADD m:num k:num) - (a:real)", values)
      gapB <- Parser.term(
        theory, notation, "(s:num -> real) (NUM_ADD m:num k:num) - (b:real)", values)
      distanceA <- Parser.term(
        theory, notation, "abs ((s:num -> real) (NUM_ADD m:num k:num) - (a:real))", values)
      distanceB <- Parser.term(
        theory, notation, "abs ((s:num -> real) (NUM_ADD m:num k:num) - (b:real))", values)
      distance <- Parser.term(theory, notation, "abs (a:real - b:real)", values)
      difference <- Parser.term(theory, notation, "a:real - b:real", values)

      // The four bounds the triangle inequality is made of, two per limit.
      aboveA <- rules.spec(gapA, bounds.above)
      aboveNegA <- rules.spec(gapA, bounds.aboveNegation)
      aboveB <- rules.spec(gapB, bounds.above)
      aboveNegB <- rules.spec(gapB, bounds.aboveNegation)

      split <- rules.spec(difference, bounds.cases)

      plain <- Parser.proposition(theory, notation, "abs (a:real - b:real) = a - b")
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        lemma <- linarith.prove(
          "!p:real. !q:real. !x:real. !u:real. !v:real. !g:real. !e:real. " +
            "-(x - p) <= u ==> x - q <= v ==> u < e / 2 ==> v < e / 2 ==> g = p - q ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, b, atIndex, distanceA, distanceB, distance, e))
          .flatMap(rules.mp(_, aboveNegA))
          .flatMap(rules.mp(_, aboveB))
          .flatMap(rules.mp(_, closeA))
          .flatMap(rules.mp(_, closeB))
          .flatMap(rules.mp(_, assumed))
      } yield result

      negated <- Parser.proposition(theory, notation, "abs (a:real - b:real) = -(a - b)")
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negated))
        lemma <- linarith.prove(
          "!p:real. !q:real. !x:real. !u:real. !v:real. !g:real. !e:real. " +
            "x - p <= u ==> -(x - q) <= v ==> u < e / 2 ==> v < e / 2 ==> g = -(p - q) ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, b, atIndex, distanceA, distanceB, distance, e))
          .flatMap(rules.mp(_, aboveA))
          .flatMap(rules.mp(_, aboveNegB))
          .flatMap(rules.mp(_, closeA))
          .flatMap(rules.mp(_, closeB))
          .flatMap(rules.mp(_, assumed))
      } yield result

      closeGap <- rules.disjElim(split, fromPlain, fromNegated)

      withoutB <- rules.existsElim(nearB, k, closeGap)
      withoutA <- rules.existsElim(nearA, m, withoutB)

      everyPositive <- rules.disch(positive, withoutA).flatMap(rules.gen(e, _))
      nonNegative <- rules.spec(difference, bounds.nonNegative)
      vanishes <- rules
        .spec(distance, epsilon)
        .flatMap(rules.mp(_, nonNegative))
        .flatMap(rules.mp(_, everyPositive))
      differenceZero <- rules.spec(difference, bounds.zero).flatMap(rules.mp(_, vanishes))
      equal <- linarith
        .prove("!p:real. !q:real. p - q = 0 ==> p = q")
        .flatMap(rules.specAll(_, List(a, b)))
        .flatMap(rules.mp(_, differenceZero))

      result <- rules
        .disch(toB, equal)
        .flatMap(rules.disch(toA, _))
        .flatMap(rules.gen(b, _))
        .flatMap(rules.gen(a, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s t a b. converges s a ==> converges t b ==> converges (\n. s n + t n) (a + b)`
   *
   * The epsilon argument [[uniqueLimit]] runs into a contradiction, run forwards instead. Both
   * sequences are put inside half the tolerance, the two witnesses are taken out with
   * `existsElim`, and the index that answers the goal is their **sum**, which is above each of them
   * by `Peano.NUM_LE_ADD` and needs no maximum that `num` has not got.
   *
   * The distance is settled by [[Bounds]] and `Linarith` rather than by the triangle inequality,
   * and [[Added]]'s note says why at length: inside each branch of `ABS_CASES` the `abs` is gone
   * and what remains is linear over eight atoms, which is inside the fragment `Linarith` decides.
   */
  private def convergesAdd(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds,
    indices: Indices
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val t = Term.variable("t", sequences)
    val a = Term.variable("a", values)
    val b = Term.variable("b", values)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)
    val k = Term.variable("k", numbers)

    for {
      toA <- Parser.proposition(theory, notation, "converges (s:num -> real) (a:real)")
      toB <- Parser.proposition(theory, notation, "converges (t:num -> real) (b:real)")
      assumedA <- LogicError.lift(Kernel.assume(toA))
      assumedB <- LogicError.lift(Kernel.assume(toB))

      unfoldedA <- Conv.unfold(convergesDefinition, List(s, a)).flatMap(normaliseRight)
      unfoldedB <- Conv.unfold(convergesDefinition, List(t, b)).flatMap(normaliseRight)
      bodyA <- LogicError.lift(Kernel.eqMp(unfoldedA, assumedA))
      bodyB <- LogicError.lift(Kernel.eqMp(unfoldedB, assumedB))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      half <- Parser.term(theory, notation, "e:real / 2", values)
      halfPositive <- linarith
        .prove("!e:real. 0 < e ==> 0 < e / 2")
        .flatMap(rules.spec(e, _))
        .flatMap(rules.mp(_, assumedPositive))

      nearA <- rules.spec(half, bodyA).flatMap(rules.mp(_, halfPositive))
      nearB <- rules.spec(half, bodyB).flatMap(rules.mp(_, halfPositive))

      insideA <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (a:real)) < e:real / 2"
      )
      insideB <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE k:num n ==> abs ((t:num -> real) n - (b:real)) < e:real / 2"
      )
      assumedInsideA <- LogicError.lift(Kernel.assume(insideA))
      assumedInsideB <- LogicError.lift(Kernel.assume(insideB))

      // One index above both, and it is a sum rather than a maximum because `num` has no maximum.
      index <- Parser.term(theory, notation, "NUM_ADD m:num k:num", numbers)
      guard <- Parser.proposition(theory, notation, "NUM_LE (NUM_ADD m:num k:num) n:num")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))

      aboveM <- rules.specAll(indices.atMostSum, List(m, k))
      pastM <- rules
        .conjIntro(aboveM, assumedGuard)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(m, index, n)).flatMap(rules.mp(_, both)))

      aboveK <- for {
        other <- rules.specAll(indices.atMostSum, List(k, m))
        swap <- rules.specAll(indices.commutative, List(k, m))
        carried <- rewriteWith(swap, other)
      } yield carried
      pastK <- rules
        .conjIntro(aboveK, assumedGuard)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(k, index, n)).flatMap(rules.mp(_, both)))

      closeA <- rules.spec(n, assumedInsideA).flatMap(rules.mp(_, pastM))
      closeB <- rules.spec(n, assumedInsideB).flatMap(rules.mp(_, pastK))

      // The atoms the two branches below are linear over, read rather than built, for the reason
      // `uniqueLimit` gives: what a reader checks against the case split is a sentence.
      atS <- Parser.term(theory, notation, "(s:num -> real) (n:num)", values)
      atT <- Parser.term(theory, notation, "(t:num -> real) (n:num)", values)
      gapA <- Parser.term(
        theory, notation, "(s:num -> real) (n:num) - (a:real)", values)
      gapB <- Parser.term(
        theory, notation, "(t:num -> real) (n:num) - (b:real)", values)
      distanceA <- Parser.term(
        theory, notation, "abs ((s:num -> real) (n:num) - (a:real))", values)
      distanceB <- Parser.term(
        theory, notation, "abs ((t:num -> real) (n:num) - (b:real))", values)
      total <- Parser.term(
        theory,
        notation,
        "(s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real))",
        values
      )
      distance <- Parser.term(
        theory,
        notation,
        "abs ((s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real)))",
        values
      )

      aboveA <- rules.spec(gapA, bounds.above)
      aboveNegA <- rules.spec(gapA, bounds.aboveNegation)
      aboveB <- rules.spec(gapB, bounds.above)
      aboveNegB <- rules.spec(gapB, bounds.aboveNegation)

      split <- rules.spec(total, bounds.cases)

      plain <- Parser.proposition(
        theory,
        notation,
        "abs ((s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real))) = " +
          "(s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real))"
      )
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        lemma <- linarith.prove(
          "!p:real. !q:real. !x:real. !y:real. !u:real. !v:real. !g:real. !e:real. " +
            "x - p <= u ==> y - q <= v ==> u < e / 2 ==> v < e / 2 ==> " +
            "g = x + y - (p + q) ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, b, atS, atT, distanceA, distanceB, distance, e))
          .flatMap(rules.mp(_, aboveA))
          .flatMap(rules.mp(_, aboveB))
          .flatMap(rules.mp(_, closeA))
          .flatMap(rules.mp(_, closeB))
          .flatMap(rules.mp(_, assumed))
      } yield result

      negatedCase <- Parser.proposition(
        theory,
        notation,
        "abs ((s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real))) = " +
          "-((s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real)))"
      )
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negatedCase))
        lemma <- linarith.prove(
          "!p:real. !q:real. !x:real. !y:real. !u:real. !v:real. !g:real. !e:real. " +
            "-(x - p) <= u ==> -(y - q) <= v ==> u < e / 2 ==> v < e / 2 ==> " +
            "g = -(x + y - (p + q)) ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, b, atS, atT, distanceA, distanceB, distance, e))
          .flatMap(rules.mp(_, aboveNegA))
          .flatMap(rules.mp(_, aboveNegB))
          .flatMap(rules.mp(_, closeA))
          .flatMap(rules.mp(_, closeB))
          .flatMap(rules.mp(_, assumed))
      } yield result

      closeGap <- rules.disjElim(split, fromPlain, fromNegated)

      guarded <- rules.disch(guard, closeGap).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> " +
          "abs ((s:num -> real) n + (t:num -> real) n - ((a:real) + (b:real))) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, index, guarded)

      withoutB <- rules.existsElim(nearB, k, witnessed)
      withoutA <- rules.existsElim(nearA, m, withoutB)
      whole <- rules.disch(positive, withoutA).flatMap(rules.gen(e, _))

      sequence <- Parser.term(
        theory, notation, "\\n:num. (s:num -> real) n + (t:num -> real) n", sequences)
      limit <- Parser.term(theory, notation, "(a:real) + (b:real)", values)
      unfoldedSum <- Conv.unfold(convergesDefinition, List(sequence, limit)).flatMap(normaliseRight)
      bodySum <- rightOf(unfoldedSum)
      _ <- sameStatement(notation, whole, bodySum)
      folded <- Conv
        .sym(unfoldedSum)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))

      result <- rules
        .disch(toB, folded)
        .flatMap(rules.disch(toA, _))
        .flatMap(rules.gen(b, _))
        .flatMap(rules.gen(a, _))
        .flatMap(rules.gen(t, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s a. converges s a ==> converges (\n. -(s n)) (-a)`
   *
   * The same index answers, and the same tolerance: negating a sequence does not move any distance,
   * so nothing is halved and nothing is put together. What the two branches of `ABS_CASES` need is
   * the two bounds the other derivation also uses, and they arrive the other way round, since the
   * quantity whose sign is split is the negation of the one they bound.
   */
  private def convergesNegated(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val a = Term.variable("a", values)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)

    for {
      toA <- Parser.proposition(theory, notation, "converges (s:num -> real) (a:real)")
      assumedA <- LogicError.lift(Kernel.assume(toA))
      unfoldedA <- Conv.unfold(convergesDefinition, List(s, a)).flatMap(normaliseRight)
      bodyA <- LogicError.lift(Kernel.eqMp(unfoldedA, assumedA))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      near <- rules.spec(e, bodyA).flatMap(rules.mp(_, assumedPositive))

      inside <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (a:real)) < e:real"
      )
      assumedInside <- LogicError.lift(Kernel.assume(inside))

      guard <- Parser.proposition(theory, notation, "NUM_LE m:num n:num")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))
      close <- rules.spec(n, assumedInside).flatMap(rules.mp(_, assumedGuard))

      atS <- Parser.term(theory, notation, "(s:num -> real) (n:num)", values)
      gap <- Parser.term(theory, notation, "(s:num -> real) (n:num) - (a:real)", values)
      distanceOf <- Parser.term(
        theory, notation, "abs ((s:num -> real) (n:num) - (a:real))", values)
      total <- Parser.term(
        theory, notation, "-((s:num -> real) (n:num)) - -(a:real)", values)
      distance <- Parser.term(
        theory, notation, "abs (-((s:num -> real) (n:num)) - -(a:real))", values)

      above <- rules.spec(gap, bounds.above)
      aboveNegation <- rules.spec(gap, bounds.aboveNegation)
      split <- rules.spec(total, bounds.cases)

      plain <- Parser.proposition(
        theory,
        notation,
        "abs (-((s:num -> real) (n:num)) - -(a:real)) = " +
          "-((s:num -> real) (n:num)) - -(a:real)"
      )
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        lemma <- linarith.prove(
          "!p:real. !x:real. !u:real. !g:real. !e:real. " +
            "-(x - p) <= u ==> u < e ==> g = -x - -p ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, atS, distanceOf, distance, e))
          .flatMap(rules.mp(_, aboveNegation))
          .flatMap(rules.mp(_, close))
          .flatMap(rules.mp(_, assumed))
      } yield result

      negatedCase <- Parser.proposition(
        theory,
        notation,
        "abs (-((s:num -> real) (n:num)) - -(a:real)) = " +
          "-(-((s:num -> real) (n:num)) - -(a:real))"
      )
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negatedCase))
        lemma <- linarith.prove(
          "!p:real. !x:real. !u:real. !g:real. !e:real. " +
            "x - p <= u ==> u < e ==> g = -(-x - -p) ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, atS, distanceOf, distance, e))
          .flatMap(rules.mp(_, above))
          .flatMap(rules.mp(_, close))
          .flatMap(rules.mp(_, assumed))
      } yield result

      closeGap <- rules.disjElim(split, fromPlain, fromNegated)

      guarded <- rules.disch(guard, closeGap).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> abs (-((s:num -> real) n) - -(a:real)) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, m, guarded)
      eliminated <- rules.existsElim(near, m, witnessed)
      whole <- rules.disch(positive, eliminated).flatMap(rules.gen(e, _))

      sequence <- Parser.term(
        theory, notation, "\\n:num. -((s:num -> real) n)", sequences)
      limit <- Parser.term(theory, notation, "-(a:real)", values)
      unfoldedNeg <- Conv.unfold(convergesDefinition, List(sequence, limit)).flatMap(normaliseRight)
      bodyNeg <- rightOf(unfoldedNeg)
      _ <- sameStatement(notation, whole, bodyNeg)
      folded <- Conv
        .sym(unfoldedNeg)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))

      result <- rules
        .disch(toA, folded)
        .flatMap(rules.gen(a, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s l. converges s l ==> lim s = l`, which is what makes `lim` more than a term.
   *
   * `select` says that a predicate holds of what it chooses **where something satisfies it**, and
   * the convergence in the hypothesis is that something. So `lim s` is a limit of `s`, and
   * [[Unique]] turns "a limit" into "the limit". Both halves are needed and neither is enough: the
   * choice alone would leave `lim s` an arbitrary limit if a sequence could have two.
   */
  private def valueOfConverges(
    logic: Logic,
    classical: Classical,
    theory: Theory,
    notation: Notation,
    valueDefinition: Kernel.Thm,
    unique: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val l = Term.variable("l", values)

    for {
      converges <- Parser.proposition(theory, notation, "converges (s:num -> real) (l:real)")
      assumed <- LogicError.lift(Kernel.assume(converges))

      existential <- Parser.proposition(theory, notation, "?m:real. converges (s:num -> real) m")
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, l, assumed)
      chosen <- classical.witness(witnessed)
      reduced <- Conv
        .betaNormalise(chosen.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chosen)))

      unfolded <- Conv.unfold(valueDefinition, List(s))
      backwards <- Conv.sym(unfolded)
      atLimit <- rewriteWith(backwards, reduced)

      value <- Parser.term(theory, notation, "lim (s:num -> real)", values)
      result <- rules
        .specAll(unique, List(s, value, l))
        .flatMap(rules.mp(_, atLimit))
        .flatMap(rules.mp(_, assumed))
        .flatMap(rules.disch(converges, _))
        .flatMap(rules.gen(l, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s t l N. (!n. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l`
   *
   * Agreement past an index is all a limit sees, and the index where the two hypotheses meet is
   * again a sum rather than a maximum. What the derivation actually spends is one congruence: at an
   * index past both, `s n = t n` turns the distance from `l` into the other sequence's distance
   * from `l`, and the tolerance never moves.
   *
   * Stated with the agreement first because that is the hypothesis a caller has: it knows its
   * sequence settles, and it is asking what that buys.
   */
  private def eventuallyEqual(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    indices: Indices
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val t = Term.variable("t", sequences)
    val l = Term.variable("l", values)
    val bound = Term.variable("N", numbers)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)

    for {
      agreement <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE N:num n ==> (s:num -> real) n = (t:num -> real) n"
      )
      assumedAgreement <- LogicError.lift(Kernel.assume(agreement))

      convergesS <- Parser.proposition(theory, notation, "converges (s:num -> real) (l:real)")
      assumedS <- LogicError.lift(Kernel.assume(convergesS))
      unfoldedS <- Conv.unfold(convergesDefinition, List(s, l)).flatMap(normaliseRight)
      bodyS <- LogicError.lift(Kernel.eqMp(unfoldedS, assumedS))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      near <- rules.spec(e, bodyS).flatMap(rules.mp(_, assumedPositive))

      inside <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (l:real)) < e:real"
      )
      assumedInside <- LogicError.lift(Kernel.assume(inside))

      index <- Parser.term(theory, notation, "NUM_ADD m:num N:num", numbers)
      guard <- Parser.proposition(theory, notation, "NUM_LE (NUM_ADD m:num N:num) n:num")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))

      aboveM <- rules.specAll(indices.atMostSum, List(m, bound))
      pastM <- rules
        .conjIntro(aboveM, assumedGuard)
        .flatMap(both => rules.specAll(indices.transitive, List(m, index, n)).flatMap(rules.mp(_, both)))

      aboveN <- for {
        other <- rules.specAll(indices.atMostSum, List(bound, m))
        swap <- rules.specAll(indices.commutative, List(bound, m))
        carried <- rewriteWith(swap, other)
      } yield carried
      pastN <- rules
        .conjIntro(aboveN, assumedGuard)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(bound, index, n)).flatMap(rules.mp(_, both)))

      close <- rules.spec(n, assumedInside).flatMap(rules.mp(_, pastM))
      same <- rules.spec(n, assumedAgreement).flatMap(rules.mp(_, pastN))
      moved <- rewriteInProposition(same, close)

      guarded <- rules.disch(guard, moved).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?M:num. !n:num. NUM_LE M n ==> abs ((t:num -> real) n - (l:real)) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, index, guarded)
      eliminated <- rules.existsElim(near, m, witnessed)

      whole <- rules.disch(positive, eliminated).flatMap(rules.gen(e, _))
      unfoldedT <- Conv.unfold(convergesDefinition, List(t, l)).flatMap(normaliseRight)
      bodyT <- rightOf(unfoldedT)
      _ <- sameStatement(notation, whole, bodyT)
      folded <- Conv
        .sym(unfoldedT)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))

      result <- rules
        .disch(convergesS, folded)
        .flatMap(rules.disch(agreement, _))
        .flatMap(rules.gen(bound, _))
        .flatMap(rules.gen(l, _))
        .flatMap(rules.gen(t, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * Rewrite the last argument of an application inside a theorem, by congruence.
   *
   * `equation` is `u = v` and `theorem` proves `P ... u`; what comes back proves `P ... v`. Written
   * once because four derivations here want it, and each of them would otherwise take an
   * application apart by hand, which is where a derivation silently starts being about the wrong
   * argument.
   */
  private def rewriteWith(
    equation: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    theorem.conclusion match {
      case App(partial, _) =>
        for {
          congruence <- Conv.apTerm(partial, equation)
          moved <- LogicError.lift(Kernel.eqMp(congruence, theorem))
        } yield moved
      case other => Left(NotOfForm("an application", other))
    }

  /**
   * Rewrite one subterm of a proposition with an equation, wherever in it the subterm occurs.
   *
   * The congruence above reaches the last argument of an application and no further, and what this
   * needs is a term buried under `abs` and a subtraction. So the proposition is abstracted over the
   * subterm, the abstraction is applied to each side of the equation, and the two applications are
   * reduced: that is the general rewrite, written here rather than reached for from `Rewrite`
   * because what is wanted is one occurrence of one term and not a normalising pass.
   */
  private def rewriteInProposition(
    equation: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    Term.destEq(equation.conclusion) match {
      case None => Left(NotOfForm("an equation", equation.conclusion))
      case Some((left, _)) =>
        val placeholder = Conv.freshVariable(
          "u",
          Term.typeOf(left),
          Term.freeVariables(theorem.conclusion) ++ Term.freeVariables(equation.conclusion)
        )

        for {
          replaced <- LogicError.lift(replace(theorem.conclusion, left, placeholder))

          // A replacement that found nothing would make the congruence below a no-op and hand back
          // the theorem it was given, which is what a rewrite that missed looks like from outside.
          _ <- if (replaced != theorem.conclusion) Right(())
               else Left(NotOfForm(s"a proposition mentioning ${left}", theorem.conclusion))

          template <- LogicError.lift(Term.abs(placeholder, replaced))
          congruence <- Conv.apTerm(template, equation)
          reduced <- Conv.betaSides(congruence)
          moved <- LogicError.lift(Kernel.eqMp(reduced, theorem))
        } yield moved
    }

  /** Every occurrence of `target` inside `term`, replaced by `replacement`. */
  private def replace(term: Term, target: Term, replacement: Term): Either[KernelError, Term] =
    if (term == target) Right(replacement)
    else
      term match {
        case App(fn, argument) =>
          for {
            left <- replace(fn, target, replacement)
            right <- replace(argument, target, replacement)
            joined <- Term.app(left, right)
          } yield joined
        // No descent under a binder: the kernel keeps those constructors to itself, and no
        // caller here rewrites inside one. An occurrence that is only under a binder therefore
        // leaves the term unchanged, which the check above turns into a refusal.
        case other => Right(other)
      }

  /** Refuse with both statements named where a derivation and its target have drifted apart. */
  private def sameStatement(
    notation: Notation,
    theorem: Kernel.Thm,
    target: Term
  ): Either[LogicError, Unit] =
    if (theorem.conclusion == target) Right(())
    else Left(NotOfForm(s"a proof of ${Show.show(notation, target)}", theorem.conclusion))

  /**
   * `|- !s. (!n. s n <= s (SUC n)) ==> !m n. NUM_LE m n ==> s m <= s n`
   *
   * A step at a time gives a step to anywhere. The induction is over the **gap** rather than over
   * either index: `NUM_LE m n` is `?d. NUM_ADD m d = n` by definition, so what an induction can
   * reach is `!m d. s m <= s (NUM_ADD m d)`, and the order statement is that with the witness put
   * back inside the existential.
   *
   * `Induct.proveBy` and not `Induct.prove`, because neither half is a rewrite. The base carries
   * the reflexivity of the order across `NUM_ADD m 0 = m` by congruence, which is `LE_OF_EQ`
   * applied to an equation rather than a normalisation, and the step chains the hypothesis with
   * the assumption at one index, which is transitivity over three atoms.
   */
  private def monotoneOrder(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    induct: Induct,
    ofEq: Kernel.Thm,
    orderDefinition: Kernel.Thm,
    addAtZero: Kernel.Thm,
    addAtSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val d = Term.variable("d", numbers)

    for {
      increasing <- Parser.proposition(theory, notation, "!n:num. (s:num -> real) n <= s (SUC n)")
      assumed <- LogicError.lift(Kernel.assume(increasing))
      transitive <- linarith.prove("!a:real. !b:real. !c:real. a <= b ==> b <= c ==> a <= c")

      statement <- Parser.proposition(
        theory, notation, "!m:num. !d:num. (s:num -> real) m <= s (NUM_ADD m d)")

      // **The variables are read off the goals the driver hands over and never taken from the
      // scope above.** `Induct.proveBy` opens the induction on its own fresh variables and leaves
      // the others free as ITS variables, so a base written with the `m` and `d` of this function
      // proves a statement about two other terms of the same name. What that produces is not a
      // type error: it is a theorem about the wrong thing, and what refuses it is `gen` reporting
      // a variable free in a hypothesis, several steps later and about a term nobody wrote.
      overTheGap <- induct.proveBy(
        statement,
        base =>
          for {
            indices <- comparisonIndices(base)
            collapsed <- rules.spec(indices._1, addAtZero)
            carried <- Conv.sym(collapsed).flatMap(Conv.apTerm(s, _))
            sides <- destructEquation(carried)
            result <- rules.specAll(ofEq, List(sides._1, sides._2)).flatMap(rules.mp(_, carried))
          } yield result,
        step =>
          for {
            indices <- comparisonIndices(step.hypothesis.conclusion)
            (index, gapSum) = indices
            opened <- rules.specAll(addAtSuccessor, List(index, argumentOf(gapSum)))
            sides <- destructEquation(opened)
            (_, successor) = sides
            above <- rules.spec(argumentOf(successor), assumed)
            here <- LogicError.lift(Term.app(s, index))
            middle <- LogicError.lift(Term.app(s, argumentOf(successor)))
            top <- LogicError.lift(Term.app(s, successor))
            chained <- rules
              .specAll(transitive, List(here, middle, top))
              .flatMap(rules.mp(_, step.hypothesis))
              .flatMap(rules.mp(_, above))
            carried <- Conv.sym(opened).flatMap(Conv.apTerm(s, _))
            result <- rewriteWith(carried, chained)
          } yield result
      )

      below <- Parser.proposition(theory, notation, "NUM_LE (m:num) (n:num)")
      assumedBelow <- LogicError.lift(Kernel.assume(below))
      unfolded <- Conv.unfold(orderDefinition, List(m, n)).flatMap(normaliseRight)
      witness <- LogicError.lift(Kernel.eqMp(unfolded, assumedBelow))

      inner <- Parser.proposition(theory, notation, "NUM_ADD (m:num) (d:num) = n:num")
      assumedInner <- LogicError.lift(Kernel.assume(inner))
      atGap <- rules.specAll(overTheGap, List(m, d))
      carriedInner <- Conv.apTerm(s, assumedInner)
      atIndex <- rewriteWith(carriedInner, atGap)
      eliminated <- rules.existsElim(witness, d, atIndex)

      result <- rules
        .disch(below, eliminated)
        .flatMap(rules.gen(n, _))
        .flatMap(rules.gen(m, _))
        .flatMap(rules.disch(increasing, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s. (!n. s n <= s (SUC n)) ==> (?b. !n. s n <= b) ==> ?l. converges s l`
   *
   * The monotone convergence theorem, and the second time `COMPLETENESS` is spent in this
   * repository. The argument is the textbook one and every step of it is here: the image of the
   * sequence is a non-empty set bounded above, so it has a least upper bound; no term passes it;
   * and past any tolerance one term does, because otherwise the supremum would not be least.
   *
   * == The step this logic could not take until today ==
   *
   * "Otherwise the supremum would not be least" is a negated universal turned into a witness, and
   * `Peano.NUM_ARCHIMEDES` records that this logic had no rule for it and that its own derivation
   * was turned around to avoid needing one. There is no turning this one around: the witness IS
   * the index the convergence needs. `Classical.NOT_FORALL` is what landed with this theorem, and
   * the theorem is what paid for it.
   *
   * == What the derivation does NOT need, which is worth knowing before reading it ==
   *
   * No maximum over indices, because monotonicity carries one index to every later one, which is
   * [[MonotoneBelow]]. No second case split on the sign of the distance beyond the one `abs`
   * forces: past the witness the terms sit between the supremum less the tolerance and the
   * supremum, so both branches are a linear step over three comparisons.
   */
  private def monotoneConvergence(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    completeness: Kernel.Thm,
    notForall: Kernel.Thm,
    doubleNegation: Kernel.Thm,
    irreflexive: Kernel.Thm,
    weakFromNegated: Kernel.Thm,
    bounds: Bounds,
    monotoneBelow: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val bound = Term.variable("b", values)
    val supremum = Term.variable("t", values)
    val e = Term.variable("e", values)
    val x = Term.variable("x", values)
    val n = Term.variable("n", numbers)
    val k = Term.variable("k", numbers)

    val memberText = "?n:num. x:real = (s:num -> real) n"

    /** `!x. (?n. x = s n) ==> x <= <ceiling>` from `!n. s n <= <ceiling>`. */
    def upperBoundOf(ceiling: String, everyTerm: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        member <- Parser.proposition(theory, notation, memberText)
        assumedMember <- LogicError.lift(Kernel.assume(member))
        witnessEquation <- Parser.proposition(
          theory, notation, "x:real = (s:num -> real) (k:num)")
        assumedWitness <- LogicError.lift(Kernel.assume(witnessEquation))
        ceilingTerm <- Parser.term(theory, notation, ceiling, values)
        atK <- rules.spec(k, everyTerm)
        applied <- LogicError.lift(Term.app(s, k))
        carry <- linarith.prove("!a:real. !b:real. !c:real. a = b ==> b <= c ==> a <= c")
        atX <- rules
          .specAll(carry, List(x, applied, ceilingTerm))
          .flatMap(rules.mp(_, assumedWitness))
          .flatMap(rules.mp(_, atK))
        eliminated <- rules.existsElim(assumedMember, k, atX)
        result <- rules.disch(member, eliminated).flatMap(rules.gen(x, _))
      } yield result

    for {
      increasing <- Parser.proposition(theory, notation, "!n:num. (s:num -> real) n <= s (SUC n)")
      assumedIncreasing <- LogicError.lift(Kernel.assume(increasing))
      boundedStatement <- Parser.proposition(
        theory, notation, "?b:real. !n:num. (s:num -> real) n <= b")
      assumedBounded <- LogicError.lift(Kernel.assume(boundedStatement))

      // The image is inhabited, by the first term and nothing cleverer.
      inhabitedStatement <- Parser.proposition(
        theory, notation, "?x:real. ?n:num. x = (s:num -> real) n")
      inhabitedPredicate <- logic
        .destExistsPredicate(inhabitedStatement)
        .toRight(NotOfForm("an existential", inhabitedStatement))
      first <- Parser.term(theory, notation, "(s:num -> real) 0", values)
      atFirstStatement <- Parser.proposition(
        theory, notation, "?n:num. (s:num -> real) 0 = s n")
      atFirstPredicate <- logic
        .destExistsPredicate(atFirstStatement)
        .toRight(NotOfForm("an existential", atFirstStatement))
      zeroIndex <- Parser.term(theory, notation, "0:num", numbers)
      atFirst <- rules.existsIntro(atFirstPredicate, zeroIndex, Kernel.refl(first))
      inhabited <- rules.existsIntro(inhabitedPredicate, first, atFirst)

      // And bounded above, which is the hypothesis with the image wrapped round it.
      insideBounded <- Parser.proposition(
        theory, notation, "!n:num. (s:num -> real) n <= b:real")
      assumedInside <- LogicError.lift(Kernel.assume(insideBounded))
      boundsTheImage <- upperBoundOf("b:real", assumedInside)
      boundedAboveStatement <- Parser.proposition(
        theory,
        notation,
        "?y:real. !x:real. (?n:num. x = (s:num -> real) n) ==> x <= y"
      )
      boundedAbovePredicate <- logic
        .destExistsPredicate(boundedAboveStatement)
        .toRight(NotOfForm("an existential", boundedAboveStatement))
      boundedAboveAt <- rules.existsIntro(boundedAbovePredicate, bound, boundsTheImage)
      boundedAbove <- rules.existsElim(assumedBounded, bound, boundedAboveAt)

      // So there is a least upper bound.
      image <- Parser.term(
        theory, notation, "\\x:real. ?n:num. x = (s:num -> real) n", Type.fun(values, Type.Bool))
      atImage <- rules.spec(image, completeness)
      opened <- Conv
        .betaNormalise(atImage.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atImage)))
      premises <- rules.conjIntro(inhabited, boundedAbove)
      supremumExists <- rules.mp(opened, premises)

      supremumStatement <- Parser.proposition(
        theory,
        notation,
        "(!x:real. (?n:num. x = (s:num -> real) n) ==> x <= t:real) /\\ " +
          "(!y:real. (!x:real. (?n:num. x = (s:num -> real) n) ==> x <= y) ==> t <= y)"
      )
      assumedSupremum <- LogicError.lift(Kernel.assume(supremumStatement))
      upper <- rules.conjElim1(assumedSupremum)
      least <- rules.conjElim2(assumedSupremum)

      // No term passes it.
      //
      // **The bound name is `u` and not `n`, and that is not style.** Written `?n. s n = s n` the
      // binder captures the free index this is about, the predicate becomes `\u. s u = s u`, and
      // what comes out is a true theorem about the wrong thing. Nothing refuses it at the point it
      // is built: `Rules.mp` does not compare its antecedent, so the mismatch travels as an extra
      // hypothesis and surfaces several steps later as a variable free in a hypothesis, naming a
      // term nobody wrote. The check below is what turns it back into a refusal where it happens.
      atNStatement <- Parser.proposition(
        theory, notation, "?u:num. (s:num -> real) (n:num) = s u")
      atNPredicate <- logic
        .destExistsPredicate(atNStatement)
        .toRight(NotOfForm("an existential", atNStatement))
      applied <- LogicError.lift(Term.app(s, n))
      isMember <- rules.existsIntro(atNPredicate, n, Kernel.refl(applied))
      _ <- sameStatement(notation, isMember, atNStatement)
      belowSupremumAtN <- rules.spec(applied, upper).flatMap(rules.mp(_, isMember))
      belowSupremum <- rules.gen(n, belowSupremumAtN)

      // The convergence itself, at an arbitrary tolerance.
      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))

      // Suppose no term passes the supremum less the tolerance.
      noneStatement <- Parser.proposition(
        theory, notation, "!n:num. ~(t:real - e:real < (s:num -> real) n)")
      assumedNone <- LogicError.lift(Kernel.assume(noneStatement))
      gap <- Parser.term(theory, notation, "t:real - e:real", values)
      belowGapAtN <- rules
        .specAll(weakFromNegated, List(gap, applied))
        .flatMap(rules.mp(_, rules.spec(n, assumedNone).getOrElse(assumedNone)))
      belowGap <- rules.gen(n, belowGapAtN)
      gapBoundsTheImage <- upperBoundOf("t:real - e:real", belowGap)
      leastAtGap <- rules.spec(gap, least).flatMap(rules.mp(_, gapBoundsTheImage))
      absurd <- linarith
        .prove("!a:real. !b:real. 0 < b ==> a <= a - b ==> a < a")
        .flatMap(rules.specAll(_, List(supremum, e)))
        .flatMap(rules.mp(_, assumedPositive))
        .flatMap(rules.mp(_, leastAtGap))
      clash <- rules.spec(supremum, irreflexive).flatMap(rules.notElim(_, absurd))
      notNone <- rules.notIntro(noneStatement, clash)

      // So one does, and that is the index the convergence wants.
      predicate <- Parser.term(
        theory,
        notation,
        "\\n:num. ~(t:real - e:real < (s:num -> real) n)",
        Type.fun(numbers, Type.Bool)
      )
      // **`NOT_FORALL` is polymorphic and has to be instantiated at `num` before it can be
      // specialised**, which is a step a reader of the derivation will not expect because nothing
      // else here is polymorphic. Without it the refusal is a type error about `'a -> bool` against
      // `num -> bool`, which names the symptom rather than the omission.
      atIndices = Kernel.instType(Map(Classical.TypeVariable -> numbers), notForall)
      passes <- rules
        .spec(predicate, atIndices)
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))
        .flatMap(rules.mp(_, notNone))

      doubledStatement <- Parser.proposition(
        theory, notation, "~(~(t:real - e:real < (s:num -> real) (k:num)))")
      assumedDoubled <- LogicError.lift(Kernel.assume(doubledStatement))
      atWitnessStatement <- Parser.proposition(
        theory, notation, "t:real - e:real < (s:num -> real) (k:num)")
      atWitness <- rules
        .spec(atWitnessStatement, doubleNegation)
        .flatMap(rules.mp(_, assumedDoubled))

      // Past the witness every term sits between the supremum less the tolerance and the supremum.
      guard <- Parser.proposition(theory, notation, "NUM_LE (k:num) (n:num)")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))
      monotone <- rules
        .spec(s, monotoneBelow)
        .flatMap(rules.mp(_, assumedIncreasing))
        .flatMap(rules.specAll(_, List(k, n)))
        .flatMap(rules.mp(_, assumedGuard))

      atK <- LogicError.lift(Term.app(s, k))
      difference <- Parser.term(
        theory, notation, "(s:num -> real) (n:num) - t:real", values)
      distance <- Parser.term(
        theory, notation, "abs ((s:num -> real) (n:num) - t:real)", values)
      split <- rules.spec(difference, bounds.cases)

      plain <- Parser.proposition(
        theory, notation, "abs ((s:num -> real) (n:num) - t:real) = s n - t")
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        lemma <- linarith.prove(
          "!g:real. !a:real. !b:real. !e:real. g = a - b ==> a <= b ==> 0 < e ==> g < e")
        result <- rules
          .specAll(lemma, List(distance, applied, supremum, e))
          .flatMap(rules.mp(_, assumed))
          .flatMap(rules.mp(_, belowSupremumAtN))
          .flatMap(rules.mp(_, assumedPositive))
      } yield result

      negated <- Parser.proposition(
        theory, notation, "abs ((s:num -> real) (n:num) - t:real) = -(s n - t)")
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negated))
        lemma <- linarith.prove(
          "!g:real. !a:real. !b:real. !c:real. !e:real. " +
            "g = -(a - b) ==> b - e < c ==> c <= a ==> g < e")
        result <- rules
          .specAll(lemma, List(distance, applied, supremum, atK, e))
          .flatMap(rules.mp(_, assumed))
          .flatMap(rules.mp(_, atWitness))
          .flatMap(rules.mp(_, monotone))
      } yield result

      close <- rules.disjElim(split, fromPlain, fromNegated)

      guarded <- rules.disch(guard, close).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> abs ((s:num -> real) n - t:real) < e:real"
      )
      existentialPredicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(existentialPredicate, k, guarded)
      atTolerance <- rules.existsElim(passes, k, witnessed)

      body <- rules.disch(positive, atTolerance).flatMap(rules.gen(e, _))
      unfolded <- Conv.unfold(convergesDefinition, List(s, supremum)).flatMap(normaliseRight)
      target <- rightOf(unfolded)
      _ <- sameStatement(notation, body, target)
      converges <- Conv
        .sym(unfolded)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, body)))

      answer <- Parser.proposition(theory, notation, "?l:real. converges (s:num -> real) l")
      answerPredicate <- logic
        .destExistsPredicate(answer)
        .toRight(NotOfForm("an existential", answer))
      someLimit <- rules.existsIntro(answerPredicate, supremum, converges)
      eliminated <- rules.existsElim(supremumExists, supremum, someLimit)

      result <- rules
        .disch(boundedStatement, eliminated)
        .flatMap(rules.disch(increasing, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /** The two sides of an equation a theorem states. */
  private def destructEquation(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
    Term.destEq(theorem.conclusion).toRight(NotOfForm("an equation", theorem.conclusion))

  /**
   * The indices two applications of one sequence are compared at.
   *
   * `s m <= s (NUM_ADD m d)` gives `m` and `NUM_ADD m d`, which is what an induction step needs in
   * order to be about the driver's variables rather than about the caller's.
   */
  private def comparisonIndices(proposition: Term): Either[LogicError, (Term, Term)] =
    proposition match {
      case App(App(_, App(_, left)), App(_, right)) => Right((left, right))
      case other => Left(NotOfForm("a comparison of two terms of one sequence", other))
    }

  /** The argument of an application, which is what a successor wraps. */
  private def argumentOf(term: Term): Term = term match {
    case App(_, argument) => argument
    case other => other
  }

  /** Beta-normalise the right side of an equation, keeping it an equation. */
  private def normaliseRight(equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      right <- rightOf(equation)
      normal <- Conv.betaNormalise(right)
      joined <- Conv.trans(equation, normal)
    } yield joined

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
