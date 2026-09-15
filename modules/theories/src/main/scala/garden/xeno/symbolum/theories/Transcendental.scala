package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The exponential, the sine, the cosine, the logarithm and the hyperbolic pair, defined rather than
 * assumed.
 *
 * Until this landed the front page said, of the first four, that *the theory has no constant for
 * them*. There are six now and none of them costs an axiom: `exp`, `sin` and `cos` are their power
 * series read through [[Limit.Value]], `ln` is the inverse of the exponential named by choice, and
 * `sinh` and `cosh` are built from `exp` for the reason the heading below gives. What that buys
 * immediately is that a claim about them is a **proposition** here, which it was not: `Ask` on
 * `sin x * sin x + cos x * cos x = 1` came back as a parse error about an unknown constant, and it
 * now comes back as a claim the prover cannot settle. Those are different answers and the second is
 * the honest one.
 *
 * == What is proved about them today, and what is not ==
 *
 * The value of each at zero, and for the hyperbolic pair two identities besides. `EXP_ZERO`,
 * `SIN_ZERO` and `COS_ZERO` are reachable because at zero every series here **stops moving**: past
 * the first term every summand carries a power of zero, so the partial sums are eventually constant
 * and `Limit.CONVERGES_EVENTUALLY` with `Limit.CONVERGES_CONSTANT` settles them without any
 * convergence theorem at all. `SINH_ZERO`, `COSH_ZERO`, `COSH_PLUS_SINH` and `COSH_MINUS_SINH` are
 * cheaper still and are pure algebra, which is the heading two below.
 *
 * **Everywhere else the constants denote and nothing is provable about them**, which is the same
 * silence `NUM_GCD ZERO ZERO` leaves and is stated here rather than left to be discovered. `exp 1`
 * is a term; that it is above `2` is not a theorem, because the series at `1` converges and nothing
 * here can say so yet. What closes that gap is the monotone convergence theorem in [[Limit]] and
 * then a comparison with a geometric series, which `Series.SUM_GEOMETRIC` already holds. The
 * addition theorem `exp (x + y) = exp x * exp y` is further: it wants the Cauchy product, and
 * `Series.SUM_SWAP` is the half of that which exists.
 *
 * `ln` has **no fact at all** and that is not an oversight either: every one of them wants the
 * exponential to be onto the positives, which is the intermediate value theorem, which wants
 * continuity, which is not written. The constant is here because it is written the moment the
 * exponential is, and a development that defined three of the four would leave a reader asking
 * which of the two reasons applied to the fourth.
 *
 * == The hyperbolic pair is not a series, and that is a decision rather than an inconsistency ==
 *
 * `sinh x` is `(exp x - exp (-x)) / 2` and `cosh x` is the same with the other sign.
 * `docs/adr/0017` records the argument; what a reader of this file needs is the shape of it.
 * `sin` and `cos` are series **because there is nothing else here to define them from**: the route
 * through the exponential needs a complex one, and `docs/adr/0007` puts the integers and the
 * rationals before anything of that kind. These two need no such detour, so the definition that
 * costs one line is available, and it is what makes [[CosinePlusSine]] provable today where the
 * series would have made it wait for a rearrangement of a series into its even and odd parts.
 *
 * What the pair does **not** get from that is the identity a reader expects next:
 * `cosh x * cosh x - sinh x * sinh x = 1` needs `exp x * exp (0 - x) = 1`, which is the addition
 * theorem, which wants the Cauchy product. So they arrive with the same silence `exp` has rather
 * than a smaller one.
 *
 * == Why the series and not an axiom ==
 *
 * `docs/adr/0017` is the decision and the alternatives it rejects. The short form: a characterising
 * axiom for each of these would add four to the trusted base and it would be the first time this
 * repository asserted something about a domain it could construct instead, where the standing rule
 * is that a result is added by proving it; `docs/adr/0007` is what commits the axiom count to
 * coming down. The cost of the construction is that the facts arrive slowly; the cost of the axiom
 * is that they arrive untrue-until-checked and nobody ever checks.
 *
 * == The sine's series is written with `0 - 1` and not with `-1` ==
 *
 * Both parse and they are different terms. What the recurrences fire on is the subtraction, which
 * `Ring` normalises; the prefix negation is a constant of its own and would leave `Power (-1) k`
 * as an atom in every derivation below. This is the one place in the file where the concrete
 * syntax was chosen for the rewriter rather than for the reader, and the reader gets this
 * paragraph instead.
 */
final class Transcendental private (
  val limit: Limit,
  val series: Series,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = limit.magnitude.classical.logic
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

  /** `|- exp 0 = 1` */
  def exponentialAtZero: Either[LogicError, Kernel.Thm] = fact(Transcendental.ExponentialAtZero)

  /** `|- sin 0 = 0` */
  def sineAtZero: Either[LogicError, Kernel.Thm] = fact(Transcendental.SineAtZero)

  /** `|- cos 0 = 1` */
  def cosineAtZero: Either[LogicError, Kernel.Thm] = fact(Transcendental.CosineAtZero)

  /** `|- sinh 0 = 0` */
  def hyperbolicSineAtZero: Either[LogicError, Kernel.Thm] =
    fact(Transcendental.HyperbolicSineAtZero)

  /** `|- cosh 0 = 1` */
  def hyperbolicCosineAtZero: Either[LogicError, Kernel.Thm] =
    fact(Transcendental.HyperbolicCosineAtZero)

  /** `|- !x. cosh x + sinh x = exp x` */
  def cosinePlusSine: Either[LogicError, Kernel.Thm] = fact(Transcendental.CosinePlusSine)
}

object Transcendental {

  /** `exp x` is the sum of `x^i / i!`. */
  val Exponential: String = "exp"

  /** `sin x` is the sum of `(-1)^k x^(2k+1) / (2k+1)!`. */
  val Sine: String = "sin"

  /** `cos x` is the sum of `(-1)^k x^(2k) / (2k)!`. */
  val Cosine: String = "cos"

  /** `ln y` is the real whose exponential is `y`, where there is one. */
  val Logarithm: String = "ln"

  /** `sinh x` is `(exp x - exp (-x)) / 2`. */
  val HyperbolicSine: String = "sinh"

  /** `cosh x` is `(exp x + exp (-x)) / 2`. */
  val HyperbolicCosine: String = "cosh"

  /**
   * The exponential series, as the text a person checks against the informal claim.
   *
   * `Sum f n` is the first `n` terms, indexed from zero, so the sequence whose limit this is has
   * `Sum f n` as its `n`th entry and the series is what it converges to. Nothing here says it
   * converges; see the file's docstring for what that costs and where it is going.
   */
  val ExponentialBody: String =
    "\\x:real. lim (\\n:num. Sum (\\i:num. Power x i / real_of_num (NUM_FACT i)) n)"

  /** The sine's series, odd powers with alternating signs. */
  val SineBody: String =
    "\\x:real. lim (\\n:num. Sum (\\k:num. Power (0 - 1) k * " +
      "(Power x (NUM_ADD (NUM_MUL 2 k) 1) / " +
      "real_of_num (NUM_FACT (NUM_ADD (NUM_MUL 2 k) 1)))) n)"

  /** The cosine's series, even powers with alternating signs. */
  val CosineBody: String =
    "\\x:real. lim (\\n:num. Sum (\\k:num. Power (0 - 1) k * " +
      "(Power x (NUM_MUL 2 k) / real_of_num (NUM_FACT (NUM_MUL 2 k)))) n)"

  /**
   * The logarithm, which is the inverse of the exponential named by choice.
   *
   * The same construction as `NUM_GCD` and `Limit.Value`, and the same silence: at an argument the
   * exponential does not reach, `ln` denotes and nothing is provable about it. Unlike those two,
   * **nothing is provable about it anywhere yet**, because what would pin it is that the
   * exponential is onto the positive reals and that is the intermediate value theorem.
   */
  val LogarithmBody: String = "\\y:real. select (\\x:real. exp x = y)"

  /**
   * The hyperbolic sine, from the exponential rather than from its own series.
   *
   * **This is the one place in the file where a constant is not a power series**, and the reason is
   * in `docs/adr/0017` under its own heading. The short form: `sin` and `cos` are series because
   * there is no complex exponential here to define them from, and these two need no such detour,
   * so defining them from `exp` costs one line, makes [[CosinePlusSine]] provable today, and makes
   * every later fact about the pair a consequence of whatever gets proved about `exp` rather than
   * of a second series argument.
   */
  val HyperbolicSineBody: String = "\\x:real. (exp x - exp (0 - x)) / 2"

  /** The hyperbolic cosine, the same construction with the other sign. */
  val HyperbolicCosineBody: String = "\\x:real. (exp x + exp (0 - x)) / 2"

  /** `|- exp 0 = 1` */
  val ExponentialAtZero: String = "EXP_ZERO"

  /** `|- sin 0 = 0` */
  val SineAtZero: String = "SIN_ZERO"

  /** `|- cos 0 = 1` */
  val CosineAtZero: String = "COS_ZERO"

  /** `|- sinh 0 = 0` */
  val HyperbolicSineAtZero: String = "SINH_ZERO"

  /** `|- cosh 0 = 1` */
  val HyperbolicCosineAtZero: String = "COSH_ZERO"

  /**
   * `|- !x. cosh x + sinh x = exp x`, which is what the definition from `exp` buys immediately.
   *
   * One linear step over two atoms, and it is the only fact in this file that relates two of these
   * constants to each other at an arbitrary argument. Under the series definition it would need the
   * rearrangement of a series into its even and odd parts, which this repository does not have.
   */
  val CosinePlusSine: String = "COSH_PLUS_SINH"

  /** `|- !x. cosh x - sinh x = exp (0 - x)`, the same step with the other sign. */
  val CosineMinusSine: String = "COSH_MINUS_SINH"

  /** Everything this development proves, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    ExponentialAtZero -> "exp 0 = 1",
    SineAtZero -> "sin 0 = 0",
    CosineAtZero -> "cos 0 = 1",
    HyperbolicSineAtZero -> "sinh 0 = 0",
    HyperbolicCosineAtZero -> "cosh 0 = 1",
    CosinePlusSine -> "!x:real. cosh x + sinh x = exp x",
    CosineMinusSine -> "!x:real. cosh x - sinh x = exp (0 - x)"
  )

  private val values: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  /** The standard development, which is the chain's own and not a second one beside it. */
  lazy val standard: Transcendental = Chain.standard.transcendental

  /**
   * The four constants over a chain that already holds a limit, and the three values at zero.
   *
   * `base` is the theory to extend rather than `limit.theory`, for the reason `Rotation` gives: a
   * constant declared into a side branch is unreachable from every link above it.
   */
  def construct(
    limit: Limit,
    series: Series,
    peano: Peano,
    coding: Coding,
    induct: Induct,
    successor: Successor,
    naturals: Natural,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Transcendental] = {
    val classical = limit.magnitude.classical

    for {
      exponentialBody <- Parser.term(base, notation, ExponentialBody)
      definedExponential <- LogicError.lift(
        Kernel.defineConstant(base, Exponential, exponentialBody))
      (afterExponential, exponentialDefinition) = definedExponential

      sineBody <- Parser.term(afterExponential, notation, SineBody)
      definedSine <- LogicError.lift(Kernel.defineConstant(afterExponential, Sine, sineBody))
      (afterSine, sineDefinition) = definedSine

      cosineBody <- Parser.term(afterSine, notation, CosineBody)
      definedCosine <- LogicError.lift(Kernel.defineConstant(afterSine, Cosine, cosineBody))
      (afterCosine, cosineDefinition) = definedCosine

      logarithmBody <- Parser.term(afterCosine, notation, LogarithmBody)
      definedLogarithm <- LogicError.lift(
        Kernel.defineConstant(afterCosine, Logarithm, logarithmBody))
      (afterLogarithm, logarithmDefinition) = definedLogarithm

      // The two that are not series, and they are defined after `exp` because they are defined
      // **from** it. `docs/adr/0017` has the argument under its own heading.
      hyperbolicSineBody <- Parser.term(afterLogarithm, notation, HyperbolicSineBody)
      definedHyperbolicSine <- LogicError.lift(
        Kernel.defineConstant(afterLogarithm, HyperbolicSine, hyperbolicSineBody))
      (afterHyperbolicSine, hyperbolicSineDefinition) = definedHyperbolicSine

      hyperbolicCosineBody <- Parser.term(afterHyperbolicSine, notation, HyperbolicCosineBody)
      definedHyperbolicCosine <- LogicError.lift(
        Kernel.defineConstant(afterHyperbolicSine, HyperbolicCosine, hyperbolicCosineBody))
      (theory, hyperbolicCosineDefinition) = definedHyperbolicCosine

      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(limit.magnitude.order)

      recurrences <- Vector(
        series.fact(Series.AtZero),
        series.fact(Series.AtSuccessor),
        series.fact(Series.PowerAtZero),
        series.fact(Series.PowerAtSuccessor),
        series.fact(Series.PowerOfSum),
        coding.fact(Coding.FactorialAtZero),
        coding.fact(Coding.FactorialAtSuccessor),
        peano.fact(Peano.MulAtZero),
        peano.fact(Peano.MulAtSuccessor),
        peano.fact(Peano.AddAtZero),
        peano.fact(Peano.AddAtSuccessor),
        peano.fact(Peano.EmbedsZero),
        peano.fact(Peano.EmbedsSuccessor)
      ).foldRight[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
        case (next, rest) => next.flatMap(one => rest.map(one +: _))
      }

      // `Power 0 2 = 0` is the one step the recurrences cannot take on their own: the exponent is a
      // numeral of `num` and every recurrence over `num` is stated at `SUC n`. `Successor` is what
      // spells it, which is the whole reason that file exists.
      squareOfZero <- Parser
        .proposition(theory, notation, "Power (0:real) (2:num) = 0")
        .flatMap(successor.prove)

      oneIsSuccessor <- peano.fact(Peano.NumeralOneIsSuccessorOfZero)

      // **Two sets and not one, and the reason is a numeral.** `NUM_ONE_SUC` rewrites the `1`
      // inside a bit encoding, so with it in the set the `2` of the cosine's exponent becomes
      // `NUM_BIT0 (SUC ZERO)` and [[squareOfZero]], which is about `NUM_BIT0 NUM_ONE`, stops
      // matching the term it was proved for. The sine needs `NUM_ONE_SUC` because its exponent
      // carries a written `1`; the cosine's carries a written `2` and needs the other. Handing
      // both to both is what was tried first, and the refusal it produced named a residue with
      // `Power 0 2` still in it, which is this paragraph.
      numeralEquations = recurrences :+ oneIsSuccessor
      evenEquations = recurrences :+ squareOfZero

      exponential <- exponentialValue(
        logic, linarith, theory, notation, limit, induct, naturals, peano,
        exponentialDefinition, numeralEquations)

      sine <- sineValue(
        logic, theory, notation, limit, series, induct, sineDefinition, numeralEquations)

      cosine <- cosineValue(
        logic, linarith, theory, notation, limit, series, induct, naturals, peano,
        cosineDefinition, recurrences, evenEquations)

      hyperbolic <- hyperbolicFacts(
        logic, linarith, series.ring, theory, notation,
        hyperbolicSineDefinition, hyperbolicCosineDefinition, exponential)
    } yield new Transcendental(
      limit,
      series,
      theory,
      notation,
      Map(
        Exponential -> exponentialDefinition,
        Sine -> sineDefinition,
        Cosine -> cosineDefinition,
        Logarithm -> logarithmDefinition,
        HyperbolicSine -> hyperbolicSineDefinition,
        HyperbolicCosine -> hyperbolicCosineDefinition
      ),
      Map(
        ExponentialAtZero -> exponential,
        SineAtZero -> sine,
        CosineAtZero -> cosine
      ) ++ hyperbolic
    )
  }

  /**
   * `|- exp 0 = 1`, which is the first value any of these constants has.
   *
   * At zero the series is `1 + 0 + 0 + ...`: the summand is `0^i / i!`, which is `1` at `i = 0` by
   * `POWER_ZERO` and zero afterwards because `0^(SUC i)` carries a factor of zero. So every partial
   * sum from the first on is `1`, which is one induction, and a sequence that is eventually
   * constant converges to that constant, which is [[Limit.Eventually]] over [[Limit.Constant]].
   *
   * The step that is easy to miss is [[agreesPastOne]]: the induction proves the partial sum at
   * `SUC n` and what the limit wants is the partial sum at every `n` from `SUC 0` on. Those are the
   * same statement only because every such `n` **is** a successor, which is `NUM_CASES`.
   */
  private def exponentialValue(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    limit: Limit,
    induct: Induct,
    naturals: Natural,
    peano: Peano,
    definition: Kernel.Thm,
    equations: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val summand = "\\i:num. Power 0 i / real_of_num (NUM_FACT i)"

    for {
      partial <- Parser
        .proposition(theory, notation, s"!n:num. Sum ($summand) (SUC n) = 1")
        .flatMap(induct.prove(_, equations))
      one <- Parser.term(theory, notation, "1:real", values)
      agreement <- agreesPastOne(
        logic, theory, notation, naturals, peano, partial, summand, "1:real")
      result <- valueOfSeries(
        logic, theory, notation, limit, definition, agreement, one, "SUC (0:num)")
    } yield result
  }

  /**
   * `|- sin 0 = 0`, and this one needs no case analysis at all.
   *
   * Every summand of the sine's series at zero carries `0^(2k+1)`, an odd power of zero, so every
   * one of them is zero and so is every partial sum, from the empty one on. That is
   * `SUM_CONGRUENCE` against the constant zero sequence and `SUM_OF_ZERO`, which is cheaper than
   * the induction the exponential needs and is the shape to reach for whenever a summand vanishes
   * pointwise.
   */
  private def sineValue(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    limit: Limit,
    series: Series,
    induct: Induct,
    definition: Kernel.Thm,
    equations: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val summand =
      "\\k:num. Power (0 - 1) k * (Power 0 (NUM_ADD (NUM_MUL 2 k) 1) / " +
        "real_of_num (NUM_FACT (NUM_ADD (NUM_MUL 2 k) 1)))"

    for {
      pointwise <- Parser
        .proposition(
          theory,
          notation,
          "!k:num. Power (0 - 1) k * (Power 0 (NUM_ADD (NUM_MUL 2 k) 1) / " +
            "real_of_num (NUM_FACT (NUM_ADD (NUM_MUL 2 k) 1))) = 0"
        )
        .flatMap(induct.prove(_, equations))

      sums <- everySumVanishes(logic, theory, notation, series, summand, pointwise)
      agreement <- agreesEverywhere(logic, theory, notation, sums)
      zero <- Parser.term(theory, notation, "0:real", values)
      result <- valueOfSeries(
        logic, theory, notation, limit, definition, agreement, zero, "0:num")
    } yield result
  }

  /**
   * `|- cos 0 = 1`, which is the exponential's argument with one extra step in front.
   *
   * The cosine's summand at zero is `1` at `k = 0` and zero afterwards, the same shape as the
   * exponential's, and the induction that proves the partial sums directly is **refused**: the
   * rewriter opens `0^(2(SUC k))` into a product and the induction hypothesis, whose left side is
   * the untouched sum, no longer matches what is left. That is the trap `Induct`'s own docstring
   * records, met here for the third time.
   *
   * The route round it is `SUM_SHIFT`: the sum of the tail is the whole sum without its first term,
   * the tail vanishes pointwise, and what is left is the first term, which is `1`. Nothing is
   * assumed about the induction hypothesis because there is no induction.
   */
  private def cosineValue(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    limit: Limit,
    series: Series,
    induct: Induct,
    naturals: Natural,
    peano: Peano,
    definition: Kernel.Thm,
    equations: Vector[Kernel.Thm],
    evenEquations: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val summand =
      "\\k:num. Power (0 - 1) k * (Power 0 (NUM_MUL 2 k) / " +
        "real_of_num (NUM_FACT (NUM_MUL 2 k)))"

    for {
      tail <- Parser
        .proposition(
          theory,
          notation,
          "!k:num. Power (0 - 1) (SUC k) * (Power 0 (NUM_MUL 2 (SUC k)) / " +
            "real_of_num (NUM_FACT (NUM_MUL 2 (SUC k)))) = 0"
        )
        .flatMap(induct.prove(_, evenEquations))

      first <- Parser
        .proposition(
          theory,
          notation,
          "Power (0 - 1) 0 * (Power 0 (NUM_MUL 2 0) / real_of_num (NUM_FACT (NUM_MUL 2 0))) = 1"
        )
        .flatMap(goal =>
          Rewrite.Rule
            .all(logic, equations)
            .flatMap(rules => Induct.afterRewriting(rules, goal)(series.ring.prove)))

      partial <- partialSumsPastOne(
        logic, linarith, theory, notation, series, summand, tail, first)

      agreement <- agreesPastOne(
        logic, theory, notation, naturals, peano, partial, summand, "1:real")
      one <- Parser.term(theory, notation, "1:real", values)
      result <- valueOfSeries(
        logic, theory, notation, limit, definition, agreement, one, "SUC (0:num)")
    } yield result
  }

  /**
   * The four facts about the hyperbolic pair, and every one of them is algebra.
   *
   * This is what defining them from `exp` rather than from their series buys, and it is worth
   * reading beside `sineValue` and `cosineValue` to see the difference: those two need a pointwise
   * argument about a summand, an induction or a shift, and a convergence lemma; these need
   * `Linarith` over two atoms. The atoms are `exp x` and `exp (0 - x)`, about which nothing at all
   * is known and nothing needs to be.
   *
   * **At zero the two atoms are the same atom**, which is the one step that is not linear:
   * `0 - 0` is `0` by `Ring`, and congruence carries that inside `exp`. Without it the two
   * occurrences stay distinct terms and no amount of linear arithmetic relates them.
   *
   * What is **not** here is `cosh x * cosh x - sinh x * sinh x = 1`. It needs
   * `exp x * exp (0 - x) = 1`, which is the addition theorem, which wants the Cauchy product; so
   * the pair arrives with exactly the silence `exp` has and not a smaller one. A reader who expects
   * the hyperbolic identity to be one step away is reading the definition correctly and the state
   * of the development incorrectly, which is why this paragraph is here rather than in a card.
   */
  private def hyperbolicFacts(
    logic: Logic,
    linarith: Linarith,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    sineDefinition: Kernel.Thm,
    cosineDefinition: Kernel.Thm,
    exponentialAtZero: Kernel.Thm
  ): Either[LogicError, Map[String, Kernel.Thm]] = {
    val rules = logic.rules
    val x = Term.variable("x", values)

    for {
      zero <- Parser.term(theory, notation, "0:real", values)
      exponential <- LogicError.lift(theory.constant(Exponential, Type.fun(values, values)))

      // `exp (0 - 0)` is `exp 0`, carried inside the constant by congruence.
      cancels <- ring.prove("(0:real) - 0 = 0")
      sameAtom <- Conv.apTerm(exponential, cancels)

      atZeroSine <- Conv.unfold(sineDefinition, List(zero)).flatMap(rewriteInProposition(sameAtom, _))
      atZeroCosine <-
        Conv.unfold(cosineDefinition, List(zero)).flatMap(rewriteInProposition(sameAtom, _))

      exponentialAtZeroTerm <- Parser.term(theory, notation, "exp (0:real)", values)

      sineIsZero <- linarith
        .prove("!a:real. (a - a) / 2 = 0")
        .flatMap(rules.spec(exponentialAtZeroTerm, _))
        .flatMap(Conv.trans(atZeroSine, _))

      cosineIsOne <- linarith
        .prove("!a:real. (a + a) / 2 = a")
        .flatMap(rules.spec(exponentialAtZeroTerm, _))
        .flatMap(Conv.trans(atZeroCosine, _))
        .flatMap(Conv.trans(_, exponentialAtZero))

      // And the two identities, at an arbitrary argument, over the same two atoms.
      atArgumentSine <- Conv.unfold(sineDefinition, List(x))
      atArgumentCosine <- Conv.unfold(cosineDefinition, List(x))
      foldedSine <- Conv.sym(atArgumentSine)
      foldedCosine <- Conv.sym(atArgumentCosine)

      positive <- Parser.term(theory, notation, "exp (x:real)", values)
      negative <- Parser.term(theory, notation, "exp (0 - x:real)", values)

      sum <- linarith
        .prove("!a:real. !b:real. (a + b) / 2 + (a - b) / 2 = a")
        .flatMap(rules.specAll(_, List(positive, negative)))
        .flatMap(rewriteInProposition(foldedCosine, _))
        .flatMap(rewriteInProposition(foldedSine, _))
        .flatMap(rules.gen(x, _))

      difference <- linarith
        .prove("!a:real. !b:real. (a + b) / 2 - (a - b) / 2 = b")
        .flatMap(rules.specAll(_, List(positive, negative)))
        .flatMap(rewriteInProposition(foldedCosine, _))
        .flatMap(rewriteInProposition(foldedSine, _))
        .flatMap(rules.gen(x, _))
    } yield Map(
      HyperbolicSineAtZero -> sineIsZero,
      HyperbolicCosineAtZero -> cosineIsOne,
      CosinePlusSine -> sum,
      CosineMinusSine -> difference
    )
  }

  /**
   * `|- !n. Sum f n = 0` from `|- !k. f k = 0`, through `SUM_CONGRUENCE` and `SUM_OF_ZERO`.
   *
   * The congruence is stated between two function **variables**, so specialising it at a lambda
   * leaves a redex at every application of it, and the hypothesis it then wants is the summand
   * reduced. That is why `pointwise` is stated in the reduced form and not as `f k = 0`: the two
   * are the same claim and only one of them is what the congruence asks for.
   */
  private def everySumVanishes(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    series: Series,
    summand: String,
    pointwise: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val n = Term.variable("n", numbers)

    for {
      congruence <- series.fact(Series.Congruence)
      ofZero <- series.fact(Series.OfZero)
      function <- Parser.term(theory, notation, s"($summand)", Type.fun(numbers, values))
      zeroes <- Parser.term(theory, notation, "\\y:num. 0:real", Type.fun(numbers, values))

      opened <- rules
        .specAll(congruence, List(function, zeroes))
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))
      agreeing <- rules.mp(opened, pointwise)

      atIndex <- rules.spec(n, agreeing)
      vanishing <- rules.spec(n, ofZero)
      result <- Conv.trans(atIndex, vanishing).flatMap(rules.gen(n, _))
    } yield result
  }

  /**
   * `|- !n. Sum f (SUC n) = 1` from the tail vanishing pointwise and the first term being one.
   *
   * `SUM_SHIFT` is `Sum (\z. f (SUC z)) n = Sum f (SUC n) - f 0`. Its left side is a sum whose
   * summand vanishes, so it is zero by the congruence above, and its right side is the sum wanted
   * less a term that is one. What joins them is one linear step.
   */
  private def partialSumsPastOne(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    series: Series,
    summand: String,
    tail: Kernel.Thm,
    first: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val n = Term.variable("n", numbers)

    for {
      shift <- series.fact(Series.Shift)
      function <- Parser.term(theory, notation, s"($summand)", Type.fun(numbers, values))

      shifted <- rules
        .specAll(shift, List(function, n))
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))

      tailSum <- everySumVanishes(logic, theory, notation, series, s"\\k:num. ($summand) (SUC k)", tail)
      atIndex <- rules.spec(n, tailSum)

      joined <- linarith
        .prove("!a:real. !b:real. !c:real. a = b - c ==> a = 0 ==> c = 1 ==> b = 1")
        .flatMap(rules.specAll(_, List(leftOf(shifted), rightWithout(shifted), firstTerm(shifted))))
      result <- rules
        .mp(joined, shifted)
        .flatMap(rules.mp(_, atIndex))
        .flatMap(rules.mp(_, first))
        .flatMap(rules.gen(n, _))
    } yield result
  }

  /**
   * `|- !n. NUM_LE (SUC 0) n ==> v = Sum f n` from `|- !n. Sum f (SUC n) = v`.
   *
   * Every index at or above `SUC 0` is a successor, which is `NUM_CASES` with the zero case refuted
   * by `NUM_LE_ZERO` against `NUM_SUC_NOT_ZERO`. The equation is then turned round, because the
   * agreement [[Limit.Eventually]] wants has the constant sequence on the left.
   */
  private def agreesPastOne(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    naturals: Natural,
    peano: Peano,
    partial: Kernel.Thm,
    summand: String,
    valueText: String
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val n = Term.variable("n", numbers)
    val y = Term.variable("y", numbers)

    for {
      cases <- naturals.fact(Natural.ZeroOrSuccessor)
      notZero <- naturals.fact(Natural.SuccessorNotZero)
      atMostZero <- peano.fact(Peano.AtMostZero)

      guard <- Parser.proposition(theory, notation, "NUM_LE (SUC 0) n:num")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))
      target <- Parser.proposition(theory, notation, s"$valueText = Sum ($summand) (n:num)")

      split <- rules.spec(n, cases)

      isZero <- Parser.proposition(theory, notation, "n:num = 0")
      fromZero <- for {
        assumed <- LogicError.lift(Kernel.assume(isZero))
        carried <- rewriteInProposition(assumed, assumedGuard)
        successorZero <- Parser.term(theory, notation, "SUC (0:num)", numbers)
        collapsed <- rules.spec(successorZero, atMostZero).flatMap(rules.mp(_, carried))
        zero <- Parser.term(theory, notation, "0:num", numbers)
        never <- rules.spec(zero, notZero)
        clash <- rules.notElim(never, collapsed)
        anything <- rules.falsityElim(target, clash)
      } yield anything

      isSuccessor <- Parser.proposition(theory, notation, "?y:num. n:num = SUC y")
      assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
      fromSuccessor <- for {
        inner <- Parser.proposition(theory, notation, "n:num = SUC (y:num)")
        assumed <- LogicError.lift(Kernel.assume(inner))
        atY <- rules.spec(y, partial)
        operator <- operatorOf(atY)
        carried <- Conv.apTerm(operator, assumed)
        equated <- Conv.trans(carried, atY)
        flipped <- Conv.sym(equated)
        eliminated <- rules.existsElim(assumedSuccessor, y, flipped)
      } yield eliminated

      settled <- rules.disjElim(split, fromZero, fromSuccessor)
      result <- rules.disch(guard, settled).flatMap(rules.gen(n, _))
    } yield result
  }

  /** `|- !n. NUM_LE 0 n ==> 0 = Sum f n` from `|- !n. Sum f n = 0`, the guard being free. */
  private def agreesEverywhere(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    sums: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val n = Term.variable("n", numbers)

    for {
      guard <- Parser.proposition(theory, notation, "NUM_LE 0 (n:num)")
      atIndex <- rules.spec(n, sums)
      flipped <- Conv.sym(atIndex)
      result <- rules.disch(guard, flipped).flatMap(rules.gen(n, _))
    } yield result
  }

  /**
   * `|- f 0 = v` for one of the four constants, from the agreement its series satisfies.
   *
   * Three steps and each of them is a lemma of [[Limit]]: the constant sequence converges, a
   * sequence agreeing with it past an index converges to the same thing, and the limit of a
   * convergent sequence is what it converges to. The fourth step is the definition, unfolded at
   * zero.
   *
   * The sequence is read off the unfolded definition rather than parsed a second time, which is
   * what keeps the term the limit is taken of and the term the agreement is about the same term.
   */
  private def valueOfSeries(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    limit: Limit,
    definition: Kernel.Thm,
    agreement: Kernel.Thm,
    value: Term,
    boundText: String
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      zero <- Parser.term(theory, notation, "0:real", values)
      unfolded <- Conv.unfold(definition, List(zero))
      taken <- rightOf(unfolded)
      sequence <- taken match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("a limit of a sequence", other))
      }

      bound <- Parser.term(theory, notation, boundText, numbers)

      constant <- limit.constantSequence.flatMap(rules.spec(value, _))
      constantSequence <- constant.conclusion match {
        case App(App(_, sequence), _) => Right(sequence)
        case other => Left(NotOfForm("a convergence", other))
      }

      eventually <- limit.eventually
        .flatMap(rules.specAll(_, List(constantSequence, sequence, value, bound)))
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))

      converges <- rules.mp(eventually, agreement).flatMap(rules.mp(_, constant))
      isValue <- limit.valueOfConverges
        .flatMap(rules.specAll(_, List(sequence, value)))
        .flatMap(rules.mp(_, converges))
      result <- Conv.trans(unfolded, isValue)
    } yield result
  }

  /** The left side of an equation. */
  private def leftOf(theorem: Kernel.Thm): Term =
    Term.destEq(theorem.conclusion).map(_._1).getOrElse(theorem.conclusion)

  /** The sum on the right of `SUM_SHIFT`, which is what the linear step concludes about. */
  private def rightWithout(theorem: Kernel.Thm): Term =
    Term.destEq(theorem.conclusion).map(_._2) match {
      case Some(App(App(_, left), _)) => left
      case _ => theorem.conclusion
    }

  /** The term subtracted on the right of `SUM_SHIFT`. */
  private def firstTerm(theorem: Kernel.Thm): Term =
    Term.destEq(theorem.conclusion).map(_._2) match {
      case Some(App(App(_, _), right)) => right
      case _ => theorem.conclusion
    }

  /** The operator of an application read off a theorem's left side. */
  private def operatorOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1) match {
      case Some(App(operator, _)) => Right(operator)
      case _ => Left(NotOfForm("an equation whose left side is an application", theorem.conclusion))
    }

  /**
   * Rewrite one subterm of a proposition with an equation, wherever in it that subterm occurs.
   *
   * The same helper `Limit` carries and for the same reason; it is duplicated rather than shared
   * because the two developments are separate links and a shared private helper would have to
   * become public surface on one of them for the other to reach it.
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
          _ <- if (replaced != theorem.conclusion) Right(())
               else Left(NotOfForm(s"a proposition mentioning $left", theorem.conclusion))
          template <- LogicError.lift(Term.abs(placeholder, replaced))
          congruence <- Conv.apTerm(template, equation)
          reduced <- Conv.betaSides(congruence)
          moved <- LogicError.lift(Kernel.eqMp(reduced, theorem))
        } yield moved
    }

  /** Every occurrence of `target` inside `term`, replaced, without descending under a binder. */
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
        case other => Right(other)
      }

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
