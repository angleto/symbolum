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
 * `docs/adr/0017` records the argument; what a reader of this file needs is the shape of it. `sin`
 * and `cos` are series **because there is nothing else here to define them from**: the route
 * through the exponential needs a complex one, and `docs/adr/0007` puts the integers and the
 * rationals before anything of that kind. These two need no such detour, so the definition that
 * costs one line is available, and it is what makes [[Transcendental.CosinePlusSine]] provable
 * today where the series would have made it wait for a rearrangement of a series into its even and
 * odd parts.
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

  /**
   * `|- 2 < exp 1`
   *
   * The first fact here about a value this development does not compute. Everything else is a
   * value at zero, where the series stops after one term; this one needs the series to **converge**
   * before `lim` says anything at all, which is `Limit.SUM_COMPARISON` spent for the first time,
   * and then a bound on where the limit sits, which is `CONVERGES_GE` over the third partial sum.
   *
   * Five documents of this repository said the comparison test bought this and were wrong for a
   * day. What was missing was `Coding.NUM_POW_LE_FACT`, a fact of arithmetic rather than of
   * analysis: `1 / i!` sits under `2 * (1/2)^i` exactly when `2^i <= 2 * i!`.
   */
  val ExponentialAboveTwo: String = "EXP_ONE_ABOVE_TWO"

  /**
   * `|- !x i. 2 * abs x <= real_of_num (SUC i) ==>
   * abs (Power x (SUC i) / real_of_num (NUM_FACT (SUC i)))
   * <= 1 / 2 * abs (Power x i / real_of_num (NUM_FACT i))`
   *
   * Past the index where `2 * abs x` is reached, each term of the exponential's series is at
   * most half the one before it. It is the whole content of the series' absolute convergence at
   * an arbitrary real: the head up to that index is a number and the tail is under a geometric
   * series, where [[ExponentialAboveTwo]]'s domination works at `x = 1` and at no other point.
   *
   * The index is not mentioned: it is whatever `Peano.NUM_CEIL_LE` returns for `2 * abs x`, and
   * this fact is stated at every `i` satisfying the bound rather than at that one.
   */
  val TermsHalve: String = "EXP_TERM_HALVES"

  /**
   * `|- !x m. 2 * abs x <= real_of_num m ==> !j. T (m + j) <= Power (1/2) j * T m`
   *
   * [[TermsHalve]] iterated, which is what makes the exponential's tail geometric. It is stated
   * at a **variable** index rather than at `NUM_CEIL (2 * abs x)`: the induction never mentions
   * the ceiling, and a caller with any index meeting the bound can spend it.
   */
  val TailIsGeometric: String = "EXP_TAIL_GEOMETRIC"

  /**
   * `|- !x. ?P. converges (Sum (\i. abs (Power x i / real_of_num (NUM_FACT i)))) P`
   *
   * The exponential's series is absolutely convergent at **every** real, which is what
   * `Limit.SUM_CAUCHY_PRODUCT` asks of both of its arguments. [[ExponentialAboveTwo]] did not
   * buy it: that one dominates `1 / i!` by `2 * (1/2)^i`, and the dominating series is the one
   * for `x = 1` and for no other.
   *
   * What it is **not** is a statement about `exp x`. It says the series converges and names no
   * value, because `lim` is what names the value and `exp` is defined through it.
   */
  val AbsolutelyConvergent: String = "EXP_ABSOLUTE"

  /**
   * The dominating series for the exponential at one, written as a sum of two copies.
   *
   * `2 * Power (1/2) i` says the same thing and is the wrong shape: `SUM_ADD` splits a sum of two
   * sequences and `SUM_LINEAR` a scaled one plus another, so the second would want a congruence in
   * front of it to put the sum in the form the lemma reads.
   */
  private val HalvesText: String = "\\i:num. Power ((1:real) / 2) i"

  /** The same, doubled, which is what dominates `1 / i!`. */
  private val DominatorText: String =
    "\\i:num. Power ((1:real) / 2) i + Power ((1:real) / 2) i"

  /**
   * Three, spelled, because every recurrence over `num` is stated at a successor.
   *
   * The partial sum at this index is computed by rewriting with those recurrences, and the numeral
   * `3` would have to go through `Successor` first. Nothing here needs the numeral.
   */
  private val ThirdIndexText: String = "SUC (SUC (SUC (0:num)))"

  /** Everything this development proves, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    ExponentialAtZero -> "exp 0 = 1",
    SineAtZero -> "sin 0 = 0",
    CosineAtZero -> "cos 0 = 1",
    HyperbolicSineAtZero -> "sinh 0 = 0",
    HyperbolicCosineAtZero -> "cosh 0 = 1",
    CosinePlusSine -> "!x:real. cosh x + sinh x = exp x",
    CosineMinusSine -> "!x:real. cosh x - sinh x = exp (0 - x)",
    ExponentialAboveTwo -> "2 < exp 1",
    TermsHalve ->
      ("!x:real. !i:num. 2 * abs x <= real_of_num (SUC i) ==> " +
        "abs (Power x (SUC i) / real_of_num (NUM_FACT (SUC i))) <= " +
        "1 / 2 * abs (Power x i / real_of_num (NUM_FACT i))"),
    TailIsGeometric ->
      ("!x:real. !m:num. 2 * abs x <= real_of_num m ==> " +
        "!j:num. abs (Power x (NUM_ADD m j) / real_of_num (NUM_FACT (NUM_ADD m j))) <= " +
        "Power (1 / 2) j * abs (Power x m / real_of_num (NUM_FACT m))"),
    AbsolutelyConvergent ->
      ("!x:real. ?P:real. " +
        "converges (Sum (\\i:num. abs (Power x i / real_of_num (NUM_FACT i)))) P")
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

      aboveTwo <- exponentialAboveTwo(
        logic, linarith, theory, notation, limit, series, peano, coding,
        exponentialDefinition, recurrences)

      field <- Field.construct(series.ring.arithmetic)
      halving <- termsHalveFromAnIndex(
        logic, linarith, field, theory, notation, series, peano, coding, limit)
      geometricTail <- tailIsGeometric(
        logic, linarith, theory, notation, series, peano, induct, halving)
      absolute <- absolutelyConvergentEverywhere(
        logic, linarith, theory, notation, series, peano, limit, geometricTail)
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
        CosineAtZero -> cosine,
        ExponentialAboveTwo -> aboveTwo,
        TermsHalve -> halving,
        TailIsGeometric -> geometricTail,
        AbsolutelyConvergent -> absolute
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

  /**
   * `|- 2 < exp 1`, which is the first thing this development says about a value it does not know.
   *
   * Every other fact here is a value at zero, where the series stops after one term and no
   * convergence question arises. This one is about `exp 1`, and `exp` is `lim` applied to a
   * sequence: at an argument where that sequence does not converge, `lim` is a choice and nothing
   * is provable about it. So the convergence has to be obtained before anything can be said, which
   * is what `Limit.SUM_COMPARISON` is for and what it had no consumer for until now.
   *
   * == The three things the comparison test asks, and where each comes from ==
   *
   * The terms are non-negative: `Power 1 i` is `1` and the factorial embeds to something positive,
   * so each term is the reciprocal of a positive real.
   *
   * They are dominated by `(1/2)^i + (1/2)^i`, and this is the half that waited on arithmetic
   * rather than on analysis. `1 / i! <= 2 * (1/2)^i` is `2^i <= 2 * i!` with the denominator
   * cleared, which is `Coding.NUM_POW_LE_FACT`, carried to the reals by `NUM_REAL_LE` and
   * `NUM_REAL_POW`. Five documents said the comparison test bought `exp 1 > 2` and were wrong for
   * a day: what was missing was that inequality on `num`, and it landed on 2026-09-20.
   *
   * The dominating series has bounded partial sums: it is the geometric series at one half twice
   * over, `SUM_ADD` splits it, and `SUM_GEOMETRIC` bounds each half by two exactly as `LimitSpec`
   * does for that series on its own. It is written as a sum of two copies rather than as `2 *`
   * anything because `SUM_ADD` splits that shape and needs no congruence in front of it.
   *
   * == How the arithmetic is put to `Linarith`, which is the shape of every step here ==
   *
   * **A quotient with a symbolic denominator is outside every procedure in this repository**, and
   * the refusal says so by name: cancelling one needs it to be non-zero, which is `Field`'s to
   * assume. So no goal here carries one. Each step is a **schematic implication over real
   * variables**, proved by `Linarith` once and then specialised at the terms of this problem and
   * discharged against the facts. The reciprocal enters as a variable `v` with the hypothesis
   * `f * v = 1`, which is `MUL_INVERSE` at a denominator already known to be positive, and what
   * closes each goal is that hypothesis multiplied by the negated goal, which is the degree-two
   * product `docs/adr/0032` describes.
   *
   * == And then where the limit is ==
   *
   * `CONVERGES_GE` takes a bound that holds from an index on, which is what makes the argument
   * possible at all: the useful lower bound on an increasing sequence is one of its own terms, and
   * that is false below that term's index. The term is the third partial sum, `1 + 1 + 1/2`, and
   * `MONOTONE_LE` carries it to every later index.
   *
   * **The index is written `SUC (SUC (SUC 0))` and not `3`**, and that is not an oversight: every
   * recurrence over `num` is stated at a successor, the partial sum is computed by rewriting with
   * those recurrences, and a numeral would have to be spelled by `Successor` first. Nothing here
   * needs the numeral, so nothing here pays for it.
   *
   * == The sequence and the partial sums are two terms and both are needed ==
   *
   * `exp 1` unfolds to `lim (\n. Sum f n)` and the comparison test speaks about `Sum f`. They are
   * eta-equivalent and not equal, so `CONVERGES_EVENTUALLY` at index zero carries the convergence
   * from the one to the other, which is a published fact rather than a use of the eta axiom here.
   */
  private def exponentialAboveTwo(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    limit: Limit,
    series: Series,
    peano: Peano,
    coding: Coding,
    definition: Kernel.Thm,
    recurrences: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val witness = Term.variable("l", values)

    for {
      one <- Parser.term(theory, notation, "1:real", values)
      unfolded <- Conv.unfold(definition, List(one))
      limited <- rightOf(unfolded)
      sequence <- limited match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("a limit of a sequence", other))
      }

      // `Sum f` and `f`, read off the definition rather than parsed a second time, so that what
      // this argument is about and what `exp 1` is are the same terms.
      partial <- sequence match {
        case Abs(_, App(sums, _)) => Right(sums)
        case other => Left(NotOfForm("a sequence of partial sums", other))
      }
      summand <- partial match {
        case App(_, function) => Right(function)
        case other => Left(NotOfForm("the partial sums of a series", other))
      }

      dominator <- Parser.term(theory, notation, DominatorText, Type.fun(numbers, values))
      halves <- Parser.term(theory, notation, HalvesText, Type.fun(numbers, values))

      nonNegative <- termsAreNonNegative(
        logic, linarith, theory, notation, series, peano, coding, limit, summand)
      dominated <- termsAreDominated(
        logic, linarith, theory, notation, series, peano, coding, limit, summand, dominator)
      bounded <- dominatingSumsAreBounded(logic, linarith, theory, notation, series, halves)

      comparison <- limit.comparison
        .flatMap(rules.specAll(_, List(summand, dominator)))
        .flatMap(betaOpened)
      converging <- rules
        .mp(comparison, nonNegative)
        .flatMap(rules.mp(_, dominated))
        .flatMap(rules.mp(_, bounded))

      // Under the assumption that it converges to `l`. The instance is taken from the existential
      // itself rather than written out, which is what lets the last step discharge it.
      predicate <- logic
        .destExistsPredicate(converging.conclusion)
        .toRight(NotOfForm("an existential quantification", converging.conclusion))
      instance <- LogicError
        .lift(Term.app(predicate, witness))
        .flatMap(Conv.betaRoot)
        .flatMap(rightOf)
      assumed <- LogicError.lift(Kernel.assume(instance))

      atThird <- thirdPartialSum(logic, linarith, theory, notation, series, partial, recurrences)
      increasing <- partialSumsIncrease(logic, linarith, series, partial, summand, nonNegative)
      everyLater <- laterSumsAreAsLarge(
        logic, linarith, theory, notation, limit, partial, increasing, atThird)

      bound <- Parser.term(theory, notation, ThirdIndexText, numbers)
      threshold <- Parser.term(theory, notation, "(5:real) / 2", values)
      aboveThreshold <- limit.aboveBound
        .flatMap(rules.specAll(_, List(partial, witness, threshold, bound)))
        .flatMap(rules.mp(_, assumed))
        .flatMap(rules.mp(_, everyLater))

      // `exp 1` is that limit. The eta step is `CONVERGES_EVENTUALLY` at index zero, where the
      // agreement between the two spellings is reflexivity once the redex is reduced.
      sequenceConverges <- convergenceOfTheSequence(
        logic, theory, notation, limit, partial, sequence, witness, assumed)
      limitIsWitness <- limit.valueOfConverges
        .flatMap(rules.specAll(_, List(sequence, witness)))
        .flatMap(rules.mp(_, sequenceConverges))
      exponentialIsWitness <- Conv.trans(unfolded, limitIsWitness)

      strict <- linarith
        .prove("!a:real. !b:real. a = b ==> (5:real) / 2 <= b ==> 2 < a")
        .flatMap(rules.specAll(_, List(leftOf(exponentialIsWitness), witness)))
        .flatMap(rules.mp(_, exponentialIsWitness))
        .flatMap(rules.mp(_, aboveThreshold))

      released <- rules.existsElim(converging, witness, strict)
    } yield released
  }

  /**
   * `|- !z. 0 <= Power 1 z / real_of_num (NUM_FACT z)`, the first of the comparison test's three.
   *
   * The quotient becomes a reciprocal before anything is asked of a procedure, because a symbolic
   * denominator is what every one of them refuses. `Power 1 z` is `1` by `POWER_ONE` and `1 / f`
   * is `inv f` by `Ring`, which owes nothing: division unfolds to multiplication by the inverse
   * and the unit law is ordinary ring algebra.
   */
  private def termsAreNonNegative(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    series: Series,
    peano: Peano,
    coding: Coding,
    limit: Limit,
    summand: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val index = Term.variable("z", numbers)

    for {
      term <- reduced(summand, index)
      parts <- quotientParts(term)
      (divisor, denominator) = parts

      positive <- factorialEmbedsPositively(logic, linarith, peano, coding, index, denominator)
      cancels <- inverseCancels(logic, limit, theory, notation, positive, denominator)
      asInverse <- quotientIsInverse(
        logic, series, theory, notation, index, divisor, denominator, term)
      inverse <- rightOf(asInverse)

      atInverse <- linarith
        .prove("!v:real. !f:real. 0 < f ==> f * v = 1 ==> 0 <= v")
        .flatMap(rules.specAll(_, List(inverse, denominator)))
        .flatMap(rules.mp(_, positive))
        .flatMap(rules.mp(_, cancels))
      carried <- Conv.sym(asInverse).flatMap(onRight(_, atInverse))
      result <- rules.gen(index, carried)
    } yield result
  }

  /**
   * `|- !z. Power 1 z / real_of_num (NUM_FACT z) <= Power (1/2) z + Power (1/2) z`.
   *
   * The domination, which is `Coding.NUM_POW_LE_FACT` carried across the embedding. Three facts
   * about this `z` go into one schematic implication: the power of two and the power of a half
   * multiply to one, the power of two is at most twice the factorial, and the factorial's
   * reciprocal is a reciprocal. What `Linarith` does with them is multiply the bound by the
   * geometric term and the negated goal by the denominator, two products of degree two.
   *
   * The embedding is a rewriting rather than a chain of congruences: `NUM_REAL_POW` and
   * `NUM_REAL_MUL` move `real_of_num` inwards, the two recurrences turn `real_of_num (SUC (SUC 0))`
   * into `(0 + 1) + 1`, and one `Ring` equation folds that to the numeral the schematic is written
   * with. Without the last of those the schematic would have to be stated over a term nobody
   * writes.
   */
  private def termsAreDominated(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    series: Series,
    peano: Peano,
    coding: Coding,
    limit: Limit,
    summand: Term,
    dominator: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val ring = series.ring
    val index = Term.variable("z", numbers)

    for {
      term <- reduced(summand, index)
      parts <- quotientParts(term)
      (divisor, denominator) = parts
      target <- reduced(dominator, index)

      two <- Parser.term(theory, notation, "2:real", values)
      half <- Parser.term(theory, notation, "(1:real) / 2", values)
      power <- Parser.term(theory, notation, "Power", Type.fun(values, Type.fun(numbers, values)))
      doubling <- LogicError.lift(Term.appAll(power, List(two, index)))
      halving <- LogicError.lift(Term.appAll(power, List(half, index)))

      positive <- factorialEmbedsPositively(logic, linarith, peano, coding, index, denominator)
      cancels <- inverseCancels(logic, limit, theory, notation, positive, denominator)
      asInverse <- quotientIsInverse(
        logic, series, theory, notation, index, divisor, denominator, term)
      inverse <- rightOf(asInverse)

      positiveHalf <- series
        .fact(Series.PowerPositive)
        .flatMap(rules.spec(half, _))
        .flatMap(theorem => linarith.prove("(0:real) < (1:real) / 2").flatMap(rules.mp(theorem, _)))
        .flatMap(rules.spec(index, _))

      // `2^z * (1/2)^z = 1`, which is what ties the geometric term to the arithmetic on `num`.
      multiplicative <- series
        .fact(Series.Multiplicative)
        .flatMap(rules.specAll(_, List(two, half, index)))
      product <- ring.prove("2 * ((1:real) / 2) = 1")
      atOne <- Conv.apTerm(power, product).flatMap(Conv.apThm(_, index))
      powerOfOne <- series.fact(Series.PowerOfOne).flatMap(rules.spec(index, _))
      unit <- Conv
        .sym(multiplicative)
        .flatMap(Conv.trans(_, atOne))
        .flatMap(Conv.trans(_, powerOfOne))

      // `2^z <= 2 * z!`, carried over from `num` by the embedding and its recurrences.
      overNaturals <- coding.fact(Coding.PowerBelowFactorial).flatMap(rules.spec(index, _))
      naturalSides <- overNaturals.conclusion match {
        case App(App(_, left), right) => Right((left, right))
        case other => Left(NotOfForm("a comparison", other))
      }
      embeddedOrder <- peano
        .fact(Peano.EmbedsOrder)
        .flatMap(rules.specAll(_, List(naturalSides._1, naturalSides._2)))
        .flatMap(rules.mp(_, overNaturals))
      folding <- ring.prove("((0:real) + 1) + 1 = 2")
      embeddingRules <- gather(
        Vector(
          series.fact(Series.EmbedsPower),
          peano.fact(Peano.EmbedsProduct),
          peano.fact(Peano.EmbedsSuccessor),
          peano.fact(Peano.EmbedsZero)
        )).map(_ :+ folding)
      embedded <- Rewrite.Rule
        .all(logic, embeddingRules)
        .flatMap(Rewrite.inTheorem(_, embeddedOrder))

      atInverse <- linarith
        .prove(
          "!p:real. !q:real. !f:real. !v:real. 0 < f ==> 0 < q ==> p * q = 1 ==> " +
            "p <= 2 * f ==> f * v = 1 ==> v <= q + q")
        .flatMap(rules.specAll(_, List(doubling, halving, denominator, inverse)))
        .flatMap(rules.mp(_, positive))
        .flatMap(rules.mp(_, positiveHalf))
        .flatMap(rules.mp(_, unit))
        .flatMap(rules.mp(_, embedded))
        .flatMap(rules.mp(_, cancels))
      carried <- Conv.sym(asInverse).flatMap(onLeft(_, atInverse))

      // The shape the comparison test asks for, compared rather than assumed: every term above is
      // assembled out of what the definition holds, and a refusal here names the step that
      // produced something else.
      relation <- relationOf(carried)
      wanted <- LogicError.lift(Term.appAll(relation, List(term, target)))
      _ <-
        if (carried.conclusion == wanted) Right(())
        else Left(NotOfForm("the domination the comparison test asks for", carried.conclusion))
      result <- rules.gen(index, carried)
    } yield result
  }

  /**
   * `|- ?b. !n. Sum (\i. (1/2)^i + (1/2)^i) n <= b`, the third hypothesis of the comparison test.
   *
   * Each half is bounded by two, which is `SUM_GEOMETRIC` cleared of its denominator and one
   * linear step, and the whole is the two halves added. The witness is four and it is not tight:
   * what the comparison test asks for is a bound and not the least one.
   */
  private def dominatingSumsAreBounded(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    series: Series,
    halves: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val index = Term.variable("n", numbers)

    for {
      half <- Parser.term(theory, notation, "(1:real) / 2", values)
      positivePower <- series
        .fact(Series.PowerPositive)
        .flatMap(rules.spec(half, _))
        .flatMap(theorem => linarith.prove("(0:real) < (1:real) / 2").flatMap(rules.mp(theorem, _)))
        .flatMap(rules.spec(index, _))

      powerAt <- Parser.term(theory, notation, "Power ((1:real) / 2) (n:num)", values)
      sumAt <- Parser.term(theory, notation, s"Sum ($HalvesText) (n:num)", values)

      geometric <- series.fact(Series.Geometric).flatMap(rules.specAll(_, List(half, index)))
      underTwo <- linarith
        .prove("!p:real. !s:real. ((1:real) / 2 - 1) * s = p - 1 ==> 0 < p ==> s <= 2")
        .flatMap(rules.specAll(_, List(powerAt, sumAt)))
        .flatMap(rules.mp(_, geometric))
        .flatMap(rules.mp(_, positivePower))

      split <- series
        .fact(Series.Additive)
        .flatMap(rules.specAll(_, List(halves, halves, index)))
        .flatMap(betaOpened)

      whole <- linarith
        .prove("!a:real. !b:real. a = b + b ==> b <= 2 ==> a <= 4")
        .flatMap(rules.specAll(_, List(leftOf(split), sumAt)))
        .flatMap(rules.mp(_, split))
        .flatMap(rules.mp(_, underTwo))
      everywhere <- rules.gen(index, whole)

      four <- Parser.term(theory, notation, "4:real", values)
      statement <- Parser.proposition(
        theory, notation, s"?b:real. !n:num. Sum ($DominatorText) n <= b")
      predicate <- logic
        .destExistsPredicate(statement)
        .toRight(NotOfForm("an existential quantification", statement))
      result <- rules.existsIntro(predicate, four, everywhere)
    } yield result
  }

  /**
   * `|- 5 / 2 <= Sum f (SUC (SUC (SUC 0)))`, which is the bound the limit inherits.
   *
   * The partial sum is **computed** rather than reasoned about: the recurrences of the sum, the
   * power, the factorial, the product and the embedding rewrite it to an expression in numerals,
   * and `Linarith` compares that with five halves. Three `Ring` equations fold what the
   * recurrences leave behind, `0 + 1`, `1 + 1` and `1 * 1`, because a denominator that is a sum of
   * numerals rather than a numeral is an atom to `Linarith` and not a rational coefficient.
   */
  private def thirdPartialSum(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    series: Series,
    partial: Term,
    recurrences: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val ring = series.ring

    for {
      bound <- Parser.term(theory, notation, ThirdIndexText, numbers)
      subject <- LogicError.lift(Term.app(partial, bound))
      folding <- gather(
        Vector(
          ring.prove("(0:real) + 1 = 1"),
          ring.prove("(1:real) + 1 = 2"),
          ring.prove("(1:real) * 1 = 1")
        ))
      computed <- Rewrite.Rule
        .all(logic, recurrences ++ folding)
        .flatMap(Rewrite.rewrite(_, subject))
      numeric <- rightOf(computed)

      order <- Parser.term(
        theory, notation, Real.NonStrictOrder, Type.fun(values, Type.fun(values, Type.Bool)))
      threshold <- Parser.term(theory, notation, "(5:real) / 2", values)
      goal <- LogicError.lift(Term.appAll(order, List(threshold, numeric)))
      atNumerals <- linarith.prove(goal)

      result <- linarith
        .prove("!a:real. !b:real. a = b ==> (5:real) / 2 <= b ==> (5:real) / 2 <= a")
        .flatMap(rules.specAll(_, List(subject, numeric)))
        .flatMap(rules.mp(_, computed))
        .flatMap(rules.mp(_, atNumerals))
    } yield result
  }

  /** `|- !y. Sum f y <= Sum f (SUC y)`, which is what `MONOTONE_LE` asks of the partial sums. */
  private def partialSumsIncrease(
    logic: Logic,
    linarith: Linarith,
    series: Series,
    partial: Term,
    summand: Term,
    nonNegative: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val step = Term.variable("y", numbers)

    for {
      recurrence <- series.fact(Series.AtSuccessor).flatMap(rules.specAll(_, List(summand, step)))
      here <- LogicError.lift(Term.app(partial, step))
      next <- Right(leftOf(recurrence))
      term <- reduced(summand, step)
      atStep <- rules.spec(step, nonNegative)
      increasing <- linarith
        .prove("!a:real. !b:real. !c:real. c = a + b ==> 0 <= b ==> a <= c")
        .flatMap(rules.specAll(_, List(here, term, next)))
        .flatMap(rules.mp(_, recurrence))
        .flatMap(rules.mp(_, atStep))
      result <- rules.gen(step, increasing)
    } yield result
  }

  /** `|- !v. SUC (SUC (SUC 0)) <= v ==> 5 / 2 <= Sum f v`, which is the bound `CONVERGES_GE` wants. */
  private def laterSumsAreAsLarge(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    limit: Limit,
    partial: Term,
    increasing: Kernel.Thm,
    atThird: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val later = Term.variable("v", numbers)

    for {
      bound <- Parser.term(theory, notation, ThirdIndexText, numbers)
      monotone <- limit.monotoneBelow
        .flatMap(rules.spec(partial, _))
        .flatMap(betaOpened)
        .flatMap(rules.mp(_, increasing))
        .flatMap(rules.specAll(_, List(bound, later)))
      parts <- logic
        .destImp(monotone.conclusion)
        .toRight(NotOfForm("an implication", monotone.conclusion))
      (premise, _) = parts
      assumed <- LogicError.lift(Kernel.assume(premise))
      ordered <- rules.mp(monotone, assumed)
      atThirdTerm <- LogicError.lift(Term.app(partial, bound))
      atLater <- LogicError.lift(Term.app(partial, later))
      reached <- linarith
        .prove("!a:real. !b:real. (5:real) / 2 <= a ==> a <= b ==> (5:real) / 2 <= b")
        .flatMap(rules.specAll(_, List(atThirdTerm, atLater)))
        .flatMap(rules.mp(_, atThird))
        .flatMap(rules.mp(_, ordered))
      result <- rules.disch(premise, reached).flatMap(rules.gen(later, _))
    } yield result
  }

  /**
   * `converges (\n. Sum f n) l` from `converges (Sum f) l`, which is eta and is not the eta axiom.
   *
   * The two spellings are the same function and not the same term, and what `exp 1` unfolds to is
   * the lambda. `CONVERGES_EVENTUALLY` at index zero asks only that the two agree from there on,
   * and they agree everywhere by reflexivity once the redex is reduced, so the transfer costs a
   * published fact rather than an appeal to the axiom `Classical` holds.
   */
  private def convergenceOfTheSequence(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    limit: Limit,
    partial: Term,
    sequence: Term,
    witness: Term,
    converges: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      zero <- Parser.term(theory, notation, "0:num", numbers)
      eventually <- limit.eventually
        .flatMap(rules.specAll(_, List(partial, sequence, witness, zero)))
        .flatMap(betaOpened)
      parts <- logic
        .destImp(eventually.conclusion)
        .toRight(NotOfForm("an implication", eventually.conclusion))
      (agreementStatement, _) = parts
      stripped <- Logic.stripForall(agreementStatement)
      variable <- stripped._1.headOption.toRight(
        NotOfForm("a claim about every index", agreementStatement))
      inner <- logic
        .destImp(stripped._2)
        .toRight(NotOfForm("an implication", stripped._2))
      (guard, equation) = inner
      sides <- Term.destEq(equation).toRight(NotOfForm("an equation", equation))
      agreement <- rules
        .disch(guard, Kernel.refl(sides._1))
        .flatMap(rules.gen(variable, _))
      result <- rules.mp(eventually, agreement).flatMap(rules.mp(_, converges))
    } yield result
  }

  /* ------------------------------------------------------------------ the small shared steps */

  /**
   * [[TermsHalve]], which is where the exponential's absolute convergence is decided.
   *
   * Past the index at which `2 * abs x` is reached, each term of the series is at most half the
   * one before it. That is the whole of what makes the tail geometric, and the index comes from
   * `Peano.NUM_CEIL_LE` rather than from anything about `exp`.
   *
   * == What owes a condition, which is three things and none of them is left assumed ==
   *
   * `Ring` unfolds `div`, so moving a quotient into a numerator times a reciprocal owes nothing,
   * which is what `Field`'s own docstring says of the two normal forms. What does owe something
   * is cancellation, asked at `NUM_FACT i` and at `NUM_FACT (SUC i)`, and the identity
   * `inv f = r * inv (f * r)`, which is `Field`'s and carries `~(f = 0)` and `~(r = 0)`. All
   * three are discharged here: the factorials by `NUM_FACT_POSITIVE` across the embedding, and
   * the successor by `NUM_REAL_SUC` with `NUM_REAL_NONNEG` under it.
   *
   * That identity is why the relation between the two reciprocals costs no fact about zero
   * divisors. Deriving it from `f * (v - r * w) = 0` would need one, and that is a case analysis
   * this development does not have to do.
   *
   * == The estimate is assembled forwards, and that is not a style choice ==
   *
   * Every equation here is proved in the direction the terms already stand and then handed to a
   * **schematic implication** over real variables, which is specialised afterwards:
   * `lhs = (a * p) * w ==> rhs = p * (r * w) ==> 2 * a <= r ==> 0 <= p * w ==> lhs <= 1/2 * rhs`.
   * The alternative is to rewrite backwards inside an inequality, and the shape this file uses
   * for that reaches the arguments of one relation and no further. What `Linarith` does with the
   * schematic is multiply `2 * a <= r` by `0 <= p * w`, one product of degree three, which is
   * inside what the procedure decides. Nothing is put to it with a quotient in it.
   */
  private def termsHalveFromAnIndex(
    logic: Logic,
    linarith: Linarith,
    field: Field,
    theory: Theory,
    notation: Notation,
    series: Series,
    peano: Peano,
    coding: Coding,
    limit: Limit
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val ring = series.ring
    val order = limit.magnitude.order
    val x = Term.variable("x", values)
    val i = Term.variable("i", numbers)

    def headOf(term: Term): Either[LogicError, Term] = term match {
      case App(head, _) => Right(head)
      case other        => Left(NotOfForm("an application to take the head of", other))
    }

    def nonZero(positive: Kernel.Thm, term: Term): Either[LogicError, Kernel.Thm] =
      order.fact(Positivity.NonZero).flatMap(rules.spec(term, _)).flatMap(rules.mp(_, positive))

    def discharged(condition: Term, proof: Kernel.Thm, theorem: Kernel.Thm) =
      rules.disch(condition, theorem).flatMap(rules.mp(_, proof))

    for {
      /* ------------------------------------------------------------------ everything, parsed */

      atIndex <- Parser.term(theory, notation, "real_of_num (NUM_FACT (i:num))", values)
      atSuccessor <- Parser.term(
        theory, notation, "real_of_num (NUM_FACT (SUC (i:num)))", values)
      successorIndex <- Parser.term(theory, notation, "SUC (i:num)", numbers)
      embedded <- Parser.term(theory, notation, "real_of_num (SUC (i:num))", values)
      embeddedIndex <- Parser.term(theory, notation, "real_of_num (i:num)", values)
      factorialHere <- Parser.term(theory, notation, "NUM_FACT (i:num)", numbers)
      reciprocal <- Parser.term(
        theory, notation, "inv (real_of_num (NUM_FACT (i:num)))", values)
      nextReciprocal <- Parser.term(
        theory, notation, "inv (real_of_num (NUM_FACT (SUC (i:num))))", values)
      splitProduct <- Parser.term(
        theory,
        notation,
        "real_of_num (NUM_FACT (i:num)) * real_of_num (SUC (i:num))",
        values)
      overSplit <- Parser.term(
        theory,
        notation,
        "real_of_num (SUC (i:num)) * " +
          "inv (real_of_num (NUM_FACT (i:num)) * real_of_num (SUC (i:num)))",
        values)
      overSuccessor <- Parser.term(
        theory,
        notation,
        "real_of_num (SUC (i:num)) * inv (real_of_num (NUM_FACT (SUC (i:num))))",
        values)
      powerAt <- Parser.term(theory, notation, "Power (x:real) (i:num)", values)
      powerAtSuccessor <- Parser.term(
        theory, notation, "Power (x:real) (SUC (i:num))", values)
      quotientAt <- Parser.term(
        theory, notation, "Power (x:real) (i:num) / real_of_num (NUM_FACT (i:num))", values)
      quotientAtSuccessor <- Parser.term(
        theory,
        notation,
        "Power (x:real) (SUC (i:num)) / real_of_num (NUM_FACT (SUC (i:num)))",
        values)
      here <- Parser.term(theory, notation, "abs (x:real)", values)
      magnitudeOfPower <- Parser.term(theory, notation, "abs (Power (x:real) (i:num))", values)
      termHere <- Parser.term(
        theory,
        notation,
        "abs (Power (x:real) (i:num) / real_of_num (NUM_FACT (i:num)))",
        values)
      termNext <- Parser.term(
        theory,
        notation,
        "abs (Power (x:real) (SUC (i:num)) / real_of_num (NUM_FACT (SUC (i:num))))",
        values)

      magnitudeConstant <- headOf(here)
      embeddingConstant <- headOf(embeddedIndex)
      inverseConstant <- headOf(reciprocal)
      scaledHead <- headOf(overSplit)

      absMul <- limit.magnitude.fact(Magnitude.Multiplicative)
      absOfNonNegative <- limit.magnitude.fact(Magnitude.OfNonNegative)
      absNonNegative <- limit.magnitude.fact(Magnitude.AbsNonNegative)

      /* --------------------------------------- positivity, and the three conditions discharged */

      positiveAtIndex <- factorialEmbedsPositively(logic, linarith, peano, coding, i, atIndex)
      positiveAtSuccessor <- factorialEmbedsPositively(
        logic, linarith, peano, coding, successorIndex, atSuccessor)
      cancels <- inverseCancels(logic, limit, theory, notation, positiveAtIndex, atIndex)
      cancelsNext <- inverseCancels(
        logic, limit, theory, notation, positiveAtSuccessor, atSuccessor)

      reciprocalNonNegative <- linarith
        .prove("!v:real. !f:real. 0 < f ==> f * v = 1 ==> 0 <= v")
        .flatMap(rules.specAll(_, List(reciprocal, atIndex)))
        .flatMap(rules.mp(_, positiveAtIndex))
        .flatMap(rules.mp(_, cancels))
      nextReciprocalNonNegative <- linarith
        .prove("!v:real. !f:real. 0 < f ==> f * v = 1 ==> 0 <= v")
        .flatMap(rules.specAll(_, List(nextReciprocal, atSuccessor)))
        .flatMap(rules.mp(_, positiveAtSuccessor))
        .flatMap(rules.mp(_, cancelsNext))

      embeddedSuccessor <- peano.fact(Peano.EmbedsSuccessor).flatMap(rules.spec(i, _))
      indexNonNegative <- peano.fact(Peano.EmbedsNonNegative).flatMap(rules.spec(i, _))
      embeddedPositive <- linarith
        .prove("!r:real. !m:real. r = m + 1 ==> 0 <= m ==> 0 < r")
        .flatMap(rules.specAll(_, List(embedded, embeddedIndex)))
        .flatMap(rules.mp(_, embeddedSuccessor))
        .flatMap(rules.mp(_, indexNonNegative))

      factorialNotZero <- nonZero(positiveAtIndex, atIndex)
      successorNotZero <- nonZero(embeddedPositive, embedded)

      /* ------------------------------------------- the two reciprocals, and what relates them */

      factorialStep <- coding.fact(Coding.FactorialAtSuccessor).flatMap(rules.spec(i, _))
      carriedStep <- Conv.apTerm(embeddingConstant, factorialStep)
      productOfEmbeddings <- peano
        .fact(Peano.EmbedsProduct)
        .flatMap(rules.specAll(_, List(factorialHere, successorIndex)))
      splitDenominator <- Conv.trans(carriedStep, productOfEmbeddings)

      overSplitEquation <- LogicError.lift(Term.eq(reciprocal, overSplit)).flatMap(field.prove)
      cleared <- discharged(factorialNotZero.conclusion, factorialNotZero, overSplitEquation)
        .flatMap(discharged(successorNotZero.conclusion, successorNotZero, _))
      foldedInner <- Conv.sym(splitDenominator).flatMap(Conv.apTerm(inverseConstant, _))
      foldedOuter <- Conv.apTerm(scaledHead, foldedInner)
      relation <- Conv.trans(cleared, foldedOuter)

      /* ------------------------- each term as a magnitude times a reciprocal, proved forwards */

      productHere <- Parser.term(
        theory,
        notation,
        "Power (x:real) (i:num) * inv (real_of_num (NUM_FACT (i:num)))",
        values)
      productNext <- Parser.term(
        theory,
        notation,
        "Power (x:real) (SUC (i:num)) * inv (real_of_num (NUM_FACT (SUC (i:num))))",
        values)
      timesConstant <- headOf(scaledHead)
      byMagnitude <- LogicError.lift(Term.app(timesConstant, magnitudeOfPower))

      asProduct <- LogicError.lift(Term.eq(quotientAt, productHere)).flatMap(ring.prove)
      asProductNext <- LogicError
        .lift(Term.eq(quotientAtSuccessor, productNext))
        .flatMap(ring.prove)

      collapseHere <- rules
        .spec(reciprocal, absOfNonNegative)
        .flatMap(rules.mp(_, reciprocalNonNegative))
      collapseNext <- rules
        .spec(nextReciprocal, absOfNonNegative)
        .flatMap(rules.mp(_, nextReciprocalNonNegative))

      termHereIs <- Conv
        .apTerm(magnitudeConstant, asProduct)
        .flatMap(opening =>
          rules
            .specAll(absMul, List(powerAt, reciprocal))
            .flatMap(Conv.trans(opening, _)))
        .flatMap(split =>
          Conv.apTerm(byMagnitude, collapseHere).flatMap(Conv.trans(split, _)))

      magnitudeAtSuccessor <- Parser.term(
        theory, notation, "abs (Power (x:real) (SUC (i:num)))", values)
      byMagnitudeNext <- LogicError.lift(Term.app(timesConstant, magnitudeAtSuccessor))
      termNextIs <- Conv
        .apTerm(magnitudeConstant, asProductNext)
        .flatMap(opening =>
          rules
            .specAll(absMul, List(powerAtSuccessor, nextReciprocal))
            .flatMap(Conv.trans(opening, _)))
        .flatMap(split =>
          Conv.apTerm(byMagnitudeNext, collapseNext).flatMap(Conv.trans(split, _)))

      /* ------------------------------------- the successor's magnitude, and the two shapes */

      powerStep <- series.fact(Series.PowerAtSuccessor).flatMap(rules.specAll(_, List(x, i)))
      magnitudeStep <- Conv
        .apTerm(magnitudeConstant, powerStep)
        .flatMap(opening =>
          rules.specAll(absMul, List(x, powerAt)).flatMap(Conv.trans(opening, _)))

      leftShape <- Conv
        .apTerm(timesConstant, magnitudeStep)
        .flatMap(Conv.apThm(_, nextReciprocal))
        .flatMap(Conv.trans(termNextIs, _))
      rightShape <- Conv
        .apTerm(byMagnitude, relation)
        .flatMap(Conv.trans(termHereIs, _))

      /* ---------------------------------------------------------------- the estimate itself */

      powerNonNegative <- rules.spec(powerAt, absNonNegative)
      productNonNegative <- order
        .multiplyNonNegatives
        .flatMap(rules.specAll(_, List(magnitudeOfPower, nextReciprocal)))
        .flatMap(rules.mp(_, powerNonNegative))
        .flatMap(rules.mp(_, nextReciprocalNonNegative))

      bound <- Parser.proposition(
        theory, notation, "2 * abs (x:real) <= real_of_num (SUC (i:num))")
      assumedBound <- LogicError.lift(Kernel.assume(bound))

      estimate <- linarith
        .prove(
          "!lhs:real. !rhs:real. !a:real. !p:real. !w:real. !r:real. " +
            "lhs = (a * p) * w ==> rhs = p * (r * w) ==> 2 * a <= r ==> 0 <= p * w ==> " +
            "lhs <= 1 / 2 * rhs")
        .flatMap(rules.specAll(
          _, List(termNext, termHere, here, magnitudeOfPower, nextReciprocal, embedded)))
        .flatMap(rules.mp(_, leftShape))
        .flatMap(rules.mp(_, rightShape))
        .flatMap(rules.mp(_, assumedBound))
        .flatMap(rules.mp(_, productNonNegative))

      result <- rules
        .disch(bound, estimate)
        .flatMap(rules.genAll(_, List(x, i)))
    } yield result
  }

  /**
   * `|- !x m. 2 * abs x <= real_of_num m ==> !j. T (m + j) <= Power (1/2) j * T m`, where `T` is
   * the exponential's term at `x` read through `abs`.
   *
   * [[TermsHalve]] once per step, and the whole of the induction is carrying the bound forward:
   * the halving asks for `2 * abs x <= real_of_num (SUC (m + j))` and what is assumed is the
   * same at `m`, so what a step spends beyond the hypothesis is `m <= SUC (m + j)` on `num`
   * carried across the embedding — `NUM_LE_ADD` and `NUM_LE_SUC` with one transitivity.
   *
   * **The index the bound holds from is not named here**, and that is the point of stating it at
   * a variable: it is whatever `Peano.NUM_CEIL_LE` returns for `2 * abs x`, and this induction
   * never mentions `NUM_CEIL`.
   */
  private def tailIsGeometric(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    series: Series,
    peano: Peano,
    induct: Induct,
    halving: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", values)
    val m = Term.variable("m", numbers)

    val termsText = "\\i:num. abs (Power (x:real) i / real_of_num (NUM_FACT i))"

    def sidesOf(proposition: Term): Either[LogicError, (Term, Term)] =
      proposition match {
        case App(App(_, left), right) => Right((left, right))
        case other                    => Left(NotOfForm("a comparison of two terms", other))
      }

    def argumentOf(term: Term): Either[LogicError, Term] = term match {
      case App(_, argument) => Right(argument)
      case other            => Left(NotOfForm("an application to take the argument of", other))
    }

    for {
      half <- Parser.term(theory, notation, "(1:real) / 2", values)
      doubled <- Parser.term(theory, notation, "2 * abs (x:real)", values)
      embeddedIndex <- Parser.term(theory, notation, "real_of_num (m:num)", values)

      bound <- Parser.proposition(
        theory, notation, "2 * abs (x:real) <= real_of_num (m:num)")
      assumedBound <- LogicError.lift(Kernel.assume(bound))

      collapseIndex <- peano.fact(Peano.AddAtZero).flatMap(rules.spec(m, _))
      unitPower <- series.fact(Series.PowerAtZero).flatMap(rules.spec(half, _))
      indexAtZero <- Rewrite.Rule.of(logic, collapseIndex)
      powerAtZero <- Rewrite.Rule.of(logic, unitPower)

      statement <- Parser.proposition(
        theory,
        notation,
        // Beta-reduced as written, because the driver compares what it proves with what it was
        // handed and every rewriting under it normalises. A statement carrying the redex is a
        // different term and the refusal names neither end.
        "!j:num. abs (Power (x:real) (NUM_ADD (m:num) j) / " +
          "real_of_num (NUM_FACT (NUM_ADD (m:num) j))) <= " +
          "Power ((1:real) / 2) j * " +
          "abs (Power (x:real) (m:num) / real_of_num (NUM_FACT (m:num)))")

      everywhere <- induct.proveBy(
        statement,
        base =>
          Induct.afterRewriting(Vector(indexAtZero, powerAtZero), base) { goal =>
            for {
              ends <- sidesOf(goal)
              settled <- linarith
                .prove("!t:real. t <= 1 * t")
                .flatMap(rules.spec(ends._1, _))
            } yield settled
          },
        step =>
          for {
            // `m + SUC j = SUC (m + j)`, which is what puts the goal where the halving applies.
            shift <- peano
              .fact(Peano.AddAtSuccessor)
              .flatMap(rules.specAll(_, List(m, step.variable)))
            successorOfInner <- Term
              .destEq(shift.conclusion)
              .map(_._2)
              .toRight(NotOfForm("an equation", shift.conclusion))
            inner <- argumentOf(successorOfInner)

            // `m <= SUC (m + j)`, on `num` and then across the embedding.
            belowSum <- peano
              .fact(Peano.AtMostSum)
              .flatMap(rules.specAll(_, List(m, step.variable)))
            belowSuccessor <- peano.fact(Peano.AtMostSuccessor).flatMap(rules.spec(inner, _))
            reaches <- rules
              .conjIntro(belowSum, belowSuccessor)
              .flatMap(both =>
                peano
                  .fact(Peano.Transitive)
                  .flatMap(rules.specAll(_, List(m, inner, successorOfInner)))
                  .flatMap(rules.mp(_, both)))
            carried <- peano
              .fact(Peano.EmbedsOrder)
              .flatMap(rules.specAll(_, List(m, successorOfInner)))
              .flatMap(rules.mp(_, reaches))
            embeddedSides <- sidesOf(carried.conclusion)

            reachedBound <- linarith
              .prove("!a:real. !p:real. !q:real. a <= p ==> p <= q ==> a <= q")
              .flatMap(rules.specAll(_, List(doubled, embeddedIndex, embeddedSides._2)))
              .flatMap(rules.mp(_, assumedBound))
              .flatMap(rules.mp(_, carried))

            halved <- rules
              .specAll(halving, List(x, inner))
              .flatMap(rules.mp(_, reachedBound))
            halvedSides <- sidesOf(halved.conclusion)
            hypothesisSides <- sidesOf(step.hypothesis.conclusion)
            previous <- argumentOf(halvedSides._2)
            scaleAndTail <- hypothesisSides._2 match {
              case App(App(_, scale), tail) => Right((scale, tail))
              case other => Left(NotOfForm("a scaled term", other))
            }

            powerStep <- series
              .fact(Series.PowerAtSuccessor)
              .flatMap(rules.specAll(_, List(half, step.variable)))
            indexRule <- Rewrite.Rule.of(logic, shift)
            powerRule <- Rewrite.Rule.of(logic, powerStep)

            result <- Induct.afterRewriting(Vector(indexRule, powerRule), step.goal) { _ =>
              linarith
                .prove(
                  "!u:real. !v:real. !p:real. !t:real. " +
                    "u <= 1 / 2 * v ==> v <= p * t ==> u <= (1 / 2 * p) * t")
                .flatMap(rules.specAll(
                  _, List(halvedSides._1, previous, scaleAndTail._1, scaleAndTail._2)))
                .flatMap(rules.mp(_, halved))
                .flatMap(rules.mp(_, step.hypothesis))
            }
          } yield result
      )

      result <- rules
        .disch(bound, everywhere)
        .flatMap(rules.genAll(_, List(x, m)))
    } yield result
  }

  /**
   * [[AbsolutelyConvergent]], which is what `Limit.SUM_CAUCHY_PRODUCT` asks of both its arguments
   * and what [[ExponentialAboveTwo]] did not buy.
   *
   * == Why the comparison test is not the instrument ==
   *
   * `Limit.SUM_COMPARISON` asks for domination at **every** index, and a uniform geometric
   * dominator for an arbitrary `x` wants `(2 * abs x)^i <= C * i!`, a fact about `num` this
   * repository does not have. Its base-two case, `Coding.NUM_POW_LE_FACT`, is two hundred and
   * twenty-seven lines, and the general one wants a split at `N` and a monotonicity of the power
   * in its exponent on top of that. **That was measured before this route was chosen** rather
   * than after.
   *
   * What is used instead is `Limit.MONOTONE_CONVERGES` on the partial sums directly. The terms
   * are non-negative so the sums increase, and the bound comes from **splitting** the series
   * rather than from dominating it: `Peano.NUM_CEIL_LE` gives `M` with
   * `2 * abs x <= real_of_num M`, [[TailIsGeometric]] puts everything past `M` under a geometric
   * series, and everything before it is one number.
   *
   * == The split, and where `SUM_REINDEX` does the work ==
   *
   * `NUM_LE_TOTAL` divides the indices and the two cases are answered differently. Up to `M` the
   * partial sums are under `Sum T M` by `Limit.SUM_GROWS`. Past it the index is `M + d`, and
   * `Series.SUM_REINDEX` reads `Sum (\u. T (M + u)) d` as a difference of two partial sums, so
   * the tail estimate becomes an estimate on `Sum T (M + d)` with no arithmetic in between.
   * `SUM_SCALE_RIGHT` takes the constant `T M` out of the dominating sum and what is left is the
   * geometric series under two, which is the same three facts `ExponentialAboveTwo` uses.
   */
  private def absolutelyConvergentEverywhere(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    series: Series,
    peano: Peano,
    limit: Limit,
    geometricTail: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val order = limit.magnitude.order
    val x = Term.variable("x", values)
    val i = Term.variable("i", numbers)
    val n = Term.variable("n", numbers)
    val d = Term.variable("d", numbers)

    val termsText = "\\i:num. abs (Power (x:real) i / real_of_num (NUM_FACT i))"
    val ceilingText = "NUM_CEIL (2 * abs (x:real))"
    val quotientAtCeiling =
      "Power (x:real) (" + ceilingText + ") / real_of_num (NUM_FACT (" + ceilingText + "))"
    val termAtCeiling = "abs (" + quotientAtCeiling + ")"

    def opened(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    def sidesOf(proposition: Term): Either[LogicError, (Term, Term)] =
      proposition match {
        case App(App(_, left), right) => Right((left, right))
        case other                    => Left(NotOfForm("two terms of one relation", other))
      }

    def chain(
      lower: Kernel.Thm,
      upper: Kernel.Thm,
      small: Term,
      middle: Term,
      large: Term
    ): Either[LogicError, Kernel.Thm] =
      linarith
        .prove("!p:real. !q:real. !r:real. p <= q ==> q <= r ==> p <= r")
        .flatMap(rules.specAll(_, List(small, middle, large)))
        .flatMap(rules.mp(_, lower))
        .flatMap(rules.mp(_, upper))

    for {
      /* ------------------------------------------------------------------- everything, parsed */

      terms <- Parser.term(theory, notation, termsText, Type.fun(numbers, values))
      partial <- Parser.term(
        theory, notation, "Sum (" + termsText + ")", Type.fun(numbers, values))
      ceiling <- Parser.term(theory, notation, ceilingText, numbers)
      half <- Parser.term(theory, notation, "(1:real) / 2", values)
      halves <- Parser.term(
        theory, notation, "\\u:num. Power ((1:real) / 2) u", Type.fun(numbers, values))
      doubled <- Parser.term(theory, notation, "2 * abs (x:real)", values)
      quotientAtIndex <- Parser.term(
        theory, notation, "Power (x:real) (i:num) / real_of_num (NUM_FACT (i:num))", values)
      quotientAtN <- Parser.term(
        theory, notation, "Power (x:real) (n:num) / real_of_num (NUM_FACT (n:num))", values)
      quotientAtM <- Parser.term(theory, notation, quotientAtCeiling, values)
      atCeiling <- Parser.term(theory, notation, termAtCeiling, values)
      sumAtCeiling <- Parser.term(
        theory, notation, "Sum (" + termsText + ") (" + ceilingText + ")", values)
      sumAtIndex <- Parser.term(theory, notation, "Sum (" + termsText + ") (n:num)", values)
      sumAtGap <- Parser.term(
        theory,
        notation,
        "Sum (" + termsText + ") (NUM_ADD (" + ceilingText + ") (d:num))",
        values)
      shifted <- Parser.term(
        theory,
        notation,
        "\\u:num. abs (Power (x:real) (NUM_ADD (" + ceilingText + ") u) / " +
          "real_of_num (NUM_FACT (NUM_ADD (" + ceilingText + ") u)))",
        Type.fun(numbers, values))
      dominating <- Parser.term(
        theory,
        notation,
        "\\u:num. Power ((1:real) / 2) u * (" + termAtCeiling + ")",
        Type.fun(numbers, values))
      geometricAtGap <- Parser.term(
        theory, notation, "Sum (\\u:num. Power ((1:real) / 2) u) (d:num)", values)
      shiftedAtGap <- Parser.term(
        theory,
        notation,
        "Sum (\\u:num. abs (Power (x:real) (NUM_ADD (" + ceilingText + ") u) / " +
          "real_of_num (NUM_FACT (NUM_ADD (" + ceilingText + ") u)))) (d:num)",
        values)
      dominatingAtGap <- Parser.term(
        theory,
        notation,
        "Sum (\\u:num. Power ((1:real) / 2) u * (" + termAtCeiling + ")) (d:num)",
        values)
      powerAtGap <- Parser.term(theory, notation, "Power ((1:real) / 2) (d:num)", values)
      two <- Parser.term(theory, notation, "2:real", values)
      ceilingBound <- Parser.term(
        theory,
        notation,
        "Sum (" + termsText + ") (" + ceilingText + ") + 2 * (" + termAtCeiling + ")",
        values)

      absNonNegative <- limit.magnitude.fact(Magnitude.AbsNonNegative)
      nonNegative <- rules.spec(quotientAtIndex, absNonNegative).flatMap(rules.gen(i, _))
      atCeilingNonNegative <- rules.spec(quotientAtM, absNonNegative)
      atIndexNonNegative <- rules.spec(quotientAtN, absNonNegative)

      /* ---------------------------------------------------- the partial sums increase, at all */

      recurrence <- series
        .fact(Series.AtSuccessor)
        .flatMap(rules.specAll(_, List(terms, n)))
        .flatMap(opened)
      recurrenceSides <- Term
        .destEq(recurrence.conclusion)
        .toRight(NotOfForm("an equation", recurrence.conclusion))
      summands <- sidesOf(recurrenceSides._2)
      increasing <- linarith
        .prove("!p:real. !q:real. !t:real. q = p + t ==> 0 <= t ==> p <= q")
        .flatMap(rules.specAll(_, List(summands._1, recurrenceSides._1, summands._2)))
        .flatMap(rules.mp(_, recurrence))
        .flatMap(rules.mp(_, atIndexNonNegative))
        .flatMap(rules.gen(n, _))

      /* ------------------------------------------- the index, and the tail geometric under it */

      magnitudeNonNegative <- rules.spec(x, absNonNegative)
      doubledNonNegative <- linarith
        .prove("!a:real. 0 <= a ==> 0 <= 2 * a")
        .flatMap(theorem =>
          sidesOf(magnitudeNonNegative.conclusion)
            .flatMap(sides => rules.specAll(theorem, List(sides._2)))
            .flatMap(rules.mp(_, magnitudeNonNegative)))
      reachesCeiling <- peano
        .fact(Peano.CeilingAtLeast)
        .flatMap(rules.spec(doubled, _))
        .flatMap(rules.mp(_, doubledNonNegative))
      tail <- rules
        .specAll(geometricTail, List(x, ceiling))
        .flatMap(rules.mp(_, reachesCeiling))

      /* ------------------------------------------------------ the geometric series under two */

      positivePower <- series
        .fact(Series.PowerPositive)
        .flatMap(rules.spec(half, _))
        .flatMap(theorem => linarith.prove("(0:real) < (1:real) / 2").flatMap(rules.mp(theorem, _)))
        .flatMap(rules.spec(d, _))
      geometric <- series.fact(Series.Geometric).flatMap(rules.specAll(_, List(half, d)))
      geometricUnderTwo <- linarith
        .prove("!p:real. !s:real. ((1:real) / 2 - 1) * s = p - 1 ==> 0 < p ==> s <= 2")
        .flatMap(rules.specAll(_, List(powerAtGap, geometricAtGap)))
        .flatMap(rules.mp(_, geometric))
        .flatMap(rules.mp(_, positivePower))

      /* ------------------------------------------------------------- the tail sum under twice */

      dominated <- series
        .fact(Series.Monotone)
        .flatMap(rules.specAll(_, List(shifted, dominating)))
        .flatMap(opened)
        .flatMap(rules.mp(_, tail))
        .flatMap(rules.spec(d, _))
      takenOut <- series
        .fact(Series.ScaledRight)
        .flatMap(rules.specAll(_, List(atCeiling, halves, d)))
        .flatMap(opened)
      scaled <- order
        .fact(Order.MultiplyLe)
        .flatMap(rules.specAll(_, List(atCeiling, geometricAtGap, two)))
        .flatMap(rules.mp(_, atCeilingNonNegative))
        .flatMap(rules.mp(_, geometricUnderTwo))
      scaledSides <- sidesOf(scaled.conclusion)
      throughTheScale <- onRight(takenOut, dominated)
      tailSum <- chain(
        throughTheScale, scaled, shiftedAtGap, scaledSides._1, scaledSides._2)

      /* ---------------------------------------------- the bound at every index, by two cases */

      reindex <- series
        .fact(Series.Reindex)
        .flatMap(rules.specAll(_, List(terms, ceiling, d)))
        .flatMap(opened)
      pastTheIndex <- linarith
        .prove("!s:real. !g:real. !h:real. !t:real. g = s - h ==> g <= 2 * t ==> s <= h + 2 * t")
        .flatMap(rules.specAll(_, List(sumAtGap, shiftedAtGap, sumAtCeiling, atCeiling)))
        .flatMap(rules.mp(_, reindex))
        .flatMap(rules.mp(_, tailSum))

      grows <- limit
        .fact(Limit.Grows)
        .flatMap(rules.spec(terms, _))
        .flatMap(rules.mp(_, nonNegative))
        .flatMap(opened)
      belowIndex <- Parser.proposition(
        theory, notation, "NUM_LE (n:num) (" + ceilingText + ")")
      assumedBelow <- LogicError.lift(Kernel.assume(belowIndex))
      beforeTheIndex <- rules
        .specAll(grows, List(n, ceiling))
        .flatMap(rules.mp(_, assumedBelow))
        .flatMap(theorem =>
          linarith
            .prove("!s:real. !h:real. !t:real. s <= h ==> 0 <= t ==> s <= h + 2 * t")
            .flatMap(rules.specAll(_, List(sumAtIndex, sumAtCeiling, atCeiling)))
            .flatMap(rules.mp(_, theorem))
            .flatMap(rules.mp(_, atCeilingNonNegative)))

      aboveIndex <- Parser.proposition(
        theory, notation, "NUM_LE (" + ceilingText + ") (n:num)")
      assumedAbove <- LogicError.lift(Kernel.assume(aboveIndex))
      orderDefinition <- peano.definition(Peano.NonStrictOrder)
      unfolded <- Conv
        .unfold(orderDefinition, List(ceiling, n))
        .flatMap(equation =>
          Term
            .destEq(equation.conclusion)
            .toRight(NotOfForm("an equation", equation.conclusion))
            .flatMap(sides => Conv.betaNormalise(sides._2).flatMap(Conv.trans(equation, _))))
      witness <- LogicError.lift(Kernel.eqMp(unfolded, assumedAbove))
      inner <- Parser.proposition(
        theory, notation, "NUM_ADD (" + ceilingText + ") (d:num) = n:num")
      assumedInner <- LogicError.lift(Kernel.assume(inner))
      carriedIndex <- Conv.apTerm(partial, assumedInner)
      atTheIndex <- onLeft(carriedIndex, pastTheIndex)
      afterTheIndex <- rules.existsElim(witness, d, atTheIndex)

      total <- peano.fact(Peano.Total).flatMap(rules.specAll(_, List(n, ceiling)))
      // Not discharged: `disjElim` discharges each disjunct itself and asks only that the two
      // cases prove the same thing.
      everyIndex <- rules
        .disjElim(total, beforeTheIndex, afterTheIndex)
        .flatMap(rules.gen(n, _))

      /* ------------------------------------------------- bounded and increasing, so convergent */

      boundClaim <- Parser.proposition(
        theory, notation, "?b:real. !n:num. Sum (" + termsText + ") n <= b")
      boundPredicate <- logic
        .destExistsPredicate(boundClaim)
        .toRight(NotOfForm("an existential quantification", boundClaim))
      bounded <- rules.existsIntro(boundPredicate, ceilingBound, everyIndex)

      converging <- limit
        .fact(Limit.MonotoneConverges)
        .flatMap(rules.spec(partial, _))
        .flatMap(opened)
        .flatMap(rules.mp(_, increasing))
        .flatMap(rules.mp(_, bounded))

      result <- rules.gen(x, converging)
    } yield result
  }

  /** `|- 0 < real_of_num (NUM_FACT z)`, the factorial's positivity carried across the embedding. */
  private def factorialEmbedsPositively(
    logic: Logic,
    linarith: Linarith,
    peano: Peano,
    coding: Coding,
    index: Term,
    denominator: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      factorial <- denominator match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("an embedded natural", other))
      }
      positive <- coding.fact(Coding.FactorialPositive).flatMap(rules.spec(index, _))
      sides <- positive.conclusion match {
        case App(App(_, left), _) => Right(left)
        case other => Left(NotOfForm("a comparison", other))
      }
      embedded <- peano
        .fact(Peano.EmbedsStrictOrder)
        .flatMap(rules.specAll(_, List(sides, factorial)))
        .flatMap(rules.mp(_, positive))
      zeroEmbeds <- peano.fact(Peano.EmbedsZero)
      folded <- Rewrite.Rule
        .all(logic, Vector(zeroEmbeds))
        .flatMap(Rewrite.inTheorem(_, embedded))
      result <- linarith
        .prove("!a:real. 0 + 1 <= a ==> 0 < a")
        .flatMap(rules.spec(denominator, _))
        .flatMap(rules.mp(_, folded))
    } yield result
  }

  /** `|- f * inv f = 1` at a denominator already known to be positive, which is where the axiom goes. */
  private def inverseCancels(
    logic: Logic,
    limit: Limit,
    theory: Theory,
    notation: Notation,
    positive: Kernel.Thm,
    denominator: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val order = limit.magnitude.order

    for {
      nonZero <- order
        .fact(Positivity.NonZero)
        .flatMap(rules.spec(denominator, _))
        .flatMap(rules.mp(_, positive))
      result <- order.ring.reals
        .axiom("MUL_INVERSE")
        .flatMap(rules.spec(denominator, _))
        .flatMap(rules.mp(_, nonZero))
    } yield result
  }

  /** `|- Power 1 z / f = inv f`, which is `POWER_ONE` and then ring algebra with nothing owed. */
  private def quotientIsInverse(
    logic: Logic,
    series: Series,
    theory: Theory,
    notation: Notation,
    index: Term,
    divisor: Term,
    denominator: Term,
    term: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      powerOfOne <- series.fact(Series.PowerOfOne).flatMap(rules.spec(index, _))
      simplified <- Conv.apTerm(divisor, powerOfOne).flatMap(Conv.apThm(_, denominator))
      quotient <- rightOf(simplified)
      inverse <- Parser
        .term(theory, notation, Real.Inverse, Type.fun(values, values))
        .flatMap(constant => LogicError.lift(Term.app(constant, denominator)))
      equation <- LogicError.lift(Term.eq(quotient, inverse)).flatMap(series.ring.prove)
      result <- Conv.trans(simplified, equation)
    } yield result
  }

  /** The divisor and the denominator of a quotient, which every term of this series is. */
  private def quotientParts(term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(divisor, _), denominator) => Right((divisor, denominator))
    case other => Left(NotOfForm("a quotient", other))
  }

  /** A function applied to an argument with the redex reduced, which is what a fact is about. */
  private def reduced(function: Term, argument: Term): Either[LogicError, Term] =
    for {
      applied <- LogicError.lift(Term.app(function, argument))
      equation <- Conv.betaRoot(applied)
      result <- rightOf(equation)
    } yield result

  /** The relation of a binary conclusion, which is what a congruence step is applied under. */
  private def relationOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    theorem.conclusion match {
      case App(App(relation, _), _) => Right(relation)
      case other => Left(NotOfForm("a comparison", other))
    }

  /** `|- left' R right` from `|- left = left'` and `|- left R right`. */
  private def onLeft(equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    theorem.conclusion match {
      case App(App(relation, _), right) =>
        for {
          congruence <- Conv.apTerm(relation, equation)
          applied <- Conv.apThm(congruence, right)
          result <- LogicError.lift(Kernel.eqMp(applied, theorem))
        } yield result
      case other => Left(NotOfForm("a comparison", other))
    }

  /** `|- left R right'` from `|- right = right'` and `|- left R right`. */
  private def onRight(equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    theorem.conclusion match {
      case App(App(relation, left), _) =>
        for {
          context <- LogicError.lift(Term.app(relation, left))
          congruence <- Conv.apTerm(context, equation)
          result <- LogicError.lift(Kernel.eqMp(congruence, theorem))
        } yield result
      case other => Left(NotOfForm("a comparison", other))
    }

  /** A theorem with the redexes of its conclusion reduced. */
  private def betaOpened(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv
      .betaNormalise(theorem.conclusion)
      .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

  /** A vector of results as a result of a vector, which three call sites here want. */
  private def gather(
    results: Vector[Either[LogicError, Kernel.Thm]]
  ): Either[LogicError, Vector[Kernel.Thm]] =
    results.foldRight[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
      case (next, rest) => next.flatMap(one => rest.map(one +: _))
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
