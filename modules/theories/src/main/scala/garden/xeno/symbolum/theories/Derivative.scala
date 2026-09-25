package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The derivative of a real function at a point, the interior extremum lemma, Rolle's theorem, the
 * mean value theorem, and since the same day the product rule with the continuity it rests on.
 *
 * `derivative f x m` says that `f` has derivative `m` at `x`, and it is the epsilon-delta statement
 * written out, the way `continuous` and `converges` are: for every positive tolerance `e` there is
 * a positive radius `d` such that every non-zero increment `h` inside it has
 * `abs (f (x + h) - f x - m * h) < e * abs h`. It is a definition and costs no axiom. What it buys
 * is [[Derivative.Rolle]]: a function continuous on `[a, b]`, with a derivative at every point
 * strictly inside, and equal values at the two ends, has derivative zero somewhere strictly inside.
 * It is the first thing to spend the extreme value theorem, which is why it is the rung after it.
 *
 * == Why the definition has no quotient in it ==
 *
 * The textbook writes `abs ((f (x + h) - f x) / h - m) < e`. For `h` not zero the two say the same,
 * because multiplying by `abs h` is an equivalence there, and `0 < abs h` is in the hypothesis for
 * exactly that reason. The quotient form would put a symbolic denominator in every goal a proof
 * about a derivative meets, and `Linarith` refuses one by name, since cancelling it needs it to be
 * non-zero and that is `Field`'s to assume. In the product form every step below is a closed
 * schematic statement over real variables that `Linarith` decides, including the one fragile
 * shape, `m / 2 * abs w` beside `abs w = w`, which it settles through its round of products.
 *
 * == The argument ==
 *
 * [[Derivative.InteriorMaximum]] is Fermat's: if `f` is greatest at `c` over `[a, b]` and `0 < m`,
 * then at tolerance `m / 2` a step `w = min (d / 2) (b - c)` to the right stays in the interval and
 * inside the radius, and the estimate gives `f (c + w) - f c > (m / 2) * w > 0`, against the
 * maximum. The step is the one `Continuity`'s intermediate value theorem already takes, and
 * `Continuity.minimumPositive` is reused rather than written again. `m < 0` is the same step to
 * the left, and `LT_TOTAL` puts the three cases on the table, so nothing classical is spent.
 *
 * [[Derivative.InteriorMinimum]] is the maximum of `\y. 0 - f y`, whose derivative is
 * [[Derivative.Negation]], as `CONTINUOUS_ATTAINS_MIN` is the maximum of the same function. And
 * Rolle takes a greatest and a least value from the extreme value theorem: if either is strictly
 * inside, the interior lemma says its derivative is zero; if both are at the ends, `f a = f b`
 * makes them equal, `f` is level on `[a, b]`, and the midpoint has derivative zero at radius
 * `(b - a) / 2`, by the same computation as [[Derivative.Constant]].
 *
 * == What it costs, and what it does not reach ==
 *
 * One constant, no axiom. Rolle spends exactly what the extreme value theorem spends, the sixteen
 * axioms of the reals and the choice that `abs` is defined by; the interior lemma and the negation
 * spend no `COMPLETENESS`, because a derivative at one point is a statement about one point.
 * `DerivativeSpec` asserts both as equalities.
 *
 * **The mean value theorem is Rolle at `(b - a) * f y - (f b - f a) * y`**, since 2026-09-25, and
 * what stood in front of it was three facts rather than analysis: that such a function is
 * continuous, which is `Continuity.Linear`; that a derivative is linear, which is
 * [[Derivative.Linear]]; and that it is unique, which is [[Derivative.Unique]] and is what carries
 * Rolle's zero back to `f`. The two linearities give each of a pair of terms half of the tolerance
 * through a reciprocal of `2 * (abs p + 1)`, which is `Root`'s arrangement, so no goal of either
 * has a quotient in it. [[Derivative.MeanValue]] costs what Rolle costs; the other three spend no
 * `COMPLETENESS`.
 *
 * It is a development of its own rather than a section of `Continuity`, for the reason that one
 * gives about `Limit`: continuity at a point is a statement about a function and a radius, and a
 * derivative is a statement about an increment and a slope.
 */
final class Derivative private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Derivative {

  /* ---------------------------------------------------------------- the constant */

  /** `derivative f x m`: `f` has derivative `m` at `x`. */
  val DerivativeName: String = "derivative"

  /** The definition, as text: the increment is `m * h` to within any positive part of `abs h`. */
  val DerivativeBody: String =
    "\\f:real -> real. \\x:real. \\m:real. !e:real. 0 < e ==> ?d:real. 0 < d /\\ " +
      "(!h:real. 0 < abs h /\\ abs h < d ==> abs (f (x + h) - f x - m * h) < e * abs h)"

  /* ------------------------------------------------------------------- the facts */

  /**
   * `|- !c x. derivative (\y. c) x 0`
   *
   * A constant function has derivative zero everywhere. Published for what it guards: a definition
   * nothing satisfies would make Rolle's theorem true and empty, and this and [[Identity]] are two
   * functions it is satisfied by, at the slopes a reader expects.
   */
  val Constant: String = "DERIVATIVE_CONST"

  /** `|- !x. derivative (\y. y) x 1`: the identity has derivative one everywhere. */
  val Identity: String = "DERIVATIVE_ID"

  /**
   * `|- !f x m. derivative f x m ==> derivative (\y. 0 - f y) x (0 - m)`
   *
   * The one fact about combining derivatives anything here has needed, which is
   * `Continuity.Negation`'s situation exactly: [[InteriorMinimum]] is [[InteriorMaximum]] at the
   * negation. [[Linear]] is the general one since 2026-09-25, and a product of two functions is not
   * here, because nothing has asked for one.
   */
  val Negation: String = "DERIVATIVE_NEG"

  /**
   * `|- !f a b c m. a < c ==> c < b ==> (!x. a <= x /\ x <= b ==> f x <= f c) ==>
   * derivative f c m ==> m = 0`
   *
   * Fermat's interior extremum lemma, for the maximum. The point has to be strictly inside: at an
   * end the step that would refute a non-zero slope leaves the interval.
   */
  val InteriorMaximum: String = "DERIVATIVE_INTERIOR_MAX"

  /** The same, for a least value strictly inside `[a, b]`. */
  val InteriorMinimum: String = "DERIVATIVE_INTERIOR_MIN"

  /**
   * `|- !f a b. a < b ==> (!x. a <= x /\ x <= b ==> continuous f x) ==>
   * (!x. a < x /\ x < b ==> ?m. derivative f x m) ==> f a = f b ==>
   * ?c. a < c /\ c < b /\ derivative f c 0`
   *
   * Rolle's theorem. The continuity hypothesis is written exactly as the extreme value theorem asks
   * for it, and the derivative only has to exist strictly inside, which is the textbook's
   * statement: `\x. abs x` on `[-1, 1]` has no derivative at zero and none is needed at the ends.
   */
  val Rolle: String = "ROLLE"

  /**
   * `|- !f g x m n p q. derivative f x m ==> derivative g x n ==>
   * derivative (\y. p * f y + q * g y) x (p * m + q * n)`
   *
   * The derivative is linear. Stated for two functions and two coefficients, as
   * `CONTINUOUS_LINEAR` is, and for the same reason: the mean value theorem asks for one
   * combination and the general statement costs nothing more.
   */
  val Linear: String = "DERIVATIVE_LINEAR"

  /**
   * `|- !f x m n. derivative f x m ==> derivative f x n ==> m = n`
   *
   * A function has at most one derivative at a point. It is what lets the definition be read as
   * naming a slope rather than admitting several, and it is what carries Rolle's zero back to `f`
   * in [[MeanValue]]. It needs the increment to be non-zero, which is why `0 < abs h` is in the
   * definition: at `h = 0` every slope fits.
   */
  val Unique: String = "DERIVATIVE_UNIQUE"

  /**
   * `|- !f a b. a < b ==> (!x. a <= x /\ x <= b ==> continuous f x) ==>
   * (!x. a < x /\ x < b ==> ?m. derivative f x m) ==>
   * ?c m. a < c /\ c < b /\ derivative f c m /\ f b - f a = m * (b - a)`
   *
   * The mean value theorem, with no quotient: the slope at some interior point times the length of
   * the interval is the change of `f` across it. The quotient form would owe `~(b - a = 0)` at
   * every use, and this one owes nothing, `a < b` being in the hypotheses already.
   */
  val MeanValue: String = "MEAN_VALUE"

  /**
   * `|- !f x m. derivative f x m ==> continuous f x`
   *
   * A function with a derivative at a point is continuous there. It is the bridge between the two
   * developments, and the product rule is what needed it: to keep `g (x + h)` bounded and near
   * `g x` while `f`'s error is multiplied by it.
   */
  val Continuous: String = "DERIVATIVE_CONTINUOUS"

  /**
   * `|- !f g x m n. derivative f x m ==> derivative g x n ==>
   * derivative (\y. f y * g y) x (m * g x + f x * n)`
   *
   * The product rule.
   */
  val ProductRule: String = "DERIVATIVE_PRODUCT"

  /** What every derived fact says, as text, in the order they are derived. */
  val Statements: Vector[(String, String)] = Vector(
    Constant -> "!c:real. !x:real. derivative (\\y:real. c) x 0",
    Identity -> "!x:real. derivative (\\y:real. y) x 1",
    Negation ->
      "!f:real -> real. !x:real. !m:real. derivative f x m ==> derivative (\\y:real. 0 - f y) x (0 - m)",
    InteriorMaximum ->
      ("!f:real -> real. !a:real. !b:real. !c:real. !m:real. a < c ==> c < b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> f x <= f c) ==> derivative f c m ==> m = 0"),
    InteriorMinimum ->
      ("!f:real -> real. !a:real. !b:real. !c:real. !m:real. a < c ==> c < b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> f c <= f x) ==> derivative f c m ==> m = 0"),
    Rolle ->
      ("!f:real -> real. !a:real. !b:real. a < b ==> (!x:real. a <= x /\\ x <= b ==> continuous f x) ==> " +
        "(!x:real. a < x /\\ x < b ==> ?m:real. derivative f x m) ==> f a = f b ==> " +
        "?c:real. a < c /\\ c < b /\\ derivative f c 0"),
    Linear ->
      ("!f:real -> real. !g:real -> real. !x:real. !m:real. !n:real. !p:real. !q:real. " +
        "derivative f x m ==> derivative g x n ==> derivative (\\y:real. p * f y + q * g y) x (p * m + q * n)"),
    Unique -> "!f:real -> real. !x:real. !m:real. !n:real. derivative f x m ==> derivative f x n ==> m = n",
    MeanValue ->
      ("!f:real -> real. !a:real. !b:real. a < b ==> (!x:real. a <= x /\\ x <= b ==> continuous f x) ==> " +
        "(!x:real. a < x /\\ x < b ==> ?m:real. derivative f x m) ==> " +
        "?c:real. ?m:real. a < c /\\ c < b /\\ derivative f c m /\\ f b - f a = m * (b - a)"),
    Continuous -> "!f:real -> real. !x:real. !m:real. derivative f x m ==> continuous f x",
    ProductRule ->
      ("!f:real -> real. !g:real -> real. !x:real. !m:real. !n:real. derivative f x m ==> derivative g x n ==> " +
        "derivative (\\y:real. f y * g y) x (m * g x + f x * n)")
  )

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Functions: Type = Type.fun(Reals, Reals)

  /** The development in the chain's signature, which is the one a consumer reaches for. */
  lazy val standard: Derivative = Chain.standard.derivative

  /**
   * The development over the reals, their order, their magnitude and continuity, extending `base`.
   *
   * `base` is the chain's end when this is built rather than `continuity.theory`, for the reason
   * every link gives: a constant declared into a side branch is unreachable from every link above
   * it. The steps are `Continuity`'s, over this theory and this definition, because the moves are
   * the same ones and a second copy of them would be a second place to get them wrong.
   */
  def construct(
    classical: Classical,
    reals: RealTheory,
    magnitude: Magnitude,
    continuity: Continuity,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Derivative] =
    for {
      body <- Parser.term(base, notation, DerivativeBody)
      defined <- LogicError.lift(Kernel.defineConstant(base, DerivativeName, body))
      (theory, definition) = defined

      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(magnitude.order)
      steps = Continuity.Steps(logic, linarith, theory, notation, definition)

      constant <- constantFunction(steps, magnitude)
      identity <- identityFunction(steps, magnitude)
      negation <- negationOf(steps, magnitude)
      interiorMax <- interiorMaximum(steps, reals, magnitude)
      interiorMin <- interiorMinimum(steps, negation, interiorMax)
      rolle <- rolleTheorem(steps, magnitude, continuity, interiorMax, interiorMin)
      linear <- linearCombination(steps, reals, magnitude)
      unique <- uniqueSlope(steps, reals, magnitude)
      continuousLinear <- continuity.fact(Continuity.Linear)
      continuousIdentity <- continuity.fact(Continuity.Identity)
      meanValue <- meanValueTheorem(steps, continuity, continuousLinear, continuousIdentity, identity, linear, unique, rolle)
      continuous <- continuousWhereDifferentiable(steps, reals, magnitude, continuity)
      productRuleFact <- productRule(steps, reals, magnitude, continuity, continuous)

      facts = Map[String, Kernel.Thm](
        Constant -> constant,
        Identity -> identity,
        Negation -> negation,
        InteriorMaximum -> interiorMax,
        InteriorMinimum -> interiorMin,
        Rolle -> rolle,
        Linear -> linear,
        Unique -> unique,
        MeanValue -> meanValue,
        Continuous -> continuous,
        ProductRule -> productRuleFact
      )

      // Each statement checked against the text a person reads it by, as `Continuity` does: a
      // development that built something other than what it says it built must not be handed out.
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { (acc, entry) =>
        val (name, text) = entry
        for {
          _ <- acc
          expected <- Parser.proposition(theory, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Derivative(theory, notation, logic, Map(DerivativeName -> definition), facts)

  /** `|- derivative f x m = <the statement>`, reduced. */
  private def unfoldDerivative(steps: Continuity.Steps, f: Term, x: Term, m: Term): Either[LogicError, Kernel.Thm] =
    for {
      equation <- Conv.unfold(steps.definition, List(f, x, m))
      right <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
      normal <- Conv.betaNormalise(right)
      joined <- Conv.trans(equation, normal)
    } yield joined

  /** A theorem `derivative f x m`, opened into its epsilon-delta statement. */
  private def openDerivative(steps: Continuity.Steps, f: Term, x: Term, m: Term, theorem: Kernel.Thm) =
    unfoldDerivative(steps, f, x, m).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

  /** `derivative f x m`, from a proof of its epsilon-delta statement. */
  private def foldDerivative(steps: Continuity.Steps, f: Term, x: Term, m: Term, statement: Kernel.Thm) =
    for {
      equation <- unfoldDerivative(steps, f, x, m)
      backwards <- Conv.sym(equation)
      result <- LogicError.lift(Kernel.eqMp(backwards, statement))
    } yield result

  /**
   * A function whose increment at `x` is exactly `m * h` for every `h`, written as `increment`, has
   * derivative `m` there at radius one: the error is zero and `e * abs h` is positive.
   */
  private def exactly(
    steps: Continuity.Steps,
    magnitude: Magnitude,
    function: Term,
    slope: String,
    increment: String
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    val e = Term.variable("e", Reals)
    val h = Term.variable("h", Reals)
    for {
      m <- real(slope)
      positive <- proposition("0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      near <- proposition("0 < abs (h:real) /\\ abs h < 1")
      assumedNear <- LogicError.lift(Kernel.assume(near))
      hPositive <- rules.conjElim1(assumedNear)
      nonNegative <- lemma(s"!x:real h:real. 0 <= $increment").flatMap(rules.specAll(_, List(x, h)))
      isItself <- at(magnitude.fact(Magnitude.OfNonNegative), increment).flatMap(mp(_, Right(nonNegative)))
      within <- at(
        lemma(s"!A:real x:real h:real e:real B:real. A = $increment ==> 0 < e ==> 0 < B ==> A < e * B"),
        s"abs ($increment)", "x:real", "h:real", "e:real", "abs (h:real)"
      ).flatMap(mp(_, Right(isItself), Right(assumedPositive), Right(hPositive)))
      everyH <- rules.disch(near, within).flatMap(rules.gen(h, _))
      radius <- conj(lemma("(0:real) < 1"), Right(everyH))
      one <- real("1:real")
      witnessed <- existential(
        s"?d:real. 0 < d /\\ (!h:real. 0 < abs h /\\ abs h < d ==> abs ($increment) < e:real * abs h)"
      ).flatMap(rules.existsIntro(_, one, radius))
      statement <- rules.disch(positive, witnessed).flatMap(rules.gen(e, _))
      result <- foldDerivative(steps, function, x, m, statement)
    } yield result
  }

  /** [[Constant]], at the increment `c - c - 0 * h`. */
  private def constantFunction(steps: Continuity.Steps, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val c = Term.variable("c", Reals)
    val x = Term.variable("x", Reals)
    for {
      function <- Parser.term(theory, notation, "\\y:real. c:real", Functions)
      proved <- exactly(steps, magnitude, function, "0:real", "c:real - c - 0 * (h:real)")
      result <- rules.gen(x, proved).flatMap(rules.gen(c, _))
    } yield result
  }

  /** [[Identity]], at the increment `x + h - x - 1 * h`. */
  private def identityFunction(steps: Continuity.Steps, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    for {
      function <- Parser.term(theory, notation, "\\y:real. y", Functions)
      proved <- exactly(steps, magnitude, function, "1:real", "x:real + h - x - 1 * (h:real)")
      result <- rules.gen(x, proved)
    } yield result
  }

  /**
   * [[Negation]]: at the same radius, the error of the negation is the negation of the error, and
   * `ABS_CASES` on it lands on one of `ABS_ABOVE` and `ABS_ABOVE_NEG` of the original.
   */
  private def negationOf(steps: Continuity.Steps, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val x = Term.variable("x", Reals)
    val m = Term.variable("m", Reals)
    val e = Term.variable("e", Reals)
    val d = Term.variable("d", Reals)
    val h = Term.variable("h", Reals)
    val increment = "(f:real -> real) (x + h) - f x - m * h"
    val negated = "(0 - (f:real -> real) (x + h)) - (0 - f x) - (0 - m) * h"
    for {
      hypothesis <- proposition("derivative (f:real -> real) x m")
      assumedHypothesis <- LogicError.lift(Kernel.assume(hypothesis))
      statement <- openDerivative(steps, f, x, m, assumedHypothesis)

      positive <- proposition("0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      near <- rules.spec(e, statement).flatMap(rules.mp(_, assumedPositive))
      radius <- assume(
        s"0 < d:real /\\ (!h:real. 0 < abs h /\\ abs h < d ==> abs ($increment) < e:real * abs h)")
      dPositive <- rules.conjElim1(radius)
      inside <- rules.conjElim2(radius)

      hNear <- proposition("0 < abs (h:real) /\\ abs h < d:real")
      assumedHNear <- LogicError.lift(Kernel.assume(hNear))
      bound <- rules.spec(h, inside).flatMap(rules.mp(_, assumedHNear))

      cases <- at(magnitude.fact(Magnitude.AbsCases), negated)
      itself <- for {
        is <- assume(s"abs ($negated) = $negated")
        below <- at(magnitude.fact(Magnitude.AbsAboveNegation), increment)
        result <- at(
          lemma("!A:real P:real Q:real m:real h:real X:real Y:real. X = (0 - P) - (0 - Q) - (0 - m) * h ==> " +
            "-(P - Q - m * h) <= A ==> A < Y ==> X < Y"),
          s"abs ($increment)", "(f:real -> real) (x + h)", "(f:real -> real) x", "m:real", "h:real",
          s"abs ($negated)", "e:real * abs (h:real)"
        ).flatMap(mp(_, Right(is), Right(below), Right(bound)))
      } yield result
      opposite <- for {
        is <- assume(s"abs ($negated) = -($negated)")
        below <- at(magnitude.fact(Magnitude.AbsAbove), increment)
        result <- at(
          lemma("!A:real P:real Q:real m:real h:real X:real Y:real. X = -((0 - P) - (0 - Q) - (0 - m) * h) ==> " +
            "P - Q - m * h <= A ==> A < Y ==> X < Y"),
          s"abs ($increment)", "(f:real -> real) (x + h)", "(f:real -> real) x", "m:real", "h:real",
          s"abs ($negated)", "e:real * abs (h:real)"
        ).flatMap(mp(_, Right(is), Right(below), Right(bound)))
      } yield result
      within <- rules.disjElim(cases, itself, opposite)

      everyH <- rules.disch(hNear, within).flatMap(rules.gen(h, _))
      both <- rules.conjIntro(dPositive, everyH)
      witnessed <- existential(
        s"?d:real. 0 < d /\\ (!h:real. 0 < abs h /\\ abs h < d ==> abs ($negated) < e:real * abs h)"
      ).flatMap(rules.existsIntro(_, d, both))
      eliminated <- rules.existsElim(near, d, witnessed)
      negatedStatement <- rules.disch(positive, eliminated).flatMap(rules.gen(e, _))

      g <- Parser.term(theory, notation, "\\y:real. 0 - (f:real -> real) y", Functions)
      slope <- real("0 - m:real")
      result <- foldDerivative(steps, g, x, slope, negatedStatement)
      discharged <- rules.disch(hypothesis, result)
      closed <- rules.genAll(discharged, List(f, x, m))
    } yield closed
  }

  /** [[InteriorMaximum]], by the three cases of `LT_TOTAL` at `0` and the slope. */
  private def interiorMaximum(
    steps: Continuity.Steps,
    reals: RealTheory,
    magnitude: Magnitude
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val c = Term.variable("c", Reals)
    val m = Term.variable("m", Reals)
    val d = Term.variable("d", Reals)

    val aBelow = assume("a:real < c:real")
    val bAbove = assume("c:real < b:real")
    val isMaximum = assume("!x:real. a:real <= x /\\ x <= b:real ==> (f:real -> real) x <= f c:real")

    /** The case of one sign, stepping by `step` from `c`, with the tolerance `tolerance`. */
    def sided(
      signCase: String,
      tolerance: String,
      tolerancePositive: String,
      gap: String,
      gapPositive: String,
      step: String => String,
      absoluteFact: String,
      absoluteIs: String => String,
      stepNonPositive: Option[String],
      insideInterval: String,
      contradiction: String
    ): Either[LogicError, Kernel.Thm] = {
      val w = s"min (d / 2) ($gap)"
      val h = step(w)
      val increment = s"(f:real -> real) (c + $h) - f c - m * $h"
      for {
        goal <- proposition("m:real = 0")
        sign <- assume(signCase)
        statement <- assume("derivative (f:real -> real) c m")
          .flatMap(openDerivative(steps, f, c, m, _))
        e <- real(tolerance)
        ePositive <- at(lemma(tolerancePositive), "m:real").flatMap(mp(_, Right(sign)))
        near <- rules.spec(e, statement).flatMap(rules.mp(_, ePositive))
        radius <- assume(
          s"0 < d:real /\\ (!h:real. 0 < abs h /\\ abs h < d ==> " +
            s"abs ((f:real -> real) (c + h) - f c - m * h) < $tolerance * abs h)")
        dPositive <- rules.conjElim1(radius)
        inside <- rules.conjElim2(radius)

        gapOk = at(lemma(gapPositive), "a:real", "c:real", "b:real").flatMap(mp(_, aBelow, bAbove))
        wPositive <- Continuity.minimumPositive(steps, magnitude, gap, Right(dPositive), gapOk)
        wHalf <- at(magnitude.fact(Magnitude.MinBelowLeft), "d / 2", gap)
        wGap <- at(magnitude.fact(Magnitude.MinBelowRight), "d / 2", gap)

        absoluteValue <- stepNonPositive match {
          case None =>
            at(magnitude.fact(absoluteFact), h)
              .flatMap(mp(_, at(lemma("!w:real. 0 < w ==> 0 <= w"), w).flatMap(mp(_, Right(wPositive)))))
          case Some(nonPositive) =>
            at(magnitude.fact(absoluteFact), h)
              .flatMap(mp(_, at(lemma(nonPositive), w).flatMap(mp(_, Right(wPositive)))))
        }
        admissible <- at(
          lemma(s"!B:real w:real d:real. B = ${absoluteIs("w")} ==> 0 < w ==> w <= d / 2 ==> 0 < d ==> 0 < B /\\ B < d"),
          s"abs ($h)", w, "d:real"
        ).flatMap(mp(_, Right(absoluteValue), Right(wPositive), Right(wHalf), Right(dPositive)))
        hTerm <- real(h)
        bound <- rules.spec(hTerm, inside).flatMap(rules.mp(_, admissible))
        below <- at(magnitude.fact(Magnitude.AbsAboveNegation), increment)

        inInterval <- at(lemma(insideInterval), "a:real", "c:real", w, "b:real")
          .flatMap(mp(_, aBelow, bAbove, Right(wPositive), Right(wGap)))
        point <- real(s"c + $h")
        notAbove <- isMaximum.flatMap(rules.spec(point, _)).flatMap(rules.mp(_, inInterval))

        absurd <- at(
          lemma(contradiction),
          s"abs ($increment)", s"abs ($h)", s"(f:real -> real) (c + $h)", "(f:real -> real) c", "m:real", w
        ).flatMap(mp(_, Right(below), Right(bound), Right(absoluteValue), Right(sign), Right(wPositive), Right(notAbove)))
        falsity <- rules.falsityElim(goal, absurd)
        result <- rules.existsElim(near, d, falsity)
      } yield result
    }

    for {
      total <- reals.axiom("LT_TOTAL")
      zero <- real("0:real")
      trichotomy <- rules.specAll(total, List(zero, m))

      rising <- sided(
        signCase = "0 < m:real",
        tolerance = "m / 2",
        tolerancePositive = "!m:real. 0 < m ==> 0 < m / 2",
        gap = "b - c",
        gapPositive = "!a:real c:real b:real. a < c ==> c < b ==> 0 < b - c",
        step = w => s"($w)",
        absoluteFact = Magnitude.OfNonNegative,
        absoluteIs = w => w,
        stepNonPositive = None,
        insideInterval = "!a:real c:real w:real b:real. a < c ==> c < b ==> 0 < w ==> w <= b - c ==> " +
          "a <= c + w /\\ c + w <= b",
        contradiction = "!A:real B:real P:real Q:real m:real w:real. -(P - Q - m * w) <= A ==> " +
          "A < m / 2 * B ==> B = w ==> 0 < m ==> 0 < w ==> P <= Q ==> F"
      )
      falling <- sided(
        signCase = "m:real < 0",
        tolerance = "(0 - m) / 2",
        tolerancePositive = "!m:real. m < 0 ==> 0 < (0 - m) / 2",
        gap = "c - a",
        gapPositive = "!a:real c:real b:real. a < c ==> c < b ==> 0 < c - a",
        step = w => s"(0 - $w)",
        absoluteFact = Magnitude.OfNonPositive,
        absoluteIs = w => s"-(0 - $w)",
        stepNonPositive = Some("!w:real. 0 < w ==> 0 - w <= 0"),
        insideInterval = "!a:real c:real w:real b:real. a < c ==> c < b ==> 0 < w ==> w <= c - a ==> " +
          "a <= c + (0 - w) /\\ c + (0 - w) <= b",
        contradiction = "!A:real B:real P:real Q:real m:real w:real. -(P - Q - m * (0 - w)) <= A ==> " +
          "A < (0 - m) / 2 * B ==> B = -(0 - w) ==> m < 0 ==> 0 < w ==> P <= Q ==> F"
      )
      level <- assume("0 = m:real").flatMap(Conv.sym)
      rest <- assume("0 = m:real \\/ m < 0").flatMap(rules.disjElim(_, level, falling))
      cases <- rules.disjElim(trichotomy, rising, rest)

      result <- List(
        "derivative (f:real -> real) c m",
        "!x:real. a:real <= x /\\ x <= b:real ==> (f:real -> real) x <= f c:real",
        "c:real < b:real",
        "a:real < c:real"
      ).foldLeft[Either[LogicError, Kernel.Thm]](Right(cases)) { (acc, text) =>
        for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
      }.flatMap(rules.genAll(_, List(f, a, b, c, m)))
    } yield result
  }

  /** [[InteriorMinimum]]: [[InteriorMaximum]] at `\y. 0 - f y`, whose slope [[Negation]] gives. */
  private def interiorMinimum(
    steps: Continuity.Steps,
    negation: Kernel.Thm,
    interiorMax: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val c = Term.variable("c", Reals)
    val m = Term.variable("m", Reals)
    val x = Term.variable("x", Reals)
    for {
      g <- Parser.term(theory, notation, "\\y:real. 0 - (f:real -> real) y", Functions)
      slope <- real("0 - m:real")
      aBelow <- assume("a:real < c:real")
      bAbove <- assume("c:real < b:real")
      isMinimum <- assume("!x:real. a:real <= x /\\ x <= b:real ==> (f:real -> real) c:real <= f x")
      hypothesis <- assume("derivative (f:real -> real) c m")
      negated <- rules.specAll(negation, List(f, c, m)).flatMap(rules.mp(_, hypothesis))

      member <- proposition("a:real <= x:real /\\ x <= b:real")
      assumedMember <- LogicError.lift(Kernel.assume(member))
      atX <- rules.spec(x, isMinimum).flatMap(rules.mp(_, assumedMember))
      flipped <- at(lemma("!p:real q:real. p <= q ==> 0 - q <= 0 - p"), "(f:real -> real) c", "(f:real -> real) x")
        .flatMap(mp(_, Right(atX)))
      isMaximum <- rules.disch(member, flipped).flatMap(rules.gen(x, _))

      specialised <- rules.specAll(interiorMax, List(g, a, b, c, slope))
      reduced <- Conv.betaNormalise(specialised.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, specialised)))
      zero <- mp(reduced, Right(aBelow), Right(bAbove), Right(isMaximum), Right(negated))
      result <- at(lemma("!m:real. 0 - m = 0 ==> m = 0"), "m:real").flatMap(mp(_, Right(zero)))

      closed <- List(
        "derivative (f:real -> real) c m",
        "!x:real. a:real <= x /\\ x <= b:real ==> (f:real -> real) c:real <= f x",
        "c:real < b:real",
        "a:real < c:real"
      ).foldLeft[Either[LogicError, Kernel.Thm]](Right(result)) { (acc, text) =>
        for { theorem <- acc; h <- proposition(text); next <- rules.disch(h, theorem) } yield next
      }.flatMap(rules.genAll(_, List(f, a, b, c, m)))
    } yield closed
  }

  /**
   * [[Rolle]]: the extreme value theorem twice, then either an extreme strictly inside, or both at
   * the ends and `f` level on the interval.
   */
  private def rolleTheorem(
    steps: Continuity.Steps,
    magnitude: Magnitude,
    continuity: Continuity,
    interiorMax: Kernel.Thm,
    interiorMin: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val bigM = Term.variable("M", Reals)
    val bigN = Term.variable("N", Reals)
    val m = Term.variable("m", Reals)
    val e = Term.variable("e", Reals)
    val h = Term.variable("h", Reals)
    val x = Term.variable("x", Reals)

    val Goal = "?c:real. a:real < c /\\ c < b:real /\\ derivative (f:real -> real) c 0"
    val middle = "(a + b) / 2"

    val aBelowB = assume("a:real < b:real")
    val ends = assume("(f:real -> real) a = f b")
    val continuous = assume("!x:real. a:real <= x /\\ x <= b:real ==> continuous (f:real -> real) x")
    val differentiable = assume("!x:real. a:real < x /\\ x < b:real ==> ?m:real. derivative (f:real -> real) x m")

    /** A point strictly inside at which `fermat` applies: its derivative is zero there. */
    def interior(point: FVar, fermat: Kernel.Thm, extremum: Either[LogicError, Kernel.Thm], inside: Kernel.Thm) =
      for {
        above <- rules.conjElim1(inside)
        below <- rules.conjElim2(inside)
        exists <- differentiable.flatMap(rules.spec(point, _)).flatMap(rules.mp(_, inside))
        slope <- assume(s"derivative (f:real -> real) ${point.name}:real m:real")
        zero <- rules.specAll(fermat, List(f, a, b, point, m)).flatMap(mp(_, Right(above), Right(below), extremum, Right(slope)))
        applied <- Parser.term(theory, notation, s"derivative (f:real -> real) ${point.name}:real", Type.fun(Reals, Type.Bool))
        equation <- Conv.apTerm(applied, zero)
        atZero <- LogicError.lift(Kernel.eqMp(equation, slope))
        both <- conj(Right(above), conj(Right(below), Right(atZero)))
        found <- existential(Goal).flatMap(rules.existsIntro(_, point, both))
        result <- rules.existsElim(exists, m, found)
      } yield result

    /** `(a < P /\ P < b) \/ f P = f a`, from `a <= P <= b` and `f a = f b`. */
    def insideOrLevel(point: String, lower: Kernel.Thm, upper: Kernel.Thm) =
      for {
        leCases <- magnitude.order.fact(Order.LeCases)
        pTerm <- real(s"$point:real")
        disjunction <- proposition(s"(a:real < $point:real /\\ $point < b:real) \\/ (f:real -> real) $point = f a")
        sides <- steps.logic.destDisj(disjunction).toRight(NotOfForm("a disjunction", disjunction))
        (insideTerm, levelTerm) = sides

        atStart <- for {
          same <- assume(s"a:real = $point:real")
          values <- Conv.apTerm(f, same).flatMap(Conv.sym)
          result <- rules.disjIntro2(insideTerm, values)
        } yield result

        afterStart <- for {
          strictly <- assume(s"a:real < $point:real")
          split <- rules.specAll(leCases, List(pTerm, b)).flatMap(rules.mp(_, upper))
          beforeEnd <- for {
            strictlyBelow <- assume(s"$point:real < b:real")
            both <- rules.conjIntro(strictly, strictlyBelow)
            result <- rules.disjIntro1(levelTerm, both)
          } yield result
          atEnd <- for {
            same <- assume(s"$point:real = b:real")
            values <- Conv.apTerm(f, same)
            back <- ends.flatMap(Conv.sym)
            joined <- Conv.trans(values, back)
            result <- rules.disjIntro2(insideTerm, joined)
          } yield result
          result <- rules.disjElim(split, beforeEnd, atEnd)
        } yield result

        split <- rules.specAll(leCases, List(a, pTerm)).flatMap(rules.mp(_, lower))
        result <- rules.disjElim(split, afterStart, atStart)
      } yield result

    for {
      ordered <- aBelowB.flatMap(below => at(lemma("!a:real b:real. a < b ==> a <= b"), "a:real", "b:real").flatMap(mp(_, Right(below))))
      maximum <- continuity.fact(Continuity.AttainsMaximum)
        .flatMap(rules.specAll(_, List(f, a, b)))
        .flatMap(mp(_, Right(ordered), continuous))
      minimum <- continuity.fact(Continuity.AttainsMinimum)
        .flatMap(rules.specAll(_, List(f, a, b)))
        .flatMap(mp(_, Right(ordered), continuous))

      atMaximum <- assume("a:real <= M:real /\\ M <= b:real /\\ (!x:real. a <= x /\\ x <= b ==> (f:real -> real) x <= f M)")
      atMinimum <- assume("a:real <= N:real /\\ N <= b:real /\\ (!x:real. a <= x /\\ x <= b ==> (f:real -> real) N <= f x)")
      mLower <- rules.conjElim1(atMaximum)
      mUpper <- rules.conjElim2(atMaximum).flatMap(rules.conjElim1)
      mIs <- rules.conjElim2(atMaximum).flatMap(rules.conjElim2)
      nLower <- rules.conjElim1(atMinimum)
      nUpper <- rules.conjElim2(atMinimum).flatMap(rules.conjElim1)
      nIs <- rules.conjElim2(atMinimum).flatMap(rules.conjElim2)

      maxCases <- insideOrLevel("M", mLower, mUpper)
      minCases <- insideOrLevel("N", nLower, nUpper)

      fromMaximum <- assume("a:real < M:real /\\ M < b:real").flatMap(interior(bigM, interiorMax, Right(mIs), _))
      fromMinimum <- assume("a:real < N:real /\\ N < b:real").flatMap(interior(bigN, interiorMin, Right(nIs), _))

      /* ------------------------------------------ both extremes at the ends: `f` is level */

      level <- for {
        maxLevel <- assume("(f:real -> real) M = f a")
        minLevel <- assume("(f:real -> real) N = f a")
        memberText = "a:real <= x:real /\\ x <= b:real"
        member <- proposition(memberText)
        assumedMember <- LogicError.lift(Kernel.assume(member))
        upper <- rules.spec(x, mIs).flatMap(rules.mp(_, assumedMember))
        lower <- rules.spec(x, nIs).flatMap(rules.mp(_, assumedMember))
        flatAtX <- at(
          lemma("!p:real q:real r:real s:real. p <= q ==> r <= p ==> q = s ==> r = s ==> p = s"),
          "(f:real -> real) x", "(f:real -> real) M", "(f:real -> real) N", "(f:real -> real) a"
        ).flatMap(mp(_, Right(upper), Right(lower), Right(maxLevel), Right(minLevel)))
        flat <- rules.disch(member, flatAtX).flatMap(rules.gen(x, _))

        centre <- real(middle)
        centred <- aBelowB.flatMap(below =>
          at(lemma("!a:real b:real. a < b ==> a < (a + b) / 2 /\\ (a + b) / 2 < b"), "a:real", "b:real")
            .flatMap(mp(_, Right(below))))
        centreAbove <- rules.conjElim1(centred)
        centreBelow <- rules.conjElim2(centred)
        centreMember <- at(lemma("!a:real c:real b:real. a < c ==> c < b ==> a <= c /\\ c <= b"), "a:real", middle, "b:real")
          .flatMap(mp(_, Right(centreAbove), Right(centreBelow)))
        atCentre <- rules.spec(centre, flat).flatMap(rules.mp(_, centreMember))

        positive <- proposition("0 < e:real")
        assumedPositive <- LogicError.lift(Kernel.assume(positive))
        near <- proposition(s"0 < abs (h:real) /\\ abs h < (b - a) / 2")
        assumedNear <- LogicError.lift(Kernel.assume(near))
        hPositive <- rules.conjElim1(assumedNear)
        hSmall <- rules.conjElim2(assumedNear)
        hAbove <- at(magnitude.fact(Magnitude.AbsAbove), "h:real")
        hBelow <- at(magnitude.fact(Magnitude.AbsAboveNegation), "h:real")
        stepMember <- at(
          lemma("!a:real b:real h:real B:real. h <= B ==> -h <= B ==> B < (b - a) / 2 ==> " +
            "a <= (a + b) / 2 + h /\\ (a + b) / 2 + h <= b"),
          "a:real", "b:real", "h:real", "abs (h:real)"
        ).flatMap(mp(_, Right(hAbove), Right(hBelow), Right(hSmall)))
        stepped <- real(s"$middle + h")
        atStep <- rules.spec(stepped, flat).flatMap(rules.mp(_, stepMember))

        increment = s"(f:real -> real) ($middle + h) - f ($middle) - 0 * h"
        nonNegative <- at(
          lemma("!P:real Q:real R:real h:real. P = R ==> Q = R ==> 0 <= P - Q - 0 * h"),
          s"(f:real -> real) ($middle + h)", s"(f:real -> real) ($middle)", "(f:real -> real) a", "h:real"
        ).flatMap(mp(_, Right(atStep), Right(atCentre)))
        isItself <- at(magnitude.fact(Magnitude.OfNonNegative), increment).flatMap(mp(_, Right(nonNegative)))
        within <- at(
          lemma("!A:real P:real Q:real R:real h:real e:real B:real. A = P - Q - 0 * h ==> P = R ==> Q = R ==> " +
            "0 < e ==> 0 < B ==> A < e * B"),
          s"abs ($increment)", s"(f:real -> real) ($middle + h)", s"(f:real -> real) ($middle)",
          "(f:real -> real) a", "h:real", "e:real", "abs (h:real)"
        ).flatMap(mp(_, Right(isItself), Right(atStep), Right(atCentre), Right(assumedPositive), Right(hPositive)))
        everyH <- rules.disch(near, within).flatMap(rules.gen(h, _))
        dPositive <- aBelowB.flatMap(below =>
          at(lemma("!a:real b:real. a < b ==> 0 < (b - a) / 2"), "a:real", "b:real").flatMap(mp(_, Right(below))))
        radius <- rules.conjIntro(dPositive, everyH)
        half <- real("(b - a) / 2")
        witnessed <- existential(
          s"?d:real. 0 < d /\\ (!h:real. 0 < abs h /\\ abs h < d ==> abs ($increment) < e:real * abs h)"
        ).flatMap(rules.existsIntro(_, half, radius))
        statement <- rules.disch(positive, witnessed).flatMap(rules.gen(e, _))
        zero <- real("0:real")
        atZero <- foldDerivative(steps, f, centre, zero, statement)
        both <- conj(Right(centreAbove), conj(Right(centreBelow), Right(atZero)))
        result <- existential(Goal).flatMap(rules.existsIntro(_, centre, both))
      } yield result

      afterMaximum <- rules.disjElim(minCases, fromMinimum, level)
      cases <- rules.disjElim(maxCases, fromMaximum, afterMaximum)
      withoutMinimum <- rules.existsElim(minimum, bigN, cases)
      withoutMaximum <- rules.existsElim(maximum, bigM, withoutMinimum)

      result <- List(
        "(f:real -> real) a = f b",
        "!x:real. a:real < x /\\ x < b:real ==> ?m:real. derivative (f:real -> real) x m",
        "!x:real. a:real <= x /\\ x <= b:real ==> continuous (f:real -> real) x",
        "a:real < b:real"
      ).foldLeft[Either[LogicError, Kernel.Thm]](Right(withoutMaximum)) { (acc, text) =>
        for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
      }.flatMap(rules.genAll(_, List(f, a, b)))
    } yield result
  }

  /**
   * [[Linear]]: [[Continuity.Linear]]'s argument at the increment, each error given its share of
   * `e * abs h`, and the combined error regrouped into `p` times one and `q` times the other.
   */
  private def linearCombination(steps: Continuity.Steps, reals: RealTheory, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val x = Term.variable("x", Reals)
    val m = Term.variable("m", Reals)
    val n = Term.variable("n", Reals)
    val p = Term.variable("p", Reals)
    val q = Term.variable("q", Reals)
    val e = Term.variable("e", Reals)
    val h = Term.variable("h", Reals)
    val d1 = Term.variable("d1", Reals)
    val d2 = Term.variable("d2", Reals)
    val ef = "(f:real -> real) (x + h) - f x - m:real * h"
    val eg = "(g:real -> real) (x + h) - g x - n:real * h"
    val whole =
      "p:real * (f:real -> real) (x + h) + q:real * (g:real -> real) (x + h) - (p * f x + q * g x) - " +
        "(p * m:real + q * n:real) * h"
    val within =
      "!H:real A:real w:real d:real. 0 < H ==> A < w ==> w <= d ==> 0 < H /\\ A < d"
    val scale = "!P:real A:real T:real. 0 <= P ==> A < T ==> P * A <= P * T"
    val half =
      "!R:real X:real P:real T:real H:real e:real. R = X ==> X <= P * (T * H) ==> 0 <= P ==> 0 < T ==> " +
        "0 < H ==> 2 * (P + 1) * T = e ==> R < e / 2 * H"
    for {
      fHyp <- proposition("derivative (f:real -> real) x m")
      gHyp <- proposition("derivative (g:real -> real) x n")
      fAt <- LogicError.lift(Kernel.assume(fHyp)).flatMap(openDerivative(steps, f, x, m, _))
      gAt <- LogicError.lift(Kernel.assume(gHyp)).flatMap(openDerivative(steps, g, x, n, _))

      positive <- proposition("0 < e:real")
      ePositive <- LogicError.lift(Kernel.assume(positive))
      forP <- Continuity.share(steps, reals, magnitude, "p:real", ePositive)
      forQ <- Continuity.share(steps, reals, magnitude, "q:real", ePositive)

      nearF <- real(forP.term).flatMap(rules.spec(_, fAt)).flatMap(rules.mp(_, forP.positive))
      nearG <- real(forQ.term).flatMap(rules.spec(_, gAt)).flatMap(rules.mp(_, forQ.positive))
      radiusF <- assume(s"0 < d1:real /\\ (!h:real. 0 < abs h /\\ abs h < d1 ==> abs ($ef) < ${forP.term} * abs h)")
      radiusG <- assume(s"0 < d2:real /\\ (!h:real. 0 < abs h /\\ abs h < d2 ==> abs ($eg) < ${forQ.term} * abs h)")
      d1Positive <- rules.conjElim1(radiusF)
      d2Positive <- rules.conjElim1(radiusG)
      insideF <- rules.conjElim2(radiusF)
      insideG <- rules.conjElim2(radiusG)
      dPositive <- Continuity.minimumOfTwo(steps, magnitude, d1Positive, d2Positive)

      near <- proposition("0 < abs (h:real) /\\ abs h < min (d1:real) (d2:real)")
      assumedNear <- LogicError.lift(Kernel.assume(near))
      hPositive <- rules.conjElim1(assumedNear)
      hSmall <- rules.conjElim2(assumedNear)
      below1 <- at(magnitude.fact(Magnitude.MinBelowLeft), "d1:real", "d2:real")
      below2 <- at(magnitude.fact(Magnitude.MinBelowRight), "d1:real", "d2:real")
      within1 <- at(lemma(within), "abs (h:real)", "abs (h:real)", "min (d1:real) (d2:real)", "d1:real")
        .flatMap(mp(_, Right(hPositive), Right(hSmall), Right(below1)))
      within2 <- at(lemma(within), "abs (h:real)", "abs (h:real)", "min (d1:real) (d2:real)", "d2:real")
        .flatMap(mp(_, Right(hPositive), Right(hSmall), Right(below2)))
      fClose <- rules.spec(h, insideF).flatMap(rules.mp(_, within1))
      gClose <- rules.spec(h, insideG).flatMap(rules.mp(_, within2))

      regrouped <- at(
        lemma("!p:real q:real F:real G:real F0:real G0:real m:real n:real h:real. " +
          "p * F + q * G - (p * F0 + q * G0) - (p * m + q * n) * h = p * (F - F0 - m * h) + q * (G - G0 - n * h)"),
        "p:real", "q:real", "(f:real -> real) (x + h)", "(g:real -> real) (x + h)", "(f:real -> real) x",
        "(g:real -> real) x", "m:real", "n:real", "h:real")
      absFn <- Parser.term(theory, notation, "abs", Functions)
      sameAbs <- Conv.apTerm(absFn, regrouped)
      triangle <- at(magnitude.fact(Magnitude.Triangle), s"p:real * ($ef)", s"q:real * ($eg)")
      mulP <- at(magnitude.fact(Magnitude.Multiplicative), "p:real", ef)
      mulQ <- at(magnitude.fact(Magnitude.Multiplicative), "q:real", eg)
      pNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), "p:real")
      qNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), "q:real")
      scaledP <- at(lemma(scale), "abs (p:real)", s"abs ($ef)", s"${forP.term} * abs (h:real)")
        .flatMap(mp(_, Right(pNonNeg), Right(fClose)))
      scaledQ <- at(lemma(scale), "abs (q:real)", s"abs ($eg)", s"${forQ.term} * abs (h:real)")
        .flatMap(mp(_, Right(qNonNeg), Right(gClose)))
      halfP <- at(lemma(half), s"abs (p:real * ($ef))", s"abs (p:real) * abs ($ef)", "abs (p:real)", forP.term,
        "abs (h:real)", "e:real")
        .flatMap(mp(_, Right(mulP), Right(scaledP), Right(pNonNeg), Right(forP.positive), Right(hPositive), Right(forP.equation)))
      halfQ <- at(lemma(half), s"abs (q:real * ($eg))", s"abs (q:real) * abs ($eg)", "abs (q:real)", forQ.term,
        "abs (h:real)", "e:real")
        .flatMap(mp(_, Right(mulQ), Right(scaledQ), Right(qNonNeg), Right(forQ.positive), Right(hPositive), Right(forQ.equation)))
      combined <- at(
        lemma("!E:real S:real X:real Y:real e:real H:real. E = S ==> S <= X + Y ==> X < e / 2 * H ==> " +
          "Y < e / 2 * H ==> E < e * H"),
        s"abs ($whole)", s"abs (p:real * ($ef) + q:real * ($eg))", s"abs (p:real * ($ef))", s"abs (q:real * ($eg))",
        "e:real", "abs (h:real)")
        .flatMap(mp(_, Right(sameAbs), Right(triangle), Right(halfP), Right(halfQ)))

      everyH <- rules.disch(near, combined).flatMap(rules.gen(h, _))
      radius <- rules.conjIntro(dPositive, everyH)
      minimum <- real("min (d1:real) (d2:real)")
      witnessed <- existential(s"?d:real. 0 < d /\\ (!h:real. 0 < abs h /\\ abs h < d ==> abs ($whole) < e:real * abs h)")
        .flatMap(rules.existsIntro(_, minimum, radius))
      withoutG <- rules.existsElim(nearG, d2, witnessed)
      withoutF <- rules.existsElim(nearF, d1, withoutG)
      statement <- rules.disch(positive, withoutF).flatMap(rules.gen(e, _))
      function <- Parser.term(theory, notation, "\\y:real. p:real * (f:real -> real) y + q:real * (g:real -> real) y", Functions)
      slope <- real("p:real * m:real + q:real * n:real")
      result <- foldDerivative(steps, function, x, slope, statement)
      closed <- rules.disch(gHyp, result).flatMap(rules.disch(fHyp, _)).flatMap(rules.genAll(_, List(f, g, x, m, n, p, q)))
    } yield closed
  }

  /**
   * `|- !f x m n. derivative f x m ==> derivative f x n ==> m < n ==> F`, not published: at
   * tolerance `(n - m) / 2` and a step half the smaller radius, the two errors differ by
   * `(n - m) * h` and each is under half of it.
   */
  private def slopesApart(steps: Continuity.Steps, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val x = Term.variable("x", Reals)
    val m = Term.variable("m", Reals)
    val n = Term.variable("n", Reals)
    val d1 = Term.variable("d1", Reals)
    val d2 = Term.variable("d2", Reals)
    val tolerance = "(n:real - m:real) / 2"
    val w = "min (d1:real) (d2:real)"
    val step = s"$w / 2"
    val increment = s"(f:real -> real) (x + $step) - f x"
    val em = s"$increment - m:real * ($step)"
    val en = s"$increment - n:real * ($step)"
    val admissible =
      "!B:real w:real d:real. B = w / 2 ==> 0 < w ==> w <= d ==> 0 < B /\\ B < d"
    for {
      mHyp <- proposition("derivative (f:real -> real) x m")
      nHyp <- proposition("derivative (f:real -> real) x n")
      order <- proposition("m:real < n")
      assumedOrder <- LogicError.lift(Kernel.assume(order))
      mAt <- LogicError.lift(Kernel.assume(mHyp)).flatMap(openDerivative(steps, f, x, m, _))
      nAt <- LogicError.lift(Kernel.assume(nHyp)).flatMap(openDerivative(steps, f, x, n, _))
      e <- real(tolerance)
      ePositive <- at(lemma("!m:real n:real. m < n ==> 0 < (n - m) / 2"), "m:real", "n:real").flatMap(mp(_, Right(assumedOrder)))
      nearM <- rules.spec(e, mAt).flatMap(rules.mp(_, ePositive))
      nearN <- rules.spec(e, nAt).flatMap(rules.mp(_, ePositive))
      radiusM <- assume(
        s"0 < d1:real /\\ (!h:real. 0 < abs h /\\ abs h < d1 ==> abs ((f:real -> real) (x + h) - f x - m:real * h) < $tolerance * abs h)")
      radiusN <- assume(
        s"0 < d2:real /\\ (!h:real. 0 < abs h /\\ abs h < d2 ==> abs ((f:real -> real) (x + h) - f x - n:real * h) < $tolerance * abs h)")
      d1Positive <- rules.conjElim1(radiusM)
      d2Positive <- rules.conjElim1(radiusN)
      insideM <- rules.conjElim2(radiusM)
      insideN <- rules.conjElim2(radiusN)
      dPositive <- Continuity.minimumOfTwo(steps, magnitude, d1Positive, d2Positive)
      below1 <- at(magnitude.fact(Magnitude.MinBelowLeft), "d1:real", "d2:real")
      below2 <- at(magnitude.fact(Magnitude.MinBelowRight), "d1:real", "d2:real")
      stepPositive <- at(lemma("!w:real. 0 < w ==> 0 < w / 2"), w).flatMap(mp(_, Right(dPositive)))
      absStep <- at(magnitude.fact(Magnitude.OfNonNegative), step)
        .flatMap(mp(_, at(lemma("!w:real. 0 < w ==> 0 <= w"), step).flatMap(mp(_, Right(stepPositive)))))
      okM <- at(lemma(admissible), s"abs ($step)", w, "d1:real").flatMap(mp(_, Right(absStep), Right(dPositive), Right(below1)))
      okN <- at(lemma(admissible), s"abs ($step)", w, "d2:real").flatMap(mp(_, Right(absStep), Right(dPositive), Right(below2)))
      stepTerm <- real(step)
      closeM <- rules.spec(stepTerm, insideM).flatMap(rules.mp(_, okM))
      closeN <- rules.spec(stepTerm, insideN).flatMap(rules.mp(_, okN))
      aboveM <- at(magnitude.fact(Magnitude.AbsAbove), em)
      aboveN <- at(magnitude.fact(Magnitude.AbsAboveNegation), en)
      absurd <- at(
        lemma("!A:real B:real K:real m:real n:real h:real H:real. m < n ==> 0 < h ==> H = h ==> K - m * h <= A ==> " +
          "-(K - n * h) <= B ==> A < (n - m) / 2 * H ==> B < (n - m) / 2 * H ==> F"),
        s"abs ($em)", s"abs ($en)", increment, "m:real", "n:real", step, s"abs ($step)")
        .flatMap(mp(_, Right(assumedOrder), Right(stepPositive), Right(absStep), Right(aboveM), Right(aboveN),
          Right(closeM), Right(closeN)))
      withoutN <- rules.existsElim(nearN, d2, absurd)
      withoutM <- rules.existsElim(nearM, d1, withoutN)
      closed <- rules.disch(order, withoutM).flatMap(rules.disch(nHyp, _)).flatMap(rules.disch(mHyp, _))
        .flatMap(rules.genAll(_, List(f, x, m, n)))
    } yield closed
  }

  /** [[Unique]]: `LT_TOTAL` at the two slopes, and [[slopesApart]] both ways round. */
  private def uniqueSlope(steps: Continuity.Steps, reals: RealTheory, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val x = Term.variable("x", Reals)
    val m = Term.variable("m", Reals)
    val n = Term.variable("n", Reals)
    for {
      apart <- slopesApart(steps, magnitude)
      mHyp <- assume("derivative (f:real -> real) x m")
      nHyp <- assume("derivative (f:real -> real) x n")
      goal <- proposition("m:real = n")
      total <- reals.axiom("LT_TOTAL")
      trichotomy <- rules.specAll(total, List(m, n))
      below <- assume("m:real < n")
        .flatMap(order => rules.specAll(apart, List(f, x, m, n)).flatMap(mp(_, Right(mHyp), Right(nHyp), Right(order))))
        .flatMap(rules.falsityElim(goal, _))
      same <- assume("m:real = n")
      above <- assume("n:real < m")
        .flatMap(order => rules.specAll(apart, List(f, x, n, m)).flatMap(mp(_, Right(nHyp), Right(mHyp), Right(order))))
        .flatMap(rules.falsityElim(goal, _))
      rest <- assume("m:real = n \\/ n < m").flatMap(rules.disjElim(_, same, above))
      cases <- rules.disjElim(trichotomy, below, rest)
      h1 <- proposition("derivative (f:real -> real) x n")
      h0 <- proposition("derivative (f:real -> real) x m")
      closed <- rules.disch(h1, cases).flatMap(rules.disch(h0, _)).flatMap(rules.genAll(_, List(f, x, m, n)))
    } yield closed
  }

  /**
   * [[MeanValue]]: [[Rolle]] at `g = \y. (b - a) * f y + (0 - (f b - f a)) * y`, whose values at
   * the ends agree, whose continuity is [[Continuity.Linear]] and whose derivative is [[Linear]];
   * at the flat point [[Unique]] turns `derivative g c 0` into the equation for `f`.
   */
  private def meanValueTheorem(
    steps: Continuity.Steps,
    continuity: Continuity,
    continuousLinear: Kernel.Thm,
    identityContinuous: Kernel.Thm,
    identitySlope: Kernel.Thm,
    derivativeLinear: Kernel.Thm,
    unique: Kernel.Thm,
    rolle: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val x = Term.variable("x", Reals)
    val c = Term.variable("c", Reals)
    val m = Term.variable("m", Reals)
    val p = "b:real - a:real"
    val q = "0 - ((f:real -> real) b - f a)"
    val Goal = "?c:real. ?m:real. a:real < c /\\ c < b:real /\\ derivative (f:real -> real) c m /\\ f b - f a = m * (b - a)"

    def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv.betaNormalise(theorem.conclusion).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, theorem)))

    for {
      identity <- Parser.term(theory, notation, "\\y:real. y", Functions)
      pTerm <- real(p)
      qTerm <- real(q)
      one <- real("1:real")
      g <- Parser.term(theory, notation, s"\\y:real. ($p) * (f:real -> real) y + ($q) * y", Functions)

      ordered <- assume("a:real < b:real")
      continuous <- assume("!x:real. a:real <= x /\\ x <= b:real ==> continuous (f:real -> real) x")
      differentiable <- assume("!x:real. a:real < x /\\ x < b:real ==> ?m:real. derivative (f:real -> real) x m")

      /* ---------------------------------------------------------- g is continuous */
      gContinuous <- for {
        member <- proposition("a:real <= x:real /\\ x <= b:real")
        assumedMember <- LogicError.lift(Kernel.assume(member))
        fAt <- rules.spec(x, continuous).flatMap(rules.mp(_, assumedMember))
        idAt <- rules.spec(x, identityContinuous)
        combined <- rules.specAll(continuousLinear, List(f, identity, x, pTerm, qTerm))
          .flatMap(reduced).flatMap(mp(_, Right(fAt), Right(idAt)))
        result <- rules.disch(member, combined).flatMap(rules.gen(x, _))
      } yield result

      /* ---------------------------------------------------------- g is differentiable */
      gDifferentiable <- for {
        member <- proposition("a:real < x:real /\\ x < b:real")
        assumedMember <- LogicError.lift(Kernel.assume(member))
        exists <- rules.spec(x, differentiable).flatMap(rules.mp(_, assumedMember))
        slope <- assume("derivative (f:real -> real) x m")
        idSlope <- rules.spec(x, identitySlope)
        combined <- rules.specAll(derivativeLinear, List(f, identity, x, m, one, pTerm, qTerm))
          .flatMap(reduced).flatMap(mp(_, Right(slope), Right(idSlope)))
        gSlope <- real(s"($p) * m:real + ($q) * 1")
        witnessed <- proposition(s"?m:real. derivative (\\y:real. ($p) * (f:real -> real) y + ($q) * y) x m")
          .flatMap(s => logic.destExistsPredicate(s).toRight(NotOfForm("an existential", s)))
          .flatMap(rules.existsIntro(_, gSlope, combined))
        found <- rules.existsElim(exists, m, witnessed)
        result <- rules.disch(member, found).flatMap(rules.gen(x, _))
      } yield result

      level <- at(lemma("!a:real b:real A:real B:real. (b - a) * A + (0 - (B - A)) * a = (b - a) * B + (0 - (B - A)) * b"),
        "a:real", "b:real", "(f:real -> real) a", "(f:real -> real) b")

      flatSomewhere <- rules.specAll(rolle, List(g, a, b)).flatMap(reduced)
        .flatMap(mp(_, Right(ordered), Right(gContinuous), Right(gDifferentiable), Right(level)))

      /* ---------------------------------------------------------- at the flat point */
      found <- for {
        inside <- assume(s"a:real < c:real /\\ c < b:real /\\ derivative (\\y:real. ($p) * (f:real -> real) y + ($q) * y) c 0")
        above <- rules.conjElim1(inside)
        below <- rules.conjElim2(inside).flatMap(rules.conjElim1)
        flat <- rules.conjElim2(inside).flatMap(rules.conjElim2)
        exists <- rules.spec(c, differentiable).flatMap(t => rules.conjIntro(above, below).flatMap(rules.mp(t, _)))
        slope <- assume("derivative (f:real -> real) c m")
        idSlope <- rules.spec(c, identitySlope)
        gSlope <- rules.specAll(derivativeLinear, List(f, identity, c, m, one, pTerm, qTerm))
          .flatMap(reduced).flatMap(mp(_, Right(slope), Right(idSlope)))
        zero <- real("0:real")
        gSlopeTerm <- real(s"($p) * m:real + ($q) * 1")
        equal <- rules.specAll(unique, List(g, c, gSlopeTerm, zero)).flatMap(mp(_, Right(gSlope), Right(flat)))
        balance <- at(lemma("!a:real b:real A:real B:real m:real. (b - a) * m + (0 - (B - A)) * 1 = 0 ==> B - A = m * (b - a)"),
          "a:real", "b:real", "(f:real -> real) a", "(f:real -> real) b", "m:real").flatMap(mp(_, Right(equal)))
        conjunction <- conj(Right(above), conj(Right(below), conj(Right(slope), Right(balance))))
        inner <- proposition(s"?m:real. a:real < c:real /\\ c < b:real /\\ derivative (f:real -> real) c m /\\ f b - f a = m * (b - a)")
          .flatMap(s => logic.destExistsPredicate(s).toRight(NotOfForm("an existential", s)))
          .flatMap(rules.existsIntro(_, m, conjunction))
        outer <- existential(Goal).flatMap(rules.existsIntro(_, c, inner))
        result <- rules.existsElim(exists, m, outer)
      } yield result

      eliminated <- rules.existsElim(flatSomewhere, c, found)
      closed <- List(
        "!x:real. a:real < x /\\ x < b:real ==> ?m:real. derivative (f:real -> real) x m",
        "!x:real. a:real <= x /\\ x <= b:real ==> continuous (f:real -> real) x",
        "a:real < b:real"
      ).foldLeft[Either[LogicError, Kernel.Thm]](Right(eliminated)) { (acc, text) =>
        for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
      }.flatMap(rules.genAll(_, List(f, a, b)))
    } yield closed
  }

  /** `|- continuous f x = <the epsilon-delta statement at f and x>`, reduced, from `Continuity`. */
  private def unfoldContinuity(continuity: Continuity, f: Term, x: Term): Either[LogicError, Kernel.Thm] =
    for {
      definition <- continuity.definition(Continuity.Continuous)
      equation <- Conv.unfold(definition, List(f, x))
      right <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
      normal <- Conv.betaNormalise(right)
      joined <- Conv.trans(equation, normal)
    } yield joined

  /** `A < w`, `w <= d` give `A < d`: a bound under a minimum is under each of the two. */
  private val Through = "!A:real w:real d:real. A < w ==> w <= d ==> A < d"

  /**
   * [[Continuous]]: at tolerance one the increment is within `abs h` of `m * h`, so the change of
   * `f` is at most `(abs m + 1) * abs h`, and a radius under half of `e`'s [[Continuity.portion]]
   * for `abs m` keeps it under `e`. The point itself, `h = 0`, is its own case.
   */
  private def continuousWhereDifferentiable(
    steps: Continuity.Steps,
    reals: RealTheory,
    magnitude: Magnitude,
    continuity: Continuity
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val x = Term.variable("x", Reals)
    val m = Term.variable("m", Reals)
    val e = Term.variable("e", Reals)
    val y = Term.variable("y", Reals)
    val d0 = Term.variable("d0", Reals)
    val increment = "(f:real -> real) (x + (y - x)) - f x - m:real * (y - x)"
    for {
      hypothesis <- proposition("derivative (f:real -> real) x m")
      statement <- LogicError.lift(Kernel.assume(hypothesis)).flatMap(openDerivative(steps, f, x, m, _))
      one <- real("1:real")
      onePositive <- lemma("(0:real) < 1")
      near0 <- rules.spec(one, statement).flatMap(rules.mp(_, onePositive))
      radius0 <- assume("0 < d0:real /\\ (!h:real. 0 < abs h /\\ abs h < d0 ==> abs ((f:real -> real) (x + h) - f x - m:real * h) < 1 * abs h)")
      d0Positive <- rules.conjElim1(radius0)
      inside0 <- rules.conjElim2(radius0)

      positive <- proposition("0 < e:real")
      ePositive <- LogicError.lift(Kernel.assume(positive))
      slopeNonNegative <- at(magnitude.fact(Magnitude.AbsNonNegative), "m:real")
      share <- Continuity.portion(steps, reals, "abs (m:real)", slopeNonNegative, 2, ePositive)
      radius = s"min (d0:real) (${share.term})"
      dPositive <- Continuity.minimumOf(steps, magnitude, "d0:real", share.term, d0Positive, share.positive)

      member <- proposition(s"abs (y:real - x) < $radius")
      assumedMember <- LogicError.lift(Kernel.assume(member))
      belowD0 <- at(magnitude.fact(Magnitude.MinBelowLeft), "d0:real", share.term)
        .flatMap(below => at(lemma(Through), "abs (y:real - x)", radius, "d0:real").flatMap(mp(_, Right(assumedMember), Right(below))))
      belowT <- at(magnitude.fact(Magnitude.MinBelowRight), "d0:real", share.term)
        .flatMap(below => at(lemma(Through), "abs (y:real - x)", radius, share.term).flatMap(mp(_, Right(assumedMember), Right(below))))
      nonNegative <- at(magnitude.fact(Magnitude.AbsNonNegative), "y:real - x")
      leCases <- magnitude.order.fact(Order.LeCases)
      zero <- real("0:real")
      distance <- real("abs (y:real - x)")
      split <- rules.specAll(leCases, List(zero, distance)).flatMap(rules.mp(_, nonNegative))

      atZero <- for {
        same <- assume("0 = abs (y:real - x)").flatMap(Conv.sym)
        difference <- at(magnitude.fact(Magnitude.AbsZero), "y:real - x").flatMap(mp(_, Right(same)))
        points <- at(lemma("!y:real x:real. y - x = 0 ==> y = x"), "y:real", "x:real").flatMap(mp(_, Right(difference)))
        values <- Conv.apTerm(f, points)
        itself <- at(magnitude.fact(Magnitude.OfNonNegative), "(f:real -> real) y - f x")
          .flatMap(mp(_, at(lemma("!P:real Q:real. P = Q ==> 0 <= P - Q"), "(f:real -> real) y", "(f:real -> real) x").flatMap(mp(_, Right(values)))))
        result <- at(lemma("!A:real P:real Q:real e:real. A = P - Q ==> P = Q ==> 0 < e ==> A < e"),
          "abs ((f:real -> real) y - f x)", "(f:real -> real) y", "(f:real -> real) x", "e:real")
          .flatMap(mp(_, Right(itself), Right(values), Right(ePositive)))
      } yield result

      awayFromZero <- for {
        apart <- assume("0 < abs (y:real - x)")
        admissible <- rules.conjIntro(apart, belowD0)
        step <- real("y:real - x")
        bound <- rules.spec(step, inside0).flatMap(rules.mp(_, admissible))
        back <- at(lemma("!x:real y:real. x + (y - x) = y"), "x:real", "y:real").flatMap(Conv.apTerm(f, _))
        regrouped <- at(lemma("!P:real F:real Q:real B:real. F = P ==> P - Q = (F - Q - B) + B"),
          "(f:real -> real) y", "(f:real -> real) (x + (y - x))", "(f:real -> real) x", "m:real * (y - x)")
          .flatMap(mp(_, Right(back)))
        absFn <- Parser.term(theory, notation, "abs", Functions)
        sameAbs <- Conv.apTerm(absFn, regrouped)
        triangle <- at(magnitude.fact(Magnitude.Triangle), increment, "m:real * (y - x)")
        product <- at(magnitude.fact(Magnitude.Multiplicative), "m:real", "y:real - x")
        firstStep <- at(lemma("!A:real B:real M:real H:real. B = M * H ==> A < 1 * H ==> A + B < (M + 1) * H"),
          s"abs ($increment)", "abs (m:real * (y - x))", "abs (m:real)", "abs (y:real - x)")
          .flatMap(mp(_, Right(product), Right(bound)))
        secondStep <- at(lemma("!M:real H:real T:real e:real. 0 <= M ==> 0 < H ==> H < T ==> 2 * (M + 1) * T = e ==> (M + 1) * H < e"),
          "abs (m:real)", "abs (y:real - x)", share.term, "e:real")
          .flatMap(mp(_, Right(slopeNonNegative), Right(apart), Right(belowT), Right(share.equation)))
        result <- at(lemma("!S:real R:real X:real Y:real e:real. S = R ==> R <= X ==> X < Y ==> Y < e ==> S < e"),
          "abs ((f:real -> real) y - f x)", s"abs ($increment + m:real * (y - x))",
          s"abs ($increment) + abs (m:real * (y - x))", "(abs (m:real) + 1) * abs (y:real - x)", "e:real")
          .flatMap(mp(_, Right(sameAbs), Right(triangle), Right(firstStep), Right(secondStep)))
      } yield result

      close <- rules.disjElim(split, awayFromZero, atZero)
      everyY <- rules.disch(member, close).flatMap(rules.gen(y, _))
      both <- rules.conjIntro(dPositive, everyY)
      radiusTerm <- real(radius)
      witnessed <- existential("?d:real. 0 < d /\\ (!y:real. abs (y - x:real) < d ==> abs ((f:real -> real) y - f x) < e:real)")
        .flatMap(rules.existsIntro(_, radiusTerm, both))
      eliminated <- rules.existsElim(near0, d0, witnessed)
      epsilonDelta <- rules.disch(positive, eliminated).flatMap(rules.gen(e, _))
      folded <- unfoldContinuity(continuity, f, x).flatMap(Conv.sym).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, epsilonDelta)))
      closed <- rules.disch(hypothesis, folded).flatMap(rules.genAll(_, List(f, x, m)))
    } yield closed
  }

  /**
   * [[ProductRule]]: the error is `Ef * g (x + h) + m * h * (g (x + h) - g x) + f x * Eg`, an
   * identity, and each of the three is held under a quarter of `e * abs h`. `g (x + h)` is kept
   * under `abs (g x) + 1` and near `g x` by [[Continuous]] at `g`, which is why that fact is here.
   * The one substitution inside a product is congruence rather than `Linarith`, which would have to
   * multiply an equation by a factor of unknown sign.
   */
  private def productRule(
    steps: Continuity.Steps,
    reals: RealTheory,
    magnitude: Magnitude,
    continuity: Continuity,
    differentiableContinuous: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val x = Term.variable("x", Reals)
    val m = Term.variable("m", Reals)
    val n = Term.variable("n", Reals)
    val e = Term.variable("e", Reals)
    val h = Term.variable("h", Reals)
    val d1 = Term.variable("d1", Reals)
    val d2 = Term.variable("d2", Reals)
    val d3 = Term.variable("d3", Reals)
    val f1 = "(f:real -> real) (x + h)"
    val f0 = "(f:real -> real) x"
    val g1 = "(g:real -> real) (x + h)"
    val g0 = "(g:real -> real) x"
    val ef = s"$f1 - $f0 - m:real * h"
    val eg = s"$g1 - $g0 - n:real * h"
    val dg = s"$g1 - $g0"
    val first = s"($ef) * $g1"
    val second = s"m:real * h * ($dg)"
    val third = s"$f0 * ($eg)"
    val whole = s"$f1 * $g1 - $f0 * $g0 - (m:real * $g0 + $f0 * n:real) * h"
    for {
      fHyp <- proposition("derivative (f:real -> real) x m")
      gHyp <- proposition("derivative (g:real -> real) x n")
      assumedF <- LogicError.lift(Kernel.assume(fHyp))
      assumedG <- LogicError.lift(Kernel.assume(gHyp))
      fAt <- openDerivative(steps, f, x, m, assumedF)
      gAt <- openDerivative(steps, g, x, n, assumedG)
      gContinuous <- rules.specAll(differentiableContinuous, List(g, x, n)).flatMap(rules.mp(_, assumedG))
      gNear <- unfoldContinuity(continuity, g, x).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, gContinuous)))

      positive <- proposition("0 < e:real")
      ePositive <- LogicError.lift(Kernel.assume(positive))
      gValueNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), g0)
      gBoundNonNeg <- at(lemma("!G:real. 0 <= G ==> 0 <= G + 1"), s"abs ($g0)").flatMap(mp(_, Right(gValueNonNeg)))
      slopeNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), "m:real")
      fValueNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), f0)
      forF <- Continuity.portion(steps, reals, s"abs ($g0) + 1", gBoundNonNeg, 4, ePositive)
      forSlope <- Continuity.portion(steps, reals, "abs (m:real)", slopeNonNeg, 4, ePositive)
      forG <- Continuity.portion(steps, reals, s"abs ($f0)", fValueNonNeg, 4, ePositive)
      tolerance = s"min 1 (${forSlope.term})"
      onePositive <- lemma("(0:real) < 1")
      tolerancePositive <- Continuity.minimumOf(steps, magnitude, "1", forSlope.term, onePositive, forSlope.positive)

      nearF <- real(forF.term).flatMap(rules.spec(_, fAt)).flatMap(rules.mp(_, forF.positive))
      nearG <- real(forG.term).flatMap(rules.spec(_, gAt)).flatMap(rules.mp(_, forG.positive))
      nearC <- real(tolerance).flatMap(rules.spec(_, gNear)).flatMap(rules.mp(_, tolerancePositive))
      radiusF <- assume(s"0 < d1:real /\\ (!h:real. 0 < abs h /\\ abs h < d1 ==> abs ((f:real -> real) (x + h) - f x - m:real * h) < ${forF.term} * abs h)")
      radiusG <- assume(s"0 < d2:real /\\ (!h:real. 0 < abs h /\\ abs h < d2 ==> abs ((g:real -> real) (x + h) - g x - n:real * h) < ${forG.term} * abs h)")
      radiusC <- assume(s"0 < d3:real /\\ (!y:real. abs (y - x:real) < d3 ==> abs ((g:real -> real) y - g x) < $tolerance)")
      d1Positive <- rules.conjElim1(radiusF)
      d2Positive <- rules.conjElim1(radiusG)
      d3Positive <- rules.conjElim1(radiusC)
      insideF <- rules.conjElim2(radiusF)
      insideG <- rules.conjElim2(radiusG)
      insideC <- rules.conjElim2(radiusC)
      inner = "min (d2:real) (d3:real)"
      radius = s"min (d1:real) ($inner)"
      innerPositive <- Continuity.minimumOf(steps, magnitude, "d2:real", "d3:real", d2Positive, d3Positive)
      radiusPositive <- Continuity.minimumOf(steps, magnitude, "d1:real", inner, d1Positive, innerPositive)

      near <- proposition(s"0 < abs (h:real) /\\ abs h < $radius")
      assumedNear <- LogicError.lift(Kernel.assume(near))
      hPositive <- rules.conjElim1(assumedNear)
      hSmall <- rules.conjElim2(assumedNear)
      hBelow1 <- at(magnitude.fact(Magnitude.MinBelowLeft), "d1:real", inner)
        .flatMap(b => at(lemma(Through), "abs (h:real)", radius, "d1:real").flatMap(mp(_, Right(hSmall), Right(b))))
      hBelowInner <- at(magnitude.fact(Magnitude.MinBelowRight), "d1:real", inner)
        .flatMap(b => at(lemma(Through), "abs (h:real)", radius, inner).flatMap(mp(_, Right(hSmall), Right(b))))
      hBelow2 <- at(magnitude.fact(Magnitude.MinBelowLeft), "d2:real", "d3:real")
        .flatMap(b => at(lemma(Through), "abs (h:real)", inner, "d2:real").flatMap(mp(_, Right(hBelowInner), Right(b))))
      hBelow3 <- at(magnitude.fact(Magnitude.MinBelowRight), "d2:real", "d3:real")
        .flatMap(b => at(lemma(Through), "abs (h:real)", inner, "d3:real").flatMap(mp(_, Right(hBelowInner), Right(b))))

      fClose <- rules.conjIntro(hPositive, hBelow1).flatMap(ok => rules.spec(h, insideF).flatMap(rules.mp(_, ok)))
      gClose <- rules.conjIntro(hPositive, hBelow2).flatMap(ok => rules.spec(h, insideG).flatMap(rules.mp(_, ok)))
      stepped <- real("x:real + h")
      shift <- at(lemma("!x:real h:real. (x + h) - x = h"), "x:real", "h:real")
      absFn <- Parser.term(theory, notation, "abs", Functions)
      shiftAbs <- Conv.apTerm(absFn, shift)
      stepInside <- at(lemma("!A:real B:real d:real. A = B ==> B < d ==> A < d"), "abs ((x:real + h) - x)", "abs (h:real)", "d3:real")
        .flatMap(mp(_, Right(shiftAbs), Right(hBelow3)))
      cClose <- rules.spec(stepped, insideC).flatMap(rules.mp(_, stepInside))
      dgBelowOne <- at(magnitude.fact(Magnitude.MinBelowLeft), "1", forSlope.term)
        .flatMap(b => at(lemma(Through), s"abs ($dg)", tolerance, "1").flatMap(mp(_, Right(cClose), Right(b))))
      dgBelowT <- at(magnitude.fact(Magnitude.MinBelowRight), "1", forSlope.term)
        .flatMap(b => at(lemma(Through), s"abs ($dg)", tolerance, forSlope.term).flatMap(mp(_, Right(cClose), Right(b))))

      /* ------------------------------------------ g (x + h) stays under abs (g x) + 1 */
      gSplit <- at(lemma("!G1:real G0:real. G1 = G0 + (G1 - G0)"), g1, g0).flatMap(Conv.apTerm(absFn, _))
      gTriangle <- at(magnitude.fact(Magnitude.Triangle), g0, dg)
      gBounded <- at(lemma("!B:real S:real G:real D:real. B = S ==> S <= G + D ==> D < 1 ==> B <= G + 1"),
        s"abs ($g1)", s"abs ($g0 + ($dg))", s"abs ($g0)", s"abs ($dg)")
        .flatMap(mp(_, Right(gSplit), Right(gTriangle), Right(dgBelowOne)))

      /* ------------------------------------------------------------- the three parts */
      regrouped <- at(lemma("!F1:real F0:real G1:real G0:real m:real n:real h:real. " +
        "F1 * G1 - F0 * G0 - (m * G0 + F0 * n) * h = (F1 - F0 - m * h) * G1 + m * h * (G1 - G0) + F0 * (G1 - G0 - n * h)"),
        f1, f0, g1, g0, "m:real", "n:real", "h:real")
      sameAbs <- Conv.apTerm(absFn, regrouped)
      outer <- at(magnitude.fact(Magnitude.Triangle), s"$first + $second", third)
      innerTriangle <- at(magnitude.fact(Magnitude.Triangle), first, second)
      split3 <- at(lemma("!S:real R:real U:real X:real Y:real Z:real. S = R ==> R <= U + Z ==> U <= X + Y ==> S <= X + Y + Z"),
        s"abs ($whole)", s"abs ($first + $second + $third)", s"abs ($first + $second)",
        s"abs ($first)", s"abs ($second)", s"abs ($third)")
        .flatMap(mp(_, Right(sameAbs), Right(outer), Right(innerTriangle)))

      part1 <- for {
        mul <- at(magnitude.fact(Magnitude.Multiplicative), ef, g1)
        aNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), ef)
        bNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), g1)
        bounded <- at(lemma("!A:real B:real T:real H:real G:real e:real. 0 <= A ==> 0 <= B ==> A < T * H ==> B <= G + 1 ==> " +
          "0 < H ==> 4 * ((G + 1) + 1) * T = e ==> A * B <= e / 4 * H"),
          s"abs ($ef)", s"abs ($g1)", forF.term, "abs (h:real)", s"abs ($g0)", "e:real")
          .flatMap(mp(_, Right(aNonNeg), Right(bNonNeg), Right(fClose), Right(gBounded), Right(hPositive), Right(forF.equation)))
        result <- at(lemma("!R:real X:real Y:real. R = X ==> X <= Y ==> R <= Y"), s"abs ($first)", s"abs ($ef) * abs ($g1)", "e:real / 4 * abs (h:real)")
          .flatMap(mp(_, Right(mul), Right(bounded)))
      } yield result

      part2 <- for {
        outerMul <- at(magnitude.fact(Magnitude.Multiplicative), "m:real * h", dg)
        innerMul <- at(magnitude.fact(Magnitude.Multiplicative), "m:real", "h:real")
        dNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), dg)
        scaled <- at(lemma("!P:real A:real B:real. 0 <= P ==> A < B ==> P * A <= P * B"), "abs (m:real)", s"abs ($dg)", forSlope.term)
          .flatMap(mp(_, Right(slopeNonNeg), Right(dgBelowT)))
        slopeShare <- at(lemma("!M:real T:real e:real. 0 <= M ==> 0 < T ==> 4 * (M + 1) * T = e ==> M * T < e / 4"),
          "abs (m:real)", forSlope.term, "e:real").flatMap(mp(_, Right(slopeNonNeg), Right(forSlope.positive), Right(forSlope.equation)))
        under <- at(lemma("!X:real Y:real Z:real. X <= Y ==> Y < Z ==> X < Z"), s"abs (m:real) * abs ($dg)", s"abs (m:real) * ${forSlope.term}", "e:real / 4")
          .flatMap(mp(_, Right(scaled), Right(slopeShare)))
        // `abs (m * h)` is replaced inside the product by congruence and not by `Linarith`, which
        // would have to multiply an equation by a factor of unknown sign to do it.
        multiply <- Term.destEq(outerMul.conclusion).map(_._2).collect { case App(App(product, _), _) => product }
          .toRight(NotOfForm("a product", outerMul.conclusion))
        dgMagnitude <- real(s"abs ($dg)")
        inner <- Conv.apTerm(multiply, innerMul).flatMap(Conv.apThm(_, dgMagnitude))
        joined <- Conv.trans(outerMul, inner)
        regroup <- at(lemma("!Y:real M:real H:real D:real. Y = M * H * D ==> Y = H * (M * D)"),
          s"abs ($second)", "abs (m:real)", "abs (h:real)", s"abs ($dg)")
          .flatMap(mp(_, Right(joined)))
        result <- at(lemma("!Y:real X:real H:real e:real. Y = H * X ==> 0 < H ==> X < e / 4 ==> Y <= e / 4 * H"),
          s"abs ($second)", s"abs (m:real) * abs ($dg)", "abs (h:real)", "e:real")
          .flatMap(mp(_, Right(regroup), Right(hPositive), Right(under)))
      } yield result

      part3 <- for {
        mul <- at(magnitude.fact(Magnitude.Multiplicative), f0, eg)
        scaled <- at(lemma("!P:real A:real B:real. 0 <= P ==> A < B ==> P * A <= P * B"), s"abs ($f0)", s"abs ($eg)", s"${forG.term} * abs (h:real)")
          .flatMap(mp(_, Right(fValueNonNeg), Right(gClose)))
        bounded <- at(lemma("!X:real F:real T:real H:real e:real. X <= F * (T * H) ==> 0 <= F ==> 0 < T ==> 0 < H ==> " +
          "4 * (F + 1) * T = e ==> X <= e / 4 * H"),
          s"abs ($f0) * abs ($eg)", s"abs ($f0)", forG.term, "abs (h:real)", "e:real")
          .flatMap(mp(_, Right(scaled), Right(fValueNonNeg), Right(forG.positive), Right(hPositive), Right(forG.equation)))
        result <- at(lemma("!R:real X:real Y:real. R = X ==> X <= Y ==> R <= Y"), s"abs ($third)", s"abs ($f0) * abs ($eg)", "e:real / 4 * abs (h:real)")
          .flatMap(mp(_, Right(mul), Right(bounded)))
      } yield result

      within <- at(lemma("!S:real X:real Y:real Z:real e:real H:real. S <= X + Y + Z ==> X <= e / 4 * H ==> Y <= e / 4 * H ==> " +
        "Z <= e / 4 * H ==> 0 < e ==> 0 < H ==> S < e * H"),
        s"abs ($whole)", s"abs ($first)", s"abs ($second)", s"abs ($third)", "e:real", "abs (h:real)")
        .flatMap(mp(_, Right(split3), Right(part1), Right(part2), Right(part3), Right(ePositive), Right(hPositive)))

      everyH <- rules.disch(near, within).flatMap(rules.gen(h, _))
      both <- rules.conjIntro(radiusPositive, everyH)
      radiusTerm <- real(radius)
      witnessed <- existential(s"?d:real. 0 < d /\\ (!h:real. 0 < abs h /\\ abs h < d ==> abs ($whole) < e:real * abs h)")
        .flatMap(rules.existsIntro(_, radiusTerm, both))
      withoutC <- rules.existsElim(nearC, d3, witnessed)
      withoutG <- rules.existsElim(nearG, d2, withoutC)
      withoutF <- rules.existsElim(nearF, d1, withoutG)
      statement <- rules.disch(positive, withoutF).flatMap(rules.gen(e, _))
      function <- Parser.term(theory, notation, "\\y:real. (f:real -> real) y * (g:real -> real) y", Functions)
      slope <- real(s"m:real * $g0 + $f0 * n:real")
      result <- foldDerivative(steps, function, x, slope, statement)
      closed <- rules.disch(gHyp, result).flatMap(rules.disch(fHyp, _)).flatMap(rules.genAll(_, List(f, g, x, m, n)))
    } yield closed
  }
}
