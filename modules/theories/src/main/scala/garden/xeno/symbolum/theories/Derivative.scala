package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The derivative of a real function at a point, the interior extremum lemma, and Rolle's theorem.
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
 * **The mean value theorem is not here.** It is Rolle at `(b - a) * f x - (f b - f a) * x`, and
 * three things stand in front of that which this repository does not have: that such a function is
 * continuous (an algebra of continuous functions, which the extreme value theorem also went
 * without), that a derivative is linear, and that it is unique, to carry the zero back to `f`.
 * Each is a statement this development can now write, which it could not before.
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
   * negation. A sum and a product are not here, because nothing has asked for them yet; the mean
   * value theorem is what will.
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
        "?c:real. a < c /\\ c < b /\\ derivative f c 0")
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

      facts = Map[String, Kernel.Thm](
        Constant -> constant,
        Identity -> identity,
        Negation -> negation,
        InteriorMaximum -> interiorMax,
        InteriorMinimum -> interiorMin,
        Rolle -> rolle
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
}
