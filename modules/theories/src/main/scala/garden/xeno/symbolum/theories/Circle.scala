package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * `pi`, the periods of `sin` and `cos`, and the inverse of `cos` on `[0, pi]`.
 *
 * `docs/adr/0057` is the decision. `pi` is twice the zero of `cos` in `[0, 2]`, chosen:
 *
 * {{{
 *   pi = 2 * select (\z. 0 <= z /\ z <= 2 /\ cos z = 0)
 * }}}
 *
 * and `acos y` is the point of `[0, pi]` where `cos` is `y`, chosen the same way. Two constants and
 * no axiom.
 *
 * == Six polynomial bounds, each spending the one before ==
 *
 * The argument needs `cos` to change sign at a written point, and the only tool for that is a bound.
 * [[Circle.SinBelowLine]] to [[Circle.CosAboveSextic]] are the Taylor polynomials of `sin` and `cos`
 * from zero on, alternately above and below, and each is `DERIVATIVE_NONNEG_MONOTONE` at the
 * difference between the function and its polynomial: the derivative of that difference is the
 * previous bound's difference, which is non-negative by the previous bound. The first is `1 - cos t`,
 * and `cos t <= 1` is the square identity. The derivatives are `Slope`'s, which the kernel checks.
 *
 * At the numbers: [[Circle.CosBelowQuartic]] at `8/5` gives `cos (8/5) < 0` and
 * [[Circle.CosAboveSextic]] at `3/2` gives `0 < cos (3/2)`. So the intermediate value theorem puts a
 * zero between them, [[Circle.SinAboveCubic]] makes `sin` positive on `(0, 2)` so `cos` falls
 * strictly there, and the zero is the only one in `[0, 2]`. That is what makes the choice pin
 * something, and [[Circle.PiBounds]] is where it lands: `3 < pi < 16/5`.
 *
 * == The route that was not taken ==
 *
 * The series itself, `cos 2 = 1 - 2 + 2/3 - ...` with a bound on the tail. `EXP_TAIL_GEOMETRIC` is
 * that bound for the exponential, and carrying it to the cosine's even terms wants sums split at an
 * index and compared term by term, which is machinery this repository writes once per series. The
 * bounds above are the same Taylor polynomials reached through the derivative, and they are
 * results a reader will want for their own sake.
 *
 * == What follows from pi ==
 *
 * The quarter turn from `COS_ADD` and `SIN_ADD` at `pi / 2`, the half turn as two quarters, the
 * whole turn as two halves, and the values at `pi`. `sin` is positive on `(0, pi)`, below `pi / 2`
 * by the cubic bound and above it through the quarter turn, so `cos` falls strictly on `[0, pi]`
 * and is one-to-one there. [[Circle.AcosSpec]] is the intermediate value theorem on `[0, pi]` read
 * through the choice; it is what a polar form wants, which is the next development.
 */
final class Circle private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Circle {

  /** `pi`, twice the zero of `cos` in `[0, 2]`. */
  val PiName: String = "pi"

  /** `acos y`, the point of `[0, pi]` where `cos` is `y`. */
  val AcosName: String = "acos"

  /** The definitions, in the order they are made: `acos` names `pi`. */
  val Bodies: Vector[(String, String)] = Vector(
    PiName -> "2 * select (\\z:real. 0 <= z /\\ z <= 2 /\\ cos z = 0)",
    AcosName -> "\\y:real. select (\\t:real. 0 <= t /\\ t <= pi /\\ cos t = y)"
  )

  val SinBelowLine: String = "SIN_LE_LINE"
  val CosAboveQuadratic: String = "COS_GE_QUADRATIC"
  val SinAboveCubic: String = "SIN_GE_CUBIC"
  val CosBelowQuartic: String = "COS_LE_QUARTIC"
  val SinBelowQuintic: String = "SIN_LE_QUINTIC"
  val CosAboveSextic: String = "COS_GE_SEXTIC"

  /** `3 < pi /\ pi < 16 / 5`: where the choice lands, from `cos (3/2) > 0` and `cos (8/5) < 0`. */
  val PiBounds: String = "PI_BOUNDS"
  val CosPiHalf: String = "COS_PI_HALF"
  val SinPiHalf: String = "SIN_PI_HALF"
  val CosShift: String = "COS_SHIFT"
  val SinShift: String = "SIN_SHIFT"
  val CosAddPi: String = "COS_ADD_PI"
  val SinAddPi: String = "SIN_ADD_PI"
  val CosPeriodic: String = "COS_PERIODIC"
  val SinPeriodic: String = "SIN_PERIODIC"
  val CosPi: String = "COS_PI"
  val SinPi: String = "SIN_PI"
  val SinPositive: String = "SIN_POSITIVE"
  val CosDecreasing: String = "COS_DECREASING"
  val CosInjective: String = "COS_INJECTIVE"

  /** `-1 <= y <= 1` gives `acos y` in `[0, pi]` with `cos (acos y) = y`. */
  val AcosSpec: String = "ACOS_SPEC"

  /** Everything published here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    SinBelowLine -> "!x:real. 0 <= x ==> sin x <= x",
    CosAboveQuadratic -> "!x:real. 0 <= x ==> 1 - x * x / 2 <= cos x",
    SinAboveCubic -> "!x:real. 0 <= x ==> x - x * x * x / 6 <= sin x",
    CosBelowQuartic -> "!x:real. 0 <= x ==> cos x <= 1 - x * x / 2 + x * x * x * x / 24",
    SinBelowQuintic -> "!x:real. 0 <= x ==> sin x <= x - x * x * x / 6 + x * x * x * x * x / 120",
    CosAboveSextic ->
      "!x:real. 0 <= x ==> 1 - x * x / 2 + x * x * x * x / 24 - x * x * x * x * x * x / 720 <= cos x",
    PiBounds -> "3 < pi /\\ pi < 16 / 5",
    CosPiHalf -> "cos (pi / 2) = 0",
    SinPiHalf -> "sin (pi / 2) = 1",
    CosShift -> "!x:real. cos (x + pi / 2) = 0 - sin x",
    SinShift -> "!x:real. sin (x + pi / 2) = cos x",
    CosAddPi -> "!x:real. cos (x + pi) = 0 - cos x",
    SinAddPi -> "!x:real. sin (x + pi) = 0 - sin x",
    CosPeriodic -> "!x:real. cos (x + 2 * pi) = cos x",
    SinPeriodic -> "!x:real. sin (x + 2 * pi) = sin x",
    CosPi -> "cos pi = 0 - 1",
    SinPi -> "sin pi = 0",
    SinPositive -> "!x:real. 0 < x /\\ x < pi ==> 0 < sin x",
    CosDecreasing -> "!x:real. !y:real. 0 <= x /\\ x < y /\\ y <= pi ==> cos y < cos x",
    CosInjective -> "!x:real. !y:real. 0 <= x /\\ x <= pi /\\ 0 <= y /\\ y <= pi /\\ cos x = cos y ==> x = y",
    AcosSpec -> "!x:real. 0 - 1 <= x /\\ x <= 1 ==> 0 <= acos x /\\ acos x <= pi /\\ cos (acos x) = x"
  )

  private val Reals: Type = TyApp(Real.TypeName, Nil)

  /** The development over the chain's links it reads, extending `base`. */
  def construct(
    classical: Classical,
    reals: RealTheory,
    magnitude: Magnitude,
    ring: Ring,
    order: Order,
    transcendental: Transcendental,
    continuity: Continuity,
    derivative: Derivative,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Circle] = {
    val introduced = Bodies.foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm])]](Right((base, Map.empty))) {
      case (accumulated, (name, text)) =>
        for {
          state <- accumulated
          (theory, defined) = state
          body <- Parser.term(theory, notation, text)
          made <- LogicError.lift(Kernel.defineConstant(theory, name, body))
          (extended, definition) = made
        } yield (extended, defined + (name -> definition))
    }
    for {
      state <- introduced
      (theory, definitions) = state
      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(magnitude.order)
      lookup = (name: String) =>
        derivative.fact(name)
          .orElse(transcendental.fact(name))
          .orElse(continuity.fact(name))
          .orElse(order.fact(name))
          .orElse(reals.axiom(name))
      slope = Slope(logic, classical, ring, theory, notation, lookup)
      proofs = Proofs(slope, classical, linarith, lookup)
      facts <- proofs.all(definitions(PiName), definitions(AcosName))
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { case (acc, (name, text)) =>
        for {
          _ <- acc
          expected <- Parser.proposition(theory, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Circle(theory, notation, logic, definitions, facts)
  }

  /** The development over the standard chain. */
  lazy val standard: Circle = Chain.standard.circle

  /** The derivations, over one theory holding both constants. */
  private final case class Proofs(
    slope: Slope,
    classical: Classical,
    linarith: Linarith,
    fact: String => Either[LogicError, Kernel.Thm]
  ) {
    private val logic = slope.logic
    private val rules = logic.rules
    private val theory = slope.theory
    private val z = Term.variable("z", Reals)
    private val x = Term.variable("x", Reals)

    private def real(text: String): Either[LogicError, Term] = Parser.term(theory, slope.notation, text, Reals)
    private def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, slope.notation, text)
    private def function(text: String): Either[LogicError, Term] =
      Parser.term(theory, slope.notation, text, Type.fun(Reals, Reals))
    private def assume(t: Term): Either[LogicError, Kernel.Thm] = LogicError.lift(Kernel.assume(t))
    private def premise(implication: Kernel.Thm): Either[LogicError, Term] =
      logic.destImp(implication.conclusion).map(_._1).toRight(NotOfForm("an implication", implication.conclusion))

    /**
     * `goal` from `facts`, put to `Linarith` as one implication and detached. Every arithmetic step
     * here is this: the facts are theorems about atoms like `sin z` and `pi`, and the goal is linear
     * in them once the facts are there.
     */
    def conclude(facts: Seq[Kernel.Thm], goal: Term): Either[LogicError, Kernel.Thm] =
      for {
        implication <- facts.reverse.foldLeft[Either[LogicError, Term]](Right(goal)) { (acc, f) =>
          acc.flatMap(g => logic.mkImp(f.conclusion, g))
        }
        proved <- linarith.prove(implication)
        result <- facts.foldLeft[Either[LogicError, Kernel.Thm]](Right(proved))((acc, f) => acc.flatMap(rules.mp(_, f)))
      } yield result

    private def concludeText(facts: Seq[Kernel.Thm], goal: String): Either[LogicError, Kernel.Thm] =
      proposition(goal).flatMap(conclude(facts, _))

    /** `|- f a = f b` from `|- a = b`, for `f` one of `sin` and `cos`. */
    private def carried(name: String, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      LogicError.lift(theory.constant(name, Type.fun(Reals, Reals))).flatMap(Conv.apTerm(_, equation))

    private def ringEquation(text: String): Either[LogicError, Kernel.Thm] = proposition(text).flatMap(slope.ring.prove)

    /** `?v. derivative g z v /\ 0 <relation> v`, witnessed by `d`. */
    private def slopeWitness(g: Term, d: Term, atZ: Kernel.Thm, sign: Kernel.Thm, strict: Boolean): Either[LogicError, Kernel.Thm] =
      for {
        derivativeConst <- atZ.conclusion match {
          case App(App(App(c, _), _), _) => Right(c)
          case other => Left(NotOfForm("a derivative", other))
        }
        v = Term.variable("v", Reals)
        atV <- LogicError.lift(Term.appAll(derivativeConst, List(g, z, v)))
        zero <- real("0")
        relation <- LogicError.lift(
          theory.constant(if (strict) Real.Order else Real.NonStrictOrder, Type.fun(Reals, Type.fun(Reals, Type.Bool))))
        bound <- LogicError.lift(Term.appAll(relation, List(zero, v)))
        body <- logic.mkConj(atV, bound)
        predicate <- LogicError.lift(Term.absAll(List(v), body))
        both <- rules.conjIntro(atZ, sign)
        result <- rules.existsIntro(predicate, d, both)
      } yield result

    /**
     * `|- !x. 0 <= x ==> g 0 <= g x`, beta-reduced, for the `g` written as `function`, whose
     * derivative at `z` is `slopeAt z`, non-negative wherever `0 < z` by `nonNegative`.
     */
    private def rises(
      functionText: String,
      slopeAt: String,
      nonNegative: Kernel.Thm => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        g <- function(functionText)
        dz <- real(slopeAt)
        atZ <- slope.at(g, z, dz)
        continuousAtZ <- fact("DERIVATIVE_CONTINUOUS").flatMap(rules.specAll(_, List(g, z, dz))).flatMap(rules.mp(_, atZ))
        closedT <- proposition("(0:real) <= z /\\ z <= x")
        continuity <- rules.disch(closedT, continuousAtZ).flatMap(rules.gen(z, _))
        openT <- proposition("(0:real) < z /\\ z < x")
        inside <- assume(openT)
        positive <- rules.conjElim1(inside)
        sign <- nonNegative(positive)
        witnessed <- slopeWitness(g, dz, atZ, sign, strict = false)
        slopes <- rules.disch(openT, witnessed).flatMap(rules.gen(z, _))
        zero <- real("0")
        monotone <- fact("DERIVATIVE_NONNEG_MONOTONE")
          .flatMap(rules.specAll(_, List(g, zero, x)))
          .flatMap(rules.mp(_, continuity))
          .flatMap(rules.mp(_, slopes))
          .flatMap(rules.specAll(_, List(zero, x)))
        hypothesisT <- proposition("(0:real) <= x")
        hypothesis <- assume(hypothesisT)
        ends <- concludeText(Seq(hypothesis), "(0:real) <= 0 /\\ (0:real) <= x /\\ (x:real) <= x")
        compared <- rules.mp(monotone, ends).flatMap(Limit.normalised)
        result <- rules.disch(hypothesisT, compared).flatMap(rules.gen(x, _))
      } yield result

    /** A monotone step closed: `g 0 <= g x` and the value at zero give `statement` for `0 <= x`. */
    private def bound(rise: Kernel.Thm, atZero: Kernel.Thm, statement: String): Either[LogicError, Kernel.Thm] =
      for {
        hypothesisT <- proposition("(0:real) <= x")
        hypothesis <- assume(hypothesisT)
        compared <- rules.spec(x, rise).flatMap(rules.mp(_, hypothesis))
        result <- concludeText(Seq(atZero, compared), statement)
        out <- rules.disch(hypothesisT, result).flatMap(rules.gen(x, _))
      } yield out

    /** The previous bound at `z`, given `0 < z`, as the sign `goal` of the next derivative. */
    private def spent(previous: Kernel.Thm, positive: Kernel.Thm, goal: String): Either[LogicError, Kernel.Thm] =
      for {
        nonNegative <- concludeText(Seq(positive), "(0:real) <= z")
        atZ <- rules.spec(z, previous).flatMap(rules.mp(_, nonNegative))
        result <- concludeText(Seq(atZ), goal)
      } yield result

    /**
     * `|- 0 <= 1 - cos z`, from the square identity with two squares handed to `Linarith`: its pool
     * is generated from the hypotheses, and `(cos z - 1)^2 >= 0` is a square of a sum, which it
     * does not complete by itself.
     */
    private def cosAtMostOne: Either[LogicError, Kernel.Thm] =
      for {
        square <- fact("SIN_COS_SQUARED").flatMap(rules.spec(z, _))
        sinZ <- real("sin z")
        s2 <- fact("SQUARE_NONNEG").flatMap(rules.spec(sinZ, _))
        shifted <- real("cos z - 1")
        c2 <- fact("SQUARE_NONNEG").flatMap(rules.spec(shifted, _))
        result <- concludeText(Seq(square, s2, c2), "(0:real) <= 1 - cos z")
      } yield result

    def bounds: Either[LogicError, Vector[(String, Kernel.Thm)]] =
      for {
        sin0 <- fact("SIN_ZERO")
        cos0 <- fact("COS_ZERO")
        l1 <- rises("\\t:real. t - sin t", "1 - cos z", _ => cosAtMostOne)
          .flatMap(bound(_, sin0, "sin x <= x"))
        l2 <- rises("\\t:real. cos t - 1 + t * t / 2", "z - sin z", spent(l1, _, "(0:real) <= z - sin z"))
          .flatMap(bound(_, cos0, "1 - x * x / 2 <= cos x"))
        l3 <- rises("\\t:real. sin t - t + t * t * t / 6", "cos z - 1 + z * z / 2",
          spent(l2, _, "(0:real) <= cos z - 1 + z * z / 2"))
          .flatMap(bound(_, sin0, "x - x * x * x / 6 <= sin x"))
        l4 <- rises("\\t:real. 1 - t * t / 2 + t * t * t * t / 24 - cos t", "sin z - z + z * z * z / 6",
          spent(l3, _, "(0:real) <= sin z - z + z * z * z / 6"))
          .flatMap(bound(_, cos0, "cos x <= 1 - x * x / 2 + x * x * x * x / 24"))
        l5 <- rises("\\t:real. t - t * t * t / 6 + t * t * t * t * t / 120 - sin t",
          "1 - z * z / 2 + z * z * z * z / 24 - cos z",
          spent(l4, _, "(0:real) <= 1 - z * z / 2 + z * z * z * z / 24 - cos z"))
          .flatMap(bound(_, sin0, "sin x <= x - x * x * x / 6 + x * x * x * x * x / 120"))
        l6 <- rises("\\t:real. cos t - 1 + t * t / 2 - t * t * t * t / 24 + t * t * t * t * t * t / 720",
          "z - z * z * z / 6 + z * z * z * z * z / 120 - sin z",
          spent(l5, _, "(0:real) <= z - z * z * z / 6 + z * z * z * z * z / 120 - sin z"))
          .flatMap(bound(_, cos0, "1 - x * x / 2 + x * x * x * x / 24 - x * x * x * x * x * x / 720 <= cos x"))
      } yield Vector(
        SinBelowLine -> l1, CosAboveQuadratic -> l2, SinAboveCubic -> l3,
        CosBelowQuartic -> l4, SinBelowQuintic -> l5, CosAboveSextic -> l6
      )

    /** `|- goal` at the number `at`, from `!x. 0 <= x ==> bound x`. */
    private def atNumber(general: Kernel.Thm, at: String, goal: String): Either[LogicError, Kernel.Thm] =
      for {
        point <- real(at)
        nonNegative <- proposition(s"(0:real) <= $at").flatMap(linarith.prove)
        instance <- rules.spec(point, general).flatMap(rules.mp(_, nonNegative))
        result <- concludeText(Seq(instance), goal)
      } yield result

    /**
     * `|- !a b. 0 <= a /\ a < b /\ b <= end ==> g a < g b` for `g = \t. 0 - cos t`, whose slope
     * `sin z` is positive on the open interval by `positive`.
     */
    private def risingOn(end: String, g: Term, continuousAt: Kernel.Thm, rising: Kernel.Thm, sinZ: Term, positive: Kernel.Thm) =
      for {
        zero <- real("0")
        e <- real(end)
        monotone <- fact("DERIVATIVE_POS_LT_MONOTONE").flatMap(rules.specAll(_, List(g, zero, e)))
        closedT <- proposition(s"(0:real) <= z /\\ z <= $end")
        continuity <- rules.disch(closedT, continuousAt).flatMap(rules.gen(z, _))
        openT <- proposition(s"(0:real) < z /\\ z < $end")
        inside <- assume(openT)
        sign <- rules.spec(z, positive).flatMap(rules.mp(_, inside))
        witnessed <- slopeWitness(g, sinZ, rising, sign, strict = true)
        slopes <- rules.disch(openT, witnessed).flatMap(rules.gen(z, _))
        result <- rules.mp(monotone, continuity).flatMap(rules.mp(_, slopes))
      } yield result

    /** `0 < z * (2 - z) * (2 + z)` under `0 < z /\ z < 2`: the cubic `Linarith` does not reach. */
    private def cubicPositive(inside: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        a <- concludeText(Seq(inside), "(0:real) < z")
        b <- concludeText(Seq(inside), "(0:real) < 2 - z")
        c <- concludeText(Seq(inside), "(0:real) < 2 + z")
        twoMinus <- real("2 - z")
        twoPlus <- real("2 + z")
        product <- real("z * (2 - z)")
        ab <- rules.conjIntro(a, b).flatMap(p => fact("LT_MUL").flatMap(rules.specAll(_, List(z, twoMinus))).flatMap(rules.mp(_, p)))
        abc <- rules.conjIntro(ab, c).flatMap(p => fact("LT_MUL").flatMap(rules.specAll(_, List(product, twoPlus))).flatMap(rules.mp(_, p)))
      } yield abc

    /**
     * `e < s` or `s < e` for the chosen zero `s`, by `LT_TOTAL`: the goal is one of the three cases,
     * the strict one on the other side is refuted by the monotonicity of `cos` and the equal one by
     * the sign of `cos` at the endpoint.
     */
    private def strictly(decreasing: Kernel.Thm, property: Kernel.Thm, s: Term, end: String, endSign: Kernel.Thm, sBelow: Boolean) =
      for {
        e <- real(end)
        inRange <- rules.conjElim1(property)
        rest <- rules.conjElim2(property)
        upTo <- rules.conjElim1(rest)
        cosS <- rules.conjElim2(rest)
        lt <- LogicError.lift(theory.constant(Real.Order, Type.fun(Reals, Type.fun(Reals, Type.Bool))))
        cosine <- LogicError.lift(theory.constant(Transcendental.Cosine, Type.fun(Reals, Reals)))
        goal <- LogicError.lift(Term.appAll(lt, if (sBelow) List(s, e) else List(e, s)))
        total <- fact("LT_TOTAL").flatMap(rules.specAll(_, List(s, e)))
        split <- logic.destDisj(total.conclusion).toRight(NotOfForm("a disjunction", total.conclusion))
        (sLess, others) = split
        split2 <- logic.destDisj(others).toRight(NotOfForm("a disjunction", others))
        (same, eLess) = split2
        monotone = (wrong: Term, left: Term, right: Term) =>
          for {
            h <- assume(wrong)
            instance <- rules.specAll(decreasing, List(left, right))
            wanted <- premise(instance)
            held <- conclude(Seq(h, inRange, upTo), wanted)
            compared <- rules.mp(instance, held).flatMap(Limit.normalised)
            out <- conclude(Seq(compared, cosS, endSign), goal)
          } yield out
        equal <- for {
          h <- assume(same)
          moved <- Conv.apTerm(cosine, h)
          out <- conclude(Seq(moved, cosS, endSign), goal)
        } yield out
        first <- if (sBelow) assume(sLess) else monotone(sLess, s, e)
        third <- if (sBelow) monotone(eLess, e, s) else assume(eLess)
        inner <- assume(others).flatMap(rules.disjElim(_, equal, third))
        result <- rules.disjElim(total, first, inner)
      } yield result

    /** `?y. P y` from `?u. Q u` where `Q u` gives `P u` by arithmetic. */
    private def rephrased(existential: Kernel.Thm, predicate: Term): Either[LogicError, Kernel.Thm] = {
      val u = Term.variable("u", Reals)
      for {
        from <- logic.destExistsPredicate(existential.conclusion).toRight(NotOfForm("an existential", existential.conclusion))
        instance <- LogicError.lift(Term.app(from, u)).flatMap(Conv.betaRoot).flatMap(Datatype.rightOf)
        assumed <- assume(instance)
        wanted <- LogicError.lift(Term.app(predicate, u)).flatMap(Conv.betaRoot).flatMap(Datatype.rightOf)
        parts <- conclude(Seq(assumed), wanted)
        introduced <- rules.existsIntro(predicate, u, parts)
        result <- rules.existsElim(existential, u, introduced)
      } yield result
    }

    /** `P (select P)` from `?y. P y`, beta-reduced. */
    private def chosen(existential: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        witness <- classical.axiom(Classical.Choice).flatMap(Classical.witnessFrom(logic, _, existential))
        reduced <- Conv.betaRoot(witness.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, witness)))
      } yield reduced

    def all(piDefinition: Kernel.Thm, acosDefinition: Kernel.Thm): Either[LogicError, Map[String, Kernel.Thm]] =
      for {
        polynomial <- bounds
        named = polynomial.toMap
        sin0 <- fact("SIN_ZERO")
        cos0 <- fact("COS_ZERO")

        below <- atNumber(named(CosBelowQuartic), "8 / 5", "cos (8 / 5) < 0")
        above <- atNumber(named(CosAboveSextic), "3 / 2", "0 < cos (3 / 2)")
        g <- function("\\t:real. 0 - cos t")
        sinZ <- real("sin z")
        rising <- slope.at(g, z, sinZ)
        continuousAt <- fact("DERIVATIVE_CONTINUOUS").flatMap(rules.specAll(_, List(g, z, sinZ))).flatMap(rules.mp(_, rising))

        // the zero, by the intermediate value theorem between 3/2 and 8/5
        zero <- real("0")
        crossing <- for {
          a <- real("3 / 2")
          b <- real("8 / 5")
          theorem <- fact("INTERMEDIATE_VALUE").flatMap(rules.specAll(_, List(g, a, b, zero))).flatMap(Limit.normalised)
          ordered <- proposition("(3:real) / 2 <= 8 / 5").flatMap(linarith.prove)
          closedT <- proposition("(3:real) / 2 <= z /\\ z <= 8 / 5")
          continuity <- rules.disch(closedT, continuousAt).flatMap(rules.gen(z, _))
          left <- concludeText(Seq(above), "(0:real) - cos (3 / 2) <= 0")
          right <- concludeText(Seq(below), "(0:real) <= 0 - cos (8 / 5)")
          result <- rules.mp(theorem, ordered).flatMap(rules.mp(_, continuity)).flatMap(rules.mp(_, left)).flatMap(rules.mp(_, right))
        } yield result

        // the chosen zero is the one the definition names
        s <- Datatype.rightOf(piDefinition).flatMap {
          case App(App(_, _), selected) => Right(selected)
          case other => Left(NotOfForm("2 * select P", other))
        }
        predicate <- s match {
          case App(_, p) => Right(p)
          case other => Left(NotOfForm("select P", other))
        }
        property <- rephrased(crossing, predicate).flatMap(chosen)

        // sin is positive on (0, 2), so cos falls strictly on [0, 2]
        openTwo <- proposition("(0:real) < z /\\ z < 2")
        sinPositiveTwo <- for {
          inside <- assume(openTwo)
          lower <- concludeText(Seq(inside), "(0:real) <= z").flatMap(n => rules.spec(z, named(SinAboveCubic)).flatMap(rules.mp(_, n)))
          cubic <- cubicPositive(inside)
          positive <- concludeText(Seq(inside, cubic, lower), "(0:real) < sin z")
          out <- rules.disch(openTwo, positive).flatMap(rules.gen(z, _))
        } yield out
        decreasingTwo <- risingOn("2", g, continuousAt, rising, sinZ, sinPositiveTwo)

        lowerBound <- strictly(decreasingTwo, property, s, "3 / 2", above, sBelow = false)
        upperBound <- strictly(decreasingTwo, property, s, "8 / 5", below, sBelow = true)
        piBounds <- concludeText(Seq(piDefinition, lowerBound, upperBound), "3 < pi /\\ pi < 16 / 5")
        cosHalf <- for {
          half <- real("pi / 2")
          equation <- LogicError.lift(Term.eq(half, s)).flatMap(conclude(Seq(piDefinition), _))
          moved <- carried(Transcendental.Cosine, equation)
          atS <- rules.conjElim2(property).flatMap(rules.conjElim2)
          result <- Conv.trans(moved, atS)
        } yield result

        half <- real("pi / 2")
        sinHalf <- for {
          square <- fact("SIN_COS_SQUARED").flatMap(rules.spec(half, _))
          inRange <- concludeText(Seq(piBounds), "(0:real) < pi / 2 /\\ pi / 2 < 2")
          positive <- rules.spec(half, sinPositiveTwo).flatMap(rules.mp(_, inRange))
          shifted <- real("sin (pi / 2) - 1")
          sq <- fact("SQUARE_NONNEG").flatMap(rules.spec(shifted, _))
          rewritten <- Limit.rewriteInProposition(cosHalf, square)
          result <- concludeText(Seq(rewritten, positive, sq), "sin (pi / 2) = 1")
        } yield result

        quarter = (name: String, statement: String) =>
          for {
            added <- fact(name).flatMap(rules.specAll(_, List(x, half)))
            a <- Limit.rewriteInProposition(cosHalf, added)
            b <- Limit.rewriteInProposition(sinHalf, a)
            result <- concludeText(Seq(b), statement)
            out <- rules.gen(x, result)
          } yield out
        cosShift <- quarter("COS_ADD", "cos (x + pi / 2) = 0 - sin x")
        sinShift <- quarter("SIN_ADD", "sin (x + pi / 2) = cos x")

        split <- ringEquation("x + pi = (x + pi / 2) + pi / 2")
        quarterAhead <- real("x + pi / 2")
        cosAddPi <- for {
          c1 <- carried(Transcendental.Cosine, split)
          c2 <- rules.spec(quarterAhead, cosShift)
          s1 <- rules.spec(x, sinShift)
          result <- concludeText(Seq(c1, c2, s1), "cos (x + pi) = 0 - cos x")
          out <- rules.gen(x, result)
        } yield out
        sinAddPi <- for {
          c1 <- carried(Transcendental.Sine, split)
          c2 <- rules.spec(quarterAhead, sinShift)
          s1 <- rules.spec(x, cosShift)
          result <- concludeText(Seq(c1, c2, s1), "sin (x + pi) = 0 - sin x")
          out <- rules.gen(x, result)
        } yield out

        twice <- ringEquation("x + 2 * pi = (x + pi) + pi")
        halfAhead <- real("x + pi")
        cosPeriodic <- for {
          c1 <- carried(Transcendental.Cosine, twice)
          c2 <- rules.spec(halfAhead, cosAddPi)
          c3 <- rules.spec(x, cosAddPi)
          result <- concludeText(Seq(c1, c2, c3), "cos (x + 2 * pi) = cos x")
          out <- rules.gen(x, result)
        } yield out
        sinPeriodic <- for {
          c1 <- carried(Transcendental.Sine, twice)
          c2 <- rules.spec(halfAhead, sinAddPi)
          c3 <- rules.spec(x, sinAddPi)
          result <- concludeText(Seq(c1, c2, c3), "sin (x + 2 * pi) = sin x")
          out <- rules.gen(x, result)
        } yield out

        fromZero <- ringEquation("(0:real) + pi = pi")
        cosPi <- for {
          c1 <- rules.spec(zero, cosAddPi)
          m <- carried(Transcendental.Cosine, fromZero)
          result <- concludeText(Seq(c1, m, cos0), "cos pi = 0 - 1")
        } yield result
        sinPi <- for {
          c1 <- rules.spec(zero, sinAddPi)
          m <- carried(Transcendental.Sine, fromZero)
          result <- concludeText(Seq(c1, m, sin0), "sin pi = 0")
        } yield result

        // sin is positive on (0, pi): below 2 by the cubic bound, from 2 on through the quarter turn
        openPi <- proposition("(0:real) < z /\\ z < pi")
        sinPositive <- for {
          inside <- assume(openPi)
          lowT <- proposition("(z:real) < 2")
          low <- for {
            h <- assume(lowT)
            both <- concludeText(Seq(inside, h), "(0:real) < z /\\ z < 2")
            out <- rules.spec(z, sinPositiveTwo).flatMap(rules.mp(_, both))
          } yield out
          notLow <- logic.mkNot(lowT)
          high <- for {
            negated <- assume(notLow)
            two <- real("2")
            h <- fact("LE_OF_NOT_LT").flatMap(rules.specAll(_, List(z, two))).flatMap(rules.mp(_, negated))
            y <- real("z - pi / 2")
            back <- ringEquation("(z - pi / 2) + pi / 2 = z")
            m <- carried(Transcendental.Sine, back)
            atY <- rules.spec(y, sinShift)
            decreasing <- rules.specAll(decreasingTwo, List(y, half))
            wanted <- premise(decreasing)
            held <- conclude(Seq(inside, h, piBounds), wanted)
            compared <- rules.mp(decreasing, held).flatMap(Limit.normalised)
            out <- concludeText(Seq(m, atY, compared, cosHalf), "(0:real) < sin z")
          } yield out
          cased <- classical.cases(lowT, low, high)
          out <- rules.disch(openPi, cased).flatMap(rules.gen(z, _))
        } yield out

        decreasingPi <- risingOn("pi", g, continuousAt, rising, sinZ, sinPositive)
        a = Term.variable("x", Reals)
        b = Term.variable("y", Reals)
        cosDecreasing <- for {
          hT <- proposition("(0:real) <= x /\\ x < y /\\ y <= pi")
          h <- assume(hT)
          instance <- rules.specAll(decreasingPi, List(a, b)).flatMap(rules.mp(_, h)).flatMap(Limit.normalised)
          result <- concludeText(Seq(instance), "cos y < cos x")
          out <- rules.disch(hT, result).flatMap(rules.genAll(_, List(a, b)))
        } yield out

        cosInjective <- for {
          hT <- proposition("(0:real) <= x /\\ x <= pi /\\ 0 <= y /\\ y <= pi /\\ cos x = cos y")
          h <- assume(hT)
          total <- fact("LT_TOTAL").flatMap(rules.specAll(_, List(a, b)))
          goal <- proposition("(x:real) = y")
          split <- logic.destDisj(total.conclusion).toRight(NotOfForm("a disjunction", total.conclusion))
          (less, others) = split
          split2 <- logic.destDisj(others).toRight(NotOfForm("a disjunction", others))
          (same, greater) = split2
          refuted = (hypothesis: Term, lower: Term, upper: Term) =>
            for {
              assumed <- assume(hypothesis)
              instance <- rules.specAll(cosDecreasing, List(lower, upper))
              wanted <- premise(instance)
              held <- conclude(Seq(h, assumed), wanted)
              compared <- rules.mp(instance, held)
              out <- conclude(Seq(compared, h), goal)
            } yield out
          first <- refuted(less, a, b)
          middle <- assume(same)
          third <- refuted(greater, b, a)
          inner <- assume(others).flatMap(rules.disjElim(_, middle, third))
          result <- rules.disjElim(total, first, inner)
          out <- rules.disch(hT, result).flatMap(rules.genAll(_, List(a, b)))
        } yield out

        // acos, by the intermediate value theorem on [0, pi] and the definition's choice
        acosSpec <- for {
          rangeT <- proposition("(0:real) - 1 <= x /\\ x <= 1")
          range <- assume(rangeT)
          piTerm <- real("pi")
          target <- real("0 - x")
          theorem <- fact("INTERMEDIATE_VALUE").flatMap(rules.specAll(_, List(g, zero, piTerm, target))).flatMap(Limit.normalised)
          ordered <- concludeText(Seq(piBounds), "(0:real) <= pi")
          closedT <- proposition("(0:real) <= z /\\ z <= pi")
          continuity <- rules.disch(closedT, continuousAt).flatMap(rules.gen(z, _))
          left <- concludeText(Seq(cos0, range), "(0:real) - cos 0 <= 0 - x")
          right <- concludeText(Seq(cosPi, range), "(0:real) - x <= 0 - cos pi")
          crossed <- rules.mp(theorem, ordered).flatMap(rules.mp(_, continuity)).flatMap(rules.mp(_, left)).flatMap(rules.mp(_, right))
          unfolded <- Conv.unfold(acosDefinition, List(x))
          selected <- Datatype.rightOf(unfolded)
          wanted <- selected match {
            case App(_, p) => Right(p)
            case other => Left(NotOfForm("select P", other))
          }
          property <- rephrased(crossed, wanted).flatMap(chosen)
          named <- Conv.sym(unfolded).flatMap(Limit.rewriteInProposition(_, property))
          out <- rules.disch(rangeT, named).flatMap(rules.gen(x, _))
        } yield out
      } yield polynomial.toMap ++ Map(
        PiBounds -> piBounds, CosPiHalf -> cosHalf, SinPiHalf -> sinHalf,
        CosShift -> cosShift, SinShift -> sinShift, CosAddPi -> cosAddPi, SinAddPi -> sinAddPi,
        CosPeriodic -> cosPeriodic, SinPeriodic -> sinPeriodic, CosPi -> cosPi, SinPi -> sinPi,
        SinPositive -> sinPositive, CosDecreasing -> cosDecreasing, CosInjective -> cosInjective,
        AcosSpec -> acosSpec
      )
  }
}
