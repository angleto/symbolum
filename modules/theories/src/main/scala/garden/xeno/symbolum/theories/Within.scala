package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

import Continuity.Steps

/**
 * Continuity relative to `[a, b]`, and the interval theorems stated with it, which is how a
 * textbook states them.
 *
 * Every interval theorem of `Continuity` and `Derivative` asks `!x. a <= x /\ x <= b ==>
 * continuous f x`, and `continuous` is two-sided: at `a` it looks at points left of `a` as well.
 * So the hypothesis is stronger than the one a reader brings, which is continuity **relative** to
 * the interval, and nothing said so until card 6257d0da found it on 2026-09-25. `continuous_within
 * f a b x` is that relative continuity, the epsilon-delta statement with the nearby points
 * restricted to `[a, b]`.
 *
 * == One lemma carries the rest ==
 *
 * The textbook forms are not proved again. A function continuous relative to `[a, b]` is extended
 * by its value at the nearer end: `E y = COND (y < a) (f a) (COND (b < y) (f b) (f y))`.
 * [[Continuity.Extension]] says `E` is continuous everywhere, two-sided, and
 * [[Continuity.ExtensionAgrees]] that it is `f` on `[a, b]`. Each textbook form is the existing
 * theorem at `E`, with every value inside the interval read back as `f`'s. The one derivation that
 * is new is the extension's continuity, and it is three cases: left of `a` the extension is
 * constant near the point, right of `b` likewise, and inside the interval a point outside it is
 * nearer the end it takes its value from than the point is, so the relative radius serves.
 *
 * `COND` rather than `max a (min y b)` inside `f`, because the two cases outside are where the
 * proof reads the extension and `COND_TRUE` reads it in one step, where a clamp would want the
 * cases of `max` and `min` taken apart at every use.
 */
private[theories] object Within {

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Functions: Type = Type.fun(Reals, Reals)

  private[theories] val F = "(f:real -> real)"

  /** The extension, as the lambda every statement names. */
  private[theories] val Extended = s"(\\y:real. COND (y < a:real) ($F a) (COND (b:real < y) ($F b) ($F y)))"

  /** The extension at a point, reduced, which is how it appears once a statement is specialised. */
  private[theories] def valueAt(t: String): String = s"COND ($t < a:real) ($F a) (COND (b:real < $t) ($F b) ($F $t))"

  private[theories] val Relative = s"!x:real. a:real <= x /\\ x <= b:real ==> continuous_within $F a b x"

  /** The facts, by the names `Continuity` publishes them under. */
  def prove(
    steps: Steps,
    within: Kernel.Thm,
    reals: RealTheory,
    magnitude: Magnitude,
    classical: Classical,
    held: Map[String, Kernel.Thm]
  ): Either[LogicError, Map[String, Kernel.Thm]] = {
    def fact(name: String) = held.get(name).toRight(MissingDefinition(name))
    for {
      ofContinuous <- relativeOfTwoSided(steps, within)
      agrees <- agreement(steps, reals, classical)
      extension <- extensionIsContinuous(steps, within, reals, magnitude, classical)
      intermediate <- fact(Continuity.IntermediateValue).flatMap(intermediateValue(steps, extension, agrees, _))
      bounded <- fact(Continuity.Bounded).flatMap(boundedness(steps, extension, agrees, _))
      highest <- fact(Continuity.AttainsMaximum).flatMap(extremum(steps, extension, agrees, _, Continuity.AttainsMaximumWithin))
      lowest <- fact(Continuity.AttainsMinimum).flatMap(extremum(steps, extension, agrees, _, Continuity.AttainsMinimumWithin))
      uniform <- fact(Continuity.Uniform).flatMap(uniformity(steps, extension, agrees, _))
    } yield Map(
      Continuity.WithinOfContinuous -> ofContinuous,
      Continuity.ExtensionAgrees -> agrees,
      Continuity.Extension -> extension,
      Continuity.IntermediateValueWithin -> intermediate,
      Continuity.BoundedWithin -> bounded,
      Continuity.AttainsMaximumWithin -> highest,
      Continuity.AttainsMinimumWithin -> lowest,
      Continuity.UniformWithin -> uniform
    )
  }

  /* ------------------------------------------------------------------ the small parts */

  private[theories] def term(steps: Steps, text: String): Either[LogicError, Term] =
    Parser.term(steps.theory, steps.notation, text)

  private[theories] def variable(steps: Steps, text: String): Either[LogicError, FVar] =
    term(steps, text).flatMap {
      case found: FVar => Right(found)
      case other => Left(NotOfForm("a variable", other))
    }

  /** `|- continuous_within f a b x = <the relative epsilon-delta statement>`, reduced. */
  private def openedWithin(within: Kernel.Thm, arguments: List[Term]): Either[LogicError, Kernel.Thm] =
    for {
      equation <- Conv.unfold(within, arguments)
      right <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
      normal <- Conv.betaNormalise(right)
      joined <- Conv.trans(equation, normal)
    } yield joined

  private[theories] def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv.betaNormalise(theorem.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

  /** `theorem` with each equation's left side replaced by its right, wherever it occurs. */
  private[theories] def forward(steps: Steps, equations: Vector[Kernel.Thm], theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Rewrite.Rule.all(steps.logic, equations).flatMap(Rewrite.inTheorem(_, theorem))

  /**
   * `|- target` from `|- other`, where `other` is `target` with each equation applied. The target is
   * rewritten rather than `other`, because an equation read backwards puts `f t` back where it came
   * from and the right side of an agreement holds its own left side's `f t`.
   */
  private[theories] def backward(steps: Steps, equations: Vector[Kernel.Thm], target: Term, other: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      rules <- Rewrite.Rule.all(steps.logic, equations)
      equation <- Rewrite.rewrite(rules, target)
      right <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
      _ <- if (right == other.conclusion) Right(()) else Left(NotOfForm("the statement read inside the interval", right))
      back <- Conv.sym(equation)
      result <- LogicError.lift(Kernel.eqMp(back, other))
    } yield result

  /** The antecedents of an implication chain, in order, and what is left. */
  private[theories] def antecedents(steps: Steps, statement: Term): (Vector[Term], Term) =
    steps.logic.destImp(statement) match {
      case Some((first, rest)) =>
        val (more, last) = antecedents(steps, rest)
        (first +: more, last)
      case None => (Vector.empty, statement)
    }

  private[theories] def closeOver(steps: Steps, theorem: Kernel.Thm, hypotheses: List[String], variables: List[String]): Either[LogicError, Kernel.Thm] =
    for {
      discharged <- hypotheses.foldLeft[Either[LogicError, Kernel.Thm]](Right(theorem)) { (acc, text) =>
        for { current <- acc; hypothesis <- steps.proposition(text); next <- steps.rules.disch(hypothesis, current) } yield next
      }
      bound <- variables.foldLeft[Either[LogicError, List[FVar]]](Right(Nil)) { (acc, text) =>
        for { found <- acc; next <- variable(steps, text) } yield found :+ next
      }
      result <- steps.rules.genAll(discharged, bound)
    } yield result

  /**
   * `|- ~(x < a)` from `|- a <= x`: with `x < a` it would put `x` below itself. Written out because
   * `Linarith` reads no negated hypothesis and proves no negated goal, which the first run of this
   * file found.
   */
  private[theories] def notBelow(steps: Steps, reals: RealTheory, x: String, a: String, lower: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      below <- proposition(s"$x < $a")
      assumedBelow <- LogicError.lift(Kernel.assume(below))
      self <- steps.at(lemma("!x:real a:real. x < a ==> a <= x ==> x < x"), x, a).flatMap(mp(_, Right(assumedBelow), Right(lower)))
      irreflexive <- steps.at(reals.axiom("LT_IRREFLEXIVE"), x)
      absurd <- rules.notElim(irreflexive, self)
      result <- rules.notIntro(below, absurd)
    } yield result
  }

  /** `|- a <= x` from `|- ~(x < a)`, which is `LE_OF_NOT_LT`. */
  private[theories] def aboveOf(steps: Steps, magnitude: Magnitude, x: String, a: String, notBelowIt: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    steps.at(magnitude.order.fact(Order.LeOfNotLt), x, a).flatMap(steps.mp(_, Right(notBelowIt)))

  /** `COND_TRUE` or `COND_FALSE` at the reals. */
  private[theories] def condition(classical: Classical, name: String): Either[LogicError, Kernel.Thm] =
    classical.fact(name).map(Kernel.instType(Map(Classical.TypeVariable -> Reals), _))

  /* ------------------------------------------------------------------ the definition's first use */

  /** [[Continuity.WithinOfContinuous]]: a two-sided radius serves the points of the interval too. */
  private def relativeOfTwoSided(steps: Steps, within: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      f <- variable(steps, "f:real -> real")
      x <- variable(steps, "x:real")
      a <- variable(steps, "a:real")
      b <- variable(steps, "b:real")
      e <- variable(steps, "e:real")
      d <- variable(steps, "d:real")
      y <- variable(steps, "y:real")
      supplied <- assume(s"continuous $F x:real")
      epsilons <- unfolded(f, x).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, supplied)))
      positive <- proposition("0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      radius <- rules.spec(e, epsilons).flatMap(rules.mp(_, assumedPositive))
      body <- assume(s"0 < d:real /\\ (!y:real. abs (y - x:real) < d ==> abs ($F y - $F x) < e:real)")
      dPositive <- rules.conjElim1(body)
      near <- rules.conjElim2(body)
      inside <- proposition("a:real <= y:real /\\ y <= b:real /\\ abs (y - x:real) < d:real")
      close <- LogicError.lift(Kernel.assume(inside)).flatMap(rules.conjElim2).flatMap(rules.conjElim2)
      value <- rules.spec(y, near).flatMap(rules.mp(_, close))
      everyPoint <- rules.disch(inside, value).flatMap(rules.gen(y, _))
      pair <- rules.conjIntro(dPositive, everyPoint)
      witnessed <- existential(
        s"?d:real. 0 < d /\\ (!y:real. a:real <= y /\\ y <= b:real /\\ abs (y - x:real) < d ==> abs ($F y - $F x) < e:real)"
      ).flatMap(rules.existsIntro(_, d, pair))
      found <- rules.existsElim(radius, d, witnessed)
      statement <- rules.disch(positive, found).flatMap(rules.gen(e, _))
      folded <- openedWithin(within, List(f, a, b, x)).flatMap(Conv.sym)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, statement)))
      result <- closeOver(steps, folded, List(s"continuous $F x:real"), List("f:real -> real", "a:real", "b:real", "x:real"))
    } yield result
  }

  /* ------------------------------------------------------------------ the extension */

  /** [[Continuity.ExtensionAgrees]]: inside the interval both conditions are false. */
  private def agreement(steps: Steps, reals: RealTheory, classical: Classical): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      condFalse <- condition(classical, Classical.CondFalse)
      notLeft <- assume("a:real <= x:real").flatMap(notBelow(steps, reals, "x:real", "a:real", _))
      notRight <- assume("x:real <= b:real").flatMap(notBelow(steps, reals, "b:real", "x:real", _))
      outer <- term(steps, "x:real < a:real").flatMap(p =>
        term(steps, s"$F a:real").flatMap(fa =>
          term(steps, s"COND (b:real < x:real) ($F b) ($F x)").flatMap(rest =>
            rules.specAll(condFalse, List(p, fa, rest)))))
        .flatMap(rules.mp(_, notLeft))
      inner <- term(steps, "b:real < x:real").flatMap(p =>
        term(steps, s"$F b:real").flatMap(fb =>
          term(steps, s"$F x:real").flatMap(fx => rules.specAll(condFalse, List(p, fb, fx)))))
        .flatMap(rules.mp(_, notRight))
      joined <- Conv.trans(outer, inner)
      both <- proposition("a:real <= x:real /\\ x <= b:real")
      assumedBoth <- LogicError.lift(Kernel.assume(both))
      lower <- rules.conjElim1(assumedBoth)
      upper <- rules.conjElim2(assumedBoth)
      fromBoth <- rules.proveHyp(lower, joined).flatMap(rules.proveHyp(upper, _))
      result <- closeOver(steps, fromBoth, List("a:real <= x:real /\\ x <= b:real"), List("f:real -> real", "a:real", "b:real", "x:real"))
    } yield result
  }

  /**
   * `|- abs (<left> - <right>) < e` when both sides are the value `c` the extension takes near the
   * point: the distance of a value from itself.
   */
  private def nothingMoves(steps: Steps, magnitude: Magnitude, c: String, positive: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      zero <- steps.at(magnitude.fact(Magnitude.OfNonNegative), s"$c - $c")
        .flatMap(mp(_, steps.at(lemma("!c:real. 0 <= c - c"), c)))
      result <- steps.at(lemma("!m:real c:real e:real. m = c - c ==> 0 < e ==> m < e"), s"abs ($c - $c)", c, "e:real")
        .flatMap(mp(_, Right(zero), Right(positive)))
    } yield result
  }

  /**
   * [[Continuity.Extension]]: the extension is continuous at every point, two-sided.
   *
   * The point is split three ways by two excluded middles. Left of `a` the radius is `a - x`, every
   * point inside it is left of `a` too, and both values are `f a`; right of `b` the same with `x -
   * b`. Inside the interval the radius is the one relative continuity gives, and a nearby point is
   * split the same three ways: inside, its value is `f`'s own; left of `a`, its value is `f a`, and
   * `a` is nearer `x` than the point is, so `a` is inside the radius and in the interval.
   */
  private def extensionIsContinuous(steps: Steps, within: Kernel.Thm, reals: RealTheory, magnitude: Magnitude, classical: Classical): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val ordered = "a:real <= b:real"
    for {
      condTrue <- condition(classical, Classical.CondTrue)
      condFalse <- condition(classical, Classical.CondFalse)
      f <- variable(steps, "f:real -> real")
      a <- variable(steps, "a:real")
      b <- variable(steps, "b:real")
      x <- variable(steps, "x:real")
      y <- variable(steps, "y:real")
      e <- variable(steps, "e:real")
      d <- variable(steps, "d:real")
      extended <- Parser.term(theory, notation, Extended, Functions)
      target <- unfolded(extended, x)
      goal <- Term.destEq(target.conclusion).map(_._2).toRight(NotOfForm("an equation", target.conclusion))
      positive <- proposition("0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))

      // The extension at `t`, read when the side `t` is on is known.
      leftValue = (t: String, left: Kernel.Thm) =>
        for {
          p <- term(steps, s"$t < a:real"); fa <- term(steps, s"$F a:real")
          rest <- term(steps, s"COND (b:real < $t) ($F b) ($F $t)")
          eq <- rules.specAll(condTrue, List(p, fa, rest)).flatMap(rules.mp(_, left))
        } yield eq
      rightValue = (t: String, notLeft: Kernel.Thm, right: Kernel.Thm) =>
        for {
          p <- term(steps, s"$t < a:real"); fa <- term(steps, s"$F a:real")
          rest <- term(steps, s"COND (b:real < $t) ($F b) ($F $t)")
          outer <- rules.specAll(condFalse, List(p, fa, rest)).flatMap(rules.mp(_, notLeft))
          q <- term(steps, s"b:real < $t"); fb <- term(steps, s"$F b:real"); ft <- term(steps, s"$F $t")
          inner <- rules.specAll(condTrue, List(q, fb, ft)).flatMap(rules.mp(_, right))
          eq <- Conv.trans(outer, inner)
        } yield eq
      insideValue = (t: String, notLeft: Kernel.Thm, notRight: Kernel.Thm) =>
        for {
          p <- term(steps, s"$t < a:real"); fa <- term(steps, s"$F a:real")
          rest <- term(steps, s"COND (b:real < $t) ($F b) ($F $t)")
          outer <- rules.specAll(condFalse, List(p, fa, rest)).flatMap(rules.mp(_, notLeft))
          q <- term(steps, s"b:real < $t"); fb <- term(steps, s"$F b:real"); ft <- term(steps, s"$F $t")
          inner <- rules.specAll(condFalse, List(q, fb, ft)).flatMap(rules.mp(_, notRight))
          eq <- Conv.trans(outer, inner)
        } yield eq

      // The distance statement at `y`, as the unfolded goal writes it.
      distance <- term(steps, s"abs (${valueAt("y:real")} - ${valueAt("x:real")}) < e:real")

      // A side of `x`, closed: the radius, a proof that it is positive, and the claim at every `y`.
      closed = (radius: String, radiusPositive: Kernel.Thm, near: Term, value: Kernel.Thm) =>
        for {
          everyPoint <- rules.disch(near, value).flatMap(rules.gen(y, _))
          pair <- rules.conjIntro(radiusPositive, everyPoint)
          witness <- term(steps, radius)
          witnessed <- existential(s"?d:real. 0 < d /\\ (!y:real. abs (y - x:real) < d ==> $distance)")
            .flatMap(rules.existsIntro(_, witness, pair))
        } yield witnessed

      // Left of `a`: at radius `a - x` every point is left of `a`, and both values are `f a`.
      xLeft <- proposition("x:real < a:real")
      leftCase <- for {
        assumedLeft <- LogicError.lift(Kernel.assume(xLeft))
        near <- proposition("abs (y:real - x:real) < a:real - x")
        assumedNear <- LogicError.lift(Kernel.assume(near))
        nearSides <- ExtremeValue.sides(steps, magnitude, "y:real - x:real", "a:real - x:real", assumedNear)
        yLeft <- steps.at(lemma("!y:real x:real a:real. y - x < a - x ==> y < a"), "y:real", "x:real", "a:real")
          .flatMap(mp(_, Right(nearSides._1)))
        atY <- leftValue("y:real", yLeft)
        atX <- leftValue("x:real", assumedLeft)
        same <- nothingMoves(steps, magnitude, s"$F a:real", assumedPositive)
        value <- backward(steps, Vector(atY, atX), distance, same)
        radiusPositive <- steps.at(lemma("!x:real a:real. x < a ==> 0 < a - x"), "x:real", "a:real")
          .flatMap(mp(_, Right(assumedLeft)))
        result <- closed("a:real - x:real", radiusPositive, near, value)
      } yield result

      // Right of `b`: at radius `x - b` every point is right of `b`, and both values are `f b`.
      xRight <- proposition("b:real < x:real")
      notXLeft <- proposition("~(x:real < a:real)")
      rightCase <- for {
        assumedRight <- LogicError.lift(Kernel.assume(xRight))
        assumedNotLeft <- LogicError.lift(Kernel.assume(notXLeft))
        near <- proposition("abs (y:real - x:real) < x:real - b:real")
        assumedNear <- LogicError.lift(Kernel.assume(near))
        nearSides <- ExtremeValue.sides(steps, magnitude, "y:real - x:real", "x:real - b:real", assumedNear)
        yRight <- steps.at(lemma("!y:real x:real b:real. -(y - x) < x - b ==> b < y"), "y:real", "x:real", "b:real")
          .flatMap(mp(_, Right(nearSides._2)))
        yNotLeft <- steps.at(lemma("!a:real b:real y:real. a <= b ==> b < y ==> a <= y"), "a:real", "b:real", "y:real")
          .flatMap(mp(_, assume(ordered), Right(yRight))).flatMap(notBelow(steps, reals, "y:real", "a:real", _))
        atY <- rightValue("y:real", yNotLeft, yRight)
        atX <- rightValue("x:real", assumedNotLeft, assumedRight)
        same <- nothingMoves(steps, magnitude, s"$F b:real", assumedPositive)
        value <- backward(steps, Vector(atY, atX), distance, same)
        radiusPositive <- steps.at(lemma("!x:real b:real. b < x ==> 0 < x - b"), "x:real", "b:real")
          .flatMap(mp(_, Right(assumedRight)))
        result <- closed("x:real - b:real", radiusPositive, near, value)
      } yield result

      // Inside: the relative radius, and a nearby point outside the interval is read at the end it
      // takes its value from, which is nearer `x` than the point is.
      notXRight <- proposition("~(b:real < x:real)")
      insideCase <- for {
        assumedNotLeft <- LogicError.lift(Kernel.assume(notXLeft))
        assumedNotRight <- LogicError.lift(Kernel.assume(notXRight))
        xAbove <- aboveOf(steps, magnitude, "x:real", "a:real", assumedNotLeft)
        xBelow <- aboveOf(steps, magnitude, "b:real", "x:real", assumedNotRight)
        member <- rules.conjIntro(xAbove, xBelow)
        relative <- assume(Relative).flatMap(rules.spec(x, _)).flatMap(rules.mp(_, member))
        epsilons <- openedWithin(within, List(f, a, b, x)).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, relative)))
        radii <- rules.spec(e, epsilons).flatMap(rules.mp(_, assumedPositive))
        bodyText = s"0 < d:real /\\ (!y:real. a:real <= y /\\ y <= b:real /\\ abs (y - x:real) < d ==> abs ($F y - $F x) < e:real)"
        body <- assume(bodyText)
        dPositive <- rules.conjElim1(body)
        serves <- rules.conjElim2(body)
        near <- proposition("abs (y:real - x:real) < d:real")
        assumedNear <- LogicError.lift(Kernel.assume(near))
        nearSides <- ExtremeValue.sides(steps, magnitude, "y:real - x:real", "d:real", assumedNear)
        atX <- insideValue("x:real", assumedNotLeft, assumedNotRight)

        yLeft <- proposition("y:real < a:real")
        pointLeft <- for {
          assumedLeft <- LogicError.lift(Kernel.assume(yLeft))
          atY <- leftValue("y:real", assumedLeft)
          up <- steps.at(lemma("!a:real x:real d:real. a <= x ==> 0 < d ==> a - x < d"), "a:real", "x:real", "d:real")
            .flatMap(mp(_, Right(xAbove), Right(dPositive)))
          down <- steps.at(lemma("!y:real x:real d:real a:real. -(y - x) < d ==> y < a ==> -(a - x) < d"),
            "y:real", "x:real", "d:real", "a:real").flatMap(mp(_, Right(nearSides._2), Right(assumedLeft)))
          close <- ExtremeValue.joined(steps, magnitude, "a:real - x:real", "d:real", up, down)
          endInside <- conj(steps.at(lemma("!a:real. a <= a"), "a:real"), conj(assume(ordered), Right(close)))
          value <- rules.spec(a, serves).flatMap(rules.mp(_, endInside))
          result <- backward(steps, Vector(atY, atX), distance, value)
        } yield result

        yRight <- proposition("b:real < y:real")
        yNotLeft <- proposition("~(y:real < a:real)")
        pointRight <- for {
          assumedRight <- LogicError.lift(Kernel.assume(yRight))
          assumedNotLeft <- LogicError.lift(Kernel.assume(yNotLeft))
          atY <- rightValue("y:real", assumedNotLeft, assumedRight)
          up <- steps.at(lemma("!y:real x:real d:real b:real. y - x < d ==> b < y ==> b - x < d"),
            "y:real", "x:real", "d:real", "b:real").flatMap(mp(_, Right(nearSides._1), Right(assumedRight)))
          down <- steps.at(lemma("!b:real x:real d:real. x <= b ==> 0 < d ==> -(b - x) < d"), "b:real", "x:real", "d:real")
            .flatMap(mp(_, Right(xBelow), Right(dPositive)))
          close <- ExtremeValue.joined(steps, magnitude, "b:real - x:real", "d:real", up, down)
          endInside <- conj(assume(ordered), conj(steps.at(lemma("!b:real. b <= b"), "b:real"), Right(close)))
          value <- rules.spec(b, serves).flatMap(rules.mp(_, endInside))
          result <- backward(steps, Vector(atY, atX), distance, value)
        } yield result

        yNotRight <- proposition("~(b:real < y:real)")
        pointInside <- for {
          assumedNotLeft <- LogicError.lift(Kernel.assume(yNotLeft))
          assumedNotRight <- LogicError.lift(Kernel.assume(yNotRight))
          atY <- insideValue("y:real", assumedNotLeft, assumedNotRight)
          yAbove <- aboveOf(steps, magnitude, "y:real", "a:real", assumedNotLeft)
          yBelow <- aboveOf(steps, magnitude, "b:real", "y:real", assumedNotRight)
          inside <- conj(Right(yAbove), conj(Right(yBelow), Right(assumedNear)))
          value <- rules.spec(y, serves).flatMap(rules.mp(_, inside))
          result <- backward(steps, Vector(atY, atX), distance, value)
        } yield result

        notLeftOfA <- classical.cases(yRight, pointRight, pointInside)
        atEveryPoint <- classical.cases(yLeft, pointLeft, notLeftOfA)
        witnessed <- closed("d:real", dPositive, near, atEveryPoint)
        result <- rules.existsElim(radii, d, witnessed)
      } yield result

      notLeft <- classical.cases(xRight, rightCase, insideCase)
      everywhere <- classical.cases(xLeft, leftCase, notLeft)
      statement <- rules.disch(positive, everywhere).flatMap(rules.gen(e, _))
      _ <- if (statement.conclusion == goal) Right(())
           else Left(NotOfForm("the extension's continuity as the definition reads it", statement.conclusion))
      continuous <- folded(extended, x, statement).flatMap(rules.gen(x, _))
      result <- closeOver(steps, continuous, List(Relative, ordered), List("f:real -> real", "a:real", "b:real"))
    } yield result
  }

  /* ------------------------------------------------------------------ the textbook forms */

  /**
   * What every textbook form starts from: the two-sided theorem at the extension, specialised and
   * with its continuity premise discharged from [[Continuity.Extension]]. Hypotheses: `a <= b` and
   * the relative continuity, each assumed under the text the statements use.
   */
  private[theories] def atTheExtension(steps: Steps, extension: Kernel.Thm, twoSided: Kernel.Thm, arguments: List[String]): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val ordered = "a:real <= b:real"
    for {
      f <- variable(steps, "f:real -> real")
      a <- variable(steps, "a:real")
      b <- variable(steps, "b:real")
      x <- variable(steps, "x:real")
      extended <- Parser.term(theory, notation, Extended, Functions)
      everywhere <- rules.specAll(extension, List(f, a, b)).flatMap(mp(_, assume(ordered), assume(Relative)))
      point <- proposition("a:real <= x:real /\\ x <= b:real")
      onInterval <- rules.spec(x, everywhere).flatMap(rules.disch(point, _)).flatMap(rules.gen(x, _))
      rest <- arguments.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, text) =>
        for { found <- acc; next <- term(steps, text) } yield found :+ next
      }
      instance <- rules.specAll(twoSided, extended :: a :: b :: rest).flatMap(reduced)
      detached <- mp(instance, assume(ordered), Right(onInterval))
    } yield detached
  }

  /** `|- E t = f t` under `a <= t` and `t <= b`, from [[Continuity.ExtensionAgrees]]. */
  private[theories] def agreesAt(steps: Steps, agrees: Kernel.Thm, t: String): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      f <- variable(steps, "f:real -> real")
      a <- variable(steps, "a:real")
      b <- variable(steps, "b:real")
      point <- term(steps, t)
      instance <- rules.specAll(agrees, List(f, a, b, point))
      member <- conj(assume(s"a:real <= $t"), assume(s"$t <= b:real"))
      result <- rules.mp(instance, member)
    } yield result
  }

  /** `|- E t = f t` with its two bounds discharged from a proof of `a <= t /\ t <= b`. */
  private[theories] def agreesWithin(steps: Steps, agrees: Kernel.Thm, t: String, membership: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      raw <- agreesAt(steps, agrees, t)
      lower <- steps.rules.conjElim1(membership)
      upper <- steps.rules.conjElim2(membership)
      result <- steps.rules.proveHyp(lower, raw).flatMap(steps.rules.proveHyp(upper, _))
    } yield result

  /** [[Continuity.IntermediateValueWithin]]: the crossing of `E`, whose ends are `f`'s. */
  private def intermediateValue(steps: Steps, extension: Kernel.Thm, agrees: Kernel.Thm, twoSided: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      x <- variable(steps, "x:real")
      detached <- atTheExtension(steps, extension, twoSided, List("y:real"))
      (premises, conclusion) = antecedents(steps, detached.conclusion)
      low <- premises.headOption.toRight(NotOfForm("a lower value", detached.conclusion))
      high <- premises.drop(1).headOption.toRight(NotOfForm("an upper value", detached.conclusion))
      aReflexive <- steps.at(lemma("!a:real. a <= a"), "a:real")
      bReflexive <- steps.at(lemma("!b:real. b <= b"), "b:real")
      atA <- agreesAt(steps, agrees, "a:real").flatMap(rules.proveHyp(aReflexive, _))
      atB <- agreesAt(steps, agrees, "b:real").flatMap(rules.proveHyp(bReflexive, _))
      lowGiven <- assume(s"$F a:real <= y:real")
      highGiven <- assume(s"y:real <= $F b:real")
      lowHeld <- backward(steps, Vector(atA), low, lowGiven)
      highHeld <- backward(steps, Vector(atB), high, highGiven)
      crossing <- mp(detached, Right(lowHeld), Right(highHeld))
      body <- assume(s"a:real <= x:real /\\ x <= b:real /\\ ${valueAt("x:real")} = y:real")
      lower <- rules.conjElim1(body)
      upper <- rules.conjElim2(body).flatMap(rules.conjElim1)
      value <- rules.conjElim2(body).flatMap(rules.conjElim2)
      membership <- rules.conjIntro(lower, upper)
      atX <- agreesWithin(steps, agrees, "x:real", membership)
      read <- forward(steps, Vector(atX), value)
      found <- conj(Right(lower), conj(Right(upper), Right(read)))
      witnessed <- existential(s"?x:real. a:real <= x /\\ x <= b:real /\\ $F x = y:real").flatMap(rules.existsIntro(_, x, found))
      opened <- rules.existsElim(crossing, x, witnessed)
      result <- closeOver(steps, opened,
        List(s"y:real <= $F b:real", s"$F a:real <= y:real", Relative, "a:real <= b:real"),
        List("f:real -> real", "a:real", "b:real", "y:real"))
    } yield result
  }

  /** [[Continuity.BoundedWithin]]: `E`'s bound, read at points of the interval. */
  private def boundedness(steps: Steps, extension: Kernel.Thm, agrees: Kernel.Thm, twoSided: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      x <- variable(steps, "x:real")
      m <- variable(steps, "M:real")
      bound <- atTheExtension(steps, extension, twoSided, Nil)
      body <- assume(s"!x:real. a:real <= x /\\ x <= b:real ==> ${valueAt("x")} <= M:real")
      point <- proposition("a:real <= x:real /\\ x <= b:real")
      assumedPoint <- LogicError.lift(Kernel.assume(point))
      value <- rules.spec(x, body).flatMap(rules.mp(_, assumedPoint))
      atX <- agreesWithin(steps, agrees, "x:real", assumedPoint)
      read <- forward(steps, Vector(atX), value)
      everyPoint <- rules.disch(point, read).flatMap(rules.gen(x, _))
      witnessed <- existential(s"?M:real. !x:real. a:real <= x /\\ x <= b:real ==> $F x <= M").flatMap(rules.existsIntro(_, m, everyPoint))
      opened <- rules.existsElim(bound, m, witnessed)
      result <- closeOver(steps, opened, List(Relative, "a:real <= b:real"), List("f:real -> real", "a:real", "b:real"))
    } yield result
  }

  /** [[Continuity.AttainsMaximumWithin]] and its minimum: `E`'s extremum, which is in the interval. */
  private def extremum(steps: Steps, extension: Kernel.Thm, agrees: Kernel.Thm, twoSided: Kernel.Thm, name: String): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val highest = name == Continuity.AttainsMaximumWithin
    def compared(t: String, m: String): String = if (highest) s"$t <= $m" else s"$m <= $t"
    for {
      x <- variable(steps, "x:real")
      m <- variable(steps, "m:real")
      attained <- atTheExtension(steps, extension, twoSided, Nil)
      body <- assume(s"a:real <= m:real /\\ m <= b:real /\\ (!x:real. a <= x /\\ x <= b ==> ${compared(valueAt("x"), valueAt("m"))})")
      mA <- rules.conjElim1(body)
      mB <- rules.conjElim2(body).flatMap(rules.conjElim1)
      every <- rules.conjElim2(body).flatMap(rules.conjElim2)
      point <- proposition("a:real <= x:real /\\ x <= b:real")
      assumedPoint <- LogicError.lift(Kernel.assume(point))
      value <- rules.spec(x, every).flatMap(rules.mp(_, assumedPoint))
      atX <- agreesWithin(steps, agrees, "x:real", assumedPoint)
      atM <- agreesAt(steps, agrees, "m:real").flatMap(rules.proveHyp(mA, _)).flatMap(rules.proveHyp(mB, _))
      read <- forward(steps, Vector(atX, atM), value)
      everyPoint <- rules.disch(point, read).flatMap(rules.gen(x, _))
      found <- conj(Right(mA), conj(Right(mB), Right(everyPoint)))
      witnessed <- existential(
        s"?m:real. a:real <= m /\\ m <= b:real /\\ (!x:real. a <= x /\\ x <= b ==> ${compared(s"$F x", s"$F m")})"
      ).flatMap(rules.existsIntro(_, m, found))
      opened <- rules.existsElim(attained, m, witnessed)
      result <- closeOver(steps, opened, List(Relative, "a:real <= b:real"), List("f:real -> real", "a:real", "b:real"))
    } yield result
  }

  /** [[Continuity.UniformWithin]]: `E`'s radius, which serves the points of the interval. */
  private def uniformity(steps: Steps, extension: Kernel.Thm, agrees: Kernel.Thm, twoSided: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      x <- variable(steps, "x:real")
      y <- variable(steps, "y:real")
      d <- variable(steps, "d:real")
      detached <- atTheExtension(steps, extension, twoSided, List("e:real"))
      radius <- mp(detached, assume("0 < e:real"))
      body <- assume(
        s"0 < d:real /\\ (!x:real. !y:real. a:real <= x /\\ x <= b:real /\\ a <= y /\\ y <= b /\\ " +
          s"abs (x - y) < d ==> abs (${valueAt("x")} - ${valueAt("y")}) < e:real)")
      dPositive <- rules.conjElim1(body)
      serves <- rules.conjElim2(body)
      pair <- proposition("a:real <= x:real /\\ x <= b:real /\\ a <= y:real /\\ y <= b /\\ abs (x - y) < d:real")
      assumedPair <- LogicError.lift(Kernel.assume(pair))
      value <- rules.specAll(serves, List(x, y)).flatMap(rules.mp(_, assumedPair))
      xA <- rules.conjElim1(assumedPair)
      xB <- rules.conjElim2(assumedPair).flatMap(rules.conjElim1)
      yA <- rules.conjElim2(assumedPair).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
      yB <- rules.conjElim2(assumedPair).flatMap(rules.conjElim2).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
      atX <- agreesAt(steps, agrees, "x:real").flatMap(rules.proveHyp(xA, _)).flatMap(rules.proveHyp(xB, _))
      atY <- agreesAt(steps, agrees, "y:real").flatMap(rules.proveHyp(yA, _)).flatMap(rules.proveHyp(yB, _))
      read <- forward(steps, Vector(atX, atY), value)
      everyPair <- rules.disch(pair, read).flatMap(rules.genAll(_, List(x, y)))
      found <- conj(Right(dPositive), Right(everyPair))
      witnessed <- existential(
        s"?d:real. 0 < d /\\ (!x:real. !y:real. a:real <= x /\\ x <= b:real /\\ a <= y /\\ y <= b /\\ " +
          s"abs (x - y) < d ==> abs ($F x - $F y) < e:real)"
      ).flatMap(rules.existsIntro(_, d, found))
      opened <- rules.existsElim(radius, d, witnessed)
      result <- closeOver(steps, opened, List("0 < e:real", Relative, "a:real <= b:real"),
        List("f:real -> real", "a:real", "b:real", "e:real"))
    } yield result
  }
}
