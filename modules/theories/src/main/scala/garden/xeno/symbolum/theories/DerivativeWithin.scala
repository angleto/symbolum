package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

import Continuity.Steps
import Within.{F, Extended, Relative, valueAt, agreesAt, backward, closeOver, forward, reduced, term, variable}

/**
 * Rolle, the mean value theorem and the facts about the sign of a derivative, with continuity
 * relative to `[a, b]`, which is how a textbook states them. `Within` has why the two-sided forms
 * ask more.
 *
 * Their derivative hypotheses were already the textbook's, on the open interval, and a derivative
 * at an interior point is a fact about the points near it. That is [[Derivative.Local]]: two
 * functions agreeing on a neighbourhood of `x` have the same derivatives there. So the extension
 * by the nearer end's value, which agrees with `f` on `[a, b]` and so on a neighbourhood of every
 * interior point, has `f`'s derivatives inside, and each theorem here is the two-sided one at the
 * extension, read back. The radius at an interior `x` is `min (x - a) (b - x)`.
 */
private[theories] object DerivativeWithin {

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Functions: Type = Type.fun(Reals, Reals)
  private val G = "(g:real -> real)"

  def prove(
    steps: Steps,
    magnitude: Magnitude,
    continuity: Continuity,
    held: Map[String, Kernel.Thm]
  ): Either[LogicError, Map[String, Kernel.Thm]] = {
    def fact(name: String) = held.get(name).toRight(MissingDefinition(name))
    for {
      local <- locality(steps, magnitude)
      extension <- continuity.fact(Continuity.Extension)
      agrees <- continuity.fact(Continuity.ExtensionAgrees)
      tools = Tools(steps, magnitude, local, extension, agrees)
      rolle <- fact(Derivative.Rolle).flatMap(rolleWithin(tools, _))
      meanValue <- fact(Derivative.MeanValue).flatMap(meanValueWithin(tools, _))
      flat <- fact(Derivative.Flat).flatMap(signWithin(tools, _, Derivative.FlatWithin))
      nonDecreasing <- fact(Derivative.NonDecreasing).flatMap(signWithin(tools, _, Derivative.NonDecreasingWithin))
      increasing <- fact(Derivative.Increasing).flatMap(signWithin(tools, _, Derivative.IncreasingWithin))
    } yield Map(
      Derivative.Local -> local,
      Derivative.RolleWithin -> rolle,
      Derivative.MeanValueWithin -> meanValue,
      Derivative.FlatWithin -> flat,
      Derivative.NonDecreasingWithin -> nonDecreasing,
      Derivative.IncreasingWithin -> increasing
    )
  }

  private final case class Tools(
    steps: Steps,
    magnitude: Magnitude,
    local: Kernel.Thm,
    extension: Kernel.Thm,
    agrees: Kernel.Thm
  )

  /* ------------------------------------------------------------------ locality */

  /**
   * [[Derivative.Local]]: at radius `min d r`, where `d` is `f`'s and `r` the agreement's, every
   * increment keeps both `x` and `x + h` where `g` is `f`, so `g`'s difference quotient is `f`'s.
   */
  private def locality(steps: Steps, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val shared = s"(!y:real. abs (y - x:real) < r:real ==> $G y = $F y)"
    for {
      f <- variable(steps, "f:real -> real")
      g <- variable(steps, "g:real -> real")
      x <- variable(steps, "x:real")
      m <- variable(steps, "m:real")
      e <- variable(steps, "e:real")
      d <- variable(steps, "d:real")
      h <- variable(steps, "h:real")
      supplied <- assume(s"derivative $F x:real m:real")
      opened <- Derivative.openDerivative(steps, f, x, m, supplied)
      positive <- proposition("0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      radii <- rules.spec(e, opened).flatMap(rules.mp(_, assumedPositive))
      body <- assume(s"0 < d:real /\\ (!h:real. 0 < abs h /\\ abs h < d ==> abs ($F (x:real + h) - $F x - m:real * h) < e:real * abs h)")
      dPositive <- rules.conjElim1(body)
      serves <- rules.conjElim2(body)
      rPositive <- assume("0 < r:real")
      same <- assume(shared)

      // `min d r` is positive: it is one of two positive numbers.
      cases <- steps.at(magnitude.fact(Magnitude.MinCases), "d:real", "r:real")
      isD <- assume("min d r = d:real").flatMap(eq =>
        steps.at(lemma("!w:real c:real. w = c ==> 0 < c ==> 0 < w"), "min d r", "d:real").flatMap(mp(_, Right(eq), Right(dPositive))))
      isR <- assume("min d r = r:real").flatMap(eq =>
        steps.at(lemma("!w:real c:real. w = c ==> 0 < c ==> 0 < w"), "min d r", "r:real").flatMap(mp(_, Right(eq), Right(rPositive))))
      wPositive <- rules.disjElim(cases, isD, isR)

      inner <- proposition("0 < abs (h:real) /\\ abs h < min d r")
      assumedInner <- LogicError.lift(Kernel.assume(inner))
      nonZero <- rules.conjElim1(assumedInner)
      small <- rules.conjElim2(assumedInner)
      belowD <- steps.at(lemma("!s:real w:real c:real. s < w ==> w <= c ==> s < c"), "abs (h:real)", "min d r", "d:real")
        .flatMap(mp(_, Right(small), steps.at(magnitude.fact(Magnitude.MinBelowLeft), "d:real", "r:real")))
      belowR <- steps.at(lemma("!s:real w:real c:real. s < w ==> w <= c ==> s < c"), "abs (h:real)", "min d r", "r:real")
        .flatMap(mp(_, Right(small), steps.at(magnitude.fact(Magnitude.MinBelowRight), "d:real", "r:real")))
      increment <- rules.conjIntro(nonZero, belowD)
      value <- rules.spec(h, serves).flatMap(rules.mp(_, increment))

      hSides <- ExtremeValue.sides(steps, magnitude, "h:real", "r:real", belowR)
      shiftUp <- steps.at(lemma("!x:real h:real r:real. h < r ==> (x + h) - x < r"), "x:real", "h:real", "r:real").flatMap(mp(_, Right(hSides._1)))
      shiftDown <- steps.at(lemma("!x:real h:real r:real. -h < r ==> -((x + h) - x) < r"), "x:real", "h:real", "r:real").flatMap(mp(_, Right(hSides._2)))
      shiftClose <- ExtremeValue.joined(steps, magnitude, "(x:real + h:real) - x", "r:real", shiftUp, shiftDown)
      atShift <- term(steps, "x:real + h:real").flatMap(rules.spec(_, same)).flatMap(rules.mp(_, shiftClose))
      stayUp <- steps.at(lemma("!x:real r:real. 0 < r ==> x - x < r"), "x:real", "r:real").flatMap(mp(_, Right(rPositive)))
      stayDown <- steps.at(lemma("!x:real r:real. 0 < r ==> -(x - x) < r"), "x:real", "r:real").flatMap(mp(_, Right(rPositive)))
      stayClose <- ExtremeValue.joined(steps, magnitude, "x:real - x", "r:real", stayUp, stayDown)
      atX <- rules.spec(x, same).flatMap(rules.mp(_, stayClose))
      target <- proposition(s"abs ($G (x:real + h:real) - $G x - m:real * h) < e:real * abs h")
      read <- backward(steps, Vector(atShift, atX), target, value)

      everyIncrement <- rules.disch(inner, read).flatMap(rules.gen(h, _))
      pair <- rules.conjIntro(wPositive, everyIncrement)
      radius <- term(steps, "min d r")
      witnessed <- existential(
        s"?d:real. 0 < d /\\ (!h:real. 0 < abs h /\\ abs h < d ==> abs ($G (x:real + h) - $G x - m:real * h) < e:real * abs h)"
      ).flatMap(rules.existsIntro(_, radius, pair))
      found <- rules.existsElim(radii, d, witnessed)
      statement <- rules.disch(positive, found).flatMap(rules.gen(e, _))
      folded <- Derivative.foldDerivative(steps, g, x, m, statement)
      result <- closeOver(steps, folded, List(s"derivative $F x:real m:real", shared, "0 < r:real"),
        List("f:real -> real", "g:real -> real", "x:real", "m:real", "r:real"))
    } yield result
  }

  /* ------------------------------------------------------------------ across the extension */

  /**
   * `|- derivative <to> t m` from `|- derivative <from> t m`, where one of the two is `f` and the
   * other the extension, for an interior `t`: they agree within `min (t - a) (b - t)`. Hypotheses:
   * `a < t`, `t < b` and `a <= b`, besides the derivative supplied.
   */
  private def across(tools: Tools, t: String, m: String, derivative: Kernel.Thm, toExtension: Boolean): Either[LogicError, Kernel.Thm] = {
    val steps = tools.steps
    import steps.*
    val magnitude = tools.magnitude
    val r = s"min ($t - a:real) (b:real - $t)"
    for {
      y <- variable(steps, "y:real")
      extended <- Parser.term(theory, notation, Extended, Functions)
      f <- variable(steps, "f:real -> real")
      point <- term(steps, t)
      slope <- term(steps, m)
      radius <- term(steps, r)
      left <- assume(s"a:real < $t")
      right <- assume(s"$t < b:real")
      cases <- steps.at(magnitude.fact(Magnitude.MinCases), s"$t - a:real", s"b:real - $t")
      fromLeft <- assume(s"$r = $t - a:real").flatMap(eq =>
        steps.at(lemma("!w:real t:real a:real. w = t - a ==> a < t ==> 0 < w"), r, t, "a:real").flatMap(mp(_, Right(eq), Right(left))))
      fromRight <- assume(s"$r = b:real - $t").flatMap(eq =>
        steps.at(lemma("!w:real t:real b:real. w = b - t ==> t < b ==> 0 < w"), r, t, "b:real").flatMap(mp(_, Right(eq), Right(right))))
      rPositive <- rules.disjElim(cases, fromLeft, fromRight)

      near <- proposition(s"abs (y:real - $t) < $r")
      assumedNear <- LogicError.lift(Kernel.assume(near))
      nearSides <- ExtremeValue.sides(steps, magnitude, s"y:real - $t", r, assumedNear)
      aboveA <- steps.at(lemma("!y:real t:real w:real a:real. -(y - t) < w ==> w <= t - a ==> a <= y"), "y:real", t, r, "a:real")
        .flatMap(mp(_, Right(nearSides._2), steps.at(magnitude.fact(Magnitude.MinBelowLeft), s"$t - a:real", s"b:real - $t")))
      belowB <- steps.at(lemma("!y:real t:real w:real b:real. y - t < w ==> w <= b - t ==> y <= b"), "y:real", t, r, "b:real")
        .flatMap(mp(_, Right(nearSides._1), steps.at(magnitude.fact(Magnitude.MinBelowRight), s"$t - a:real", s"b:real - $t")))
      agreement <- agreesAt(steps, tools.agrees, "y:real").flatMap(rules.proveHyp(aboveA, _)).flatMap(rules.proveHyp(belowB, _))
      oriented <- if (toExtension) Right(agreement) else Conv.sym(agreement)
      everywhere <- rules.disch(near, oriented).flatMap(rules.gen(y, _))
      (from, to) = if (toExtension) (f, extended) else (extended, f)
      instance <- rules.specAll(tools.local, List(from, to, point, slope, radius)).flatMap(reduced)
      result <- mp(instance, Right(rPositive), Right(everywhere), Right(derivative))
    } yield result
  }

  /** `|- !x. a <= x /\ x <= b ==> continuous E x`, under `a <= b` and the relative continuity. */
  private def extensionOnInterval(tools: Tools): Either[LogicError, Kernel.Thm] = {
    val steps = tools.steps
    import steps.*
    for {
      f <- variable(steps, "f:real -> real")
      a <- variable(steps, "a:real")
      b <- variable(steps, "b:real")
      x <- variable(steps, "x:real")
      everywhere <- rules.specAll(tools.extension, List(f, a, b)).flatMap(mp(_, assume("a:real <= b:real"), assume(Relative)))
      point <- proposition("a:real <= x:real /\\ x <= b:real")
      result <- rules.spec(x, everywhere).flatMap(rules.disch(point, _)).flatMap(rules.gen(x, _))
    } yield result
  }

  /**
   * The interior premise at the extension, `!x. a < x /\ x < b ==> ?m. derivative E x m /\ <sign>`,
   * from the same premise at `f`. `sign` is the conjunct beside the derivative, or nothing; `fixed`
   * is a slope written into the premise rather than bound by it, which is [[Derivative.Flat]]'s.
   */
  private def interiorAtExtension(tools: Tools, supplied: Kernel.Thm, sign: Option[String], fixed: Option[String]): Either[LogicError, Kernel.Thm] = {
    val steps = tools.steps
    import steps.*
    val slope = fixed.getOrElse("m:real")
    def claim(function: String): String =
      s"derivative $function x:real $slope" + sign.map(s => s" /\\ $s").getOrElse("")
    for {
      x <- variable(steps, "x:real")
      m <- variable(steps, "m:real")
      point <- proposition("a:real < x:real /\\ x < b:real")
      assumedPoint <- LogicError.lift(Kernel.assume(point))
      left <- rules.conjElim1(assumedPoint)
      right <- rules.conjElim2(assumedPoint)
      atF <- rules.spec(x, supplied).flatMap(rules.mp(_, assumedPoint))
      moved <- fixed match {
        case Some(_) =>
          across(tools, "x:real", slope, atF, toExtension = true)
        case None =>
          for {
            body <- assume(claim(F))
            derivative <- if (sign.isDefined) rules.conjElim1(body) else Right(body)
            carried <- across(tools, "x:real", slope, derivative, toExtension = true)
            both <- sign match {
              case Some(_) => rules.conjElim2(body).flatMap(rules.conjIntro(carried, _))
              case None => Right(carried)
            }
            witnessed <- existential(s"?m:real. ${claim(Extended)}").flatMap(rules.existsIntro(_, m, both))
            opened <- rules.existsElim(atF, m, witnessed)
          } yield opened
      }
      withLeft <- rules.proveHyp(left, moved)
      withBoth <- rules.proveHyp(right, withLeft)
      result <- rules.disch(point, withBoth).flatMap(rules.gen(x, _))
    } yield result
  }

  /* ------------------------------------------------------------------ the textbook forms */

  /** [[Derivative.RolleWithin]]. */
  private def rolleWithin(tools: Tools, twoSided: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val steps = tools.steps
    import steps.*
    val interior = s"!x:real. a:real < x /\\ x < b:real ==> ?m:real. derivative $F x m"
    for {
      a <- variable(steps, "a:real")
      b <- variable(steps, "b:real")
      c <- variable(steps, "c:real")
      extended <- Parser.term(theory, notation, Extended, Functions)
      strictly <- assume("a:real < b:real")
      ordered <- steps.at(lemma("!a:real b:real. a < b ==> a <= b"), "a:real", "b:real").flatMap(mp(_, Right(strictly)))
      continuous <- extensionOnInterval(tools).flatMap(rules.proveHyp(ordered, _))
      slopes <- assume(interior).flatMap(interiorAtExtension(tools, _, None, None)).flatMap(rules.proveHyp(ordered, _))
      instance <- rules.specAll(twoSided, List(extended, a, b)).flatMap(reduced)
      (premises, _) = Within.antecedents(steps, instance.conclusion)
      ends <- premises.drop(3).headOption.toRight(NotOfForm("the two ends' values", instance.conclusion))
      aReflexive <- steps.at(lemma("!a:real. a <= a"), "a:real")
      bReflexive <- steps.at(lemma("!b:real. b <= b"), "b:real")
      atA <- agreesAt(steps, tools.agrees, "a:real").flatMap(rules.proveHyp(aReflexive, _)).flatMap(rules.proveHyp(ordered, _))
      atB <- agreesAt(steps, tools.agrees, "b:real").flatMap(rules.proveHyp(bReflexive, _)).flatMap(rules.proveHyp(ordered, _))
      endsGiven <- assume(s"$F a:real = $F b:real")
      equalEnds <- backward(steps, Vector(atA, atB), ends, endsGiven)
      found <- mp(instance, Right(strictly), Right(continuous), Right(slopes), Right(equalEnds))
      body <- assume(s"a:real < c:real /\\ c < b:real /\\ derivative $Extended c 0")
      cLeft <- rules.conjElim1(body)
      cRight <- rules.conjElim2(body).flatMap(rules.conjElim1)
      flat <- rules.conjElim2(body).flatMap(rules.conjElim2)
      back <- across(tools, "c:real", "0:real", flat, toExtension = false)
        .flatMap(rules.proveHyp(cLeft, _)).flatMap(rules.proveHyp(cRight, _)).flatMap(rules.proveHyp(ordered, _))
      pair <- conj(Right(cLeft), conj(Right(cRight), Right(back)))
      witnessed <- existential(s"?c:real. a:real < c /\\ c < b:real /\\ derivative $F c 0").flatMap(rules.existsIntro(_, c, pair))
      opened <- rules.existsElim(found, c, witnessed)
      result <- closeOver(steps, opened, List(s"$F a:real = $F b:real", interior, Relative, "a:real < b:real"),
        List("f:real -> real", "a:real", "b:real"))
    } yield result
  }

  /** [[Derivative.MeanValueWithin]]. */
  private def meanValueWithin(tools: Tools, twoSided: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val steps = tools.steps
    import steps.*
    val interior = s"!x:real. a:real < x /\\ x < b:real ==> ?m:real. derivative $F x m"
    for {
      a <- variable(steps, "a:real")
      b <- variable(steps, "b:real")
      c <- variable(steps, "c:real")
      m <- variable(steps, "m:real")
      extended <- Parser.term(theory, notation, Extended, Functions)
      strictly <- assume("a:real < b:real")
      ordered <- steps.at(lemma("!a:real b:real. a < b ==> a <= b"), "a:real", "b:real").flatMap(mp(_, Right(strictly)))
      continuous <- extensionOnInterval(tools).flatMap(rules.proveHyp(ordered, _))
      slopes <- assume(interior).flatMap(interiorAtExtension(tools, _, None, None)).flatMap(rules.proveHyp(ordered, _))
      instance <- rules.specAll(twoSided, List(extended, a, b)).flatMap(reduced)
      found <- mp(instance, Right(strictly), Right(continuous), Right(slopes))
      aReflexive <- steps.at(lemma("!a:real. a <= a"), "a:real")
      bReflexive <- steps.at(lemma("!b:real. b <= b"), "b:real")
      atA <- agreesAt(steps, tools.agrees, "a:real").flatMap(rules.proveHyp(aReflexive, _)).flatMap(rules.proveHyp(ordered, _))
      atB <- agreesAt(steps, tools.agrees, "b:real").flatMap(rules.proveHyp(bReflexive, _)).flatMap(rules.proveHyp(ordered, _))
      inner <- assume(s"?m:real. a:real < c:real /\\ c < b:real /\\ derivative $Extended c m /\\ ${valueAt("b:real")} - ${valueAt("a:real")} = m * (b - a)")
      body <- assume(s"a:real < c:real /\\ c < b:real /\\ derivative $Extended c m:real /\\ ${valueAt("b:real")} - ${valueAt("a:real")} = m * (b - a)")
      cLeft <- rules.conjElim1(body)
      cRight <- rules.conjElim2(body).flatMap(rules.conjElim1)
      slope <- rules.conjElim2(body).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
      difference <- rules.conjElim2(body).flatMap(rules.conjElim2).flatMap(rules.conjElim2)
      back <- across(tools, "c:real", "m:real", slope, toExtension = false)
        .flatMap(rules.proveHyp(cLeft, _)).flatMap(rules.proveHyp(cRight, _)).flatMap(rules.proveHyp(ordered, _))
      read <- forward(steps, Vector(atA, atB), difference)
      all <- conj(Right(cLeft), conj(Right(cRight), conj(Right(back), Right(read))))
      goal = s"?c:real. ?m:real. a:real < c /\\ c < b:real /\\ derivative $F c m /\\ $F b - $F a = m * (b - a)"
      withM <- existential(s"?m:real. a:real < c:real /\\ c < b:real /\\ derivative $F c m /\\ $F b - $F a = m * (b - a)")
        .flatMap(rules.existsIntro(_, m, all))
      withC <- existential(goal).flatMap(rules.existsIntro(_, c, withM))
      overM <- rules.existsElim(inner, m, withC)
      overC <- rules.existsElim(found, c, overM)
      result <- closeOver(steps, overC, List(interior, Relative, "a:real < b:real"), List("f:real -> real", "a:real", "b:real"))
    } yield result
  }

  /**
   * [[Derivative.FlatWithin]], [[Derivative.NonDecreasingWithin]] and [[Derivative.IncreasingWithin]].
   *
   * None of the three two-sided statements carries `a <= b`, since an empty interval makes each
   * vacuous, and the extension needs it. So it is read off the points the conclusion is about,
   * which lie in `[a, b]`, before anything is asked of the extension.
   */
  private def signWithin(tools: Tools, twoSided: Kernel.Thm, name: String): Either[LogicError, Kernel.Thm] = {
    val steps = tools.steps
    import steps.*
    val flat = name == Derivative.FlatWithin
    val strict = name == Derivative.IncreasingWithin
    val sign = if (flat) None else Some(if (strict) "0 < m:real" else "0 <= m:real")
    val interior =
      if (flat) s"!x:real. a:real < x /\\ x < b:real ==> derivative $F x 0"
      else s"!x:real. a:real < x /\\ x < b:real ==> ?m:real. derivative $F x m /\\ ${sign.get}"
    val (points, pointNames) =
      if (flat) ("a:real <= x:real /\\ x <= b:real", List("x:real"))
      else (s"a:real <= u:real /\\ u ${if (strict) "<" else "<="} v:real /\\ v <= b:real", List("u:real", "v:real"))
    for {
      a <- variable(steps, "a:real")
      b <- variable(steps, "b:real")
      extended <- Parser.term(theory, notation, Extended, Functions)
      pointVariables <- pointNames.foldLeft[Either[LogicError, List[FVar]]](Right(Nil)) { (acc, text) =>
        for { found <- acc; next <- variable(steps, text) } yield found :+ next
      }
      supplied <- proposition(points)
      assumedPoints <- LogicError.lift(Kernel.assume(supplied))
      ordered <- (if (flat)
        steps.at(lemma("!a:real x:real b:real. a <= x /\\ x <= b ==> a <= b"), "a:real", "x:real", "b:real")
      else if (strict)
        steps.at(lemma("!a:real u:real v:real b:real. a <= u /\\ u < v /\\ v <= b ==> a <= b"), "a:real", "u:real", "v:real", "b:real")
      else
        steps.at(lemma("!a:real u:real v:real b:real. a <= u /\\ u <= v /\\ v <= b ==> a <= b"), "a:real", "u:real", "v:real", "b:real")
      ).flatMap(mp(_, Right(assumedPoints)))
      continuous <- extensionOnInterval(tools).flatMap(rules.proveHyp(ordered, _))
      slopes <- assume(interior).flatMap(interiorAtExtension(tools, _, sign, if (flat) Some("0:real") else None))
        .flatMap(rules.proveHyp(ordered, _))
      instance <- rules.specAll(twoSided, List(extended, a, b)).flatMap(reduced)
      everyPair <- mp(instance, Right(continuous), Right(slopes))
      atPoints <- rules.specAll(everyPair, pointVariables).flatMap(rules.mp(_, assumedPoints))
      names = pointNames.map(_.stripSuffix(":real"))
      binder = s"!a:real ${names.map(_ + ":real").mkString(" ")} b:real."
      bounds = ("a:real" :: pointNames) :+ "b:real"
      agreements <- (if (flat) List("x", "a") else names).foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, n) =>
        for {
          found <- acc
          raw <- agreesAt(steps, tools.agrees, s"$n:real")
          lower <- if (n == "a") steps.at(lemma("!a:real. a <= a"), "a:real")
                   else steps.at(lemma(s"$binder $points ==> a <= $n"), bounds: _*).flatMap(mp(_, Right(assumedPoints)))
          upper <- if (n == "a") Right(ordered)
                   else steps.at(lemma(s"$binder $points ==> $n <= b"), bounds: _*).flatMap(mp(_, Right(assumedPoints)))
          held <- rules.proveHyp(lower, raw).flatMap(rules.proveHyp(upper, _))
        } yield found :+ held
      }
      read <- forward(steps, agreements, atPoints)
      result <- rules.disch(supplied, read).flatMap(rules.genAll(_, pointVariables))
        .flatMap(closeOver(steps, _, List(interior, Relative), List("f:real -> real", "a:real", "b:real")))
    } yield result
  }
}
