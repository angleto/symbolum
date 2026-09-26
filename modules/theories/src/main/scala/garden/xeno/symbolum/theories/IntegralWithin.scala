package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

import Continuity.Steps
import Within.{F, Extended, Relative, agreesWithin, closeOver, forward, reduced, term, valueAt, variable}

/**
 * The integral's theorems about a continuous function, stated with continuity relative to `[a, b]`,
 * which is how a textbook states them.
 *
 * Not a development: `Integral` publishes what this derives, under names it declares.
 *
 * `CONTINUOUS_HAS_INTEGRAL`, `CONTINUOUS_INTEGRAL`, `DERIVATIVE_WITHIN_INTEGRAL` and
 * `DERIVATIVE_INTEGRAL` ask `!x. a <= x /\ x <= b ==> continuous f x`, and `continuous` is
 * two-sided, so at the ends it asks about points outside the interval. The verification of card
 * 6257d0da found on 2026-09-25 that these four had no relative form while every other interval
 * theorem had one, and a sentence saying every interval theorem had a textbook form.
 *
 * == The same extension as `Within`, and one fact `Within` did not need ==
 *
 * The forms here are the existing theorems at the extension `E` of `Within`, which is continuous
 * everywhere and is `f` on `[a, b]`. What `Within` never needed is to carry a statement **about the
 * whole function** back from `E` to `f`: a bound or a crossing is read at one point, where `E` and
 * `f` agree, but an integral is a statement about every fine sum over the interval, and a derivative
 * relative to `[a, b]` about every point near one. So three congruences come first, each saying the
 * thing depends only on the values in `[a, b]`:
 *
 *  - `FINE_SUM_CONGRUENCE`, by induction over the division, carrying `u <= v` beside the property
 *    because a join needs the middle point inside the interval and nothing else says it is;
 *  - `HAS_INTEGRAL_CONGRUENCE`, the same gauge serving both functions, since their fine sums are one;
 *  - `DERIVATIVE_WITHIN_CONGRUENCE`, the same radius, since the increments it quantifies over stay in
 *    `[a, b]` by the definition's own clause.
 *
 * The integral of `E` from `a` to a point `y` of `[a, b]` is then `f`'s by congruence on `[a, y]` and
 * uniqueness, which is what moves the relative derivative across.
 */
private[theories] object IntegralWithin {

  /** What the derivations read, by role. */
  final case class Held(
    extension: Kernel.Thm,
    agrees: Kernel.Thm,
    piece: Kernel.Thm,
    join: Kernel.Thm,
    induction: Kernel.Thm,
    hasDefinition: Kernel.Thm,
    withinDefinition: Kernel.Thm,
    continuousHas: Kernel.Thm,
    continuousIntegral: Kernel.Thm,
    unique: Kernel.Thm,
    derivativeWithin: Kernel.Thm,
    withinInterior: Kernel.Thm
  )

  /** The facts, by the names `Integral` publishes them under. */
  def prove(steps: Steps, held: Held): Either[LogicError, Map[String, Kernel.Thm]] =
    for {
      sums <- fineSumCongruence(steps, held)
      integrals <- hasIntegralCongruence(steps, held, sums)
      slopes <- derivativeWithinCongruence(steps, held)
      has <- hasWithin(steps, held, integrals)
      named <- integralWithin(steps, held, has)
      relative <- derivativeWithinWithin(steps, held, integrals, slopes)
      interior <- derivativeInteriorWithin(steps, held, relative)
    } yield Map(
      Integral.SumCongruence -> sums,
      Integral.HasCongruence -> integrals,
      Integral.WithinCongruence -> slopes,
      Integral.ContinuousHasWithin -> has,
      Integral.ContinuousIntegralWithin -> named,
      Integral.DerivativeWithinWithin -> relative,
      Integral.DerivativeOfIntegralWithin -> interior
    )

  private val Agreement = "!x:real. a:real <= x /\\ x <= b:real ==> (f:real -> real) x = (g:real -> real) x"

  /** `|- p x` for the theorem `|- !x. p x`, at each argument in turn, with the result beta-reduced. */
  private def specialised(steps: Steps, theorem: Kernel.Thm, arguments: String*): Either[LogicError, Kernel.Thm] =
    arguments.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, text) =>
      for { found <- acc; next <- term(steps, text) } yield found :+ next
    }.flatMap(steps.rules.specAll(theorem, _)).flatMap(reduced)

  /** `x <= z` from `x <= y` and `y <= z`. */
  private def chain(steps: Steps, x: String, y: String, z: String, left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    steps.at(steps.lemma("!x:real y:real z:real. x <= y ==> y <= z ==> x <= z"), x, y, z)
      .flatMap(steps.mp(_, Right(left), Right(right)))

  /** `|- lhs = rhs` read as `|- P rhs` from `|- P lhs`, for `P` a lambda written as text. */
  private def moved(steps: Steps, lambdaText: String, equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      lambda <- term(steps, lambdaText)
      both <- Conv.apTerm(lambda, equation).flatMap(Conv.betaSides)
      result <- LogicError.lift(Kernel.eqMp(both, theorem))
    } yield result

  /** The definition of `name` at `arguments`, with its right side beta-reduced. */
  private def opened(definition: Kernel.Thm, arguments: List[Term]): Either[LogicError, Kernel.Thm] =
    for {
      equation <- Conv.unfold(definition, arguments)
      right <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
      normal <- Conv.betaNormalise(right)
      joined <- Conv.trans(equation, normal)
    } yield joined

  /* ------------------------------------------------------------------ the three congruences */

  /**
   * `|- !f g d a b s. (!x. a <= x /\ x <= b ==> f x = g x) ==> fine_sum g d a b s ==>
   *     fine_sum f d a b s`
   */
  private def fineSumCongruence(steps: Steps, held: Held): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      u <- variable(steps, "u:real")
      v <- variable(steps, "v:real")
      w <- variable(steps, "w:real")
      x1 <- variable(steps, "x1:real")
      y1 <- variable(steps, "y1:real")
      agreement <- assume(Agreement)
      property <- term(steps,
        "\\u:real. \\v:real. \\w:real. (a:real <= u /\\ v <= b:real ==> " +
          "fine_sum (f:real -> real) (d:real -> real) u v w) /\\ u <= v")
      g <- term(steps, "g:real -> real")
      d <- term(steps, "d:real -> real")
      instance <- rules.specAll(held.induction, List(g, d, property)).flatMap(reduced)
      parts <- Right(Within.antecedents(steps, instance.conclusion))
      pieceGoal = parts._1(0)
      joinGoal = parts._1(1)

      // one piece: a tag inside [u, v], and [u, v] inside [a, b] when asked
      piece <- for {
        hypothesis <- proposition("u:real <= w:real /\\ w <= v:real /\\ v - u < (d:real -> real) w")
        h <- LogicError.lift(Kernel.assume(hypothesis))
        uw <- rules.conjElim1(h)
        wv <- rules.conjElim2(h).flatMap(rules.conjElim1)
        uv <- chain(steps, "u:real", "w:real", "v:real", uw, wv)
        inside <- proposition("a:real <= u:real /\\ v:real <= b:real")
        i <- LogicError.lift(Kernel.assume(inside))
        au <- rules.conjElim1(i)
        vb <- rules.conjElim2(i)
        aw <- chain(steps, "a:real", "u:real", "w:real", au, uw)
        wb <- chain(steps, "w:real", "v:real", "b:real", wv, vb)
        member <- rules.conjIntro(aw, wb)
        same <- specialised(steps, agreement, "w:real").flatMap(rules.mp(_, member))
        onF <- specialised(steps, held.piece, "f:real -> real", "d:real -> real", "u:real", "v:real", "w:real").flatMap(rules.mp(_, h))
        onG <- moved(steps, "\\t:real. fine_sum (f:real -> real) (d:real -> real) u v (t * (v - u))", same, onF)
        asked <- rules.disch(inside, onG)
        both <- rules.conjIntro(asked, uv)
        result <- rules.disch(hypothesis, both).flatMap(rules.genAll(_, List(u, v, w)))
        _ <- if (result.conclusion == pieceGoal) Right(()) else Left(NotOfForm("the piece case", result.conclusion))
      } yield result

      // a join: the middle point is inside [a, b] because both halves carry their order
      join <- for {
        leftText <- proposition(
          "(a:real <= u:real /\\ v <= b:real ==> fine_sum (f:real -> real) (d:real -> real) u v x1) /\\ u <= v")
        rightText <- proposition(
          "(a:real <= v:real /\\ w <= b:real ==> fine_sum (f:real -> real) (d:real -> real) v w y1) /\\ v <= w")
        left <- LogicError.lift(Kernel.assume(leftText))
        right <- LogicError.lift(Kernel.assume(rightText))
        uv <- rules.conjElim2(left)
        vw <- rules.conjElim2(right)
        uw <- chain(steps, "u:real", "v:real", "w:real", uv, vw)
        inside <- proposition("a:real <= u:real /\\ w:real <= b:real")
        i <- LogicError.lift(Kernel.assume(inside))
        au <- rules.conjElim1(i)
        wb <- rules.conjElim2(i)
        vb <- chain(steps, "v:real", "w:real", "b:real", vw, wb)
        av <- chain(steps, "a:real", "u:real", "v:real", au, uv)
        leftSum <- rules.conjIntro(au, vb).flatMap(inner => rules.conjElim1(left).flatMap(rules.mp(_, inner)))
        rightSum <- rules.conjIntro(av, wb).flatMap(inner => rules.conjElim1(right).flatMap(rules.mp(_, inner)))
        joined <- specialised(steps, held.join, "f:real -> real", "d:real -> real", "u:real", "v:real", "w:real", "x1:real", "y1:real")
          .flatMap(rules.mp(_, leftSum)).flatMap(rules.mp(_, rightSum))
        asked <- rules.disch(inside, joined)
        both <- rules.conjIntro(asked, uw)
        result <- rules.disch(rightText, both).flatMap(rules.disch(leftText, _))
          .flatMap(rules.genAll(_, List(u, v, w, x1, y1)))
        _ <- if (result.conclusion == joinGoal) Right(()) else Left(NotOfForm("the join case", result.conclusion))
      } yield result

      every <- rules.mp(instance, piece).flatMap(rules.mp(_, join))
      summed <- assume("fine_sum (g:real -> real) (d:real -> real) a b s:real")
      atAB <- specialised(steps, every, "a:real", "b:real", "s:real").flatMap(rules.mp(_, summed))
      aa <- steps.at(lemma("!a:real. a <= a"), "a:real")
      bb <- steps.at(lemma("!a:real. a <= a"), "b:real")
      ends <- rules.conjIntro(aa, bb)
      result0 <- rules.conjElim1(atAB).flatMap(rules.mp(_, ends))
      result <- closeOver(steps, result0,
        List("fine_sum (g:real -> real) (d:real -> real) a b s:real", Agreement),
        List("f:real -> real", "g:real -> real", "d:real -> real", "a:real", "b:real", "s:real"))
    } yield result
  }

  /**
   * `|- !f g a b i. (!x. a <= x /\ x <= b ==> f x = g x) ==> has_integral f a b i ==>
   *     has_integral g a b i`
   */
  private def hasIntegralCongruence(steps: Steps, held: Held, sums: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      f <- term(steps, "f:real -> real")
      g <- term(steps, "g:real -> real")
      a <- term(steps, "a:real")
      b <- term(steps, "b:real")
      i <- term(steps, "i:real")
      e <- variable(steps, "e:real")
      d <- variable(steps, "d:real -> real")
      s <- variable(steps, "s:real")
      agreement <- assume(Agreement)
      integrated <- assume("has_integral (f:real -> real) a b i:real")
      openF <- opened(held.hasDefinition, List(f, a, b, i))
      openG <- opened(held.hasDefinition, List(g, a, b, i))
      epsilons <- LogicError.lift(Kernel.eqMp(openF, integrated))
      positive <- proposition("0 < e:real")
      p <- LogicError.lift(Kernel.assume(positive))
      gauged <- rules.spec(e, epsilons).flatMap(rules.mp(_, p))
      predicateF <- logic.destExistsPredicate(gauged.conclusion).toRight(NotOfForm("an existential", gauged.conclusion))
      instanceF <- LogicError.lift(Term.app(predicateF, d)).flatMap(Conv.betaNormalise).flatMap(eq =>
        Term.destEq(eq.conclusion).map(_._2).toRight(NotOfForm("an equation", eq.conclusion)))
      body <- LogicError.lift(Kernel.assume(instanceF))
      positiveGauge <- rules.conjElim1(body)
      bound <- rules.conjElim2(body)
      onG <- assume("fine_sum (g:real -> real) (d:real -> real) a b s:real")
      onF <- specialised(steps, sums, "f:real -> real", "g:real -> real", "d:real -> real", "a:real", "b:real", "s:real")
        .flatMap(rules.mp(_, agreement)).flatMap(rules.mp(_, onG))
      close <- rules.spec(s, bound).flatMap(rules.mp(_, onF))
      everySum <- rules.disch(onG.conclusion, close).flatMap(rules.gen(s, _))
      both <- rules.conjIntro(positiveGauge, everySum)
      gRight <- Term.destEq(openG.conclusion).map(_._2).toRight(NotOfForm("an equation", openG.conclusion))
      gAtE <- LogicError.lift(Kernel.assume(gRight)).flatMap(rules.spec(e, _))
      gExists <- steps.logic.destImp(gAtE.conclusion).map(_._2).toRight(NotOfForm("an implication", gAtE.conclusion))
      predicateG <- logic.destExistsPredicate(gExists).toRight(NotOfForm("an existential", gExists))
      witnessed <- rules.existsIntro(predicateG, d, both)
      found <- rules.existsElim(gauged, d, witnessed)
      statement <- rules.disch(positive, found).flatMap(rules.gen(e, _))
      folded <- Conv.sym(openG).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, statement)))
      result <- closeOver(steps, folded,
        List("has_integral (f:real -> real) a b i:real", Agreement),
        List("f:real -> real", "g:real -> real", "a:real", "b:real", "i:real"))
    } yield result
  }

  /**
   * `|- !g k a b t m. (!y. a <= y /\ y <= b ==> g y = k y) ==> a <= t ==> t <= b ==>
   *     derivative_within g a b t m ==> derivative_within k a b t m`
   */
  private def derivativeWithinCongruence(steps: Steps, held: Held): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val agreement = "!y:real. a:real <= y /\\ y <= b:real ==> (g:real -> real) y = (k:real -> real) y"
    for {
      g <- term(steps, "g:real -> real")
      k <- term(steps, "k:real -> real")
      a <- term(steps, "a:real")
      b <- term(steps, "b:real")
      t <- term(steps, "t:real")
      m <- term(steps, "m:real")
      e <- variable(steps, "e:real")
      d <- variable(steps, "d:real")
      z <- variable(steps, "z:real")
      agree <- assume(agreement)
      at0 <- assume("a:real <= t:real")
      tb <- assume("t:real <= b:real")
      slope <- assume("derivative_within (g:real -> real) a b t m:real")
      openG <- opened(held.withinDefinition, List(g, a, b, t, m))
      openK <- opened(held.withinDefinition, List(k, a, b, t, m))
      epsilons <- LogicError.lift(Kernel.eqMp(openG, slope))
      positive <- proposition("0 < e:real")
      p <- LogicError.lift(Kernel.assume(positive))
      radius <- rules.spec(e, epsilons).flatMap(rules.mp(_, p))
      body <- assume(
        "0 < d:real /\\ (!z:real. 0 < abs z /\\ abs z < d /\\ a:real <= t:real + z /\\ t + z <= b:real ==> " +
          "abs ((g:real -> real) (t + z) - g t - m:real * z) < e:real * abs z)")
      dPositive <- rules.conjElim1(body)
      near <- rules.conjElim2(body)
      condition <- proposition("0 < abs z:real /\\ abs z < d:real /\\ a:real <= t:real + z /\\ t + z <= b:real")
      c <- LogicError.lift(Kernel.assume(condition))
      value <- rules.spec(z, near).flatMap(rules.mp(_, c))
      moved <- rules.conjElim2(c).flatMap(rules.conjElim2)
      atMoved <- specialised(steps, agree, "t:real + z:real").flatMap(rules.mp(_, moved))
      member <- rules.conjIntro(at0, tb)
      atPoint <- specialised(steps, agree, "t:real").flatMap(rules.mp(_, member))
      read <- forward(steps, Vector(atMoved, atPoint), value)
      everyZ <- rules.disch(condition, read).flatMap(rules.gen(z, _))
      both <- rules.conjIntro(dPositive, everyZ)
      kRight <- Term.destEq(openK.conclusion).map(_._2).toRight(NotOfForm("an equation", openK.conclusion))
      kAtE <- LogicError.lift(Kernel.assume(kRight)).flatMap(rules.spec(e, _))
      kExists <- steps.logic.destImp(kAtE.conclusion).map(_._2).toRight(NotOfForm("an implication", kAtE.conclusion))
      predicate <- logic.destExistsPredicate(kExists).toRight(NotOfForm("an existential", kExists))
      witnessed <- rules.existsIntro(predicate, d, both)
      found <- rules.existsElim(radius, d, witnessed)
      statement <- rules.disch(positive, found).flatMap(rules.gen(e, _))
      folded <- Conv.sym(openK).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, statement)))
      result <- closeOver(steps, folded,
        List("derivative_within (g:real -> real) a b t m:real", "t:real <= b:real", "a:real <= t:real", agreement),
        List("g:real -> real", "k:real -> real", "a:real", "b:real", "t:real", "m:real"))
    } yield result
  }

  /* ------------------------------------------------------------------ the four forms */

  /** `!x. a <= x /\ x <= b ==> E x = f x`, from [[Continuity.ExtensionAgrees]]. */
  private def agreeing(steps: Steps, held: Held): Either[LogicError, Kernel.Thm] =
    List("f:real -> real", "a:real", "b:real").foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, text) =>
      for { found <- acc; next <- term(steps, text) } yield found :+ next
    }.flatMap(steps.rules.specPrefix(held.agrees, _)).flatMap(reduced)

  /** `!x. continuous E x` under `a <= b` and relative continuity, from [[Continuity.Extension]]. */
  private def extended(steps: Steps, held: Held): Either[LogicError, Kernel.Thm] =
    specialised(steps, held.extension, "f:real -> real", "a:real", "b:real")
      .flatMap(steps.mp(_, steps.assume("a:real <= b:real"), steps.assume(Relative)))

  /** `!x. p <= x /\ x <= q ==> continuous E x`, from the extension's continuity everywhere. */
  private def onInterval(steps: Steps, everywhere: Kernel.Thm, p: String, q: String): Either[LogicError, Kernel.Thm] =
    for {
      x <- variable(steps, "x:real")
      point <- steps.proposition(s"$p <= x:real /\\ x <= $q")
      result <- steps.rules.spec(x, everywhere).flatMap(steps.rules.disch(point, _)).flatMap(steps.rules.gen(x, _))
    } yield result

  /**
   * `|- !f a b. a <= b ==> (!x. a <= x /\ x <= b ==> continuous_within f a b x) ==>
   *     ?i. has_integral f a b i`
   */
  private def hasWithin(steps: Steps, held: Held, congruence: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      u <- variable(steps, "u:real")
      everywhere <- extended(steps, held)
      interval <- onInterval(steps, everywhere, "a:real", "b:real")
      exists <- specialised(steps, held.continuousHas, Extended, "a:real", "b:real")
        .flatMap(mp(_, assume("a:real <= b:real"), Right(interval)))
      onE <- assume(s"has_integral $Extended a b u:real").flatMap(reduced)
      agree <- agreeing(steps, held)
      onF <- specialised(steps, congruence, Extended, F, "a:real", "b:real", "u:real")
        .flatMap(rules.mp(_, agree)).flatMap(rules.mp(_, onE))
      witnessed <- existential(s"?i:real. has_integral $F a b i").flatMap(rules.existsIntro(_, u, onF))
      found <- rules.existsElim(exists, u, witnessed)
      result <- closeOver(steps, found, List(Relative, "a:real <= b:real"), List("f:real -> real", "a:real", "b:real"))
    } yield result
  }

  /**
   * `|- !f a b. a <= b ==> (!x. a <= x /\ x <= b ==> continuous_within f a b x) ==>
   *     has_integral f a b (integral f a b)`
   */
  private def integralWithin(steps: Steps, held: Held, has: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      i <- variable(steps, "i:real")
      exists <- specialised(steps, has, "f:real -> real", "a:real", "b:real")
        .flatMap(mp(_, assume("a:real <= b:real"), assume(Relative)))
      hi <- assume(s"has_integral $F a b i:real")
      named <- specialised(steps, held.unique, "f:real -> real", "a:real", "b:real", "i:real")
        .flatMap(mp(_, assume("a:real <= b:real"), Right(hi)))
      back <- Conv.sym(named)
      read <- moved(steps, s"\\t:real. has_integral $F a b t", back, hi)
      found <- rules.existsElim(exists, i, read)
      result <- closeOver(steps, found, List(Relative, "a:real <= b:real"), List("f:real -> real", "a:real", "b:real"))
    } yield result
  }

  /**
   * `|- !f a b t. (!x. a <= x /\ x <= b ==> continuous_within f a b x) ==> a <= t ==> t <= b ==>
   *     derivative_within (\y. integral f a y) a b t (f t)`
   */
  private def derivativeWithinWithin(steps: Steps, held: Held, congruence: Kernel.Thm, slopes: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      y <- variable(steps, "y:real")
      at0 <- assume("a:real <= t:real")
      tb <- assume("t:real <= b:real")
      ordered <- chain(steps, "a:real", "t:real", "b:real", at0, tb)
      everywhere <- extended(steps, held)
      interval <- onInterval(steps, everywhere, "a:real", "b:real")
      onE <- specialised(steps, held.derivativeWithin, Extended, "a:real", "b:real", "t:real")
        .flatMap(mp(_, Right(interval), Right(at0), Right(tb)))

      // the integrals of E and of f from a agree at every point of [a, b]
      ay <- assume("a:real <= y:real")
      yb <- assume("y:real <= b:real")
      toY <- onInterval(steps, everywhere, "a:real", "y:real")
      integralE <- specialised(steps, held.continuousIntegral, Extended, "a:real", "y:real").flatMap(mp(_, Right(ay), Right(toY)))
      agreeToY <- for {
        z <- variable(steps, "z:real")
        point <- proposition("a:real <= z:real /\\ z <= y:real")
        pz <- LogicError.lift(Kernel.assume(point))
        az <- rules.conjElim1(pz)
        zy <- rules.conjElim2(pz)
        zb <- chain(steps, "z:real", "y:real", "b:real", zy, yb)
        member <- rules.conjIntro(az, zb)
        value <- agreesWithin(steps, held.agrees, "z:real", member)
        result <- rules.disch(point, value).flatMap(rules.gen(z, _))
      } yield result
      integralF <- specialised(steps, congruence, Extended, F, "a:real", "y:real", s"integral $Extended a y")
        .flatMap(rules.mp(_, agreeToY)).flatMap(rules.mp(_, integralE))
      same <- specialised(steps, held.unique, F, "a:real", "y:real", s"integral $Extended a y")
        .flatMap(mp(_, Right(ay), Right(integralF))).flatMap(Conv.sym)
      point <- proposition("a:real <= y:real /\\ y <= b:real")
      py <- LogicError.lift(Kernel.assume(point))
      fromBoth <- rules.conjElim1(py).flatMap(rules.proveHyp(_, same))
        .flatMap(r => rules.conjElim2(py).flatMap(rules.proveHyp(_, r)))
      everyY <- rules.disch(point, fromBoth).flatMap(rules.gen(y, _))

      onF <- specialised(steps, slopes, s"\\y:real. integral $Extended a y", s"\\y:real. integral $F a y",
        "a:real", "b:real", "t:real", valueAt("t:real"))
        .flatMap(mp(_, Right(everyY), Right(at0), Right(tb), Right(onE)))
      member <- rules.conjIntro(at0, tb)
      atT <- agreesWithin(steps, held.agrees, "t:real", member)
      read <- moved(steps, s"\\q:real. derivative_within (\\y:real. integral $F a y) a b t q", atT, onF)
      withoutOrder <- rules.proveHyp(ordered, read)
      result <- closeOver(steps, withoutOrder,
        List("t:real <= b:real", "a:real <= t:real", Relative),
        List("f:real -> real", "a:real", "b:real", "t:real"))
    } yield result
  }

  /**
   * `|- !f a b t. (!x. a <= x /\ x <= b ==> continuous_within f a b x) ==> a < t ==> t < b ==>
   *     derivative (\y. integral f a y) t (f t)`
   */
  private def derivativeInteriorWithin(steps: Steps, held: Held, relative: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      below <- assume("a:real < t:real")
      above <- assume("t:real < b:real")
      atMost <- steps.at(lemma("!x:real y:real. x < y ==> x <= y"), "a:real", "t:real").flatMap(rules.mp(_, below))
      upTo <- steps.at(lemma("!x:real y:real. x < y ==> x <= y"), "t:real", "b:real").flatMap(rules.mp(_, above))
      slope <- specialised(steps, relative, "f:real -> real", "a:real", "b:real", "t:real")
        .flatMap(mp(_, assume(Relative), Right(atMost), Right(upTo)))
      result0 <- specialised(steps, held.withinInterior, s"\\y:real. integral $F a y", "a:real", "b:real", "t:real", s"$F t")
        .flatMap(mp(_, Right(below), Right(above), Right(slope)))
      result <- closeOver(steps, result0,
        List("t:real < b:real", "a:real < t:real", Relative),
        List("f:real -> real", "a:real", "b:real", "t:real"))
    } yield result
  }
}
