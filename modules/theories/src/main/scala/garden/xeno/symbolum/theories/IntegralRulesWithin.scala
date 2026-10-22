package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

import Continuity.Steps
import Within.{closeOver, forward, notBelow, aboveOf, reduced, term, variable}

/**
 * Integration by parts and the change of variables with the derivative relative to `[a, b]`, which
 * is how a textbook states them, and the lemma that carries a relative derivative to a two-sided one.
 * The change of variables comes twice: with `F` asked a slope everywhere, and with `F` asked it
 * only relative to an interval holding the image of `[a, b]`, where `F` is extended as `g` is.
 *
 * Not a development: `Integral` publishes what this derives, under names it declares.
 *
 * `HAS_INTEGRAL_PARTS` and `HAS_INTEGRAL_SUBST` ask `derivative f x (df x)` at every point of
 * `[a, b]`, and `derivative` is two-sided, so at the ends it asks about points outside the interval.
 * Card 3caa8541 is that excess, one notion over from the continuity card 6257d0da.
 *
 * == A tangent extension, rather than relative product and chain rules ==
 *
 * The two-sided rules are not proved again. A function with derivative `df x` relative to `[a, b]`
 * at every point of it is extended by its tangent lines past the ends:
 *
 * {{{
 *   T y = COND (y < a) (f a + df a * (y - a)) (COND (b < y) (f b + df b * (y - b)) (f y))
 * }}}
 *
 * and `DERIVATIVE_WITHIN_TANGENT` says `T` has the two-sided derivative `df x` at every point of
 * `[a, b]`. Inside the interval that is `DERIVATIVE_LOCAL`: `T` is `f` near the point, and a relative
 * derivative inside is a derivative. At an end it is two relative derivatives glued, one from each
 * side: the tangent line's on the outside, `f`'s on the inside, and at `a = b` two tangent lines of
 * one slope. The constant extension `Within` uses would not do here, since a constant beside `f`
 * has slope nought at the end and `f` need not.
 *
 * Each rule is then the two-sided one at the extensions, the integrand carried to and from them by
 * `HAS_INTEGRAL_CONGRUENCE`, since they agree with the functions on `[a, b]`, and the value read
 * back at the ends, where they agree too. The alternative, relative forms of the product and chain
 * rules, would be two epsilon-delta derivations that repeat the two-sided ones; the extension is one
 * lemma, and it is reusable for any rule stated with two-sided derivatives on an interval.
 */
private[theories] object IntegralRulesWithin {

  /** What the derivations read, by role. */
  final case class Held(
    reals: RealTheory,
    magnitude: Magnitude,
    classical: Classical,
    derivativeDefinition: Kernel.Thm,
    withinDefinition: Kernel.Thm,
    constant: Kernel.Thm,
    identity: Kernel.Thm,
    linear: Kernel.Thm,
    local: Kernel.Thm,
    interior: Kernel.Thm,
    ofDerivative: Kernel.Thm,
    withinCongruence: Kernel.Thm,
    hasCongruence: Kernel.Thm,
    hasParts: Kernel.Thm,
    hasSubstitution: Kernel.Thm,
    hasSubstitutionAtImage: Kernel.Thm
  )

  /** The tangent extension of `fn` with slopes `dfn` past `lo` and `hi`, as a lambda. */
  private[theories] def tangent(fn: String, dfn: String, lo: String = "a:real", hi: String = "b:real"): String =
    s"(\\y:real. COND (y < ($lo)) ($fn ($lo) + $dfn ($lo) * (y - ($lo))) (COND (($hi) < y) ($fn ($hi) + $dfn ($hi) * (y - ($hi))) ($fn y)))"

  /** The same at a point, reduced. */
  private def tangentAt(fn: String, dfn: String, u: String, lo: String = "a:real", hi: String = "b:real"): String =
    s"COND (($u) < ($lo)) ($fn ($lo) + $dfn ($lo) * (($u) - ($lo))) (COND (($hi) < ($u)) ($fn ($hi) + $dfn ($hi) * (($u) - ($hi))) ($fn ($u)))"

  private val F = "(f:real -> real)"
  private val DF = "(df:real -> real)"
  private val T = tangent(F, DF)
  private val Slopes = s"!y:real. a:real <= y /\\ y <= b:real ==> derivative_within $F a b y ($DF y)"

  /** The facts, by the names `Integral` publishes them under. */
  def prove(steps: Steps, held: Held): Either[LogicError, Map[String, Kernel.Thm]] =
    for {
      glued <- glue(steps, held)
      line <- lineSlope(steps, held)
      extension <- tangentSlope(steps, held, glued, line)
      parts <- partsWithin(steps, held, extension)
      substitution <- substitutionWithin(steps, held, extension)
      image <- substitutionImage(steps, held, extension)
    } yield Map(
      Integral.TangentSlope -> extension,
      Integral.HasPartsWithin -> parts,
      Integral.HasSubstitutionWithin -> substitution,
      Integral.HasSubstitutionImage -> image
    )

  /* ------------------------------------------------------------------ small parts */

  private def specialised(steps: Steps, theorem: Kernel.Thm, arguments: String*): Either[LogicError, Kernel.Thm] =
    arguments.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, text) =>
      for { found <- acc; next <- term(steps, text) } yield found :+ next
    }.flatMap(steps.rules.specAll(theorem, _)).flatMap(reduced)

  private def opened(definition: Kernel.Thm, arguments: List[Term]): Either[LogicError, Kernel.Thm] =
    for {
      equation <- Conv.unfold(definition, arguments)
      right <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
      normal <- Conv.betaNormalise(right)
      joined <- Conv.trans(equation, normal)
    } yield joined

  /** The existential's predicate at `witness`, reduced, as a term. */
  private def instanceOf(steps: Steps, existential: Term, witness: Term): Either[LogicError, Term] =
    for {
      predicate <- steps.logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
      applied <- LogicError.lift(Term.app(predicate, witness))
      equation <- Conv.betaNormalise(applied)
      result <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
    } yield result

  /** `P rhs` from `P lhs` and `lhs = rhs`, `P` a lambda written as text. */
  private def moved(steps: Steps, lambdaText: String, equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      lambda <- term(steps, lambdaText)
      both <- Conv.apTerm(lambda, equation).flatMap(Conv.betaSides)
      result <- LogicError.lift(Kernel.eqMp(both, theorem))
    } yield result

  /** `0 < min u v` from `0 < u` and `0 < v`. */
  private def minPositive(steps: Steps, held: Held, u: String, v: String, pu: Kernel.Thm, pv: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val rule = "!w:real u:real. w = u ==> 0 < u ==> 0 < w"
    for {
      minCases <- held.magnitude.fact(Magnitude.MinCases)
      cases <- specialised(steps, minCases, u, v)
      left <- assume(s"min ($u) ($v) = $u").flatMap(eq => steps.at(lemma(rule), s"min ($u) ($v)", u).flatMap(mp(_, Right(eq), Right(pu))))
      right <- assume(s"min ($u) ($v) = $v").flatMap(eq => steps.at(lemma(rule), s"min ($u) ($v)", v).flatMap(mp(_, Right(eq), Right(pv))))
      result <- rules.disjElim(cases, left, right)
    } yield result
  }

  /** A case split on `p`, over the excluded middle. */
  private def split(steps: Steps, held: Held, p: String)(yes: Kernel.Thm => Either[LogicError, Kernel.Thm], no: Kernel.Thm => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      proposition <- steps.proposition(p)
      middle <- held.classical.fact(Classical.ExcludedMiddle).flatMap(rules.spec(proposition, _))
      negated <- logic.mkNot(proposition)
      whenYes <- LogicError.lift(Kernel.assume(proposition)).flatMap(yes)
      whenNo <- LogicError.lift(Kernel.assume(negated)).flatMap(no)
      result <- rules.disjElim(middle, whenYes, whenNo)
    } yield result
  }

  /* ------------------------------------------------------------------ gluing two sides */

  /**
   * `|- !h p q x m. p < x ==> x < q ==> derivative_within h p x x m ==> derivative_within h x q x m ==>
   *     derivative h x m`
   *
   * A derivative from the left and one from the right, of one slope, are a derivative. The radius is
   * the smaller of the two, cut to the two intervals so that an increment on either side stays in
   * its interval.
   */
  private def glue(steps: Steps, held: Held): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val magnitude = held.magnitude
    val r = "min (min d1 d2) (min (x - p) (q - x))"
    for {
      belowLeft <- magnitude.fact(Magnitude.MinBelowLeft)
      belowRight <- magnitude.fact(Magnitude.MinBelowRight)
      h <- term(steps, "h:real -> real")
      p <- term(steps, "p:real")
      q <- term(steps, "q:real")
      x <- term(steps, "x:real")
      m <- term(steps, "m:real")
      e <- variable(steps, "e:real")
      d1 <- variable(steps, "d1:real")
      d2 <- variable(steps, "d2:real")
      d <- term(steps, r)
      yv <- variable(steps, "y:real")
      px <- assume("p:real < x:real")
      xq <- assume("x:real < q:real")
      left <- assume("derivative_within (h:real -> real) p x x m:real")
      right <- assume("derivative_within (h:real -> real) x q x m:real")
      openL <- opened(held.withinDefinition, List(h, p, x, x, m))
      openR <- opened(held.withinDefinition, List(h, x, q, x, m))
      openD <- opened(held.derivativeDefinition, List(h, x, m))
      positive <- proposition("0 < e:real")
      pe <- LogicError.lift(Kernel.assume(positive))
      fromL <- LogicError.lift(Kernel.eqMp(openL, left)).flatMap(rules.spec(e, _)).flatMap(rules.mp(_, pe))
      fromR <- LogicError.lift(Kernel.eqMp(openR, right)).flatMap(rules.spec(e, _)).flatMap(rules.mp(_, pe))
      bodyLText <- instanceOf(steps, fromL.conclusion, d1)
      bodyRText <- instanceOf(steps, fromR.conclusion, d2)
      bodyL <- LogicError.lift(Kernel.assume(bodyLText))
      bodyR <- LogicError.lift(Kernel.assume(bodyRText))
      d1Positive <- rules.conjElim1(bodyL)
      d2Positive <- rules.conjElim1(bodyR)
      nearL <- rules.conjElim2(bodyL)
      nearR <- rules.conjElim2(bodyR)
      xp <- steps.at(lemma("!p:real x:real. p < x ==> 0 < x - p"), "p:real", "x:real").flatMap(mp(_, Right(px)))
      qx <- steps.at(lemma("!x:real q:real. x < q ==> 0 < q - x"), "x:real", "q:real").flatMap(mp(_, Right(xq)))
      dd <- minPositive(steps, held, "d1:real", "d2:real", d1Positive, d2Positive)
      ends <- minPositive(steps, held, "x:real - p:real", "q:real - x:real", xp, qx)
      rPositive <- minPositive(steps, held, "min (d1:real) (d2:real)", "min (x:real - p:real) (q:real - x:real)", dd, ends)
      trans = "!u:real v:real w:real. u <= v ==> v <= w ==> u <= w"
      toDD <- specialised(steps, belowLeft, "min (d1:real) (d2:real)", "min (x:real - p:real) (q:real - x:real)")
      toEnds <- specialised(steps, belowRight, "min (d1:real) (d2:real)", "min (x:real - p:real) (q:real - x:real)")
      ddD1 <- specialised(steps, belowLeft, "d1:real", "d2:real")
      ddD2 <- specialised(steps, belowRight, "d1:real", "d2:real")
      endsP <- specialised(steps, belowLeft, "x:real - p:real", "q:real - x:real")
      endsQ <- specialised(steps, belowRight, "x:real - p:real", "q:real - x:real")
      rD1 <- steps.at(lemma(trans), r, "min (d1:real) (d2:real)", "d1:real").flatMap(mp(_, Right(toDD), Right(ddD1)))
      rD2 <- steps.at(lemma(trans), r, "min (d1:real) (d2:real)", "d2:real").flatMap(mp(_, Right(toDD), Right(ddD2)))
      rP <- steps.at(lemma(trans), r, "min (x:real - p:real) (q:real - x:real)", "x:real - p:real").flatMap(mp(_, Right(toEnds), Right(endsP)))
      rQ <- steps.at(lemma(trans), r, "min (x:real - p:real) (q:real - x:real)", "q:real - x:real").flatMap(mp(_, Right(toEnds), Right(endsQ)))

      condition <- proposition(s"0 < abs y:real /\\ abs y < $r")
      c <- LogicError.lift(Kernel.assume(condition))
      nonZero <- rules.conjElim1(c)
      small <- rules.conjElim2(c)
      sided <- ExtremeValue.sides(steps, magnitude, "y:real", r, small)
      (up, down) = sided
      below = "!a:real r:real d:real. a < r ==> r <= d ==> a < d"
      value <- split(steps, held, "y:real < 0")(
        negative =>
          for {
            pLow <- steps.at(lemma("!y:real r:real x:real p:real. -y < r ==> r <= x - p ==> p <= x + y"), "y:real", r, "x:real", "p:real")
              .flatMap(mp(_, Right(down), Right(rP)))
            xHigh <- steps.at(lemma("!x:real y:real. y < 0 ==> x + y <= x"), "x:real", "y:real").flatMap(mp(_, Right(negative)))
            inD1 <- steps.at(lemma(below), "abs (y:real)", r, "d1:real").flatMap(mp(_, Right(small), Right(rD1)))
            all <- conj(Right(nonZero), conj(Right(inD1), conj(Right(pLow), Right(xHigh))))
            result <- rules.spec(yv, nearL).flatMap(rules.mp(_, all))
          } yield result,
        notNegative =>
          for {
            atLeast <- aboveOf(steps, magnitude, "y:real", "0", notNegative)
            xLow <- steps.at(lemma("!x:real y:real. 0 <= y ==> x <= x + y"), "x:real", "y:real").flatMap(mp(_, Right(atLeast)))
            qHigh <- steps.at(lemma("!y:real r:real q:real x:real. y < r ==> r <= q - x ==> x + y <= q"), "y:real", r, "q:real", "x:real")
              .flatMap(mp(_, Right(up), Right(rQ)))
            inD2 <- steps.at(lemma(below), "abs (y:real)", r, "d2:real").flatMap(mp(_, Right(small), Right(rD2)))
            all <- conj(Right(nonZero), conj(Right(inD2), conj(Right(xLow), Right(qHigh))))
            result <- rules.spec(yv, nearR).flatMap(rules.mp(_, all))
          } yield result
      )
      everyY <- rules.disch(condition, value).flatMap(rules.gen(yv, _))
      both <- rules.conjIntro(rPositive, everyY)
      dRight <- Term.destEq(openD.conclusion).map(_._2).toRight(NotOfForm("an equation", openD.conclusion))
      dAtE <- LogicError.lift(Kernel.assume(dRight)).flatMap(rules.spec(e, _))
      dExists <- logic.destImp(dAtE.conclusion).map(_._2).toRight(NotOfForm("an implication", dAtE.conclusion))
      predicate <- logic.destExistsPredicate(dExists).toRight(NotOfForm("an existential", dExists))
      witnessed <- rules.existsIntro(predicate, d, both)
      dropR <- rules.existsElim(fromR, d2, witnessed)
      dropL <- rules.existsElim(fromL, d1, dropR)
      statement <- rules.disch(positive, dropL).flatMap(rules.gen(e, _))
      folded <- Conv.sym(openD).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, statement)))
      result <- closeOver(steps, folded,
        List("derivative_within (h:real -> real) x q x m:real", "derivative_within (h:real -> real) p x x m:real",
          "x:real < q:real", "p:real < x:real"),
        List("h:real -> real", "p:real", "q:real", "x:real", "m:real"))
    } yield result
  }

  /* ------------------------------------------------------------------ the tangent line */

  /** `|- !c m p x. derivative (\y. c + m * (y - p)) x m`, from the constant, the identity and linearity. */
  private def lineSlope(steps: Steps, held: Held): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      u <- variable(steps, "u:real")
      one <- specialised(steps, held.constant, "1:real", "x:real")
      itself <- specialised(steps, held.identity, "x:real")
      combined <- specialised(steps, held.linear, "\\z:real. (1:real)", "\\y:real. y", "x:real", "0:real", "1:real",
        "c:real - m:real * p:real", "m:real").flatMap(mp(_, Right(one), Right(itself)))
      pointwise <- steps.at(lemma("!c:real m:real p:real u:real. c + m * (u - p) = (c - m * p) * 1 + m * u"),
        "c:real", "m:real", "p:real", "u:real")
      near <- proposition("abs (u:real - x:real) < 1")
      everyU <- rules.disch(near, pointwise).flatMap(rules.gen(u, _))
      localised <- specialised(steps, held.local, "\\w:real. (c:real - m:real * p:real) * 1 + m * w",
        "\\y:real. c:real + m:real * (y - p:real)", "x:real", "(c:real - m:real * p:real) * 0 + m * 1", "1:real")
        .flatMap(mp(_, lemma("(0:real) < 1"), Right(everyU), Right(combined)))
      slope <- steps.at(lemma("!c:real m:real p:real. (c - m * p) * 0 + m * 1 = m"), "c:real", "m:real", "p:real")
      result0 <- moved(steps, "\\s:real. derivative (\\y:real. c:real + m:real * (y - p:real)) x:real s", slope, localised)
      result <- closeOver(steps, result0, Nil, List("c:real", "m:real", "p:real", "x:real"))
    } yield result
  }

  /* ------------------------------------------------------------------ the extension's slope */

  /**
   * `|- !f df a b x. (!y. a <= y /\ y <= b ==> derivative_within f a b y (df y)) ==>
   *     a <= x ==> x <= b ==> derivative T x (df x)`, `T` the tangent extension. `a <= b` is not
   *     asked: it follows from the point's two bounds, and the derivation reads it off them.
   */
  private def tangentSlope(steps: Steps, held: Held, glued: Kernel.Thm, line: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val reals = held.reals
    val condTrue = Within.condition(held.classical, Classical.CondTrue)
    val condFalse = Within.condition(held.classical, Classical.CondFalse)

    // `T u = f u` for `a <= u` and `u <= b`.
    def inside(u: String, au: Kernel.Thm, ub: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        notLeft <- notBelow(steps, reals, u, "a:real", au)
        notRight <- notBelow(steps, reals, "b:real", u, ub)
        cf <- condFalse
        outer <- specialised(steps, cf, s"$u < a:real", s"$F a + $DF a * ($u - a:real)",
          s"COND (b:real < $u) ($F b + $DF b * ($u - b)) ($F $u)").flatMap(rules.mp(_, notLeft))
        inner <- specialised(steps, cf, s"b:real < $u", s"$F b + $DF b * ($u - b:real)", s"$F $u").flatMap(rules.mp(_, notRight))
        joined <- Conv.trans(outer, inner)
      } yield joined

    // `T u = f a + df a * (u - a)` for `u < a`.
    def leftOf(u: String, ua: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      condTrue.flatMap(ct => specialised(steps, ct, s"$u < a:real", s"$F a + $DF a * ($u - a:real)",
        s"COND (b:real < $u) ($F b + $DF b * ($u - b)) ($F $u)")).flatMap(rules.mp(_, ua))

    // `T u = f b + df b * (u - b)` for `b < u`, under `a <= b`.
    def rightOf(u: String, bu: Kernel.Thm, ab: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        au <- steps.at(lemma("!a:real b:real u:real. a <= b ==> b < u ==> a <= u"), "a:real", "b:real", u).flatMap(mp(_, Right(ab), Right(bu)))
        notLeft <- notBelow(steps, reals, u, "a:real", au)
        cf <- condFalse
        ct <- condTrue
        outer <- specialised(steps, cf, s"$u < a:real", s"$F a + $DF a * ($u - a:real)",
          s"COND (b:real < $u) ($F b + $DF b * ($u - b)) ($F $u)").flatMap(rules.mp(_, notLeft))
        inner <- specialised(steps, ct, s"b:real < $u", s"$F b + $DF b * ($u - b:real)", s"$F $u").flatMap(rules.mp(_, bu))
        joined <- Conv.trans(outer, inner)
      } yield joined

    // `derivative_within T lo hi z s` from the same of `g`, which equals `T` on `[lo, hi]`.
    def carried(g: String, lo: String, hi: String, z: String, s: String, agree: Kernel.Thm, loZ: Kernel.Thm, zHi: Kernel.Thm, slope: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      specialised(steps, held.withinCongruence, g, T, lo, hi, z, s).flatMap(mp(_, Right(agree), Right(loZ), Right(zHi), Right(slope)))

    // the line through `(p, f p)` of slope `df p`, as a lambda
    def lineAt(p: String): String = s"\\y:real. $F $p + $DF $p * (y - $p)"

    // `derivative_within T (a - 1) a a (df a)`, from the tangent line at `a`, under `a <= b`
    def fromTheLeft(ab: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        yv <- variable(steps, "y:real")
        slope <- specialised(steps, line, s"$F a:real", s"$DF a:real", "a:real", "a:real")
        relative <- specialised(steps, held.ofDerivative, lineAt("a:real"), "a:real - 1", "a:real", "a:real", s"$DF a:real")
          .flatMap(rules.mp(_, slope))
        member <- proposition("a:real - 1 <= y:real /\\ y <= a")
        pm <- LogicError.lift(Kernel.assume(member))
        agreeY <- split(steps, held, "y:real < a:real")(
          below => leftOf("y:real", below).flatMap(Conv.sym),
          notBelowIt => for {
            ya <- rules.conjElim2(pm)
            ay <- aboveOf(steps, held.magnitude, "y:real", "a:real", notBelowIt)
            same <- steps.at(lemma("!a:real y:real. a <= y ==> y <= a ==> y = a"), "a:real", "y:real").flatMap(mp(_, Right(ay), Right(ya)))
            yb <- steps.at(lemma("!y:real a:real b:real. y <= a ==> a <= b ==> y <= b"), "y:real", "a:real", "b:real").flatMap(mp(_, Right(ya), Right(ab)))
            atT <- inside("y:real", ay, yb)
            atEnd <- steps.at(lemma("!c:real m:real p:real. c + m * (p - p) = c"), s"$F a:real", s"$DF a:real", "a:real")
            toY <- Conv.sym(same)
            flat <- moved(steps, s"\\t:real. $F a:real + $DF a * (t - a) = $F a", toY, atEnd)
            back <- Conv.sym(same)
            fy <- term(steps, s"$F a:real").flatMap(t => moved(steps, s"\\t:real. $F a:real = $F t", back, Kernel.refl(t)))
            lineIsF <- Conv.trans(flat, fy)
            fromT <- Conv.sym(atT)
            result <- Conv.trans(lineIsF, fromT)
          } yield result
        )
        agree <- rules.disch(member, agreeY).flatMap(rules.gen(yv, _))
        low <- steps.at(lemma("!a:real. a - 1 <= a"), "a:real")
        self <- steps.at(lemma("!a:real. a <= a"), "a:real")
        result <- carried(lineAt("a:real"), "a:real - 1", "a:real", "a:real", s"$DF a:real", agree, low, self, relative)
      } yield result

    // `derivative_within T b (b + 1) b (df b)`, from the tangent line at `b`, under `a <= b`
    def fromTheRight(ab: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        yv <- variable(steps, "y:real")
        slope <- specialised(steps, line, s"$F b:real", s"$DF b:real", "b:real", "b:real")
        relative <- specialised(steps, held.ofDerivative, lineAt("b:real"), "b:real", "b:real + 1", "b:real", s"$DF b:real")
          .flatMap(rules.mp(_, slope))
        member <- proposition("b:real <= y:real /\\ y <= b + 1")
        pm <- LogicError.lift(Kernel.assume(member))
        agreeY <- split(steps, held, "b:real < y:real")(
          above => rightOf("y:real", above, ab).flatMap(Conv.sym),
          notAbove => for {
            by <- rules.conjElim1(pm)
            yb <- aboveOf(steps, held.magnitude, "b:real", "y:real", notAbove)
            same <- steps.at(lemma("!b:real y:real. b <= y ==> y <= b ==> y = b"), "b:real", "y:real").flatMap(mp(_, Right(by), Right(yb)))
            ay <- steps.at(lemma("!a:real b:real y:real. a <= b ==> b <= y ==> a <= y"), "a:real", "b:real", "y:real").flatMap(mp(_, Right(ab), Right(by)))
            atT <- inside("y:real", ay, yb)
            atEnd <- steps.at(lemma("!c:real m:real p:real. c + m * (p - p) = c"), s"$F b:real", s"$DF b:real", "b:real")
            toY <- Conv.sym(same)
            flat <- moved(steps, s"\\t:real. $F b:real + $DF b * (t - b) = $F b", toY, atEnd)
            back <- Conv.sym(same)
            fy <- term(steps, s"$F b:real").flatMap(t => moved(steps, s"\\t:real. $F b:real = $F t", back, Kernel.refl(t)))
            lineIsF <- Conv.trans(flat, fy)
            fromT <- Conv.sym(atT)
            result <- Conv.trans(lineIsF, fromT)
          } yield result
        )
        agree <- rules.disch(member, agreeY).flatMap(rules.gen(yv, _))
        self <- steps.at(lemma("!b:real. b <= b"), "b:real")
        high <- steps.at(lemma("!b:real. b <= b + 1"), "b:real")
        result <- carried(lineAt("b:real"), "b:real", "b:real + 1", "b:real", s"$DF b:real", agree, self, high, relative)
      } yield result

    // `derivative_within T a b z (df z)` for `z` in `[a, b]`, from `f`'s
    def fromInside(z: String, az: Kernel.Thm, zb: Kernel.Thm, slopes: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        yv <- variable(steps, "y:real")
        member <- proposition("a:real <= y:real /\\ y <= b:real")
        pm <- LogicError.lift(Kernel.assume(member))
        ay <- rules.conjElim1(pm)
        yb <- rules.conjElim2(pm)
        atY <- inside("y:real", ay, yb).flatMap(Conv.sym)
        agree <- rules.disch(member, atY).flatMap(rules.gen(yv, _))
        both <- rules.conjIntro(az, zb)
        relative <- specialised(steps, slopes, z).flatMap(rules.mp(_, both))
        result <- carried(F, "a:real", "b:real", z, s"$DF $z", agree, az, zb, relative)
      } yield result

    for {
      slopes <- assume(Slopes)
      ax <- assume("a:real <= x:real")
      xb <- assume("x:real <= b:real")
      ab <- steps.at(lemma("!a:real x:real b:real. a <= x ==> x <= b ==> a <= b"), "a:real", "x:real", "b:real")
        .flatMap(mp(_, Right(ax), Right(xb)))
      target = s"\\t:real. derivative $T t ($DF t)"
      result0 <- split(steps, held, "a:real < x:real")(
        strictlyAbove =>
          split(steps, held, "x:real < b:real")(
            strictlyBelow =>
              // inside: T is f near x, and f's relative derivative there is a derivative
              for {
                belowLeft <- held.magnitude.fact(Magnitude.MinBelowLeft)
                belowRight <- held.magnitude.fact(Magnitude.MinBelowRight)
                uv <- variable(steps, "u:real")
                relative <- specialised(steps, slopes, "x:real").flatMap(r => rules.conjIntro(ax, xb).flatMap(rules.mp(r, _)))
                twoSided <- specialised(steps, held.interior, F, "a:real", "b:real", "x:real", s"$DF x:real")
                  .flatMap(mp(_, Right(strictlyAbove), Right(strictlyBelow), Right(relative)))
                r = "min (x:real - a:real) (b:real - x:real)"
                xa <- steps.at(lemma("!a:real x:real. a < x ==> 0 < x - a"), "a:real", "x:real").flatMap(mp(_, Right(strictlyAbove)))
                bx <- steps.at(lemma("!x:real b:real. x < b ==> 0 < b - x"), "x:real", "b:real").flatMap(mp(_, Right(strictlyBelow)))
                rPositive <- minPositive(steps, held, "x:real - a:real", "b:real - x:real", xa, bx)
                near <- proposition(s"abs (u:real - x:real) < $r")
                pn <- LogicError.lift(Kernel.assume(near))
                sided <- ExtremeValue.sides(steps, held.magnitude, "u:real - x:real", r, pn)
                toA <- specialised(steps, belowLeft, "x:real - a:real", "b:real - x:real")
                toB <- specialised(steps, belowRight, "x:real - a:real", "b:real - x:real")
                au <- steps.at(lemma("!u:real x:real r:real a:real. -(u - x) < r ==> r <= x - a ==> a <= u"), "u:real", "x:real", r, "a:real")
                  .flatMap(mp(_, Right(sided._2), Right(toA)))
                ub <- steps.at(lemma("!u:real x:real r:real b:real. u - x < r ==> r <= b - x ==> u <= b"), "u:real", "x:real", r, "b:real")
                  .flatMap(mp(_, Right(sided._1), Right(toB)))
                atU <- inside("u:real", au, ub)
                everyU <- rules.disch(near, atU).flatMap(rules.gen(uv, _))
                result <- specialised(steps, held.local, F, T, "x:real", s"$DF x:real", r)
                  .flatMap(mp(_, Right(rPositive), Right(everyU), Right(twoSided)))
              } yield result,
            notBelowB =>
              // x = b, and a < b: f's side on the left, the tangent line at b on the right
              for {
                bx <- aboveOf(steps, held.magnitude, "x:real", "b:real", notBelowB)
                same <- steps.at(lemma("!x:real b:real. x <= b ==> b <= x ==> x = b"), "x:real", "b:real").flatMap(mp(_, Right(xb), Right(bx)))
                ab2 <- steps.at(lemma("!a:real x:real b:real. a < x ==> x = b ==> a < b"), "a:real", "x:real", "b:real").flatMap(mp(_, Right(strictlyAbove), Right(same)))
                self <- steps.at(lemma("!b:real. b <= b"), "b:real")
                left <- fromInside("b:real", ab, self, slopes)
                right <- fromTheRight(ab)
                oneMore <- steps.at(lemma("!b:real. b < b + 1"), "b:real")
                atB <- specialised(steps, glued, T, "a:real", "b:real + 1", "b:real", s"$DF b:real")
                  .flatMap(mp(_, Right(ab2), Right(oneMore), Right(left), Right(right)))
                back <- Conv.sym(same)
                result <- moved(steps, target, back, atB)
              } yield result
          ),
        notAboveA =>
          // x = a: the tangent line at a on the left, and on the right f's side when a < b or the
          // tangent line at b, of the same slope, when a = b
          for {
            xa <- aboveOf(steps, held.magnitude, "a:real", "x:real", notAboveA)
            same <- steps.at(lemma("!a:real x:real. a <= x ==> x <= a ==> x = a"), "a:real", "x:real").flatMap(mp(_, Right(ax), Right(xa)))
            left <- fromTheLeft(ab)
            below <- steps.at(lemma("!a:real. a - 1 < a"), "a:real")
            atA <- split(steps, held, "a:real < b:real")(
              strictly =>
                for {
                  self <- steps.at(lemma("!a:real. a <= a"), "a:real")
                  right <- fromInside("a:real", self, ab, slopes)
                  result <- specialised(steps, glued, T, "a:real - 1", "b:real", "a:real", s"$DF a:real")
                    .flatMap(mp(_, Right(below), Right(strictly), Right(left), Right(right)))
                } yield result,
              notStrictly =>
                for {
                  ba <- aboveOf(steps, held.magnitude, "a:real", "b:real", notStrictly)
                  equal <- steps.at(lemma("!a:real b:real. a <= b ==> b <= a ==> b = a"), "a:real", "b:real").flatMap(mp(_, Right(ab), Right(ba)))
                  right <- fromTheRight(ab)
                  // at a = b the right side is at b; move it to a, point and slope
                  lambda = s"\\z:real. derivative_within $T z (z + 1) z ($DF z)"
                  atA <- moved(steps, lambda, equal, right)
                  oneMore <- steps.at(lemma("!a:real. a < a + 1"), "a:real")
                  result <- specialised(steps, glued, T, "a:real - 1", "a:real + 1", "a:real", s"$DF a:real")
                    .flatMap(mp(_, Right(below), Right(oneMore), Right(left), Right(atA)))
                } yield result
            )
            back <- Conv.sym(same)
            result <- moved(steps, target, back, atA)
          } yield result
      )
      result <- closeOver(steps, result0, List("x:real <= b:real", "a:real <= x:real", Slopes),
        List("f:real -> real", "df:real -> real", "a:real", "b:real", "x:real"))
    } yield result
  }

  /* ------------------------------------------------------------------ the two rules */

  /**
   * `T x = f x` for every `x` in `[lo, hi]`, at the tangent extension of `fn` with slopes `dfn` past
   * `lo` and `hi`.
   */
  private def agreesOn(steps: Steps, held: Held, fn: String, dfn: String, lo: String = "a:real", hi: String = "b:real"): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val condFalse = Within.condition(held.classical, Classical.CondFalse)
    for {
      xv <- variable(steps, "x:real")
      member <- proposition(s"($lo) <= x:real /\\ x <= ($hi)")
      pm <- LogicError.lift(Kernel.assume(member))
      ax <- rules.conjElim1(pm)
      xb <- rules.conjElim2(pm)
      notLeft <- notBelow(steps, held.reals, "x:real", lo, ax)
      notRight <- notBelow(steps, held.reals, hi, "x:real", xb)
      cf <- condFalse
      outer <- specialised(steps, cf, s"x:real < ($lo)", s"$fn ($lo) + $dfn ($lo) * (x:real - ($lo))",
        s"COND (($hi) < x:real) ($fn ($hi) + $dfn ($hi) * (x - ($hi))) ($fn x)").flatMap(rules.mp(_, notLeft))
      inner <- specialised(steps, cf, s"($hi) < x:real", s"$fn ($hi) + $dfn ($hi) * (x:real - ($hi))", s"$fn x:real").flatMap(rules.mp(_, notRight))
      joined <- Conv.trans(outer, inner)
      result <- rules.disch(member, joined).flatMap(rules.gen(xv, _))
    } yield result
  }

  /** `!x. a <= x /\ x <= b ==> derivative T x (dfn x)`, from the relative slopes of `fn`. */
  private def extendedSlopes(steps: Steps, extension: Kernel.Thm, fn: String, dfn: String, relative: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      xv <- variable(steps, "x:real")
      member <- proposition("a:real <= x:real /\\ x <= b:real")
      pm <- LogicError.lift(Kernel.assume(member))
      ax <- rules.conjElim1(pm)
      xb <- rules.conjElim2(pm)
      slope <- specialised(steps, extension, fn, dfn, "a:real", "b:real", "x:real")
        .flatMap(mp(_, Right(relative), Right(ax), Right(xb)))
      result <- rules.disch(member, slope).flatMap(rules.gen(xv, _))
    } yield result
  }

  private val PartsRelative = List(
    "a:real <= b:real",
    "!x:real. a:real <= x /\\ x <= b:real ==> derivative_within (f:real -> real) a b x ((df:real -> real) x)",
    "!x:real. a:real <= x /\\ x <= b:real ==> derivative_within (g:real -> real) a b x ((dg:real -> real) x)",
    "has_integral (\\x:real. (f:real -> real) x * (dg:real -> real) x) a b i")

  /**
   * `|- !f g df dg a b i. a <= b ==> (!x. a <= x /\ x <= b ==> derivative_within f a b x (df x)) ==>
   *     (!x. ... derivative_within g a b x (dg x)) ==> has_integral (\x. f x * dg x) a b i ==>
   *     has_integral (\x. df x * g x) a b (f b * g b - f a * g a - i)`
   */
  private def partsWithin(steps: Steps, held: Held, extension: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val (fn, dfn, gn, dgn) = ("(f:real -> real)", "(df:real -> real)", "(g:real -> real)", "(dg:real -> real)")
    val tf = tangent(fn, dfn)
    val tg = tangent(gn, dgn)
    for {
      assumed <- PartsRelative.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (acc, text) =>
        for { done <- acc; one <- assume(text) } yield done :+ one
      }
      ab = assumed(0)
      slopesF <- extendedSlopes(steps, extension, fn, dfn, assumed(1))
      slopesG <- extendedSlopes(steps, extension, gn, dgn, assumed(2))
      agreeF <- agreesOn(steps, held, fn, dfn)
      agreeG <- agreesOn(steps, held, gn, dgn)
      xv <- variable(steps, "x:real")
      // the integrand, carried to the extension of f
      toExtension <- for {
        member <- proposition("a:real <= x:real /\\ x <= b:real")
        pm <- LogicError.lift(Kernel.assume(member))
        atX <- rules.spec(xv, agreeF).flatMap(rules.mp(_, pm)).flatMap(Conv.sym)
        product <- term(steps, s"$fn x:real * $dgn x")
        timesDg <- moved(steps, s"\\t:real. $fn x:real * $dgn x = t * $dgn x", atX, Kernel.refl(product))
        r <- rules.disch(member, timesDg).flatMap(rules.gen(xv, _))
      } yield r
      integrand <- specialised(steps, held.hasCongruence, s"\\x:real. $fn x * $dgn x", s"\\x:real. ${tangentAt(fn, dfn, "x")} * $dgn x",
        "a:real", "b:real", "i:real").flatMap(mp(_, Right(toExtension), Right(assumed(3))))
      rule <- specialised(steps, held.hasParts, tf, tg, dfn, dgn, "a:real", "b:real", "i:real")
        .flatMap(mp(_, Right(ab), Right(slopesF), Right(slopesG), Right(integrand)))
      // and back from the extension of g
      fromExtension <- for {
        member <- proposition("a:real <= x:real /\\ x <= b:real")
        pm <- LogicError.lift(Kernel.assume(member))
        atX <- rules.spec(xv, agreeG).flatMap(rules.mp(_, pm))
        product <- term(steps, s"$dfn x:real * ${tangentAt(gn, dgn, "x:real")}")
        timesDf <- moved(steps, s"\\t:real. $dfn x:real * ${tangentAt(gn, dgn, "x:real")} = $dfn x * t", atX, Kernel.refl(product))
        r <- rules.disch(member, timesDf).flatMap(rules.gen(xv, _))
      } yield r
      onG <- specialised(steps, held.hasCongruence, s"\\x:real. $dfn x * ${tangentAt(gn, dgn, "x")}", s"\\x:real. $dfn x * $gn x",
        "a:real", "b:real", s"${tangentAt(fn, dfn, "b:real")} * ${tangentAt(gn, dgn, "b:real")} - ${tangentAt(fn, dfn, "a:real")} * ${tangentAt(gn, dgn, "a:real")} - i:real")
        .flatMap(mp(_, Right(fromExtension), Right(rule)))
      aa <- steps.at(lemma("!a:real. a <= a"), "a:real")
      bb <- steps.at(lemma("!b:real. b <= b"), "b:real")
      atAF <- specialised(steps, agreeF, "a:real").flatMap(r => rules.conjIntro(aa, ab).flatMap(rules.mp(r, _)))
      atBF <- specialised(steps, agreeF, "b:real").flatMap(r => rules.conjIntro(ab, bb).flatMap(rules.mp(r, _)))
      atAG <- specialised(steps, agreeG, "a:real").flatMap(r => rules.conjIntro(aa, ab).flatMap(rules.mp(r, _)))
      atBG <- specialised(steps, agreeG, "b:real").flatMap(r => rules.conjIntro(ab, bb).flatMap(rules.mp(r, _)))
      read <- forward(steps, Vector(atAF, atBF, atAG, atBG), onG)
      result <- closeOver(steps, read, PartsRelative.reverse,
        List("f:real -> real", "g:real -> real", "df:real -> real", "dg:real -> real", "a:real", "b:real", "i:real"))
    } yield result
  }

  private val SubstitutionRelative = List(
    "a:real <= b:real",
    "!y:real. derivative (Fn:real -> real) y ((f:real -> real) y)",
    "!x:real. a:real <= x /\\ x <= b:real ==> derivative_within (g:real -> real) a b x ((dg:real -> real) x)")

  /**
   * `|- !F f g dg a b. a <= b ==> (!y. derivative F y (f y)) ==>
   *     (!x. a <= x /\ x <= b ==> derivative_within g a b x (dg x)) ==>
   *     has_integral (\x. f (g x) * dg x) a b (F (g b) - F (g a))`
   */
  private def substitutionWithin(steps: Steps, held: Held, extension: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val (bigF, fn, gn, dgn) = ("(Fn:real -> real)", "(f:real -> real)", "(g:real -> real)", "(dg:real -> real)")
    val tg = tangent(gn, dgn)
    for {
      assumed <- SubstitutionRelative.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (acc, text) =>
        for { done <- acc; one <- assume(text) } yield done :+ one
      }
      ab = assumed(0)
      slopesG <- extendedSlopes(steps, extension, gn, dgn, assumed(2))
      rule <- specialised(steps, held.hasSubstitution, bigF, fn, tg, dgn, "a:real", "b:real")
        .flatMap(mp(_, Right(ab), Right(assumed(1)), Right(slopesG)))
      agreeG <- agreesOn(steps, held, gn, dgn)
      xv <- variable(steps, "x:real")
      back <- for {
        member <- proposition("a:real <= x:real /\\ x <= b:real")
        pm <- LogicError.lift(Kernel.assume(member))
        atX <- rules.spec(xv, agreeG).flatMap(rules.mp(_, pm))
        product <- term(steps, s"$fn (${tangentAt(gn, dgn, "x:real")}) * $dgn x:real")
        composed <- moved(steps, s"\\t:real. $fn (${tangentAt(gn, dgn, "x:real")}) * $dgn x = $fn t * $dgn x", atX, Kernel.refl(product))
        r <- rules.disch(member, composed).flatMap(rules.gen(xv, _))
      } yield r
      onG <- specialised(steps, held.hasCongruence, s"\\x:real. $fn (${tangentAt(gn, dgn, "x")}) * $dgn x", s"\\x:real. $fn ($gn x) * $dgn x",
        "a:real", "b:real", s"$bigF (${tangentAt(gn, dgn, "b:real")}) - $bigF (${tangentAt(gn, dgn, "a:real")})")
        .flatMap(mp(_, Right(back), Right(rule)))
      aa <- steps.at(lemma("!a:real. a <= a"), "a:real")
      bb <- steps.at(lemma("!b:real. b <= b"), "b:real")
      atA <- specialised(steps, agreeG, "a:real").flatMap(r => rules.conjIntro(aa, ab).flatMap(rules.mp(r, _)))
      atB <- specialised(steps, agreeG, "b:real").flatMap(r => rules.conjIntro(ab, bb).flatMap(rules.mp(r, _)))
      read <- forward(steps, Vector(atA, atB), onG)
      result <- closeOver(steps, read, SubstitutionRelative.reverse,
        List("Fn:real -> real", "f:real -> real", "g:real -> real", "dg:real -> real", "a:real", "b:real"))
    } yield result
  }

  private val SubstitutionImageRelative = List(
    "a:real <= b:real",
    "!x:real. a:real <= x /\\ x <= b:real ==> c:real <= (g:real -> real) x /\\ g x <= d:real",
    "!y:real. c:real <= y /\\ y <= d:real ==> derivative_within (Fn:real -> real) c d y ((f:real -> real) y)",
    "!x:real. a:real <= x /\\ x <= b:real ==> derivative_within (g:real -> real) a b x ((dg:real -> real) x)")

  /**
   * `|- !F f g dg a b c d. a <= b ==> (!x. a <= x /\ x <= b ==> c <= g x /\ g x <= d) ==>
   *     (!y. c <= y /\ y <= d ==> derivative_within F c d y (f y)) ==>
   *     (!x. a <= x /\ x <= b ==> derivative_within g a b x (dg x)) ==>
   *     has_integral (\x. f (g x) * dg x) a b (F (g b) - F (g a))`
   *
   * Both functions are extended by their tangent lines, `g` past `a` and `b` and `F` past `c` and
   * `d`. The extension of `F` has the two-sided slope `f y` only on `[c, d]`, so the rule applied is
   * the one asking `F`'s slope at `g x` alone, and `g x` is in `[c, d]` because the extension of `g`
   * is `g` on `[a, b]`. The integrand and the two values are then read back, `F`'s at `g a` and
   * `g b`, which lie in `[c, d]` too.
   */
  private def substitutionImage(steps: Steps, held: Held, extension: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val (bigF, fn, gn, dgn) = ("(Fn:real -> real)", "(f:real -> real)", "(g:real -> real)", "(dg:real -> real)")
    val (lo, hi) = ("c:real", "d:real")
    val tF = tangent(bigF, fn, lo, hi)
    val tg = tangent(gn, dgn)
    for {
      assumed <- SubstitutionImageRelative.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (acc, text) =>
        for { done <- acc; one <- assume(text) } yield done :+ one
      }
      List(ab, image, slopesF, slopesG0) = assumed: @unchecked
      aa <- steps.at(lemma("!a:real. a <= a"), "a:real")
      bb <- steps.at(lemma("!b:real. b <= b"), "b:real")
      aIn <- rules.conjIntro(aa, ab)
      bIn <- rules.conjIntro(ab, bb)
      imageA <- specialised(steps, image, "a:real").flatMap(rules.mp(_, aIn))
      imageB <- specialised(steps, image, "b:real").flatMap(rules.mp(_, bIn))
      slopesG <- extendedSlopes(steps, extension, gn, dgn, slopesG0)
      agreeG <- agreesOn(steps, held, gn, dgn)
      agreeF <- agreesOn(steps, held, bigF, fn, lo, hi)
      xv <- variable(steps, "x:real")
      // the extension of F has slope f at the extension of g, at every x in [a, b]
      outer <- for {
        member <- proposition("a:real <= x:real /\\ x <= b:real")
        pm <- LogicError.lift(Kernel.assume(member))
        inImage <- specialised(steps, image, "x:real").flatMap(rules.mp(_, pm))
        low <- rules.conjElim1(inImage)
        high <- rules.conjElim2(inImage)
        atG <- specialised(steps, extension, bigF, fn, lo, hi, s"$gn x:real")
          .flatMap(mp(_, Right(slopesF), Right(low), Right(high)))
        toExtension <- rules.spec(xv, agreeG).flatMap(rules.mp(_, pm)).flatMap(Conv.sym)
        atT <- moved(steps, s"\\t:real. derivative $tF t ($fn t)", toExtension, atG)
        r <- rules.disch(member, atT).flatMap(rules.gen(xv, _))
      } yield r
      rule <- specialised(steps, held.hasSubstitutionAtImage, tF, fn, tg, dgn, "a:real", "b:real")
        .flatMap(mp(_, Right(ab), Right(outer), Right(slopesG)))
      // the integrand, back from the extension of g
      back <- for {
        member <- proposition("a:real <= x:real /\\ x <= b:real")
        pm <- LogicError.lift(Kernel.assume(member))
        atX <- rules.spec(xv, agreeG).flatMap(rules.mp(_, pm))
        product <- term(steps, s"$fn (${tangentAt(gn, dgn, "x:real")}) * $dgn x:real")
        composed <- moved(steps, s"\\t:real. $fn (${tangentAt(gn, dgn, "x:real")}) * $dgn x = $fn t * $dgn x", atX, Kernel.refl(product))
        r <- rules.disch(member, composed).flatMap(rules.gen(xv, _))
      } yield r
      valueAt = (u: String) => tangentAt(bigF, fn, tangentAt(gn, dgn, u), lo, hi)
      onG <- specialised(steps, held.hasCongruence, s"\\x:real. $fn (${tangentAt(gn, dgn, "x")}) * $dgn x", s"\\x:real. $fn ($gn x) * $dgn x",
        "a:real", "b:real", s"${valueAt("b:real")} - ${valueAt("a:real")}")
        .flatMap(mp(_, Right(back), Right(rule)))
      // and the two values: the extension of g is g at a and b, and the extension of F is F at g a and g b
      atA <- specialised(steps, agreeG, "a:real").flatMap(rules.mp(_, aIn))
      atB <- specialised(steps, agreeG, "b:real").flatMap(rules.mp(_, bIn))
      atFA <- specialised(steps, agreeF, s"$gn a:real").flatMap(rules.mp(_, imageA))
      atFB <- specialised(steps, agreeF, s"$gn b:real").flatMap(rules.mp(_, imageB))
      read <- forward(steps, Vector(atA, atB), onG).flatMap(forward(steps, Vector(atFA, atFB), _))
      result <- closeOver(steps, read, SubstitutionImageRelative.reverse,
        List("Fn:real -> real", "f:real -> real", "g:real -> real", "dg:real -> real", "a:real", "b:real", "c:real", "d:real"))
    } yield result
  }
}
