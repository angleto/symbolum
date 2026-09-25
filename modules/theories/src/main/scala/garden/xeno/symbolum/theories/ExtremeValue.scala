package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

import Continuity.Steps

/**
 * The extreme value theorem and uniform continuity, and the compactness of `[a, b]` both need, as one
 * argument used three times.
 *
 * `Continuity` publishes the facts and this is their derivation, as `Trigonometric` is for
 * `SIN_COS_SQUARED`: the file that owns a constant says what is true of it, and a derivation long
 * enough to bury that is kept beside it.
 *
 * == One supremum argument, not two ==
 *
 * The textbook proof spends a least upper bound twice: once to show that a function continuous on
 * `[a, b]` is bounded, and once to show that its supremum is a value. Written out, both are the same
 * argument about a different property of an interval: take the least upper bound `s` of the `x` for
 * which the property holds on `[a, x]`, and use continuity at `s` to carry it a little further. So
 * the argument is proved once, as [[Continuity.IntervalGluing]], over a property `P u v` of the
 * interval `[u, v]` that glues (`P u v` and `P v w` give `P u w`) and holds on every short enough
 * interval around each point; and it is spent twice for the extreme value theorem and, since
 * 2026-09-25, once more for [[Continuity.Uniform]]. It is the local-to-global principle usually
 * obtained from Cousin's lemma, proved here directly by the supremum rather than through tagged
 * partitions, because every consumer reads one radius per point off continuity and needs nothing
 * finer.
 *
 * == The maximum, without a reciprocal ==
 *
 * The usual second step says that if the supremum `M` of the values is not one of them, then
 * `1 / (M - f x)` is continuous and unbounded, against the first step. That wants the continuity of
 * a quotient, and nothing here has an algebra of continuous functions. What is used instead is the
 * gluing again, at "`f` stays at least some positive `e` under `M` on `[u, v]`": it holds near each
 * point, because `f x < M` and continuity at half the distance keeps `f` under `M` by that half, and
 * two gaps glue at the smaller. On all of `[a, b]` it makes `M - e` an upper bound of the values, so
 * `M` was not the least. The minimum is the maximum of `\y. 0 - f y`, and the continuity of that
 * negation, [[Continuity.Negation]], is the one fact about combining continuous functions the whole
 * derivation needed.
 *
 * == What it spends ==
 *
 * `COMPLETENESS` twice, once inside the gluing and once for the supremum of the values, and the
 * choice that `abs` and the excluded middle both cost. Nothing past the reals and that choice, which
 * `ContinuitySpec` asserts as an equality.
 */
private[theories] object ExtremeValue {

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Functions: Type = Type.fun(Reals, Reals)
  private val Relations: Type = Type.fun(Reals, Type.fun(Reals, Type.Bool))

  /** The function every fact below is about, and the continuity it is given on `[a, b]`. */
  private val F = "(f:real -> real)"
  private val Everywhere = s"!x:real. a:real <= x /\\ x <= b:real ==> continuous $F x"

  /** The six facts, by the names `Continuity` publishes them under. */
  def prove(
    steps: Steps,
    reals: RealTheory,
    magnitude: Magnitude,
    classical: Classical
  ): Either[LogicError, Map[String, Kernel.Thm]] =
    for {
      glued <- gluing(steps, reals, magnitude, classical)
      negated <- negation(steps, magnitude)
      bounded <- boundedness(steps, reals, magnitude, glued)
      highest <- maximum(steps, reals, magnitude, classical, glued, bounded)
      lowest <- minimum(steps, highest, negated)
      uniform <- uniformity(steps, reals, magnitude, glued)
    } yield Map(
      Continuity.IntervalGluing -> glued,
      Continuity.Negation -> negated,
      Continuity.Bounded -> bounded,
      Continuity.AttainsMaximum -> highest,
      Continuity.AttainsMinimum -> lowest,
      Continuity.Uniform -> uniform
    )

  /* ------------------------------------------------------------------ the gluing */

  private val Relation = "(P:real -> real -> bool)"

  /** A point of `[a, b]` where the property holds from `a`: the set whose supremum is taken. */
  private def memberAt(v: String): String = s"a:real <= $v /\\ $v <= b:real /\\ $Relation a $v"

  /** The radius at a point, opened: every short interval around it has the property. */
  private def radiusAt(x: String): String =
    s"0 < d:real /\\ (!u:real. !v:real. a:real <= u /\\ u <= $x /\\ $x <= v /\\ v <= b:real /\\ v - u < d ==> $Relation u v)"

  private val LocalText: String =
    s"!x:real. a:real <= x /\\ x <= b:real ==> ?d:real. 0 < d /\\ " +
      s"(!u:real. !v:real. a <= u /\\ u <= x /\\ x <= v /\\ v <= b /\\ v - u < d ==> $Relation u v)"

  private val GlueText: String =
    s"!u:real. !v:real. !w:real. u <= v /\\ v <= w /\\ $Relation u v /\\ P v w ==> P u w"

  /** `|- A /\\ B /\\ ...` from its parts, nested to the right as the parser nests it. */
  private def chain(steps: Steps, parts: Either[LogicError, Kernel.Thm]*): Either[LogicError, Kernel.Thm] =
    parts.reduceRight((l, r) => steps.conj(l, r))

  /**
   * [[Continuity.IntervalGluing]], from `COMPLETENESS` at the points `x` of `[a, b]` with `P a x`.
   *
   * `P a a` is the radius at `a` read at the interval of length zero. With `s` the supremum, the
   * radius `d` at `s` either finds a member `u` within `d / 2` below `s`, or `s - d / 2` bounds the
   * set and `s` was not the least; the case split is the excluded middle on the first. From such a
   * `u`, the interval `[u, v]` with `v` a little past `s` has the property and glues onto `[a, u]`:
   * at `s = b` that is `P a b`, and before `b` it puts `v` in the set above its supremum.
   */
  private def gluing(steps: Steps, reals: RealTheory, magnitude: Magnitude, classical: Classical): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val p = Term.variable("P", Relations)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val s = Term.variable("s", Reals)
    val d = Term.variable("d", Reals)
    val u = Term.variable("u", Reals)
    val x = Term.variable("x", Reals)

    val ordered = assume("a:real <= b:real")
    val glue = assume(GlueText)
    val local = assume(LocalText)
    val Member = memberAt("x:real")
    def within(v: String): String = s"(${memberAt(v)}) /\\ s:real - d:real / 2 < $v"
    val reached = s"?u:real. ${within("u")}"
    def reflexive(point: String) = at(lemma("!a:real. a <= a"), point)

    for {
      completeness <- reals.axiom("COMPLETENESS")
      total <- reals.axiom("LT_TOTAL")
      leCases <- magnitude.order.fact(Order.LeCases)
      goal <- proposition(s"$Relation a:real b:real")
      memberStatement <- proposition(Member)

      /* ------------------------------------ `P a a`, from the radius at `a` at a point interval */

      localAtA <- at(local, "a:real").flatMap(mp(_, conj(reflexive("a:real"), ordered)))
      radiusA <- assume(radiusAt("a:real"))
      insideA <- rules.conjElim2(radiusA)
      dPositiveA <- rules.conjElim1(radiusA)
      degenerate <- at(Right(insideA), "a:real", "a:real").flatMap(mp(_, chain(steps,
        reflexive("a:real"), reflexive("a:real"), reflexive("a:real"), ordered,
        at(lemma("!a:real d:real. 0 < d ==> a - a < d"), "a:real", "d:real").flatMap(mp(_, Right(dPositiveA))))))
      pointInterval <- rules.existsElim(localAtA, d, degenerate)

      /* ---------------------------------------------- inhabited by `a`, bounded by `b` */

      set <- Parser.term(theory, notation, s"\\x:real. $Member", Type.fun(Reals, Type.Bool))
      aMember <- conj(reflexive("a:real"), conj(ordered, Right(pointInterval)))
      inhabited <- existential(s"?x:real. $Member").flatMap(rules.existsIntro(_, a, aMember))
      assumedMember <- LogicError.lift(Kernel.assume(memberStatement))
      memberBelowB <- rules.conjElim2(assumedMember).flatMap(rules.conjElim1)
      everyBelowB <- rules.disch(memberStatement, memberBelowB).flatMap(rules.gen(x, _))
      bounded <- existential(s"?c:real. !x:real. $Member ==> x <= c").flatMap(rules.existsIntro(_, b, everyBelowB))

      atSet <- rules.spec(set, completeness)
      opened <- Conv.betaNormalise(atSet.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atSet)))
      supremumExists <- conj(Right(inhabited), Right(bounded)).flatMap(rules.mp(opened, _))

      supremum <- assume(
        s"(!x:real. $Member ==> x <= s:real) /\\ (!c:real. (!x:real. $Member ==> x <= c) ==> s <= c)")
      upper <- rules.conjElim1(supremum)
      least <- rules.conjElim2(supremum)
      sAboveA <- rules.spec(a, upper).flatMap(rules.mp(_, aMember))
      sBelowB <- rules.spec(b, least).flatMap(rules.mp(_, everyBelowB))

      near <- at(local, "s:real").flatMap(mp(_, conj(Right(sAboveA), Right(sBelowB))))
      radius <- assume(radiusAt("s:real"))
      dPositive <- rules.conjElim1(radius)
      inside <- rules.conjElim2(radius)

      /* -------------------- a member within half the radius of `s`, or `s` was not the least */

      positive <- for {
        witness <- assume(within("u:real"))
        member <- rules.conjElim1(witness)
        beyond <- rules.conjElim2(witness)
        uAboveA <- rules.conjElim1(member)
        uBelowB <- rules.conjElim2(member).flatMap(rules.conjElim1)
        fromA <- rules.conjElim2(member).flatMap(rules.conjElim2)
        uBelowS <- rules.spec(u, upper).flatMap(rules.mp(_, member))

        // At `s = b` the interval from the member to `b` is inside the radius, and joins.
        atEnd <- for {
          same <- assume("s:real = b:real")
          close <- at(lemma("!s:real b:real u:real d:real. s = b ==> s - d / 2 < u ==> 0 < d ==> b - u < d"),
            "s:real", "b:real", "u:real", "d:real").flatMap(mp(_, Right(same), Right(beyond), Right(dPositive)))
          toB <- at(Right(inside), "u:real", "b:real").flatMap(mp(_, chain(steps,
            Right(uAboveA), Right(uBelowS), Right(sBelowB), reflexive("b:real"), Right(close))))
          joined <- at(glue, "a:real", "u:real", "b:real").flatMap(mp(_, chain(steps,
            Right(uAboveA), Right(uBelowB), Right(fromA), Right(toB))))
        } yield joined

        // Before it, the interval reaches `s + min (d / 2) (b - s)`, which is then a member past `s`.
        beforeEnd <- {
          val gap = "b - s"
          val w = s"min (d / 2) ($gap)"
          val t = s"s + $w"
          for {
            strictly <- assume("s:real < b:real")
            gapPositive = at(lemma("!s:real b:real. s < b ==> 0 < b - s"), "s:real", "b:real").flatMap(mp(_, Right(strictly)))
            wPositive <- Continuity.minimumPositive(steps, magnitude, gap, Right(dPositive), gapPositive)
            wHalf <- at(magnitude.fact(Magnitude.MinBelowLeft), "d / 2", gap)
            wGap <- at(magnitude.fact(Magnitude.MinBelowRight), "d / 2", gap)
            sBelowT <- at(lemma("!s:real w:real. 0 < w ==> s <= s + w"), "s:real", w).flatMap(mp(_, Right(wPositive)))
            tBelowB <- at(lemma("!s:real w:real b:real. w <= b - s ==> s + w <= b"), "s:real", w, "b:real")
              .flatMap(mp(_, Right(wGap)))
            close <- at(lemma("!s:real w:real u:real d:real. s - d / 2 < u ==> w <= d / 2 ==> (s + w) - u < d"),
              "s:real", w, "u:real", "d:real").flatMap(mp(_, Right(beyond), Right(wHalf)))
            toT <- at(Right(inside), "u:real", t).flatMap(mp(_, chain(steps,
              Right(uAboveA), Right(uBelowS), Right(sBelowT), Right(tBelowB), Right(close))))
            uBelowT <- at(lemma("!u:real s:real t:real. u <= s ==> s <= t ==> u <= t"), "u:real", "s:real", t)
              .flatMap(mp(_, Right(uBelowS), Right(sBelowT)))
            joined <- at(glue, "a:real", "u:real", t).flatMap(mp(_, chain(steps,
              Right(uAboveA), Right(uBelowT), Right(fromA), Right(toT))))
            tAboveA <- at(lemma("!a:real s:real t:real. a <= s ==> s <= t ==> a <= t"), "a:real", "s:real", t)
              .flatMap(mp(_, Right(sAboveA), Right(sBelowT)))
            tMember <- conj(Right(tAboveA), conj(Right(tBelowB), Right(joined)))
            tTerm <- real(t)
            passes <- rules.spec(tTerm, upper).flatMap(rules.mp(_, tMember))
            absurd <- at(lemma("!s:real w:real. 0 < w ==> s + w <= s ==> F"), "s:real", w)
              .flatMap(mp(_, Right(wPositive), Right(passes)))
            result <- rules.falsityElim(goal, absurd)
          } yield result
        }

        split <- rules.specAll(leCases, List(s, b)).flatMap(rules.mp(_, sBelowB))
        cases <- rules.disjElim(split, beforeEnd, atEnd)
        assumedReached <- assume(reached)
        result <- rules.existsElim(assumedReached, u, cases)
      } yield result

      negative <- {
        val lower = "s - d / 2"
        for {
          unreached <- assume(s"~($reached)")
          member <- LogicError.lift(Kernel.assume(memberStatement))
          lowerTerm <- real(lower)
          trichotomy <- rules.specAll(total, List(lowerTerm, x))
          past <- for {
            beyond <- assume(s"$lower < x:real")
            both <- rules.conjIntro(member, beyond)
            found <- existential(reached).flatMap(rules.existsIntro(_, x, both))
            absurd <- rules.notElim(unreached, found)
            claim <- proposition(s"x:real <= $lower")
            result <- rules.falsityElim(claim, absurd)
          } yield result
          meets <- assume(s"$lower = x:real").flatMap(equation =>
            at(lemma("!p:real q:real. p = q ==> q <= p"), lower, "x:real").flatMap(mp(_, Right(equation))))
          short <- assume(s"x:real < $lower").flatMap(strict =>
            at(lemma("!p:real q:real. p < q ==> p <= q"), "x:real", lower).flatMap(mp(_, Right(strict))))
          rest <- assume(s"$lower = x:real \\/ x:real < $lower").flatMap(rules.disjElim(_, meets, short))
          underLower <- rules.disjElim(trichotomy, past, rest)
          bound <- rules.disch(memberStatement, underLower).flatMap(rules.gen(x, _))
          passes <- rules.spec(lowerTerm, least).flatMap(rules.mp(_, bound))
          absurd <- at(lemma("!s:real d:real. 0 < d ==> s <= s - d / 2 ==> F"), "s:real", "d:real")
            .flatMap(mp(_, Right(dPositive), Right(passes)))
          result <- rules.falsityElim(goal, absurd)
        } yield result
      }

      question <- proposition(reached)
      decided <- classical.cases(question, positive, negative)
      withRadius <- rules.existsElim(near, d, decided)
      eliminated <- rules.existsElim(supremumExists, s, withRadius)

      result <- List(LocalText, GlueText, "a:real <= b:real")
        .foldLeft[Either[LogicError, Kernel.Thm]](Right(eliminated)) { (acc, text) =>
          for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
        }.flatMap(rules.genAll(_, List(p, a, b)))
    } yield result
  }

  /* ------------------------------------------------------ what the consumers share */

  /**
   * A fact specialised at a lambda, with the redexes that leaves reduced. Both consumers of the
   * gluing hand it their property as a lambda, and its premises have to be read in reduced form to
   * be compared with what the consumer proves.
   */
  private def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv.betaNormalise(theorem.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

  /**
   * The first `count` antecedents of an implication chain, in order. A consumer checks its own
   * proofs of the gluing's premises against these before detaching, so that a premise proved in a
   * shape the instance does not have is refused by name rather than by `mp`.
   */
  private def antecedents(steps: Steps, term: Term, count: Int): Either[LogicError, List[Term]] =
    if (count == 0) Right(Nil)
    else
      steps.logic.destImp(term).toRight(NotOfForm("an implication", term)).flatMap { case (left, right) =>
        antecedents(steps, right, count - 1).map(left :: _)
      }

  /**
   * `abs (y - x) < d` for `y` in `[u, v]`, `x` in `[u, v]` and `v - u < d`: the one estimate every
   * local step below makes, by the two cases of `abs`.
   */
  private def withinRadius(
    steps: Steps,
    magnitude: Magnitude,
    y: String, x: String, u: String, v: String, d: String,
    uy: Kernel.Thm, yv: Kernel.Thm, ux: Kernel.Thm, xv: Kernel.Thm, short: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val m = s"abs ($y - $x)"
    for {
      cases <- at(magnitude.fact(Magnitude.AbsCases), s"$y - $x")
      plain <- proposition(s"$m = $y - $x")
      negated <- proposition(s"$m = -($y - $x)")
      fromPlain <- LogicError.lift(Kernel.assume(plain)).flatMap(assumed =>
        at(lemma("!m:real y:real x:real u:real v:real d:real. m = y - x ==> y <= v ==> u <= x ==> v - u < d ==> m < d"),
          m, y, x, u, v, d).flatMap(mp(_, Right(assumed), Right(yv), Right(ux), Right(short))))
      fromNegated <- LogicError.lift(Kernel.assume(negated)).flatMap(assumed =>
        at(lemma("!m:real y:real x:real u:real v:real d:real. m = -(y - x) ==> u <= y ==> x <= v ==> v - u < d ==> m < d"),
          m, y, x, u, v, d).flatMap(mp(_, Right(assumed), Right(uy), Right(xv), Right(short))))
      result <- rules.disjElim(cases, fromPlain, fromNegated)
    } yield result
  }

  /**
   * A proof by cases on `p <= q` or `q <= p`, which is what gluing two intervals at `v` asks of a
   * point: the three cases of `LT_TOTAL`, the first two delivered to `below` and the third to
   * `above`. The order is total by an axiom, so nothing classical is spent here.
   */
  private def byOrder(
    steps: Steps,
    total: Kernel.Thm,
    p: String, q: String,
    below: Kernel.Thm => Either[LogicError, Kernel.Thm],
    above: Kernel.Thm => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      pTerm <- real(p)
      qTerm <- real(q)
      trichotomy <- rules.specAll(total, List(pTerm, qTerm))
      strict <- assume(s"$p < $q").flatMap(h =>
        at(lemma("!p:real q:real. p < q ==> p <= q"), p, q).flatMap(mp(_, Right(h)))).flatMap(below)
      equal <- assume(s"$p = $q").flatMap(h =>
        at(lemma("!p:real q:real. p = q ==> p <= q"), p, q).flatMap(mp(_, Right(h)))).flatMap(below)
      reverse <- assume(s"$q < $p").flatMap(h =>
        at(lemma("!p:real q:real. q < p ==> q <= p"), p, q).flatMap(mp(_, Right(h)))).flatMap(above)
      rest <- assume(s"$p = $q \\/ $q < $p").flatMap(rules.disjElim(_, equal, reverse))
      result <- rules.disjElim(trichotomy, strict, rest)
    } yield result
  }

  /**
   * [[Continuity.Negation]]: the radius that keeps `f y` within `e` of `f x` keeps `0 - f y` within
   * `e` of `0 - f x`, since the two differences are negations of each other.
   */
  private def negation(steps: Steps, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val x = Term.variable("x", Reals)
    val e = Term.variable("e", Reals)
    val d = Term.variable("d", Reals)
    val y = Term.variable("y", Reals)
    for {
      hypothesis <- proposition(s"continuous $F x:real")
      assumed <- LogicError.lift(Kernel.assume(hypothesis))
      epsilonDelta <- unfolded(f, x).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumed)))
      positive <- proposition("0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      near <- rules.spec(e, epsilonDelta).flatMap(rules.mp(_, assumedPositive))
      radius <- assume(s"0 < d:real /\\ (!y:real. abs (y - x:real) < d ==> abs ($F y - f x) < e:real)")
      dPositive <- rules.conjElim1(radius)
      inside <- rules.conjElim2(radius)
      close <- proposition("abs (y:real - x:real) < d:real")
      assumedClose <- LogicError.lift(Kernel.assume(close))
      valueClose <- rules.spec(y, inside).flatMap(rules.mp(_, assumedClose))
      t = s"(0 - $F y) - (0 - f x)"
      m = s"abs ($t)"
      cases <- at(magnitude.fact(Magnitude.AbsCases), t)
      plain <- assume(s"$m = $t").flatMap(h =>
        at(lemma("!m:real p:real q:real n:real e:real. m = (0 - p) - (0 - q) ==> -(p - q) <= n ==> n < e ==> m < e"),
          m, s"$F y", s"$F x", s"abs ($F y - f x)", "e:real")
          .flatMap(mp(_, Right(h), at(magnitude.fact(Magnitude.AbsAboveNegation), s"$F y - f x"), Right(valueClose))))
      negated <- assume(s"$m = -($t)").flatMap(h =>
        at(lemma("!m:real p:real q:real n:real e:real. m = -((0 - p) - (0 - q)) ==> p - q <= n ==> n < e ==> m < e"),
          m, s"$F y", s"$F x", s"abs ($F y - f x)", "e:real")
          .flatMap(mp(_, Right(h), at(magnitude.fact(Magnitude.AbsAbove), s"$F y - f x"), Right(valueClose))))
      within <- rules.disjElim(cases, plain, negated)
      everyPoint <- rules.disch(close, within).flatMap(rules.gen(y, _))
      both <- rules.conjIntro(dPositive, everyPoint)
      witnessed <- existential(s"?d:real. 0 < d /\\ (!y:real. abs (y - x:real) < d ==> abs ($t) < e:real)")
        .flatMap(rules.existsIntro(_, d, both))
      opened <- rules.existsElim(near, d, witnessed)
      statement <- rules.disch(positive, opened).flatMap(rules.gen(e, _))
      function <- Parser.term(theory, notation, s"\\y:real. 0 - $F y", Functions)
      folded <- folded(function, x, statement)
      result <- rules.disch(hypothesis, folded).flatMap(rules.genAll(_, List(f, x)))
    } yield result
  }

  /**
   * [[Continuity.Bounded]]: the gluing at "`f` is bounded above on `[u, v]`". Two bounds glue at
   * their `max`, and continuity at tolerance one bounds every short interval around a point by
   * `f x + 1`.
   */
  private def boundedness(steps: Steps, reals: RealTheory, magnitude: Magnitude, gluing: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val x = Term.variable("x", Reals)
    val y = Term.variable("y", Reals)
    val u = Term.variable("u", Reals)
    val v = Term.variable("v", Reals)
    val w = Term.variable("w", Reals)
    val d = Term.variable("d", Reals)
    val m = Term.variable("m", Reals)
    val n = Term.variable("n", Reals)
    val ordered = assume("a:real <= b:real")
    val everywhere = assume(Everywhere)
    def boundedOn(lo: String, hi: String, bound: String) =
      s"!x:real. $lo <= x /\\ x <= $hi ==> $F x <= $bound"

    for {
      total <- reals.axiom("LT_TOTAL")
      relation <- Parser.term(theory, notation,
        s"\\u:real. \\v:real. ?M:real. ${boundedOn("u", "v", "M")}", Relations)
      instance <- rules.specAll(gluing, List(relation, a, b)).flatMap(reduced)
      parts <- antecedents(steps, instance.conclusion, 3)
      List(_, glueTerm, localTerm) = parts: @unchecked

      /* ----------------------------------------------------------- two bounds give one */

      glued <- {
        val premise = s"u:real <= v:real /\\ v <= w:real /\\ (?M:real. ${boundedOn("u", "v", "M")}) /\\ " +
          s"(?M:real. ${boundedOn("v", "w", "M")})"
        for {
          premiseTerm <- proposition(premise)
          assumed <- LogicError.lift(Kernel.assume(premiseTerm))
          first <- rules.conjElim2(assumed).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
          second <- rules.conjElim2(assumed).flatMap(rules.conjElim2).flatMap(rules.conjElim2)
          left <- assume(boundedOn("u:real", "v:real", "m:real"))
          right <- assume(boundedOn("v:real", "w:real", "n:real"))
          point <- proposition("u:real <= x:real /\\ x <= w:real")
          atPoint <- LogicError.lift(Kernel.assume(point))
          xAboveU <- rules.conjElim1(atPoint)
          xBelowW <- rules.conjElim2(atPoint)
          under <- byOrder(steps, total, "x:real", "v:real",
            xv => at(Right(left), "x:real").flatMap(mp(_, conj(Right(xAboveU), Right(xv)))).flatMap(fx =>
              at(lemma("!p:real q:real r:real. p <= q ==> q <= r ==> p <= r"), s"$F x", "m:real", "max m n")
                .flatMap(mp(_, Right(fx), at(magnitude.fact(Magnitude.MaxAboveLeft), "m:real", "n:real")))),
            vx => at(Right(right), "x:real").flatMap(mp(_, conj(Right(vx), Right(xBelowW)))).flatMap(fx =>
              at(lemma("!p:real q:real r:real. p <= q ==> q <= r ==> p <= r"), s"$F x", "n:real", "max m n")
                .flatMap(mp(_, Right(fx), at(magnitude.fact(Magnitude.MaxAboveRight), "m:real", "n:real")))))
          everyPoint <- rules.disch(point, under).flatMap(rules.gen(x, _))
          bound <- real("max m n")
          joined <- existential(s"?M:real. ${boundedOn("u:real", "w:real", "M")}").flatMap(rules.existsIntro(_, bound, everyPoint))
          withN <- rules.existsElim(second, n, joined)
          withM <- rules.existsElim(first, m, withN)
          result <- rules.disch(premiseTerm, withM).flatMap(rules.genAll(_, List(u, v, w)))
        } yield result
      }

      /* --------------------------------------- continuity at tolerance one bounds a small interval */

      local <- {
        val small = "a:real <= u:real /\\ u <= x:real /\\ x <= v:real /\\ v <= b:real /\\ v - u < d:real"
        for {
          point <- proposition("a:real <= x:real /\\ x <= b:real")
          atPoint <- LogicError.lift(Kernel.assume(point))
          continuous <- everywhere.flatMap(rules.spec(x, _)).flatMap(rules.mp(_, atPoint))
          epsilonDelta <- unfolded(f, x).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, continuous)))
          near <- at(Right(epsilonDelta), "1").flatMap(mp(_, lemma("(0:real) < 1")))
          radius <- assume(s"0 < d:real /\\ (!y:real. abs (y - x:real) < d ==> abs ($F y - f x) < 1)")
          dPositive <- rules.conjElim1(radius)
          inside <- rules.conjElim2(radius)
          smallTerm <- proposition(small)
          interval <- LogicError.lift(Kernel.assume(smallTerm))
          uA <- rules.conjElim1(interval)
          ux <- rules.conjElim2(interval).flatMap(rules.conjElim1)
          xv <- rules.conjElim2(interval).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
          short <- rules.conjElim2(interval).flatMap(rules.conjElim2).flatMap(rules.conjElim2).flatMap(rules.conjElim2)
          inner <- proposition("u:real <= y:real /\\ y <= v:real")
          atY <- LogicError.lift(Kernel.assume(inner))
          uy <- rules.conjElim1(atY)
          yv <- rules.conjElim2(atY)
          close <- withinRadius(steps, magnitude, "y:real", "x:real", "u:real", "v:real", "d:real", uy, yv, ux, xv, short)
          valueClose <- rules.spec(y, inside).flatMap(rules.mp(_, close))
          under <- at(lemma("!n:real p:real q:real. p - q <= n ==> n < 1 ==> p <= q + 1"),
            s"abs ($F y - f x)", s"$F y", s"$F x")
            .flatMap(mp(_, at(magnitude.fact(Magnitude.AbsAbove), s"$F y - f x"), Right(valueClose)))
          everyY <- rules.disch(inner, under).flatMap(rules.gen(y, _))
          bound <- real(s"$F x + 1")
          bounded <- existential(s"?M:real. !y:real. u:real <= y /\\ y <= v:real ==> $F y <= M")
            .flatMap(rules.existsIntro(_, bound, everyY))
          everyInterval <- rules.disch(smallTerm, bounded).flatMap(rules.genAll(_, List(u, v)))
          both <- rules.conjIntro(dPositive, everyInterval)
          witnessed <- existential(
            s"?d:real. 0 < d /\\ (!u:real. !v:real. a:real <= u /\\ u <= x:real /\\ x <= v /\\ v <= b:real /\\ v - u < d ==> " +
              s"(?M:real. !y:real. u <= y /\\ y <= v ==> $F y <= M))")
            .flatMap(rules.existsIntro(_, d, both))
          opened <- rules.existsElim(near, d, witnessed)
          result <- rules.disch(point, opened).flatMap(rules.gen(x, _))
        } yield result
      }

      _ <- if (glued.conclusion == glueTerm) Right(()) else Left(NotOfForm("the gluing premise", glued.conclusion))
      _ <- if (local.conclusion == localTerm) Right(()) else Left(NotOfForm("the local premise", local.conclusion))
      concluded <- mp(instance, ordered, Right(glued), Right(local))
      result <- List(Everywhere, "a:real <= b:real")
        .foldLeft[Either[LogicError, Kernel.Thm]](Right(concluded)) { (acc, text) =>
          for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
        }.flatMap(rules.genAll(_, List(f, a, b)))
    } yield result
  }

  /**
   * [[Continuity.AttainsMaximum]]. The values of `f` on `[a, b]` are bounded, by [[Continuity.Bounded]],
   * so they have a least upper bound `M`, and either some point of `[a, b]` has the value `M`, which
   * is the theorem, or none has. In that case every value is strictly under `M`, and the gluing at
   * "`f` stays some positive `e` under `M` on `[u, v]`" puts a gap under `M` on the whole interval,
   * which makes `M - e` an upper bound of the values and `M` not the least. The case split is the
   * excluded middle on "`M` is attained".
   */
  private def maximum(
    steps: Steps,
    reals: RealTheory,
    magnitude: Magnitude,
    classical: Classical,
    gluing: Kernel.Thm,
    bounded: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val x = Term.variable("x", Reals)
    val y = Term.variable("y", Reals)
    val z = Term.variable("z", Reals)
    val u = Term.variable("u", Reals)
    val v = Term.variable("v", Reals)
    val w = Term.variable("w", Reals)
    val d = Term.variable("d", Reals)
    val e = Term.variable("e", Reals)
    val p = Term.variable("p", Reals)
    val q = Term.variable("q", Reals)
    val m = Term.variable("m", Reals)
    val top = Term.variable("M", Reals)
    val ceiling = Term.variable("C", Reals)
    val ordered = assume("a:real <= b:real")
    val everywhere = assume(Everywhere)
    def value(point: String) = s"(?t:real. a:real <= t /\\ t <= b:real /\\ $point = $F t)"
    val Goal = s"?m:real. a:real <= m /\\ m <= b:real /\\ (!x:real. a <= x /\\ x <= b ==> $F x <= f m)"
    val Attained = s"?m:real. a:real <= m /\\ m <= b:real /\\ $F m = M:real"
    def gapBelow(lo: String, hi: String, gap: String) =
      s"!x:real. $lo <= x /\\ x <= $hi ==> $F x <= M:real - $gap"

    for {
      total <- reals.axiom("LT_TOTAL")
      completeness <- reals.axiom("COMPLETENESS")
      goal <- proposition(Goal)
      falsity = logic.falsity

      /* -------------------------------------------- the values have a least upper bound `M` */

      boundedAt <- rules.specAll(bounded, List(f, a, b)).flatMap(mp(_, ordered, everywhere))
      ceilingBound <- assume(s"!x:real. a:real <= x /\\ x <= b:real ==> $F x <= C:real")

      set <- Parser.term(theory, notation, s"\\z:real. ${value("z")}", Type.fun(Reals, Type.Bool))
      aValue <- conj(at(lemma("!a:real. a <= a"), "a:real"), conj(ordered, real(s"$F a").map(Kernel.refl)))
      fAIsValue <- existential(value(s"$F a")).flatMap(rules.existsIntro(_, a, aValue))
      fATerm <- real(s"$F a")
      inhabited <- existential(s"?z:real. ${value("z")}").flatMap(rules.existsIntro(_, fATerm, fAIsValue))

      valueStatement <- proposition(value("z:real"))
      assumedValue <- LogicError.lift(Kernel.assume(valueStatement))
      // `z <= c` for a value `z`, from a bound `c` on `f` over the interval.
      underBound = (bound: Kernel.Thm, c: String) => for {
        body <- assume(s"a:real <= x:real /\\ x <= b:real /\\ z:real = $F x")
        inInterval <- conj(rules.conjElim1(body), rules.conjElim2(body).flatMap(rules.conjElim1))
        valueUnder <- rules.spec(x, bound).flatMap(rules.mp(_, inInterval))
        equation <- rules.conjElim2(body).flatMap(rules.conjElim2)
        result <- at(lemma("!z:real p:real c:real. z = p ==> p <= c ==> z <= c"), "z:real", s"$F x", c)
          .flatMap(mp(_, Right(equation), Right(valueUnder)))
        opened <- rules.existsElim(assumedValue, x, result)
      } yield opened
      zUnderC <- underBound(ceilingBound, "C:real")
      everyUnderC <- rules.disch(valueStatement, zUnderC).flatMap(rules.gen(z, _))
      boundedSet <- existential(s"?c:real. !z:real. ${value("z")} ==> z <= c").flatMap(rules.existsIntro(_, ceiling, everyUnderC))

      atSet <- rules.spec(set, completeness)
      opened <- reduced(atSet)
      supremumExists <- conj(Right(inhabited), Right(boundedSet)).flatMap(rules.mp(opened, _))
      supremum <- assume(
        s"(!z:real. ${value("z")} ==> z <= M:real) /\\ (!c:real. (!z:real. ${value("z")} ==> z <= c) ==> M <= c)")
      upper <- rules.conjElim1(supremum)
      least <- rules.conjElim2(supremum)

      point <- proposition("a:real <= x:real /\\ x <= b:real")
      atPoint <- LogicError.lift(Kernel.assume(point))
      // `f x <= M` at a point of the interval, because `f x` is a value.
      fxValue <- conj(rules.conjElim1(atPoint), conj(rules.conjElim2(atPoint), real(s"$F x").map(Kernel.refl)))
      fxIsValue <- existential(value(s"$F x")).flatMap(rules.existsIntro(_, x, fxValue))
      fxTerm <- real(s"$F x")
      fxUnderM <- rules.spec(fxTerm, upper).flatMap(rules.mp(_, fxIsValue))

      /* ----------------------------------------------------------------- attained: done */

      positive <- for {
        body <- assume(s"a:real <= m:real /\\ m <= b:real /\\ $F m = M:real")
        mA <- rules.conjElim1(body)
        mB <- rules.conjElim2(body).flatMap(rules.conjElim1)
        hit <- rules.conjElim2(body).flatMap(rules.conjElim2)
        under <- at(lemma("!p:real q:real r:real. p <= q ==> r = q ==> p <= r"), s"$F x", "M:real", s"$F m")
          .flatMap(mp(_, Right(fxUnderM), Right(hit)))
        everyPoint <- rules.disch(point, under).flatMap(rules.gen(x, _))
        found <- conj(Right(mA), conj(Right(mB), Right(everyPoint)))
        witnessed <- existential(Goal).flatMap(rules.existsIntro(_, m, found))
        assumedAttained <- assume(Attained)
        result <- rules.existsElim(assumedAttained, m, witnessed)
      } yield result

      /* ------------------- not attained: every value is below `M`, and a gap glues across [a, b] */

      negative <- for {
        missed <- assume(s"~($Attained)")
        fxBelowM <- {
          for {
            trichotomy <- rules.specAll(total, List(fxTerm, top))
            strict <- assume(s"$F x < M:real")
            equal <- for {
              hit <- assume(s"$F x = M:real")
              both <- conj(rules.conjElim1(atPoint), conj(rules.conjElim2(atPoint), Right(hit)))
              found <- existential(Attained).flatMap(rules.existsIntro(_, x, both))
              absurd <- rules.notElim(missed, found)
              claim <- proposition(s"$F x < M:real")
              result <- rules.falsityElim(claim, absurd)
            } yield result
            over <- for {
              above <- assume(s"M:real < $F x")
              absurd <- at(lemma("!p:real q:real. q < p ==> p <= q ==> F"), s"$F x", "M:real")
                .flatMap(mp(_, Right(above), Right(fxUnderM)))
              claim <- proposition(s"$F x < M:real")
              result <- rules.falsityElim(claim, absurd)
            } yield result
            rest <- assume(s"$F x = M:real \\/ M:real < $F x").flatMap(rules.disjElim(_, equal, over))
            result <- rules.disjElim(trichotomy, strict, rest)
          } yield result
        }

        relation <- Parser.term(theory, notation,
          s"\\u:real. \\v:real. ?e:real. 0 < e /\\ (${gapBelow("u", "v", "e")})", Relations)
        instance <- rules.specAll(gluing, List(relation, a, b)).flatMap(reduced)
        parts <- antecedents(steps, instance.conclusion, 3)
        List(_, glueTerm, localTerm) = parts: @unchecked

        // Two gaps give the smaller one.
        glued <- {
          val premise = s"u:real <= v:real /\\ v <= w:real /\\ (?e:real. 0 < e /\\ (${gapBelow("u", "v", "e")})) /\\ " +
            s"(?e:real. 0 < e /\\ (${gapBelow("v", "w", "e")}))"
          for {
            premiseTerm <- proposition(premise)
            assumed <- LogicError.lift(Kernel.assume(premiseTerm))
            first <- rules.conjElim2(assumed).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
            second <- rules.conjElim2(assumed).flatMap(rules.conjElim2).flatMap(rules.conjElim2)
            left <- assume(s"0 < p:real /\\ (${gapBelow("u:real", "v:real", "p")})")
            right <- assume(s"0 < q:real /\\ (${gapBelow("v:real", "w:real", "q")})")
            pPositive <- rules.conjElim1(left)
            qPositive <- rules.conjElim1(right)
            leftGap <- rules.conjElim2(left)
            rightGap <- rules.conjElim2(right)
            smaller = "min p q"
            cases <- at(magnitude.fact(Magnitude.MinCases), "p:real", "q:real")
            fromP <- assume(s"$smaller = p:real").flatMap(h =>
              at(lemma("!w:real g:real. w = g ==> 0 < g ==> 0 < w"), smaller, "p:real").flatMap(mp(_, Right(h), Right(pPositive))))
            fromQ <- assume(s"$smaller = q:real").flatMap(h =>
              at(lemma("!w:real g:real. w = g ==> 0 < g ==> 0 < w"), smaller, "q:real").flatMap(mp(_, Right(h), Right(qPositive))))
            smallerPositive <- rules.disjElim(cases, fromP, fromQ)
            span <- proposition("u:real <= x:real /\\ x <= w:real")
            atX <- LogicError.lift(Kernel.assume(span))
            xAboveU <- rules.conjElim1(atX)
            xBelowW <- rules.conjElim2(atX)
            lower = "!y:real Mv:real g:real h:real. y <= Mv - g ==> h <= g ==> y <= Mv - h"
            under <- byOrder(steps, total, "x:real", "v:real",
              xv => at(Right(leftGap), "x:real").flatMap(mp(_, conj(Right(xAboveU), Right(xv)))).flatMap(fx =>
                at(lemma(lower), s"$F x", "M:real", "p:real", smaller)
                  .flatMap(mp(_, Right(fx), at(magnitude.fact(Magnitude.MinBelowLeft), "p:real", "q:real")))),
              vx => at(Right(rightGap), "x:real").flatMap(mp(_, conj(Right(vx), Right(xBelowW)))).flatMap(fx =>
                at(lemma(lower), s"$F x", "M:real", "q:real", smaller)
                  .flatMap(mp(_, Right(fx), at(magnitude.fact(Magnitude.MinBelowRight), "p:real", "q:real")))))
            everyPoint <- rules.disch(span, under).flatMap(rules.gen(x, _))
            both <- rules.conjIntro(smallerPositive, everyPoint)
            gapTerm <- real(smaller)
            joined <- existential(s"?e:real. 0 < e /\\ (${gapBelow("u:real", "w:real", "e")})").flatMap(rules.existsIntro(_, gapTerm, both))
            withQ <- rules.existsElim(second, q, joined)
            withP <- rules.existsElim(first, p, withQ)
            result <- rules.disch(premiseTerm, withP).flatMap(rules.genAll(_, List(u, v, w)))
          } yield result
        }

        // Continuity at half the distance to `M` keeps a small interval that far under it.
        local <- {
          val small = "a:real <= u:real /\\ u <= x:real /\\ x <= v:real /\\ v <= b:real /\\ v - u < d:real"
          val half = s"(M:real - $F x) / 2"
          for {
            continuous <- everywhere.flatMap(rules.spec(x, _)).flatMap(rules.mp(_, atPoint))
            epsilonDelta <- unfolded(f, x).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, continuous)))
            halfPositive <- at(lemma("!q:real Mv:real. q < Mv ==> 0 < (Mv - q) / 2"), s"$F x", "M:real")
              .flatMap(mp(_, Right(fxBelowM)))
            near <- at(Right(epsilonDelta), half).flatMap(mp(_, Right(halfPositive)))
            radius <- assume(s"0 < d:real /\\ (!y:real. abs (y - x:real) < d ==> abs ($F y - f x) < $half)")
            dPositive <- rules.conjElim1(radius)
            inside <- rules.conjElim2(radius)
            smallTerm <- proposition(small)
            interval <- LogicError.lift(Kernel.assume(smallTerm))
            ux <- rules.conjElim2(interval).flatMap(rules.conjElim1)
            xv <- rules.conjElim2(interval).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
            short <- rules.conjElim2(interval).flatMap(rules.conjElim2).flatMap(rules.conjElim2).flatMap(rules.conjElim2)
            inner <- proposition("u:real <= y:real /\\ y <= v:real")
            atY <- LogicError.lift(Kernel.assume(inner))
            uy <- rules.conjElim1(atY)
            yv <- rules.conjElim2(atY)
            close <- withinRadius(steps, magnitude, "y:real", "x:real", "u:real", "v:real", "d:real", uy, yv, ux, xv, short)
            valueClose <- rules.spec(y, inside).flatMap(rules.mp(_, close))
            under <- at(lemma("!n:real p:real q:real Mv:real. p - q <= n ==> n < (Mv - q) / 2 ==> p <= Mv - (Mv - q) / 2"),
              s"abs ($F y - f x)", s"$F y", s"$F x", "M:real")
              .flatMap(mp(_, at(magnitude.fact(Magnitude.AbsAbove), s"$F y - f x"), Right(valueClose)))
            everyY <- rules.disch(inner, under).flatMap(rules.gen(y, _))
            both <- rules.conjIntro(halfPositive, everyY)
            halfTerm <- real(half)
            gapped <- existential(s"?e:real. 0 < e /\\ (!y:real. u:real <= y /\\ y <= v:real ==> $F y <= M:real - e)")
              .flatMap(rules.existsIntro(_, halfTerm, both))
            everyInterval <- rules.disch(smallTerm, gapped).flatMap(rules.genAll(_, List(u, v)))
            withRadius <- rules.conjIntro(dPositive, everyInterval)
            witnessed <- existential(
              s"?d:real. 0 < d /\\ (!u:real. !v:real. a:real <= u /\\ u <= x:real /\\ x <= v /\\ v <= b:real /\\ v - u < d ==> " +
                s"(?e:real. 0 < e /\\ (!y:real. u <= y /\\ y <= v ==> $F y <= M:real - e)))")
              .flatMap(rules.existsIntro(_, d, withRadius))
            opened <- rules.existsElim(near, d, witnessed)
            result <- rules.disch(point, opened).flatMap(rules.gen(x, _))
          } yield result
        }

        _ <- if (glued.conclusion == glueTerm) Right(()) else Left(NotOfForm("the gluing premise", glued.conclusion))
        _ <- if (local.conclusion == localTerm) Right(()) else Left(NotOfForm("the local premise", local.conclusion))
        gap <- mp(instance, ordered, Right(glued), Right(local))

        // A gap under `M` on the whole interval makes `M - e` an upper bound of the values.
        body <- assume(s"0 < e:real /\\ (${gapBelow("a:real", "b:real", "e")})")
        ePositive <- rules.conjElim1(body)
        gapEverywhere <- rules.conjElim2(body)
        zUnder <- underBound(gapEverywhere, "M:real - e:real")
        everyUnder <- rules.disch(valueStatement, zUnder).flatMap(rules.gen(z, _))
        lowered <- real("M:real - e:real")
        passes <- rules.spec(lowered, least).flatMap(rules.mp(_, everyUnder))
        absurd <- at(lemma("!Mv:real e:real. 0 < e ==> Mv <= Mv - e ==> F"), "M:real", "e:real")
          .flatMap(mp(_, Right(ePositive), Right(passes)))
        contradiction <- rules.existsElim(gap, e, absurd)
        result <- rules.falsityElim(goal, contradiction)
      } yield result

      question <- proposition(Attained)
      decided <- classical.cases(question, positive, negative)
      withTop <- rules.existsElim(supremumExists, top, decided)
      withCeiling <- rules.existsElim(boundedAt, ceiling, withTop)
      result <- List(Everywhere, "a:real <= b:real")
        .foldLeft[Either[LogicError, Kernel.Thm]](Right(withCeiling)) { (acc, text) =>
          for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
        }.flatMap(rules.genAll(_, List(f, a, b)))
    } yield result
  }

  /**
   * [[Continuity.AttainsMinimum]]: the maximum of `\y. 0 - f y`, which is continuous wherever `f` is by
   * [[Continuity.Negation]], read back through `0 - p <= 0 - q ==> q <= p`.
   */
  private def minimum(steps: Steps, maximum: Kernel.Thm, negation: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val x = Term.variable("x", Reals)
    val m = Term.variable("m", Reals)
    val Goal = s"?m:real. a:real <= m /\\ m <= b:real /\\ (!x:real. a <= x /\\ x <= b ==> $F m <= f x)"
    for {
      negated <- Parser.term(theory, notation, s"\\y:real. 0 - $F y", Functions)
      point <- proposition("a:real <= x:real /\\ x <= b:real")
      atPoint <- LogicError.lift(Kernel.assume(point))
      continuous <- assume(Everywhere).flatMap(rules.spec(x, _)).flatMap(rules.mp(_, atPoint))
      reflected <- rules.specAll(negation, List(f, x)).flatMap(rules.mp(_, continuous))
      everyPoint <- rules.disch(point, reflected).flatMap(rules.gen(x, _))
      instance <- rules.specAll(maximum, List(negated, a, b)).flatMap(reduced)
      highest <- mp(instance, assume("a:real <= b:real"), Right(everyPoint))
      body <- assume(s"a:real <= m:real /\\ m <= b:real /\\ (!x:real. a <= x /\\ x <= b ==> 0 - $F x <= 0 - f m)")
      mA <- rules.conjElim1(body)
      mB <- rules.conjElim2(body).flatMap(rules.conjElim1)
      above <- rules.conjElim2(body).flatMap(rules.conjElim2)
      under <- at(Right(above), "x:real").flatMap(rules.mp(_, atPoint)).flatMap(flipped =>
        at(lemma("!p:real q:real. 0 - p <= 0 - q ==> q <= p"), s"$F x", s"$F m").flatMap(mp(_, Right(flipped))))
      lowest <- rules.disch(point, under).flatMap(rules.gen(x, _))
      found <- conj(Right(mA), conj(Right(mB), Right(lowest)))
      witnessed <- existential(Goal).flatMap(rules.existsIntro(_, m, found))
      opened <- rules.existsElim(highest, m, witnessed)
      result <- List(Everywhere, "a:real <= b:real")
        .foldLeft[Either[LogicError, Kernel.Thm]](Right(opened)) { (acc, text) =>
          for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
        }.flatMap(rules.genAll(_, List(f, a, b)))
    } yield result
  }

  /* ----------------------------------------------------------------- the uniformity */

  /*
   * `Continuity.Uniform`, the gluing's third use. What glues is not "one radius serves for `e` on
   * `[u, v]`": two such intervals leave the pairs straddling `v` covered by neither radius. It is
   * "one radius serves every point of `[u, v]` against **every** point at all", and that glues at
   * the smaller of the two radii, since a point of `[u, w]` is in one of the halves and its partner
   * is unrestricted. Near each point `x` it holds at half the radius continuity gives for half the
   * tolerance: a point `z` of a short interval around `x` and anything within half a radius of `z`
   * are both within a radius of `x`, so both values are within half the tolerance of `f x`.
   *
   * Every `abs` is taken apart into its two sides with `ABS_ABOVE` and `ABS_ABOVE_NEG`, the sides
   * are compared by `Linarith`, and `ABS_CASES` puts them back, which is what `sides` and
   * `joined` are. No triangle inequality is named: the two sides are linear and `Linarith` adds
   * them.
   */
  /** `R u v`: one radius serves every point of `[u, v]` against every point at all. */
  private def radiusFor(lo: String, hi: String, d: String): String =
    s"!x:real. !y:real. $lo <= x /\\ x <= $hi /\\ abs (x - y) < $d ==> abs ($F x - $F y) < e:real"

  /** `|- t < c` and `|- -(t) < c` from `|- abs (t) < c`. */
  private[theories] def sides(steps: Steps, magnitude: Magnitude, t: String, c: String, bound: Kernel.Thm): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    import steps.*
    for {
      up <- at(lemma("!m:real a:real c:real. a <= m ==> m < c ==> a < c"), s"abs ($t)", s"$t", c)
        .flatMap(mp(_, at(magnitude.fact(Magnitude.AbsAbove), t), Right(bound)))
      down <- at(lemma("!m:real a:real c:real. -a <= m ==> m < c ==> -a < c"), s"abs ($t)", s"$t", c)
        .flatMap(mp(_, at(magnitude.fact(Magnitude.AbsAboveNegation), t), Right(bound)))
    } yield (up, down)
  }

  /** `|- abs (t) < c` from `|- t < c` and `|- -(t) < c`, by the two cases of `abs`. */
  private[theories] def joined(steps: Steps, magnitude: Magnitude, t: String, c: String, up: Kernel.Thm, down: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val m = s"abs ($t)"
    for {
      cases <- at(magnitude.fact(Magnitude.AbsCases), t)
      plain <- assume(s"$m = $t").flatMap(eq =>
        at(lemma("!m:real a:real c:real. m = a ==> a < c ==> m < c"), m, t, c).flatMap(mp(_, Right(eq), Right(up))))
      negated <- assume(s"$m = -($t)").flatMap(eq =>
        at(lemma("!m:real a:real c:real. m = -a ==> -a < c ==> m < c"), m, t, c).flatMap(mp(_, Right(eq), Right(down))))
      result <- rules.disjElim(cases, plain, negated)
    } yield result
  }

  private def uniformity(steps: Steps, reals: RealTheory, magnitude: Magnitude, gluing: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val e = Term.variable("e", Reals)
    val x = Term.variable("x", Reals)
    val y = Term.variable("y", Reals)
    val z = Term.variable("z", Reals)
    val u = Term.variable("u", Reals)
    val v = Term.variable("v", Reals)
    val w = Term.variable("w", Reals)
    val d = Term.variable("d", Reals)
    val d1 = Term.variable("d1", Reals)
    val d2 = Term.variable("d2", Reals)
    val ordered = assume("a:real <= b:real")
    val everywhere = assume(Everywhere)
    val tolerance = assume("0 < e:real")
    def some(lo: String, hi: String) = s"?d:real. 0 < d /\\ (${radiusFor(lo, hi, "d")})"

    for {
      total <- reals.axiom("LT_TOTAL")
      relation <- Parser.term(theory, notation, s"\\u:real. \\v:real. ${some("u", "v")}", Relations)
      instance <- rules.specAll(gluing, List(relation, a, b)).flatMap(reduced)
      parts <- antecedents(steps, instance.conclusion, 3)
      List(_, glueTerm, localTerm) = parts: @unchecked

      /* ------------------------------------------------ two radii glue at the smaller */

      glued <- {
        val premise = s"u:real <= v:real /\\ v <= w:real /\\ (${some("u", "v")}) /\\ (${some("v", "w")})"
        for {
          premiseTerm <- proposition(premise)
          assumed <- LogicError.lift(Kernel.assume(premiseTerm))
          first <- rules.conjElim2(assumed).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
          second <- rules.conjElim2(assumed).flatMap(rules.conjElim2).flatMap(rules.conjElim2)
          left <- assume(s"0 < d1:real /\\ (${radiusFor("u:real", "v:real", "d1")})")
          right <- assume(s"0 < d2:real /\\ (${radiusFor("v:real", "w:real", "d2")})")
          leftRadius <- rules.conjElim2(left)
          rightRadius <- rules.conjElim2(right)
          leftPositive <- rules.conjElim1(left)
          rightPositive <- rules.conjElim1(right)
          positive <- Continuity.minimumOfTwo(steps, magnitude, leftPositive, rightPositive)
          pointText = "u:real <= x:real /\\ x <= w:real /\\ abs (x - y:real) < min d1 d2"
          point <- proposition(pointText)
          atPoint <- LogicError.lift(Kernel.assume(point))
          ux <- rules.conjElim1(atPoint)
          xw <- rules.conjElim2(atPoint).flatMap(rules.conjElim1)
          close <- rules.conjElim2(atPoint).flatMap(rules.conjElim2)
          shorter = (bound: String, below: Either[LogicError, Kernel.Thm]) =>
            at(lemma("!m:real n:real p:real. m < n ==> n <= p ==> m < p"), "abs (x - y:real)", "min d1 d2", bound)
              .flatMap(mp(_, Right(close), below))
          value <- byOrder(steps, total, "x:real", "v:real",
            xv => shorter("d1:real", at(magnitude.fact(Magnitude.MinBelowLeft), "d1:real", "d2:real")).flatMap(near =>
              at(Right(leftRadius), "x:real", "y:real").flatMap(mp(_, conj(Right(ux), conj(Right(xv), Right(near)))))),
            vx => shorter("d2:real", at(magnitude.fact(Magnitude.MinBelowRight), "d1:real", "d2:real")).flatMap(near =>
              at(Right(rightRadius), "x:real", "y:real").flatMap(mp(_, conj(Right(vx), conj(Right(xw), Right(near)))))))
          everyPoint <- rules.disch(point, value).flatMap(rules.genAll(_, List(x, y)))
          radius <- real("min d1 d2")
          both <- rules.conjIntro(positive, everyPoint)
          witnessed <- existential(some("u:real", "w:real")).flatMap(rules.existsIntro(_, radius, both))
          withD2 <- rules.existsElim(second, d2, witnessed)
          withD1 <- rules.existsElim(first, d1, withD2)
          result <- rules.disch(premiseTerm, withD1).flatMap(rules.genAll(_, List(u, v, w)))
        } yield result
      }

      /* ------------------- continuity at half the tolerance serves a short interval, at half its radius */

      local <- {
        val small = "a:real <= u:real /\\ u <= x:real /\\ x <= v:real /\\ v <= b:real /\\ v - u < d / 2"
        for {
          point <- proposition("a:real <= x:real /\\ x <= b:real")
          atPoint <- LogicError.lift(Kernel.assume(point))
          continuous <- everywhere.flatMap(rules.spec(x, _)).flatMap(rules.mp(_, atPoint))
          epsilonDelta <- unfolded(f, x).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, continuous)))
          halfTolerance <- at(lemma("!e:real. 0 < e ==> 0 < e / 2"), "e:real").flatMap(mp(_, tolerance))
          near <- at(Right(epsilonDelta), "e / 2").flatMap(mp(_, Right(halfTolerance)))
          radius <- assume(s"0 < d:real /\\ (!y:real. abs (y - x:real) < d ==> abs ($F y - f x) < e / 2)")
          dPositive <- rules.conjElim1(radius)
          inside <- rules.conjElim2(radius)
          halfRadius <- at(lemma("!d:real. 0 < d ==> 0 < d / 2"), "d:real").flatMap(mp(_, Right(dPositive)))
          smallTerm <- proposition(small)
          interval <- LogicError.lift(Kernel.assume(smallTerm))
          ux <- rules.conjElim2(interval).flatMap(rules.conjElim1)
          xv <- rules.conjElim2(interval).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
          short <- rules.conjElim2(interval).flatMap(rules.conjElim2).flatMap(rules.conjElim2).flatMap(rules.conjElim2)

          // A point `z` of `[u, v]` and any `y` within `d / 2` of it are both within `d` of `x`.
          pairText = "u:real <= z:real /\\ z <= v:real /\\ abs (z - y:real) < d / 2"
          pair <- proposition(pairText)
          atPair <- LogicError.lift(Kernel.assume(pair))
          uz <- rules.conjElim1(atPair)
          zv <- rules.conjElim2(atPair).flatMap(rules.conjElim1)
          zy <- rules.conjElim2(atPair).flatMap(rules.conjElim2)
          zyUp <- sides(steps, magnitude, "z - y:real", "d / 2", zy)
          (zyBelow, zyAbove) = zyUp
          // `z - x` and `x - z` are under `v - u`, which is under `d / 2`.
          zxBelow <- at(lemma("!z:real x:real u:real v:real d:real. z <= v ==> u <= x ==> v - u < d / 2 ==> z - x < d / 2"),
            "z:real", "x:real", "u:real", "v:real", "d:real").flatMap(mp(_, Right(zv), Right(ux), Right(short)))
          zxAbove <- at(lemma("!z:real x:real u:real v:real d:real. u <= z ==> x <= v ==> v - u < d / 2 ==> -(z - x) < d / 2"),
            "z:real", "x:real", "u:real", "v:real", "d:real").flatMap(mp(_, Right(uz), Right(xv), Right(short)))
          zx <- joined(steps, magnitude, "z - x:real", "d / 2", zxBelow, zxAbove)
          zxWide <- at(lemma("!m:real d:real. m < d / 2 ==> 0 < d ==> m < d"), "abs (z - x:real)", "d:real")
            .flatMap(mp(_, Right(zx), Right(dPositive)))
          yxBelow <- at(lemma("!z:real y:real x:real d:real. -(z - y) < d / 2 ==> z - x < d / 2 ==> y - x < d"),
            "z:real", "y:real", "x:real", "d:real").flatMap(mp(_, Right(zyAbove), Right(zxBelow)))
          yxAbove <- at(lemma("!z:real y:real x:real d:real. z - y < d / 2 ==> -(z - x) < d / 2 ==> -(y - x) < d"),
            "z:real", "y:real", "x:real", "d:real").flatMap(mp(_, Right(zyBelow), Right(zxAbove)))
          yx <- joined(steps, magnitude, "y - x:real", "d:real", yxBelow, yxAbove)
          fz <- rules.spec(z, inside).flatMap(rules.mp(_, zxWide))
          fy <- rules.spec(y, inside).flatMap(rules.mp(_, yx))
          fzUp <- sides(steps, magnitude, s"$F z - f x", "e / 2", fz)
          fyUp <- sides(steps, magnitude, s"$F y - f x", "e / 2", fy)
          valuesBelow <- at(lemma("!p:real q:real r:real e:real. p - r < e / 2 ==> -(q - r) < e / 2 ==> p - q < e"),
            s"$F z", s"$F y", s"$F x", "e:real").flatMap(mp(_, Right(fzUp._1), Right(fyUp._2)))
          valuesAbove <- at(lemma("!p:real q:real r:real e:real. -(p - r) < e / 2 ==> q - r < e / 2 ==> -(p - q) < e"),
            s"$F z", s"$F y", s"$F x", "e:real").flatMap(mp(_, Right(fzUp._2), Right(fyUp._1)))
          values <- joined(steps, magnitude, s"$F z - f y", "e:real", valuesBelow, valuesAbove)
          everyPair <- rules.disch(pair, values).flatMap(rules.genAll(_, List(z, y)))
          radiusTerm <- real("d / 2")
          serves <- rules.conjIntro(halfRadius, everyPair)
          target <- existential(s"?d1:real. 0 < d1 /\\ (${radiusFor("u:real", "v:real", "d1")})")
          served <- rules.existsIntro(target, radiusTerm, serves)
          everyInterval <- rules.disch(smallTerm, served).flatMap(rules.genAll(_, List(u, v)))
          both <- rules.conjIntro(halfRadius, everyInterval)
          localTarget <- existential(
            s"?r:real. 0 < r /\\ (!u:real. !v:real. a:real <= u /\\ u <= x:real /\\ x <= v /\\ v <= b:real /\\ v - u < r ==> " +
              s"(${some("u", "v")}))")
          witnessed <- rules.existsIntro(localTarget, radiusTerm, both)
          opened <- rules.existsElim(near, d, witnessed)
          result <- rules.disch(point, opened).flatMap(rules.gen(x, _))
        } yield result
      }

      _ <- if (glued.conclusion == glueTerm) Right(()) else Left(NotOfForm("the gluing premise", glued.conclusion))
      _ <- if (local.conclusion == localTerm) Right(()) else Left(NotOfForm("the local premise", local.conclusion))
      concluded <- mp(instance, ordered, Right(glued), Right(local))

      /* ------------------------------------------ the whole interval, read as the published form */

      published <- {
        val bothIn = "a:real <= x:real /\\ x <= b:real /\\ a <= y:real /\\ y <= b /\\ abs (x - y) < d"
        for {
          radius <- assume(s"0 < d:real /\\ (${radiusFor("a:real", "b:real", "d")})")
          positive <- rules.conjElim1(radius)
          serves <- rules.conjElim2(radius)
          pointTerm <- proposition(bothIn)
          atPoint <- LogicError.lift(Kernel.assume(pointTerm))
          ax <- rules.conjElim1(atPoint)
          xb <- rules.conjElim2(atPoint).flatMap(rules.conjElim1)
          close <- rules.conjElim2(atPoint).flatMap(rules.conjElim2).flatMap(rules.conjElim2).flatMap(rules.conjElim2)
          value <- at(Right(serves), "x:real", "y:real").flatMap(mp(_, conj(Right(ax), conj(Right(xb), Right(close)))))
          everyPair <- rules.disch(pointTerm, value).flatMap(rules.genAll(_, List(x, y)))
          both <- rules.conjIntro(positive, everyPair)
          finalTarget <- existential(
            s"?d:real. 0 < d /\\ (!x:real. !y:real. a:real <= x /\\ x <= b:real /\\ a <= y /\\ y <= b /\\ abs (x - y) < d ==> " +
              s"abs ($F x - $F y) < e:real)")
          witnessed <- rules.existsIntro(finalTarget, d, both)
          result <- rules.existsElim(concluded, d, witnessed)
        } yield result
      }

      result <- List("0 < e:real", Everywhere, "a:real <= b:real")
        .foldLeft[Either[LogicError, Kernel.Thm]](Right(published)) { (acc, text) =>
          for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
        }.flatMap(rules.genAll(_, List(f, a, b, e)))
    } yield result
  }
}
