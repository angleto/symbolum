package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * L'Hopital's rule for `0 / 0` at a point, the fact [[Derivative.LHopital]] publishes.
 *
 * == The argument ==
 *
 * Near `x`, at a `y` with `0 < abs (y - x) < r`, the two functions are continuous on the closed
 * interval between `x` and `y` (at `x` by hypothesis, elsewhere because they are differentiable
 * there) and differentiable inside it, so [[Derivative.CauchyMeanValue]] gives a `c` strictly
 * between with `f y * dg c = g y * df c`, the values at `x` being zero. `g y` is not zero, since
 * otherwise [[Derivative.Rolle]] would put a zero of `dg` between `x` and `y`, where the hypothesis
 * says there is none; so `f y / g y = df c / dg c`, which `Field` decides once both denominators are
 * known not to vanish. And `c` is nearer `x` than `y` is, so the radius the limit of `df / dg` gives
 * at a tolerance serves `f / g` at the same one, cut down to `r`.
 *
 * The side `y` is on is read off `ABS_CASES` at `y - x`, and the two sides are one derivation with
 * the interval's ends exchanged. Every inequality about an absolute value is `Linarith` handed the
 * two cases of that absolute value and the lower bounds `ABS_ABOVE` and `ABS_ABOVE_NEG` give, since
 * `abs` is an atom to it.
 */
private[theories] object LHopitalRule {

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Functions: Type = Type.fun(Reals, Reals)

  private val Neighbourhood: String =
    "!y:real. 0 < abs (y - x:real) /\\ abs (y - x) < r:real ==> derivative (f:real -> real) y ((df:real -> real) y) /\\ " +
      "derivative (g:real -> real) y ((dg:real -> real) y) /\\ ~(dg y = 0)"
  private val Ratio: String = "tends (\\y:real. (df:real -> real) y / (dg:real -> real) y) x:real l:real"
  private val Hypotheses: List[String] = List(
    "0 < r:real",
    Neighbourhood,
    "continuous (f:real -> real) x:real",
    "continuous (g:real -> real) x:real",
    "(f:real -> real) x:real = 0",
    "(g:real -> real) x:real = 0",
    Ratio)

  /** What the derivation reads, by name. */
  final case class Sources(
    steps: Continuity.Steps,
    magnitude: Magnitude,
    field: Field,
    tendsDefinition: Kernel.Thm,
    total: Kernel.Thm,
    continuous: Kernel.Thm,
    rolle: Kernel.Thm,
    unique: Kernel.Thm,
    cauchy: Kernel.Thm
  )

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv.betaNormalise(theorem.conclusion).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, theorem)))

  /** `|- tends f x l = <the statement>`, reduced. */
  private def unfoldTends(sources: Sources, f: Term, x: Term, l: Term): Either[LogicError, Kernel.Thm] =
    for {
      equation <- Conv.unfold(sources.tendsDefinition, List(f, x, l))
      right <- rightOf(equation)
      normal <- Conv.betaNormalise(right)
      joined <- Conv.trans(equation, normal)
    } yield joined

  /** `|- goal` by `Linarith` from `known`, each read as a premise. */
  private def decide(sources: Sources, known: List[Kernel.Thm], goal: Term): Either[LogicError, Kernel.Thm] = {
    import sources.steps.*
    for {
      implication <- known.reverse.foldLeft[Either[LogicError, Term]](Right(goal))((acc, k) => acc.flatMap(logic.mkImp(k.conclusion, _)))
      decided <- linarith.prove(implication)
      result <- known.foldLeft[Either[LogicError, Kernel.Thm]](Right(decided))((acc, k) => acc.flatMap(rules.mp(_, k)))
    } yield result
  }

  /**
   * `|- goal` by [[decide]] in each case of `abs z`, with the lower bounds of `abs z` and of every
   * absolute value in `bounded` among the premises.
   */
  private def byCases(sources: Sources, z: String, bounded: List[String], known: List[Kernel.Thm], goal: String): Either[LogicError, Kernel.Thm] = {
    import sources.steps.*
    val magnitude = sources.magnitude
    for {
      goalTerm <- proposition(goal)
      lower <- (z :: bounded).foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (acc, t) =>
        for {
          done <- acc
          above <- at(magnitude.fact(Magnitude.AbsAbove), t)
          aboveNegation <- at(magnitude.fact(Magnitude.AbsAboveNegation), t)
        } yield done ++ List(above, aboveNegation)
      }
      cases <- at(magnitude.fact(Magnitude.AbsCases), z)
      disjuncts <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      first <- LogicError.lift(Kernel.assume(disjuncts._1)).flatMap(c => decide(sources, known ++ lower :+ c, goalTerm))
      second <- LogicError.lift(Kernel.assume(disjuncts._2)).flatMap(c => decide(sources, known ++ lower :+ c, goalTerm))
      result <- rules.disjElim(cases, first, second)
    } yield result
  }

  def prove(sources: Sources): Either[LogicError, Kernel.Thm] = {
    val steps = sources.steps
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val df = Term.variable("df", Functions)
    val dg = Term.variable("dg", Functions)
    val x = Term.variable("x", Reals)
    val l = Term.variable("l", Reals)
    val r = Term.variable("r", Reals)
    val y = Term.variable("y", Reals)
    val c = Term.variable("c", Reals)
    val e = Term.variable("e", Reals)
    val d = Term.variable("d", Reals)
    val Near = "0 < abs (y:real - x:real) /\\ abs (y - x) < r:real"
    val Between = "?c:real. 0 < abs (c - x:real) /\\ abs (c - x) < abs (y:real - x) /\\ " +
      "(f:real -> real) y / (g:real -> real) y = (df:real -> real) c / (dg:real -> real) c"

    for {
      assumed <- Hypotheses.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (acc, text) =>
        for { done <- acc; one <- assume(text) } yield done :+ one
      }
      List(radiusPositive, neighbourhood, continuousF, continuousG, fZero, gZero, ratio) = assumed: @unchecked

      /* ------------------------------------------------ at one y near x, a c between with the same ratio */
      near <- assume(Near)
      nearPositive <- rules.conjElim1(near)
      nearInside <- rules.conjElim2(near)
      between <- for {
        cases <- at(sources.magnitude.fact(Magnitude.AbsCases), "y:real - x:real")
        disjuncts <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
        right <- LogicError.lift(Kernel.assume(disjuncts._1)).flatMap(side(sources, _, List(nearPositive, nearInside), "x:real", "y:real", Between))
        left <- LogicError.lift(Kernel.assume(disjuncts._2)).flatMap(side(sources, _, List(nearPositive, nearInside), "y:real", "x:real", Between))
        result <- rules.disjElim(cases, right, left)
      } yield result
      betweenEverywhere <- rules.disch(near.conclusion, between).flatMap(rules.gen(y, _))

      /* ------------------------------------------------ the radius at e */
      ratioFn <- Parser.term(theory, notation, "\\y:real. (df:real -> real) y / (dg:real -> real) y", Functions)
      ratioOpened <- unfoldTends(sources, ratioFn, x, l).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, ratio)))
      positive <- proposition("0 < e:real")
      ePositive <- LogicError.lift(Kernel.assume(positive))
      nearRatio <- rules.spec(e, ratioOpened).flatMap(rules.mp(_, ePositive))
      radius <- assume("0 < d:real /\\ (!y:real. 0 < abs (y - x:real) /\\ abs (y - x) < d ==> " +
        "abs ((df:real -> real) y / (dg:real -> real) y - l:real) < e:real)")
      dPositive <- rules.conjElim1(radius)
      ratioInside <- rules.conjElim2(radius)
      minimumPositive <- Continuity.minimumOf(steps, sources.magnitude, "d:real", "r:real", dPositive, radiusPositive)
      everyY <- for {
        member <- proposition("0 < abs (y:real - x:real) /\\ abs (y - x) < min (d:real) (r:real)")
        assumedMember <- LogicError.lift(Kernel.assume(member))
        memberPositive <- rules.conjElim1(assumedMember)
        memberInside <- rules.conjElim2(assumedMember)
        belowD <- at(sources.magnitude.fact(Magnitude.MinBelowLeft), "d:real", "r:real")
        belowR <- at(sources.magnitude.fact(Magnitude.MinBelowRight), "d:real", "r:real")
        withinD <- at(lemma("!A:real w:real d:real. A < w ==> w <= d ==> A < d"), "abs (y:real - x:real)", "min (d:real) (r:real)", "d:real")
          .flatMap(mp(_, Right(memberInside), Right(belowD)))
        withinR <- at(lemma("!A:real w:real d:real. A < w ==> w <= d ==> A < d"), "abs (y:real - x:real)", "min (d:real) (r:real)", "r:real")
          .flatMap(mp(_, Right(memberInside), Right(belowR)))
        inNeighbourhood <- rules.conjIntro(memberPositive, withinR)
        found <- rules.spec(y, betweenEverywhere).flatMap(rules.mp(_, inNeighbourhood))
        atC <- for {
          body <- assume("0 < abs (c:real - x:real) /\\ abs (c - x) < abs (y:real - x) /\\ " +
            "(f:real -> real) y / (g:real -> real) y = (df:real -> real) c / (dg:real -> real) c")
          cPositive <- rules.conjElim1(body)
          cCloser <- rules.conjElim2(body).flatMap(rules.conjElim1)
          same <- rules.conjElim2(body).flatMap(rules.conjElim2)
          cWithinD <- at(lemma("!A:real B:real d:real. A < B ==> B < d ==> A < d"), "abs (c:real - x:real)", "abs (y:real - x:real)", "d:real")
            .flatMap(mp(_, Right(cCloser), Right(withinD)))
          ratioAtC <- rules.spec(c, ratioInside).flatMap(t => rules.conjIntro(cPositive, cWithinD).flatMap(rules.mp(t, _)))
          minus <- real("u:real - v:real")
          subtraction <- minus match {
            case App(App(op, _), _) => Right(op)
            case other              => Left(NotOfForm("a subtraction", other))
          }
          absolute <- Parser.term(theory, notation, "abs", Functions)
          shifted <- Conv.apTerm(subtraction, same).flatMap(Conv.apThm(_, l)).flatMap(Conv.apTerm(absolute, _))
          result <- lemma("!P:real Q:real e:real. P = Q ==> Q < e ==> P < e")
            .flatMap(t => Term.destEq(shifted.conclusion).toRight(NotOfForm("an equation", shifted.conclusion))
              .flatMap(sides => rules.specAll(t, List(sides._1, sides._2, e))))
            .flatMap(mp(_, Right(shifted), Right(ratioAtC)))
        } yield result
        closer <- rules.existsElim(found, c, atC)
        closed <- rules.disch(member, closer).flatMap(rules.gen(y, _))
      } yield closed
      pair <- rules.conjIntro(minimumPositive, everyY)
      minimum <- real("min (d:real) (r:real)")
      witnessed <- existential("?d:real. 0 < d /\\ (!y:real. 0 < abs (y - x:real) /\\ abs (y - x) < d ==> " +
        "abs ((f:real -> real) y / (g:real -> real) y - l:real) < e:real)").flatMap(rules.existsIntro(_, minimum, pair))
      withoutD <- rules.existsElim(nearRatio, d, witnessed)
      statement <- rules.disch(positive, withoutD).flatMap(rules.gen(e, _))
      quotientFn <- Parser.term(theory, notation, "\\y:real. (f:real -> real) y / (g:real -> real) y", Functions)
      folded <- unfoldTends(sources, quotientFn, x, l).flatMap(Conv.sym).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, statement)))
      closed <- assumed.reverse.foldLeft[Either[LogicError, Kernel.Thm]](Right(folded))((acc, h) => acc.flatMap(rules.disch(h.conclusion, _)))
        .flatMap(rules.genAll(_, List(f, g, df, dg, x, l, r)))
    } yield closed
  }

  /**
   * `Between` at the `y` assumed near `x`, on the side where the interval is `[lo, hi]`: `branch` is
   * the case of `abs (y - x)` that says which side, and `nearFacts` are `0 < abs (y - x)` and
   * `abs (y - x) < r`. The hypotheses of the rule are assumed as they are written.
   */
  private def side(
    sources: Sources,
    branch: Kernel.Thm,
    nearFacts: List[Kernel.Thm],
    lo: String,
    hi: String,
    betweenText: String
  ): Either[LogicError, Kernel.Thm] = {
    val steps = sources.steps
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val t = Term.variable("t", Reals)
    val c = Term.variable("c", Reals)
    val m = Term.variable("m", Reals)
    val n = Term.variable("n", Reals)
    val known = branch :: nearFacts
    val bounded = List("y:real - x:real")

    /** `0 < abs (p - x) /\ abs (p - x) < r` from what is known about `p`, which is not `x`. */
    def inNeighbourhood(point: String, facts: List[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for {
        positive <- byCases(sources, s"$point - x:real", bounded, known ++ facts, s"0 < abs ($point - x:real)")
        inside <- byCases(sources, s"$point - x:real", bounded, known ++ facts, s"abs ($point - x:real) < r:real")
        both <- rules.conjIntro(positive, inside)
      } yield both

    /** `derivative f p (df p) /\ derivative g p (dg p) /\ ~(dg p = 0)` from the neighbourhood at `p`. */
    def slopes(point: Term, near: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        neighbourhood <- assume(Neighbourhood)
        result <- rules.spec(point, neighbourhood).flatMap(rules.mp(_, near))
      } yield result

    /** `!t. lo <= t /\ t <= hi ==> continuous h t`, for `h` one of `f` and `g`. */
    def continuousOn(h: String, which: Int): Either[LogicError, Kernel.Thm] =
      for {
        member <- proposition(s"$lo <= t:real /\\ t <= $hi")
        assumedMember <- LogicError.lift(Kernel.assume(member))
        lower <- rules.conjElim1(assumedMember)
        upper <- rules.conjElim2(assumedMember)
        x <- real("x:real")
        order <- rules.specAll(sources.total, List(t, x))
        split <- logic.destDisj(order.conclusion).toRight(NotOfForm("a disjunction", order.conclusion))
        rest <- logic.destDisj(split._2).toRight(NotOfForm("a disjunction", split._2))
        viaSlope = (strict: Kernel.Thm) =>
          for {
            near <- inNeighbourhood("t:real", List(lower, upper, strict))
            all <- slopes(t, near)
            one <- (if (which == 0) rules.conjElim1(all) else rules.conjElim2(all).flatMap(rules.conjElim1))
            continuous <- one.conclusion match {
              case App(App(App(_, fn), point), slope) => rules.specAll(sources.continuous, List(fn, point, slope)).flatMap(rules.mp(_, one))
              case other                              => Left(NotOfForm("a derivative", other))
            }
          } yield continuous
        below <- LogicError.lift(Kernel.assume(split._1)).flatMap(viaSlope)
        equal <- for {
          same <- LogicError.lift(Kernel.assume(rest._1))
          atX <- assume(s"continuous $h x:real")
          head <- atX.conclusion match {
            case App(prefix, _) => Right(prefix)
            case other          => Left(NotOfForm("a continuity", other))
          }
          back <- Conv.sym(same)
          moved <- Conv.apTerm(head, back).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, atX)))
        } yield moved
        above <- LogicError.lift(Kernel.assume(rest._2)).flatMap(viaSlope)
        inner <- LogicError.lift(Kernel.assume(split._2)).flatMap(rules.disjElim(_, equal, above))
        joined <- rules.disjElim(order, below, inner)
        closed <- rules.disch(member, joined).flatMap(rules.gen(t, _))
      } yield closed

    /** `!t. lo < t /\ t < hi ==> ?m. derivative h t m`. */
    def differentiableOn(h: String, which: Int): Either[LogicError, Kernel.Thm] =
      for {
        member <- proposition(s"$lo < t:real /\\ t < $hi")
        assumedMember <- LogicError.lift(Kernel.assume(member))
        lower <- rules.conjElim1(assumedMember)
        upper <- rules.conjElim2(assumedMember)
        near <- inNeighbourhood("t:real", List(lower, upper))
        all <- slopes(t, near)
        one <- (if (which == 0) rules.conjElim1(all) else rules.conjElim2(all).flatMap(rules.conjElim1))
        slope <- one.conclusion match {
          case App(_, s) => Right(s)
          case other     => Left(NotOfForm("a derivative", other))
        }
        predicate <- proposition(s"?m:real. derivative $h t:real m").flatMap(p => logic.destExistsPredicate(p).toRight(NotOfForm("an existential", p)))
        witnessed <- rules.existsIntro(predicate, slope, one)
        closed <- rules.disch(member, witnessed).flatMap(rules.gen(t, _))
      } yield closed

    for {
      ordered <- proposition(s"$lo < $hi").flatMap(decide(sources, known, _))
      loTerm <- real(lo)
      hiTerm <- real(hi)
      continuousF <- continuousOn("(f:real -> real)", 0)
      continuousG <- continuousOn("(g:real -> real)", 1)
      differentiableF <- differentiableOn("(f:real -> real)", 0)
      differentiableG <- differentiableOn("(g:real -> real)", 1)
      fZero <- assume("(f:real -> real) x:real = 0")
      gZero <- assume("(g:real -> real) x:real = 0")

      /* ------------------------------------------------ g y is not zero, by Rolle */
      gNonZero <- for {
        vanishing <- proposition("(g:real -> real) y:real = 0")
        assumedVanishing <- LogicError.lift(Kernel.assume(vanishing))
        level <- at(lemma("!A:real B:real. A = 0 ==> B = 0 ==> A = B"), s"(g:real -> real) $lo", s"(g:real -> real) $hi")
          .flatMap(t => if (lo.startsWith("x")) mp(t, Right(gZero), Right(assumedVanishing)) else mp(t, Right(assumedVanishing), Right(gZero)))
        flatSomewhere <- rules.specAll(sources.rolle, List(g, loTerm, hiTerm))
          .flatMap(mp(_, Right(ordered), Right(continuousG), Right(differentiableG), Right(level)))
        absurd <- for {
          body <- assume(s"$lo < c:real /\\ c < $hi /\\ derivative (g:real -> real) c 0")
          lower <- rules.conjElim1(body)
          upper <- rules.conjElim2(body).flatMap(rules.conjElim1)
          flat <- rules.conjElim2(body).flatMap(rules.conjElim2)
          near <- inNeighbourhood("c:real", List(lower, upper))
          all <- slopes(c, near)
          slopeG <- rules.conjElim2(all).flatMap(rules.conjElim1)
          notZero <- rules.conjElim2(all).flatMap(rules.conjElim2)
          value <- real("(dg:real -> real) c:real")
          zero <- real("0:real")
          equal <- rules.specAll(sources.unique, List(g, c, value, zero)).flatMap(mp(_, Right(slopeG), Right(flat)))
          contradiction <- rules.notElim(notZero, equal)
        } yield contradiction
        eliminated <- rules.existsElim(flatSomewhere, c, absurd)
        refused <- rules.notIntro(vanishing, eliminated)
      } yield refused

      /* ------------------------------------------------ Cauchy between the ends */
      mean <- rules.specAll(sources.cauchy, List(f, g, loTerm, hiTerm))
        .flatMap(mp(_, Right(ordered), Right(continuousF), Right(continuousG), Right(differentiableF), Right(differentiableG)))
      numerator <- real("(f:real -> real) y:real / (g:real -> real) y")
      ratio <- real("(df:real -> real) c:real / (dg:real -> real) c")
      difference <- real("(f:real -> real) y:real / (g:real -> real) y - (df:real -> real) c:real / (dg:real -> real) c")
      scale <- real("inv ((g:real -> real) y:real) * inv ((dg:real -> real) c:real)")
      cross <- real("(f:real -> real) y:real * (dg:real -> real) c:real - (g:real -> real) y * (df:real -> real) c")
      times <- real("u:real * v:real").flatMap {
        case App(App(op, _), _) => Right(op)
        case other              => Left(NotOfForm("a product", other))
      }
      byScale <- LogicError.lift(Term.app(times, scale))
      scaled <- LogicError.lift(Term.app(byScale, cross))
      // f y / g y - df c / dg c is inv (g y) * inv (dg c) times the cross difference, as an identity
      // of the field under the two denominators it names.
      identity <- LogicError.lift(Term.eq(difference, scaled)).flatMap(sources.field.prove)
      crossedGoal <- proposition("(f:real -> real) y:real * (dg:real -> real) c:real = (g:real -> real) y * (df:real -> real) c")
      betweenGoal <- proposition(betweenText)
      predicate <- logic.destExistsPredicate(betweenGoal).toRight(NotOfForm("an existential", betweenGoal))
      atThePoint = (body: Term) =>
        for {
          assumedBody <- LogicError.lift(Kernel.assume(body))
          lower <- rules.conjElim1(assumedBody)
          upper <- rules.conjElim2(assumedBody).flatMap(rules.conjElim1)
          slopeF <- rules.conjElim2(assumedBody).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
          slopeG <- rules.conjElim2(assumedBody).flatMap(rules.conjElim2).flatMap(rules.conjElim2).flatMap(rules.conjElim1)
          balance <- rules.conjElim2(assumedBody).flatMap(rules.conjElim2).flatMap(rules.conjElim2).flatMap(rules.conjElim2)
          near <- inNeighbourhood("c:real", List(lower, upper))
          all <- slopes(c, near)
          ownF <- rules.conjElim1(all)
          ownG <- rules.conjElim2(all).flatMap(rules.conjElim1)
          dgNonZero <- rules.conjElim2(all).flatMap(rules.conjElim2)
          dfc <- real("(df:real -> real) c:real")
          dgc <- real("(dg:real -> real) c:real")
          mIs <- rules.specAll(sources.unique, List(f, c, m, dfc)).flatMap(mp(_, Right(slopeF), Right(ownF)))
          nIs <- rules.specAll(sources.unique, List(g, c, n, dgc)).flatMap(mp(_, Right(slopeG), Right(ownG)))
          values <- Rewrite.Rule.all(logic, Vector(fZero, gZero, mIs, nIs))
          rewritten <- Rewrite.inTheorem(values, balance)
          crossed <- decide(sources, List(rewritten), crossedGoal)
          cleared <- List(gNonZero, dgNonZero).foldLeft[Either[LogicError, Kernel.Thm]](Right(identity)) { (acc, proof) =>
            acc.flatMap(current =>
              if (current.hypotheses.contains(proof.conclusion)) rules.disch(proof.conclusion, current).flatMap(rules.mp(_, proof))
              else Right(current))
          }
          crossZero <- lemma("!P:real Q:real. P = Q ==> P - Q = 0")
            .flatMap(t => Term.destEq(crossed.conclusion).toRight(NotOfForm("an equation", crossed.conclusion))
              .flatMap(sides => rules.specAll(t, List(sides._1, sides._2))))
            .flatMap(rules.mp(_, crossed))
          substituted <- Conv.apTerm(byScale, crossZero)
          sameRatio <- lemma("!A:real B:real M:real K:real. A - B = M ==> M = K * 0 ==> A = B")
            .flatMap(rules.specAll(_, List(numerator, ratio, scaled, scale)))
            .flatMap(mp(_, Right(cleared), Right(substituted)))
          cPositive <- byCases(sources, "c:real - x:real", bounded, known ++ List(lower, upper), "0 < abs (c:real - x:real)")
          cCloser <- byCases(sources, "c:real - x:real", bounded, known ++ List(lower, upper), "abs (c:real - x:real) < abs (y:real - x)")
          conjunction <- conj(Right(cPositive), conj(Right(cCloser), Right(sameRatio)))
          witnessed <- rules.existsIntro(predicate, c, conjunction)
        } yield witnessed
      result <- eliminateFrom(steps, mean, List(c, m, n), atThePoint)
    } yield result
  }

  /** The body of an existential at a variable, with the root application contracted. */
  private def instanceOf(logic: Logic, existential: Term, witness: Term): Either[LogicError, Term] =
    for {
      predicate <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
      applied <- LogicError.lift(Term.app(predicate, witness))
      body <- Conv.betaRoot(applied).flatMap(rightOf)
    } yield body

  /**
   * From `?x1 ... xn. body` assumed, whatever `useBody` proves from the body at the variables: the
   * existentials are eliminated from the inside out.
   */
  private def eliminate(steps: Continuity.Steps, existential: Term, variables: List[FVar], useBody: Term => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    variables match {
      case Nil => useBody(existential)
      case variable :: rest =>
        for {
          body <- instanceOf(steps.logic, existential, variable)
          inner <- eliminate(steps, body, rest, useBody)
          assumed <- LogicError.lift(Kernel.assume(existential))
          result <- steps.rules.existsElim(assumed, variable, inner)
        } yield result
    }

  /** [[eliminate]] from a proved existential. */
  private def eliminateFrom(steps: Continuity.Steps, existential: Kernel.Thm, variables: List[FVar], useBody: Term => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    for {
      opened <- eliminate(steps, existential.conclusion, variables, useBody)
      closed <- steps.rules.disch(existential.conclusion, opened)
      result <- steps.rules.mp(closed, existential)
    } yield result
}
