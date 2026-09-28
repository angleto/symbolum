package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The derivative of a power and Taylor's theorem with the remainder in Lagrange's form, the two
 * facts [[Derivative.Power]] and [[Derivative.Taylor]] publish.
 *
 * == The statement ==
 *
 * The derivatives are a **family** `D : num -> real -> real` handed in as a hypothesis, `D (SUC k)`
 * the derivative of `D k`, rather than an n-th derivative defined as a constant: a constant would
 * have to be chosen, and what a caller holds is always the family, `\k. exp` for the exponential and
 * a table for a polynomial. The hypotheses are the textbook's and exactly what Rolle asks for:
 * `D k` continuous on `[a, b]` and differentiable inside, for every `k <= n`. The conclusion has no
 * quotient: `k!` enters as `inv (real_of_num (NUM_FACT k))`, which is never a division by zero
 * because the factorial never vanishes.
 *
 * == The argument ==
 *
 * Rolle at `psi t = p * S t + q * H t`, where `S t` is the Taylor polynomial of degree `n` expanded
 * at `t` and read at `b`, `H t = Power (b - t) (SUC n)`, `p = 0 - H a` and `q = 0 - (D 0 b - S a)`.
 * At `b` the polynomial is `D 0 b`, every other term carrying a factor `b - b`, and `H b` is zero,
 * so `psi a = psi b`. The derivative of `S` telescopes: term `k`'s derivative is the difference of
 * two consecutive terms of `inv (k!) * D (SUC k) t * Power (b - t) k`, because `(k + 1) * inv ((k +
 * 1)!)` is `inv (k!)`, and what is left is the last. Rolle's point then gives the remainder after
 * cancelling `Power (b - c) n`, which is positive because `c < b`.
 *
 * == The algebra is `Field`'s, once each side is written out ==
 *
 * Every equation between two terms here is proved the same way: both sides are rewritten with the
 * recurrences of the power, the sum and the factorial, and `Field` is handed the two normal forms,
 * with each denominator it needs to be non-zero discharged by the positivity of what it is. Two
 * things about that are decisions rather than details. `real_of_num (SUC n)` is **not** rewritten to
 * `real_of_num n + 1` except at zero: the product `n! * (n + 1)` would be multiplied out into a sum,
 * and `Field` takes a product under an inverse apart and a sum not. And a sum over a lambda is
 * handed to `Field` as a variable: its summand's denominator has its index bound by the lambda, and
 * `Field` would otherwise read it as a denominator of the whole.
 */
private[theories] object TaylorExpansion {

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Functions: Type = Type.fun(Reals, Reals)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Family: Type = Type.fun(Numbers, Functions)

  /** The family, written the way every text here writes it. */
  private val D = "(D:num -> real -> real)"

  private def weight(k: String): String = s"inv (real_of_num (NUM_FACT $k))"

  /** The Taylor polynomial of degree `n` expanded at `t` and read at `b`, as a function of `t`. */
  private def polynomial(n: String): String =
    s"\\t:real. Sum (\\k:num. ${weight("k")} * $D k t * Power (b:real - t) k) (SUC $n)"

  private val AtA: String = s"Sum (\\k:num. ${weight("k")} * $D k a:real * Power (b:real - a) k) (SUC n:num)"
  private val Remainder: String = s"${weight("(SUC n:num)")} * $D (SUC n) c:real * Power (b:real - a:real) (SUC n)"
  private val Conclusion: String = s"?c:real. a:real < c /\\ c < b:real /\\ $D ZERO b = $AtA + $Remainder"
  private val ContinuousHypothesis: String =
    s"!k:num. !x:real. NUM_LE k n:num ==> a:real <= x /\\ x <= b:real ==> continuous ($D k) x"
  private val SlopeHypothesis: String =
    s"!k:num. !x:real. NUM_LE k n:num ==> a:real < x /\\ x < b:real ==> derivative ($D k) x ($D (SUC k) x)"

  /** The same three for [[Derivative.TaylorLeft]], where the point read is below the one expanded at. */
  private val LeftConclusion: String = s"?c:real. b:real < c /\\ c < a:real /\\ $D ZERO b = $AtA + $Remainder"
  private val LeftContinuousHypothesis: String =
    s"!k:num. !x:real. NUM_LE k n:num ==> b:real <= x /\\ x <= a:real ==> continuous ($D k) x"
  private val LeftSlopeHypothesis: String =
    s"!k:num. !x:real. NUM_LE k n:num ==> b:real < x /\\ x < a:real ==> derivative ($D k) x ($D (SUC k) x)"

  /** What every fact here needs: the steps, the field tactic, induction, and the three rule sets. */
  private final case class Kit(
    steps: Continuity.Steps,
    field: Field,
    induction: Kernel.Thm,
    fact: String => Either[LogicError, Kernel.Thm],
    /** The power, the factorial and the embedding of a product, and `real_of_num (SUC ZERO) = 1`. */
    arithmetic: Vector[Rewrite.Rule],
    /** [[arithmetic]] and the two recurrences of the sum. */
    sums: Vector[Rewrite.Rule],
    /** [[arithmetic]] and the embedding of every successor, for the power's derivative, which has no inverse. */
    counting: Vector[Rewrite.Rule]
  )

  def prove(
    steps: Continuity.Steps,
    transcendental: Transcendental,
    coding: Coding,
    continuity: Continuity,
    held: Map[String, Kernel.Thm]
  ): Either[LogicError, Map[String, Kernel.Thm]] = {
    import steps.*
    val series = transcendental.series
    val peano = transcendental.limit.peano
    def fact(name: String): Either[LogicError, Kernel.Thm] =
      held.get(name)
        .orElse(continuity.facts.get(name))
        .orElse(series.facts.get(name))
        .orElse(coding.facts.get(name))
        .orElse(peano.facts.get(name))
        .toRight(MissingDefinition(name))
    def facts(names: String*): Either[LogicError, Vector[Kernel.Thm]] =
      names.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, name) =>
        for { done <- acc; one <- fact(name) } yield done :+ one
      }
    for {
      field <- Field.construct(series.ring.arithmetic)
      induction <- peano.naturals.fact(Natural.Induction)
      recurrences <- facts(Series.PowerAtSuccessor, Series.PowerAtZero, Coding.FactorialAtSuccessor, Coding.FactorialAtZero,
        Peano.EmbedsProduct)
      zero <- Parser.term(theory, notation, "ZERO", Numbers)
      embeddedOne <- fact(Peano.EmbedsSuccessor).flatMap(rules.spec(zero, _))
      embeddedZero <- fact(Peano.EmbedsZero)
      one <- at(lemma("!R:real Z:real. R = Z + 1 ==> Z = 0 ==> R = 1"), "real_of_num (SUC ZERO)", "real_of_num ZERO")
        .flatMap(mp(_, Right(embeddedOne), Right(embeddedZero)))
      sumRecurrences <- facts(Series.AtSuccessor, Series.AtZero)
      embeddings <- facts(Peano.EmbedsSuccessor, Peano.EmbedsZero)
      arithmetic <- Rewrite.Rule.all(logic, recurrences :+ one)
      sums <- Rewrite.Rule.all(logic, (recurrences :+ one) ++ sumRecurrences)
      counting <- Rewrite.Rule.all(logic, recurrences ++ embeddings)
      kit = Kit(steps, field, induction, fact, arithmetic, sums, counting)

      power <- powerSlope(kit)
      reflected <- reflectedSlope(kit, power)
      product <- fact(Continuity.Product)
      powers <- powerContinuous(kit, product)
      continuousSums <- sumContinuous(kit, product, powers)
      slopes <- sumSlope(kit, reflected)
      atEnd <- sumAtEnd(kit)
      rolle <- fact(Derivative.Rolle)
      unique <- fact(Derivative.Unique)
      theorem <- taylor(kit, rolle, unique, powers, continuousSums, slopes, atEnd, reflected)
      left <- taylorLeft(kit, theorem)
    } yield Map(Derivative.Power -> power, Derivative.Taylor -> theorem, Derivative.TaylorLeft -> left)
  }

  /* ------------------------------------------------------------------ shared pieces */

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv.betaNormalise(theorem.conclusion).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, theorem)))

  private def proving(target: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    if (theorem.conclusion == target) Right(theorem) else Left(NotEqualTo(target, theorem.conclusion))

  /** A head and its arguments: `derivative F x m` is `derivative` and `F, x, m`. */
  private def spine(term: Term): (Term, List[Term]) = {
    def go(t: Term, arguments: List[Term]): (Term, List[Term]) = t match {
      case App(f, x) => go(f, x :: arguments)
      case other     => (other, arguments)
    }
    go(term, Nil)
  }

  /** The function a `derivative` or `continuous` fact is about. */
  private def functionOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    spine(theorem.conclusion)._2.headOption.toRight(NotOfForm("a fact about a function", theorem.conclusion))

  /** The slope a `derivative` fact names. */
  private def slopeOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    spine(theorem.conclusion)._2.lift(2).toRight(NotOfForm("a derivative", theorem.conclusion))

  /** `body` with `variable` replaced by `value`. */
  private def instance(body: Term, variable: FVar, value: Term): Either[LogicError, Term] =
    LogicError.lift(Term.abs(variable, body)).flatMap(p => LogicError.lift(Term.app(p, value)))
      .flatMap(Conv.betaRoot).flatMap(rightOf)

  /**
   * `|- !n. body` by induction on `n`: `base` proves the body at `ZERO`, and `step` the body at
   * `SUC n` with the body at `n` assumed. Each is handed the instance it has to prove and is held to
   * it exactly.
   */
  private def induct(
    kit: Kit,
    n: FVar,
    body: Term,
    base: Term => Either[LogicError, Kernel.Thm],
    step: Term => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    for {
      zero <- Parser.term(theory, notation, "ZERO", Numbers)
      successor <- Parser.term(theory, notation, s"SUC ${n.name}:num", Numbers)
      atZero <- instance(body, n, zero)
      atSuccessor <- instance(body, n, successor)
      baseProof <- base(atZero).flatMap(proving(atZero, _))
      stepProof <- step(atSuccessor).flatMap(proving(atSuccessor, _))
      stepClosed <- rules.disch(body, stepProof).flatMap(rules.gen(n, _))
      predicate <- LogicError.lift(Term.abs(n, body))
      opened <- rules.spec(predicate, kit.induction).flatMap(reduced)
      premise <- rules.conjIntro(baseProof, stepClosed)
      result <- rules.mp(opened, premise)
    } yield result
  }

  /** The hypotheses `~(d = 0)` of a theorem `Field` proved, each discharged by `provider`. */
  private def discharged(kit: Kit, theorem: Kernel.Thm, provider: Term => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    theorem.hypotheses.foldLeft[Either[LogicError, Kernel.Thm]](Right(theorem)) { (acc, hypothesis) =>
      for {
        current <- acc
        proof <- provider(hypothesis).flatMap(proving(hypothesis, _))
        closed <- kit.steps.rules.disch(hypothesis, current)
        result <- kit.steps.rules.mp(closed, proof)
      } yield result
    }

  /**
   * Every sum over a lambda in `term` replaced by a variable, the same sum by the same variable, with
   * what each variable stands for.
   */
  private def opaque(term: Term, found: Vector[(Term, FVar)]): Either[LogicError, (Term, Vector[(Term, FVar)])] = term match {
    case App(App(Const(Series.SumName, _), _: Abs), _) =>
      found.find(_._1 == term) match {
        case Some((_, variable)) => Right((variable, found))
        case None =>
          val variable = Term.variable(s"sum_${found.size}", Term.typeOf(term))
          Right((variable, found :+ (term -> variable)))
      }
    case App(f, x) =>
      for {
        left <- opaque(f, found)
        right <- opaque(x, left._2)
        rebuilt <- LogicError.lift(Term.app(left._1, right._1))
      } yield (rebuilt, right._2)
    case other => Right((other, found))
  }

  /**
   * `|- lhs = rhs`: both sides rewritten with `rules`, the sums over a lambda made opaque, the two
   * forms equal by `Field`, and each denominator `Field` needed discharged by `provider`. A rule that
   * did not fire leaves the two forms apart, and `Field` refuses rather than proving something else.
   */
  private def equalBy(
    kit: Kit,
    rules: Vector[Rewrite.Rule],
    lhs: Term,
    rhs: Term,
    provider: Term => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      left <- Rewrite.rewrite(rules, lhs)
      right <- Rewrite.rewrite(rules, rhs)
      l <- rightOf(left)
      r <- rightOf(right)
      openedLeft <- opaque(l, Vector.empty)
      openedRight <- opaque(r, openedLeft._2)
      standing = openedRight._2
      middle <- LogicError.lift(Term.eq(openedLeft._1, openedRight._1)).flatMap(kit.field.prove)
      cleared <- discharged(kit, middle, provider)
      general <- kit.steps.rules.genAll(cleared, standing.map(_._2).toList)
      restored <- kit.steps.rules.specAll(general, standing.map(_._1).toList)
      expected <- LogicError.lift(Term.eq(l, r))
      checked <- proving(expected, restored)
      back <- Conv.sym(right)
      result <- Conv.trans(left, checked).flatMap(Conv.trans(_, back))
    } yield result

  /** `(\t. l) = (\t. r)` from the equation of the two bodies at `t`, which `Kernel.abs` lifts at no cost. */
  private def functionsEqual(
    kit: Kit,
    rules: Vector[Rewrite.Rule],
    t: FVar,
    lhs: Term,
    rhs: Term,
    provider: Term => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      l <- LogicError.lift(Term.app(lhs, t)).flatMap(Conv.betaRoot).flatMap(rightOf)
      r <- LogicError.lift(Term.app(rhs, t)).flatMap(Conv.betaRoot).flatMap(rightOf)
      pointwise <- equalBy(kit, rules, l, r, provider)
      result <- LogicError.lift(Kernel.abs(t, pointwise))
    } yield result

  /**
   * A `derivative F x m` or `continuous F x` fact restated as `target`, which names the same point:
   * the function by [[functionsEqual]] and the slope by [[equalBy]], each only where they differ.
   */
  private def restate(
    kit: Kit,
    rules: Vector[Rewrite.Rule],
    theorem: Kernel.Thm,
    target: Term,
    provider: Term => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val u = Term.variable("u", Reals)
    val (head, have) = spine(theorem.conclusion)
    val (_, want) = spine(target)
    def equal(h: Term, w: Term, prove: => Either[LogicError, Kernel.Thm]) = if (h == w) Right(Kernel.refl(h)) else prove
    for {
      pairs <- if (have.size == want.size && have.size >= 2) Right(have.zip(want)) else Left(NotEqualTo(target, theorem.conclusion))
      functionEq <- equal(pairs.head._1, pairs.head._2, functionsEqual(kit, rules, u, pairs.head._1, pairs.head._2, provider))
      rest <- pairs.tail.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { case (acc, (h, w)) =>
        for { done <- acc; eq <- equal(h, w, equalBy(kit, rules, h, w, provider)) } yield done :+ eq
      }
      start <- Conv.apTerm(head, functionEq)
      whole <- rest.foldLeft[Either[LogicError, Kernel.Thm]](Right(start)) { (acc, eq) =>
        acc.flatMap(current => LogicError.lift(Kernel.mkComb(current, eq)))
      }
      result <- LogicError.lift(Kernel.eqMp(whole, theorem))
      checked <- proving(target, result)
    } yield checked
  }

  /**
   * `~(d = 0)` for the denominators this file meets, by `Linarith` from what is known about the parts
   * of `d`: a factorial is positive, an embedded successor is one more than something non-negative,
   * any embedded number is non-negative, and a power is positive when `positives` makes its base so.
   */
  private def provider(kit: Kit, positives: List[Kernel.Thm])(hypothesis: Term): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    def lessThan(left: Term, right: Term): Either[LogicError, Term] =
      for {
        template <- proposition("0:real < 1")
        operator = spine(template)._1
        applied <- LogicError.lift(Term.app(operator, left)).flatMap(f => LogicError.lift(Term.app(f, right)))
      } yield applied
    def fromKnown(known: List[Kernel.Thm], goal: Term): Either[LogicError, Kernel.Thm] =
      for {
        implication <- known.reverse.foldLeft[Either[LogicError, Term]](Right(goal))((acc, k) => acc.flatMap(logic.mkImp(k.conclusion, _)))
        decided <- kit.steps.linarith.prove(implication)
        result <- known.foldLeft[Either[LogicError, Kernel.Thm]](Right(decided))((acc, k) => acc.flatMap(rules.mp(_, k)))
      } yield result
    def about(term: Term): List[Either[LogicError, Kernel.Thm]] = term match {
      case App(Const(Peano.EmbeddingName, _), factorial @ App(Const(Coding.FactorialName, _), m)) =>
        List(for {
          positive <- kit.fact(Coding.FactorialPositive).flatMap(rules.spec(m, _))
          zero <- Parser.term(theory, notation, "ZERO", Numbers)
          gap <- kit.fact(Peano.EmbedsStrictOrder).flatMap(rules.specAll(_, List(zero, factorial))).flatMap(rules.mp(_, positive))
          embedsZero <- kit.fact(Peano.EmbedsZero)
          embeddedZero <- Term.destEq(embedsZero.conclusion).map(_._1).toRight(NotOfForm("an equation", embedsZero.conclusion))
          result <- lemma("!Z:real R:real. Z + 1 <= R ==> Z = 0 ==> 0 < R")
            .flatMap(rules.specAll(_, List(embeddedZero, term))).flatMap(mp(_, Right(gap), Right(embedsZero)))
        } yield result)
      case App(Const(Peano.EmbeddingName, _), App(Const(Natural.NumberSuccessor, _), m)) =>
        List(kit.fact(Peano.EmbedsSuccessor).flatMap(rules.spec(m, _)), kit.fact(Peano.EmbedsNonNegative).flatMap(rules.spec(m, _)))
      case App(Const(Peano.EmbeddingName, _), m) =>
        List(kit.fact(Peano.EmbedsNonNegative).flatMap(rules.spec(m, _)))
      case App(App(Const(Series.PowerName, _), base), m) =>
        List(for {
          zero <- real("0:real")
          goal <- lessThan(zero, base)
          basePositive <- fromKnown(positives, goal)
          result <- kit.fact(Series.PowerPositive).flatMap(rules.spec(base, _)).flatMap(rules.mp(_, basePositive)).flatMap(rules.spec(m, _))
        } yield result)
      case App(f, x) => about(f) ++ about(x)
      case _         => Nil
    }
    for {
      denominator <- (hypothesis match {
        case App(_, equation) => Term.destEq(equation).map(_._1)
        case _                => None
      }).toRight(NotOfForm("a denominator that is not zero", hypothesis))
      known <- about(denominator).foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (acc, e) =>
        for { done <- acc; one <- e } yield done :+ one
      }
      zero <- real("0:real")
      goal <- lessThan(zero, denominator)
      positive <- fromKnown(known, goal)
      nonZero <- lemma("!D:real. 0 < D ==> ~(D = 0)").flatMap(rules.spec(denominator, _)).flatMap(rules.mp(_, positive))
    } yield nonZero
  }

  private def plainly(kit: Kit): Term => Either[LogicError, Kernel.Thm] = provider(kit, Nil)

  /** From `!k. NUM_LE k m ==> P k` assumed, `!k. NUM_LE k n ==> P k` for the `n` below `m = SUC n`. */
  private def below(kit: Kit, assumed: Kernel.Thm, n: FVar): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    val k = Term.variable("k", Numbers)
    for {
      successor <- Parser.term(theory, notation, s"SUC ${n.name}:num", Numbers)
      le <- assume(s"NUM_LE k:num ${n.name}:num")
      step <- kit.fact(Peano.AtMostSuccessor).flatMap(rules.spec(n, _))
      chained <- kit.fact(Peano.Transitive).flatMap(rules.specAll(_, List(k, n, successor)))
        .flatMap(t => rules.conjIntro(le, step).flatMap(rules.mp(t, _)))
      at <- rules.spec(k, assumed).flatMap(rules.mp(_, chained))
      closed <- rules.disch(le.conclusion, at).flatMap(rules.gen(k, _))
    } yield closed
  }

  /** `P m` from `!k. NUM_LE k m ==> P k` assumed, at `k = m`. */
  private def atTop(kit: Kit, assumed: Kernel.Thm, m: Term): Either[LogicError, Kernel.Thm] =
    for {
      le <- kit.fact(Peano.Reflexive).flatMap(kit.steps.rules.spec(m, _))
      result <- kit.steps.rules.spec(m, assumed).flatMap(kit.steps.rules.mp(_, le))
    } yield result

  /* ------------------------------------------------------------------ the power */

  /**
   * [[Derivative.Power]], by induction on the exponent: at one it is the identity, and `y * Power y
   * (SUC n)` has by the product rule the slope `Power x (SUC n) + x * ((n + 1) * Power x n)`.
   */
  private def powerSlope(kit: Kit): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    val x = Term.variable("x", Reals)
    val n = Term.variable("n", Numbers)
    for {
      body <- proposition("derivative (\\y:real. Power y (SUC n:num)) (x:real) (real_of_num (SUC n) * Power x n)")
      identitySlope <- kit.fact(Derivative.Identity).flatMap(rules.spec(x, _))
      identity <- Parser.term(theory, notation, "\\y:real. y", Functions)
      one <- real("1:real")
      all <- induct(kit, n, body,
        target => restate(kit, kit.counting, identitySlope, target, plainly(kit)),
        target =>
          for {
            hypothesis <- LogicError.lift(Kernel.assume(body))
            function <- functionOf(hypothesis)
            slope <- slopeOf(hypothesis)
            product <- kit.fact(Derivative.ProductRule).flatMap(rules.specAll(_, List(identity, function, x, one, slope)))
              .flatMap(reduced).flatMap(mp(_, Right(identitySlope), Right(hypothesis)))
            result <- restate(kit, kit.counting, product, target, plainly(kit))
          } yield result)
      closed <- rules.gen(x, all)
    } yield closed
  }

  /**
   * `derivative (\t. Power (b - t) (SUC m)) x (real_of_num (SUC m) * Power (b - x) m * (0 - 1))`, with
   * `m`, `b` and `x` free: [[Derivative.Power]] after `\t. b - t`, by the chain rule.
   */
  private def reflectedSlope(kit: Kit, power: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    val x = Term.variable("x", Reals)
    val b = Term.variable("b", Reals)
    val m = Term.variable("m", Numbers)
    for {
      constant <- kit.fact(Derivative.Constant).flatMap(rules.specAll(_, List(b, x)))
      identitySlope <- kit.fact(Derivative.Identity).flatMap(rules.spec(x, _))
      constantFn <- Parser.term(theory, notation, "\\y:real. b:real", Functions)
      identity <- Parser.term(theory, notation, "\\y:real. y", Functions)
      zero <- real("0:real")
      one <- real("1:real")
      minusOne <- real("0 - 1:real")
      linear <- kit.fact(Derivative.Linear).flatMap(rules.specAll(_, List(constantFn, identity, x, zero, one, one, minusOne)))
        .flatMap(reduced).flatMap(mp(_, Right(constant), Right(identitySlope)))
      inner <- proposition("derivative (\\t:real. b:real - t) (x:real) (0 - 1)").flatMap(restate(kit, kit.arithmetic, linear, _, plainly(kit)))
      distance <- real("b:real - x:real")
      outer <- rules.specAll(power, List(distance, m))
      outerFn <- Parser.term(theory, notation, "\\y:real. Power y (SUC m:num)", Functions)
      innerFn <- functionOf(inner)
      outerSlope <- slopeOf(outer)
      chained <- kit.fact(Derivative.ChainRule).flatMap(rules.specAll(_, List(outerFn, innerFn, x, outerSlope, minusOne)))
        .flatMap(reduced).flatMap(mp(_, Right(inner), Right(outer)))
    } yield chained
  }

  /** `!k. continuous (\t. Power (b - t) k) x`, `b` and `x` free, by induction through [[Continuity.Product]]. */
  private def powerContinuous(kit: Kit, product: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    val x = Term.variable("x", Reals)
    val b = Term.variable("b", Reals)
    val k = Term.variable("k", Numbers)
    for {
      body <- proposition("continuous (\\t:real. Power (b:real - t) k:num) x:real")
      one <- real("1:real")
      minusOne <- real("0 - 1:real")
      constantOne <- kit.fact(Continuity.Constant).flatMap(rules.specAll(_, List(one, x)))
      constantB <- kit.fact(Continuity.Constant).flatMap(rules.specAll(_, List(b, x)))
      identity <- kit.fact(Continuity.Identity).flatMap(rules.spec(x, _))
      constantFn <- Parser.term(theory, notation, "\\y:real. b:real", Functions)
      identityFn <- Parser.term(theory, notation, "\\y:real. y", Functions)
      linear <- kit.fact(Continuity.Linear).flatMap(rules.specAll(_, List(constantFn, identityFn, x, one, minusOne)))
        .flatMap(reduced).flatMap(mp(_, Right(constantB), Right(identity)))
      distance <- proposition("continuous (\\t:real. b:real - t) x:real").flatMap(restate(kit, kit.arithmetic, linear, _, plainly(kit)))
      all <- induct(kit, k, body,
        target => restate(kit, kit.arithmetic, constantOne, target, plainly(kit)),
        target =>
          for {
            hypothesis <- LogicError.lift(Kernel.assume(body))
            distanceFn <- functionOf(distance)
            powerFn <- functionOf(hypothesis)
            joined <- rules.specAll(product, List(distanceFn, powerFn, x)).flatMap(reduced)
              .flatMap(mp(_, Right(distance), Right(hypothesis)))
            result <- restate(kit, kit.arithmetic, joined, target, plainly(kit))
          } yield result)
    } yield all
  }

  /* ------------------------------------------------------------------ the polynomial */

  /** The weight of the `k`-th term, `inv (real_of_num (NUM_FACT k))`, at a term `k`. */
  private def weightAt(kit: Kit, k: Term): Either[LogicError, Term] = {
    val index = Term.variable("index", Numbers)
    kit.steps.real(weight("(index:num)")).flatMap(instance(_, index, k))
  }

  /** From `continuous (D k) x`, `continuous (\y. (inv (k!) * D k y + 0 * D k y) * Power (b - y) k) x`. */
  private def termContinuous(kit: Kit, product: Kernel.Thm, powers: Kernel.Thm, k: Term, derivativeK: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    val x = Term.variable("x", Reals)
    for {
      family <- Parser.term(theory, notation, D, Family)
      function <- LogicError.lift(Term.app(family, k))
      scale <- weightAt(kit, k)
      zero <- real("0:real")
      scaled <- kit.fact(Continuity.Linear).flatMap(rules.specAll(_, List(function, function, x, scale, zero)))
        .flatMap(reduced).flatMap(mp(_, Right(derivativeK), Right(derivativeK)))
      power <- rules.spec(k, powers)
      scaledFn <- functionOf(scaled)
      powerFn <- functionOf(power)
      joined <- rules.specAll(product, List(scaledFn, powerFn, x)).flatMap(reduced).flatMap(mp(_, Right(scaled), Right(power)))
    } yield joined
  }

  /**
   * `!n. (!k. NUM_LE k n ==> continuous (D k) x) ==> continuous (<the polynomial of degree n>) x`,
   * with `D`, `b` and `x` free: each term is continuous by [[Continuity.Product]], and a sum of two by
   * [[Continuity.Linear]].
   */
  private def sumContinuous(kit: Kit, product: Kernel.Thm, powers: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    val x = Term.variable("x", Reals)
    val n = Term.variable("n", Numbers)
    for {
      body <- proposition(s"(!k:num. NUM_LE k n:num ==> continuous ($D k) x:real) ==> continuous (${polynomial("n:num")}) x")
      zero <- Parser.term(theory, notation, "ZERO", Numbers)
      successor <- Parser.term(theory, notation, "SUC n:num", Numbers)
      one <- real("1:real")
      all <- induct(kit, n, body,
        target =>
          for {
            parts <- logic.destImp(target).toRight(NotOfForm("an implication", target))
            assumed <- LogicError.lift(Kernel.assume(parts._1))
            first <- atTop(kit, assumed, zero)
            term <- termContinuous(kit, product, powers, zero, first)
            restated <- restate(kit, kit.sums, term, parts._2, plainly(kit))
            result <- rules.disch(parts._1, restated)
          } yield result,
        target =>
          for {
            parts <- logic.destImp(target).toRight(NotOfForm("an implication", target))
            assumed <- LogicError.lift(Kernel.assume(parts._1))
            hypothesis <- LogicError.lift(Kernel.assume(body))
            previous <- below(kit, assumed, n).flatMap(rules.mp(hypothesis, _))
            last <- atTop(kit, assumed, successor)
            term <- termContinuous(kit, product, powers, successor, last)
            previousFn <- functionOf(previous)
            termFn <- functionOf(term)
            combined <- kit.fact(Continuity.Linear).flatMap(rules.specAll(_, List(previousFn, termFn, x, one, one)))
              .flatMap(reduced).flatMap(mp(_, Right(previous), Right(term)))
            restated <- restate(kit, kit.sums, combined, parts._2, plainly(kit))
            result <- rules.disch(parts._1, restated)
          } yield result)
    } yield all
  }

  /**
   * `!n. (!k. NUM_LE k n ==> derivative (D k) x (D (SUC k) x)) ==>
   * derivative (<the polynomial of degree n>) x (inv (n!) * D (SUC n) x * Power (b - x) n)`, with `D`,
   * `b` and `x` free. The telescoping: the next term's derivative is the next slope minus this one.
   */
  private def sumSlope(kit: Kit, reflected: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    val x = Term.variable("x", Reals)
    val n = Term.variable("n", Numbers)
    val m = Term.variable("m", Numbers)
    /** `derivative (\y. c * D k y + 0 * D k y) x (c * m + 0 * m)` from `derivative (D k) x m`: `D k` as a lambda, scaled. */
    def scaled(slope: Kernel.Thm, coefficient: Term): Either[LogicError, Kernel.Thm] =
      for {
        function <- functionOf(slope)
        value <- slopeOf(slope)
        zero <- real("0:real")
        result <- kit.fact(Derivative.Linear).flatMap(rules.specAll(_, List(function, function, x, value, value, coefficient, zero)))
          .flatMap(reduced).flatMap(mp(_, Right(slope), Right(slope)))
      } yield result
    for {
      body <- proposition(
        s"(!k:num. NUM_LE k n:num ==> derivative ($D k) (x:real) ($D (SUC k) x)) ==> " +
          s"derivative (${polynomial("n:num")}) x (${weight("n")} * $D (SUC n) x * Power (b:real - x) n)")
      zero <- Parser.term(theory, notation, "ZERO", Numbers)
      successor <- Parser.term(theory, notation, "SUC n:num", Numbers)
      one <- real("1:real")
      all <- induct(kit, n, body,
        target =>
          for {
            parts <- logic.destImp(target).toRight(NotOfForm("an implication", target))
            assumed <- LogicError.lift(Kernel.assume(parts._1))
            first <- atTop(kit, assumed, zero)
            lambda <- scaled(first, one)
            restated <- restate(kit, kit.sums, lambda, parts._2, plainly(kit))
            result <- rules.disch(parts._1, restated)
          } yield result,
        target =>
          for {
            parts <- logic.destImp(target).toRight(NotOfForm("an implication", target))
            assumed <- LogicError.lift(Kernel.assume(parts._1))
            hypothesis <- LogicError.lift(Kernel.assume(body))
            previous <- below(kit, assumed, n).flatMap(rules.mp(hypothesis, _))
            last <- atTop(kit, assumed, successor)
            scale <- weightAt(kit, successor)
            u <- scaled(last, scale)
            v <- rules.gen(m, reflected).flatMap(rules.spec(n, _))
            uFn <- functionOf(u)
            vFn <- functionOf(v)
            uSlope <- slopeOf(u)
            vSlope <- slopeOf(v)
            term <- kit.fact(Derivative.ProductRule).flatMap(rules.specAll(_, List(uFn, vFn, x, uSlope, vSlope)))
              .flatMap(reduced).flatMap(mp(_, Right(u), Right(v)))
            previousFn <- functionOf(previous)
            termFn <- functionOf(term)
            previousSlope <- slopeOf(previous)
            termSlope <- slopeOf(term)
            combined <- kit.fact(Derivative.Linear).flatMap(rules.specAll(_, List(previousFn, termFn, x, previousSlope, termSlope, one, one)))
              .flatMap(reduced).flatMap(mp(_, Right(previous), Right(term)))
            restated <- restate(kit, kit.sums, combined, parts._2, plainly(kit))
            result <- rules.disch(parts._1, restated)
          } yield result)
    } yield all
  }

  /** `!n. Sum (\k. inv (k!) * D k b * Power (b - b) k) (SUC n) = D ZERO b`, `D` and `b` free. */
  private def sumAtEnd(kit: Kit): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    val n = Term.variable("n", Numbers)
    val summand = s"(\\k:num. ${weight("k")} * $D k b:real * Power (b - b) k)"
    for {
      body <- proposition(s"Sum $summand (SUC n:num) = $D ZERO b:real")
      f <- Parser.term(theory, notation, summand, Type.fun(Numbers, Reals))
      successor <- Parser.term(theory, notation, "SUC n:num", Numbers)
      zero <- real("0:real")
      joining <- lemma("!A:real S:real T:real Z:real. A = S + T ==> S = Z ==> T = 0 ==> A = Z")
      all <- induct(kit, n, body,
        target => Term.destEq(target).toRight(NotOfForm("an equation", target)).flatMap(sides => equalBy(kit, kit.sums, sides._1, sides._2, plainly(kit))),
        target =>
          for {
            hypothesis <- LogicError.lift(Kernel.assume(body))
            split <- kit.fact(Series.AtSuccessor).flatMap(rules.specAll(_, List(f, successor))).flatMap(reduced)
            sides <- Term.destEq(split.conclusion).toRight(NotOfForm("an equation", split.conclusion))
            last <- sides._2 match {
              case App(App(_, _), t) => Right(t)
              case other             => Left(NotOfForm("a sum of two", other))
            }
            vanishes <- equalBy(kit, kit.arithmetic, last, zero, plainly(kit))
            previous <- Term.destEq(hypothesis.conclusion).toRight(NotOfForm("an equation", hypothesis.conclusion))
            joined <- rules.specAll(joining, List(sides._1, previous._1, last, previous._2))
              .flatMap(mp(_, Right(split), Right(hypothesis), Right(vanishes)))
          } yield joined)
    } yield all
  }

  /* ------------------------------------------------------------------ the theorem */

  /** [[Derivative.Taylor]]: Rolle at `psi`, as the file's opening describes. */
  private def taylor(
    kit: Kit,
    rolle: Kernel.Thm,
    unique: Kernel.Thm,
    powers: Kernel.Thm,
    sums: Kernel.Thm,
    slopes: Kernel.Thm,
    atEnd: Kernel.Thm,
    reflected: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    val family = Term.variable("D", Family)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val x = Term.variable("x", Reals)
    val c = Term.variable("c", Reals)
    val n = Term.variable("n", Numbers)
    val k = Term.variable("k", Numbers)
    val m = Term.variable("m", Numbers)
    val slopeVariable = Term.variable("slope", Reals)

    /** `!k. NUM_LE k n ==> <the hypothesis at k and the point>`, with the point's membership assumed. */
    def atPoint(hypothesis: Kernel.Thm, point: Term, member: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        le <- assume("NUM_LE k:num n:num")
        at <- rules.specAll(hypothesis, List(k, point)).flatMap(mp(_, Right(le), Right(member)))
        closed <- rules.disch(le.conclusion, at).flatMap(rules.gen(k, _))
      } yield closed

    for {
      ordered <- assume("a:real < b:real")
      continuousHypothesis <- assume(ContinuousHypothesis)
      slopeHypothesis <- assume(SlopeHypothesis)
      p <- real("0 - Power (b:real - a:real) (SUC n:num)")
      q <- real(s"0 - ($D ZERO b:real - $AtA)")
      successor <- Parser.term(theory, notation, "SUC n:num", Numbers)
      power <- rules.spec(successor, powers)
      powerFn <- functionOf(power)

      /* ---------------------------------------------------------- psi is continuous on [a, b] */
      continuous <- for {
        member <- proposition("a:real <= x:real /\\ x <= b:real")
        assumed <- LogicError.lift(Kernel.assume(member))
        polynomialThere <- atPoint(continuousHypothesis, x, assumed).flatMap(each => rules.spec(n, sums).flatMap(rules.mp(_, each)))
        polynomialFn <- functionOf(polynomialThere)
        combined <- kit.fact(Continuity.Linear).flatMap(rules.specAll(_, List(polynomialFn, powerFn, x, p, q)))
          .flatMap(reduced).flatMap(mp(_, Right(polynomialThere), Right(power)))
        closed <- rules.disch(member, combined).flatMap(rules.gen(x, _))
      } yield closed
      psi <- Logic.stripForall(continuous.conclusion)
        .flatMap(stripped => logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2)))
        .map(parts => spine(parts._2)._2.head)

      /* ---------------------------------------------------------- psi's slope inside */
      slopeAt = (point: Term, member: Kernel.Thm) =>
        for {
          each <- atPoint(slopeHypothesis, point, member)
          polynomialSlope <- rules.gen(x, slopes).flatMap(rules.specAll(_, List(point, n))).flatMap(rules.mp(_, each))
          powerSlope <- rules.genAll(reflected, List(x, m)).flatMap(rules.specAll(_, List(point, n)))
          polynomialFn <- functionOf(polynomialSlope)
          reflectedFn <- functionOf(powerSlope)
          first <- slopeOf(polynomialSlope)
          second <- slopeOf(powerSlope)
          combined <- kit.fact(Derivative.Linear).flatMap(rules.specAll(_, List(polynomialFn, reflectedFn, point, first, second, p, q)))
            .flatMap(reduced).flatMap(mp(_, Right(polynomialSlope), Right(powerSlope)))
        } yield combined
      differentiable <- for {
        member <- proposition("a:real < x:real /\\ x < b:real")
        assumed <- LogicError.lift(Kernel.assume(member))
        slope <- slopeAt(x, assumed)
        value <- slopeOf(slope)
        derivativeConstant = spine(slope.conclusion)._1
        predicate <- LogicError.lift(Term.app(derivativeConstant, psi))
          .flatMap(f => LogicError.lift(Term.app(f, x)))
          .flatMap(f => LogicError.lift(Term.app(f, slopeVariable)))
          .flatMap(body => LogicError.lift(Term.abs(slopeVariable, body)))
        witnessed <- rules.existsIntro(predicate, value, slope)
        closed <- rules.disch(member, witnessed).flatMap(rules.gen(x, _))
      } yield closed

      /* ---------------------------------------------------------- psi a = psi b */
      rolleAt <- rules.specAll(rolle, List(psi, a, b)).flatMap(reduced)
      level <- {
        def premises(t: Term): List[Term] = logic.destImp(t) match {
          case Some((h, rest)) => h :: premises(rest)
          case None            => Nil
        }
        premises(rolleAt.conclusion).lift(3).toRight(NotOfForm("Rolle's four hypotheses", rolleAt.conclusion))
      }
      ends <- Term.destEq(level).toRight(NotOfForm("an equation", level))
      polynomialAtB <- rules.spec(n, atEnd)
      powerAtB <- real("Power (b:real - b) (SUC n:num)").flatMap(t => real("0:real").flatMap(equalBy(kit, kit.arithmetic, t, _, plainly(kit))))
      endRules <- Rewrite.Rule.all(logic, Vector(polynomialAtB, powerAtB))
      balanced <- equalBy(kit, endRules, ends._1, ends._2, plainly(kit))
      flatSomewhere <- mp(rolleAt, Right(ordered), Right(continuous), Right(differentiable), Right(balanced))

      /* ---------------------------------------------------------- the remainder, at Rolle's point */
      found <- for {
        inside <- flatSomewhere.conclusion match {
          case App(_, lambda) => LogicError.lift(Term.app(lambda, c)).flatMap(Conv.betaRoot).flatMap(rightOf)
          case other          => Left(NotOfForm("an existential", other))
        }
        assumed <- LogicError.lift(Kernel.assume(inside))
        above <- rules.conjElim1(assumed)
        underB <- rules.conjElim2(assumed).flatMap(rules.conjElim1)
        flat <- rules.conjElim2(assumed).flatMap(rules.conjElim2)
        member <- rules.conjIntro(above, underB)
        slope <- slopeAt(c, member)
        value <- slopeOf(slope)
        zero <- real("0:real")
        vanishing <- rules.specAll(unique, List(psi, c, value, zero)).flatMap(mp(_, Right(slope), Right(flat)))
        gap <- at(lemma("!c:real b:real. c < b ==> 0 < b - c"), "c:real", "b:real").flatMap(rules.mp(_, underB))

        // D ZERO b - (S a + R) is inv (Power (b - c) n) * inv (n + 1) times psi's slope at c, as an
        // identity of the field; the slope is zero, so the difference is.
        difference <- real(s"$D ZERO b:real - ($AtA + $Remainder)")
        scale <- real("inv (Power (b:real - c:real) n:num) * inv (real_of_num (SUC n))")
        times <- real("x:real * y:real").map(t => spine(t)._1)
        byScale <- LogicError.lift(Term.app(times, scale))
        scaled <- LogicError.lift(Term.app(byScale, value))
        identity <- equalBy(kit, kit.arithmetic, difference, scaled, provider(kit, List(gap)))
        substituted <- Conv.apTerm(byScale, vanishing)
        atB <- real(s"$D ZERO b:real")
        polynomialAtA <- real(AtA)
        remainder <- real(Remainder)
        equation <- lemma("!A:real B:real C:real M:real K:real. A - (B + C) = M ==> M = K * 0 ==> A = B + C")
          .flatMap(rules.specAll(_, List(atB, polynomialAtA, remainder, scaled, scale)))
          .flatMap(mp(_, Right(identity), Right(substituted)))

        conjunction <- conj(Right(above), conj(Right(underB), Right(equation)))
        goal <- proposition(Conclusion)
        predicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
        witnessed <- rules.existsIntro(predicate, c, conjunction)
        eliminated <- rules.existsElim(flatSomewhere, c, witnessed)
      } yield eliminated

      closed <- List(slopeHypothesis, continuousHypothesis, ordered).foldLeft[Either[LogicError, Kernel.Thm]](Right(found)) { (acc, h) =>
        acc.flatMap(rules.disch(h.conclusion, _))
      }.flatMap(rules.genAll(_, List(family, a, b, n)))
    } yield closed
  }

  /* ------------------------------------------------------------------ expanding to the left */

  /**
   * [[Derivative.TaylorLeft]]: the same expansion at `a` read at a point `b` **below** it, which is
   * the half of the textbook's statement [[Derivative.Taylor]] does not cover, since it asks `a < b`.
   *
   * By reflection rather than by a second Rolle argument: [[Derivative.Taylor]] at the family
   * `E k t = Power (0 - 1) k * D k (0 - t)` over `[0 - a, 0 - b]`. Each `E k` is continuous where
   * `D k` is at the mirrored point, by composition with `\t. 0 - t` and a constant factor, and its
   * derivative is `E (SUC k)`, by the chain rule: the inner slope is `0 - 1` and it is absorbed into
   * the sign's exponent. What comes back is read at `0 - a`, `0 - b` and the mirrored Rolle point,
   * where `Power (0 - 1) k * Power ((0 - b) - (0 - a)) k` is `Power (b - a) k` once both are written
   * over `Power (a - b) k`; that identity is the only algebra here, and `Field` checks it pointwise
   * under the sum's binder.
   *
   * A separate statement rather than one with `~(a = b)` and the point between the two, because every
   * caller knows which side it is on and a disjunction in the conclusion would make each of them
   * split it. The conclusion's formula is word for word the right-hand one's, so a reader compares
   * the two by the order hypotheses alone.
   */
  private def taylorLeft(kit: Kit, taylor: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import kit.steps.*
    val family = Term.variable("D", Family)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val x = Term.variable("x", Reals)
    val z = Term.variable("z", Reals)
    val n = Term.variable("n", Numbers)
    val k = Term.variable("k", Numbers)
    val reflection = s"\\k:num. \\t:real. Power (0 - 1) k * $D k (0 - t)"

    /** `b <= 0 - x /\ 0 - x <= a` from the mirrored membership, or the strict one. */
    def mirrored(member: Kernel.Thm, strict: Boolean): Either[LogicError, Kernel.Thm] = {
      val le = if (strict) "<" else "<="
      for {
        lower <- at(lemma(s"!a:real b:real x:real. 0 - a $le x /\\ x $le 0 - b ==> b $le 0 - x"), "a:real", "b:real", "x:real")
          .flatMap(rules.mp(_, member))
        upper <- at(lemma(s"!a:real b:real x:real. 0 - a $le x /\\ x $le 0 - b ==> 0 - x $le a"), "a:real", "b:real", "x:real")
          .flatMap(rules.mp(_, member))
        both <- rules.conjIntro(lower, upper)
      } yield both
    }

    for {
      ordered <- assume("b:real < a:real")
      continuousHypothesis <- assume(LeftContinuousHypothesis)
      slopeHypothesis <- assume(LeftSlopeHypothesis)
      family0 <- Parser.term(theory, notation, reflection, Family)
      minusA <- real("0 - a:real")
      minusB <- real("0 - b:real")
      instance <- rules.specAll(taylor, List(family0, minusA, minusB, n)).flatMap(reduced)
      flipped <- at(lemma("!a:real b:real. b < a ==> 0 - a < 0 - b"), "a:real", "b:real").flatMap(rules.mp(_, ordered))
      point <- real("0 - x:real")
      sign <- real("Power (0 - 1) k:num")
      dk <- Parser.term(theory, notation, s"$D k:num", Functions)
      identityFn <- Parser.term(theory, notation, "\\y:real. y", Functions)
      zero <- real("0:real")
      one <- real("1:real")

      /* ---------------------------------------------------------- each E k is continuous */
      continuous <- for {
        le <- assume("NUM_LE k:num n:num")
        member <- proposition("0 - a:real <= x:real /\\ x <= 0 - b:real")
        assumedMember <- LogicError.lift(Kernel.assume(member))
        there <- mirrored(assumedMember, strict = false)
        outer <- rules.specAll(continuousHypothesis, List(k, point)).flatMap(mp(_, Right(le), Right(there)))
        identity <- kit.fact(Continuity.Identity).flatMap(rules.spec(x, _))
        inner <- kit.fact(Continuity.Negation).flatMap(rules.specAll(_, List(identityFn, x))).flatMap(reduced)
          .flatMap(rules.mp(_, identity))
        innerFn <- functionOf(inner)
        composed <- kit.fact(Continuity.Compose).flatMap(rules.specAll(_, List(dk, innerFn, x))).flatMap(reduced)
          .flatMap(mp(_, Right(inner), Right(outer)))
        constant <- kit.fact(Continuity.Constant).flatMap(rules.specAll(_, List(sign, x)))
        constantFn <- functionOf(constant)
        composedFn <- functionOf(composed)
        product <- kit.fact(Continuity.Product).flatMap(rules.specAll(_, List(constantFn, composedFn, x))).flatMap(reduced)
          .flatMap(mp(_, Right(constant), Right(composed)))
        closed <- rules.disch(member, product).flatMap(rules.disch(le.conclusion, _)).flatMap(rules.genAll(_, List(k, x)))
      } yield closed

      /* ---------------------------------------------------------- and has E (SUC k) for its slope */
      differentiable <- for {
        le <- assume("NUM_LE k:num n:num")
        member <- proposition("0 - a:real < x:real /\\ x < 0 - b:real")
        assumedMember <- LogicError.lift(Kernel.assume(member))
        there <- mirrored(assumedMember, strict = true)
        outer <- rules.specAll(slopeHypothesis, List(k, point)).flatMap(mp(_, Right(le), Right(there)))
        identity <- kit.fact(Derivative.Identity).flatMap(rules.spec(x, _))
        inner <- kit.fact(Derivative.Negation).flatMap(rules.specAll(_, List(identityFn, x, one))).flatMap(reduced)
          .flatMap(rules.mp(_, identity))
        innerFn <- functionOf(inner)
        outerSlope <- slopeOf(outer)
        innerSlope <- slopeOf(inner)
        chained <- kit.fact(Derivative.ChainRule).flatMap(rules.specAll(_, List(dk, innerFn, x, outerSlope, innerSlope)))
          .flatMap(reduced).flatMap(mp(_, Right(inner), Right(outer)))
        chainedFn <- functionOf(chained)
        chainedSlope <- slopeOf(chained)
        constant <- kit.fact(Derivative.Constant).flatMap(rules.specAll(_, List(sign, x)))
        constantFn <- functionOf(constant)
        product <- kit.fact(Derivative.ProductRule).flatMap(rules.specAll(_, List(constantFn, chainedFn, x, zero, chainedSlope)))
          .flatMap(reduced).flatMap(mp(_, Right(constant), Right(chained)))
        target <- proposition(
          s"derivative (\\t:real. Power (0 - 1) (k:num) * $D k (0 - t)) (x:real) (Power (0 - 1) (SUC k) * $D (SUC k) (0 - x))")
        restated <- restate(kit, kit.arithmetic, product, target, plainly(kit))
        closed <- rules.disch(member, restated).flatMap(rules.disch(le.conclusion, _)).flatMap(rules.genAll(_, List(k, x)))
      } yield closed

      found <- mp(instance, Right(flipped), Right(continuous), Right(differentiable))

      /* ---------------------------------------------------------- read back at a, b and 0 - z */
      power <- real("Power x:real k:num").map(t => spine(t)._1)
      doubleNegation <- lemma("!x:real. 0 - (0 - x) = x")
      shifted <- for {
        base <- at(lemma("!a:real b:real. (0 - b) - (0 - a) = a - b"), "a:real", "b:real")
        onPower <- Conv.apTerm(power, base)
        applied <- LogicError.lift(Kernel.mkComb(onPower, Kernel.refl(k)))
        closed <- rules.gen(k, applied)
      } yield closed
      signed <- for {
        base <- at(lemma("!a:real b:real. b - a = (0 - 1) * (a - b)"), "a:real", "b:real")
        onPower <- Conv.apTerm(power, base)
        applied <- LogicError.lift(Kernel.mkComb(onPower, Kernel.refl(k)))
        minusOne <- real("0 - 1:real")
        distance <- real("a:real - b:real")
        split <- kit.fact(Series.Multiplicative).flatMap(rules.specAll(_, List(minusOne, distance, k)))
        joined <- Conv.trans(applied, split)
        closed <- rules.gen(k, joined)
      } yield closed
      atZero <- kit.fact(Series.PowerAtZero)
      readRules <- Rewrite.Rule.all(logic, Vector(doubleNegation, shifted, signed, atZero))

      result <- for {
        inside <- found.conclusion match {
          case App(_, lambda) => LogicError.lift(Term.app(lambda, z)).flatMap(Conv.betaRoot).flatMap(rightOf)
          case other          => Left(NotOfForm("an existential", other))
        }
        assumed <- LogicError.lift(Kernel.assume(inside))
        above <- rules.conjElim1(assumed)
        below <- rules.conjElim2(assumed).flatMap(rules.conjElim1)
        equation <- rules.conjElim2(assumed).flatMap(rules.conjElim2)
        cAbove <- at(lemma("!b:real z:real. z < 0 - b ==> b < 0 - z"), "b:real", "z:real").flatMap(rules.mp(_, below))
        cBelow <- at(lemma("!a:real z:real. 0 - a < z ==> 0 - z < a"), "a:real", "z:real").flatMap(rules.mp(_, above))

        sides <- Term.destEq(equation.conclusion).toRight(NotOfForm("an equation", equation.conclusion))
        (reflectedEnd, reflectedRight) = sides
        parts <- spine(reflectedRight) match {
          case (plus, List(sum, remainder)) => Right((plus, sum, remainder))
          case _                            => Left(NotOfForm("a sum of two terms", reflectedRight))
        }
        (plus, reflectedSum, reflectedRemainder) = parts
        goal <- proposition(LeftConclusion)
        predicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
        witness <- real("0 - z:real")
        wanted <- LogicError.lift(Term.app(predicate, witness)).flatMap(Conv.betaRoot).flatMap(rightOf)
        wantedEquation <- LogicError.lift(Kernel.assume(wanted)).flatMap(rules.conjElim2).flatMap(rules.conjElim2)
          .map(_.conclusion)
        wantedSides <- Term.destEq(wantedEquation).toRight(NotOfForm("an equation", wantedEquation))
        (atB, wantedRight) = wantedSides
        wantedParts <- spine(wantedRight) match {
          case (_, List(sum, remainder)) => Right((sum, remainder))
          case _                         => Left(NotOfForm("a sum of two terms", wantedRight))
        }
        (wantedSum, wantedRemainder) = wantedParts

        endEq <- equalBy(kit, readRules, reflectedEnd, atB, plainly(kit))
        sumEq <- (spine(reflectedSum), spine(wantedSum)) match {
          case ((sumConstant, List(have, bound)), (_, List(want, _))) =>
            for {
              summands <- functionsEqual(kit, readRules, Term.variable("k", Numbers), have, want, plainly(kit))
              onSum <- Conv.apTerm(sumConstant, summands)
              applied <- LogicError.lift(Kernel.mkComb(onSum, Kernel.refl(bound)))
            } yield applied
          case _ => Left(NotOfForm("a sum over a lambda", reflectedSum))
        }
        remainderEq <- equalBy(kit, readRules, reflectedRemainder, wantedRemainder, plainly(kit))
        rightEq <- Conv.apTerm(plus, sumEq).flatMap(eq => LogicError.lift(Kernel.mkComb(eq, remainderEq)))
        back <- Conv.sym(endEq)
        readBack <- Conv.trans(back, equation).flatMap(Conv.trans(_, rightEq))
        conjunction <- conj(Right(cAbove), conj(Right(cBelow), Right(readBack)))
        witnessed <- rules.existsIntro(predicate, witness, conjunction)
        eliminated <- rules.existsElim(found, z, witnessed)
      } yield eliminated

      closed <- List(slopeHypothesis, continuousHypothesis, ordered).foldLeft[Either[LogicError, Kernel.Thm]](Right(result)) {
        (acc, h) => acc.flatMap(rules.disch(h.conclusion, _))
      }.flatMap(rules.genAll(_, List(family, a, b, n)))
    } yield closed
  }
}
