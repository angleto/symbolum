package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The first facts about `ln`, and the facts about the exponential they wait on.
 *
 * `ln y` is `select (\x. exp x = y)`, declared in `Transcendental` the day the exponential was, and
 * until this development it had no fact at all: a choice is silent until something says the
 * predicate is satisfiable, and what says so here is that the exponential is onto the positive
 * reals. That is `Continuity.INTERMEDIATE_VALUE` at the exponential, and what the theorem asks of it
 * is two things, which are most of this file: that it is continuous at every point, and that every
 * positive number has a value of it on each side.
 *
 * == The one estimate, and why no factorial is dominated ==
 *
 * Continuity at a point is continuity at zero carried by the addition theorem,
 * `exp (x + h) - exp x = exp x * (exp h - 1)`, so what is needed is `abs (exp h - 1) <= 2 * abs h`
 * for small `h`, which is [[Logarithm.NearOne]]. For `0 < t <= 1/2` it is two bounds on the series.
 * Below, the partial sums increase and the one with two terms is `1 + t`, so `1 + t <= exp t`
 * ([[Logarithm.AboveLine]]). Above, each term `t^i / i!` is at most `t^i` because `i! >= 1`, and the
 * geometric series at a ratio of at most a half sums to at most `1 + 2 t` ([[Logarithm.SmallAbove]]).
 * [[Logarithm.NearLine]], one order higher, is the tail after two terms under a geometric series
 * by `Transcendental.EXP_TAIL_GEOMETRIC`, and it is what the exponential's derivative is made of.
 * `Transcendental.EXP_ONE_ABOVE_TWO` put `1 / i!` under a geometric series instead, which wants
 * `2^i <= 2 * i!`; at a ratio `t` of at most a half the factorial is not needed, only that it is at
 * least one. A negative `h` is the positive one reflected through `exp h * exp (0 - h) = 1`.
 *
 * == What it declares ==
 *
 * Nothing. It is a link of the chain for the reason `Deduction` is one: its facts are about
 * constants declared below it, `exp`, `ln` and `continuous`, and a development that states them has
 * to see all three, which only the end of the chain does. The theory it hands on is the one it was
 * given, and `LogarithmSpec` asserts that constant for constant.
 */
final class Logarithm private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Logarithm {

  /** `|- !x. 0 < exp x`: a square, and not zero because it has a reciprocal. */
  val Positive: String = "EXP_POSITIVE"

  /** `|- !x. 0 < x ==> 1 + x <= exp x`: the series' first two terms, under a series that grows. */
  val AboveLine: String = "EXP_ABOVE_LINE"

  /** `|- !x. 0 < x ==> x <= 1 / 2 ==> exp x <= 1 + 2 * x`: the series under a geometric one. */
  val SmallAbove: String = "EXP_SMALL_ABOVE"

  /**
   * `|- !h. abs h <= 1 / 2 ==> abs (exp h - 1) <= 2 * abs h`
   *
   * The estimate continuity is made of. The constant two and the radius one half are what the two
   * bounds above give with nothing optimised: a reader wanting a sharper constant wants a sharper
   * geometric comparison, and nothing downstream does.
   */
  val NearOne: String = "EXP_NEAR_ONE"

  /**
   * `|- !h. abs h <= 1 / 2 ==> abs (exp h - 1 - h) <= h * h`
   *
   * The estimate a derivative is made of, one order above [[NearOne]]: the exponential leaves its
   * tangent line at zero by at most `h * h`. It is what `Derivative.DERIVATIVE_EXP` spends, and
   * the constant one and the radius one half are, again, what the bounds give with nothing
   * optimised.
   */
  val NearLine: String = "EXP_NEAR_LINE"

  /** `|- !x. continuous exp x` */
  val Continuous: String = "EXP_CONTINUOUS"

  /** `|- !a b. a < b ==> exp a < exp b` */
  val StrictlyIncreasing: String = "EXP_LT_MONOTONE"

  /** `|- !a b. exp a = exp b ==> a = b` */
  val Injective: String = "EXP_INJECTIVE"

  /**
   * `|- !y. 0 < y ==> ?x. exp x = y`
   *
   * The intermediate value theorem on `[0, y]` for `y` at least one, where `exp 0 = 1 <= y` and
   * `y <= 1 + y <= exp y`; and below one, the same at `inv y`, reflected.
   */
  val Onto: String = "EXP_ONTO"

  /** `|- !y. 0 < y ==> exp (ln y) = y`: the choice in `ln`'s definition, read back. */
  val ExpOfLn: String = "EXP_LN"

  /** `|- !x. ln (exp x) = x`: the other composition, by injectivity. */
  val LnOfExp: String = "LN_EXP"

  /** `|- ln 1 = 0` */
  val AtOne: String = "LN_ONE"

  /** `|- !a b. 0 < a ==> 0 < b ==> ln (a * b) = ln a + ln b`: the addition theorem, inverted. */
  val Multiplicative: String = "LN_MUL"

  /** What every derived fact says, as text, in the order they are derived. */
  val Statements: Vector[(String, String)] = Vector(
    Positive -> "!x:real. 0 < exp x",
    AboveLine -> "!x:real. 0 < x ==> 1 + x <= exp x",
    SmallAbove -> "!x:real. 0 < x ==> x <= 1 / 2 ==> exp x <= 1 + 2 * x",
    NearOne -> "!h:real. abs h <= 1 / 2 ==> abs (exp h - 1) <= 2 * abs h",
    NearLine -> "!h:real. abs h <= 1 / 2 ==> abs (exp h - 1 - h) <= h * h",
    Continuous -> "!x:real. continuous exp x",
    StrictlyIncreasing -> "!a:real. !b:real. a < b ==> exp a < exp b",
    Injective -> "!a:real. !b:real. exp a = exp b ==> a = b",
    Onto -> "!y:real. 0 < y ==> (?x:real. exp x = y)",
    ExpOfLn -> "!y:real. 0 < y ==> exp (ln y) = y",
    LnOfExp -> "!x:real. ln (exp x) = x",
    AtOne -> "ln 1 = 0",
    Multiplicative -> "!a:real. !b:real. 0 < a ==> 0 < b ==> ln (a * b) = ln a + ln b"
  )

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)

  /** What the derivations take from the developments under this one. */
  private final case class Steps(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    classical: Classical,
    reals: RealTheory,
    magnitude: Magnitude,
    series: Series,
    peano: Peano,
    coding: Coding,
    limit: Limit,
    transcendental: Transcendental,
    continuity: Continuity
  ) {
    val rules: Rules = logic.rules
    val ring: Ring = series.ring

    def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)
    def real(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, Reals)
    def number(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, Numbers)
    def assume(text: String): Either[LogicError, Kernel.Thm] =
      proposition(text).flatMap(statement => LogicError.lift(Kernel.assume(statement)))
    def lemma(text: String): Either[LogicError, Kernel.Thm] = linarith.prove(text)

    def at(theorem: Either[LogicError, Kernel.Thm], arguments: String*): Either[LogicError, Kernel.Thm] =
      theorem.flatMap(proved =>
        arguments.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, text) =>
          for { terms <- acc; term <- real(text) } yield terms :+ term
        }.flatMap(rules.specAll(proved, _)))

    def mp(implication: Kernel.Thm, premises: Either[LogicError, Kernel.Thm]*): Either[LogicError, Kernel.Thm] =
      premises.foldLeft[Either[LogicError, Kernel.Thm]](Right(implication)) { (acc, premise) =>
        for { current <- acc; proved <- premise; next <- rules.mp(current, proved) } yield next
      }

    def conj(left: Either[LogicError, Kernel.Thm], right: Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for { l <- left; r <- right; both <- rules.conjIntro(l, r) } yield both

    def existential(text: String): Either[LogicError, Term] =
      proposition(text).flatMap(statement =>
        logic.destExistsPredicate(statement).toRight(NotOfForm("an existential", statement)))

    def opened(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv.betaNormalise(theorem.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    def ringEquation(left: String, right: String): Either[LogicError, Kernel.Thm] =
      for {
        l <- real(left)
        r <- real(right)
        proved <- LogicError.lift(Term.eq(l, r)).flatMap(ring.prove)
      } yield proved

    /** The body of an existential at a chosen witness, beta reduced, ready to be assumed. */
    def instanceAt(existential: Kernel.Thm, witness: Term): Either[LogicError, Term] =
      logic
        .destExistsPredicate(existential.conclusion)
        .toRight(NotOfForm("an existential quantification", existential.conclusion))
        .flatMap(predicate =>
          LogicError.lift(Term.app(predicate, witness)).flatMap(Conv.betaNormalise).flatMap(rightOf))

    /** `|- P b` from `|- a = b` and `|- P a`, where the equation's left side occurs in `P a`. */
    def rewrite(equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Rewrite.Rule.of(logic, equation).flatMap(rule => Rewrite.inTheorem(Vector(rule), theorem))
  }

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def sidesOf(term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(_, left), right) => Right((left, right))
    case other                    => Left(NotOfForm("two arguments of one operator", other))
  }

  /** The development over the chain's end, which it extends by nothing. */
  def construct(
    classical: Classical,
    reals: RealTheory,
    magnitude: Magnitude,
    series: Series,
    peano: Peano,
    coding: Coding,
    limit: Limit,
    transcendental: Transcendental,
    continuity: Continuity
  ): Either[LogicError, Logarithm] = {
    val theory = continuity.theory
    val notation = continuity.notation
    for {
      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(magnitude.order)
      steps = Steps(logic, linarith, theory, notation, classical, reals, magnitude, series, peano,
        coding, limit, transcendental, continuity)

      positive <- exponentialPositive(steps)
      aboveLine <- exponentialAboveLine(steps)
      smallAbove <- exponentialSmallAbove(steps)
      nearOne <- exponentialNearOne(steps, aboveLine, smallAbove)
      nearLine <- exponentialNearLine(steps)
      continuous <- exponentialContinuous(steps, positive, nearOne)
      increasing <- exponentialIncreasing(steps, positive, aboveLine)
      injective <- exponentialInjective(steps, increasing)
      onto <- exponentialOnto(steps, aboveLine, continuous)
      expOfLn <- exponentialOfLogarithm(steps, onto)
      lnOfExp <- logarithmOfExponential(steps, positive, injective, expOfLn)
      atOne <- logarithmAtOne(steps, lnOfExp)
      multiplicative <- logarithmOfProduct(steps, injective, expOfLn)

      facts = Map(
        Positive -> positive,
        AboveLine -> aboveLine,
        SmallAbove -> smallAbove,
        NearOne -> nearOne,
        NearLine -> nearLine,
        Continuous -> continuous,
        StrictlyIncreasing -> increasing,
        Injective -> injective,
        Onto -> onto,
        ExpOfLn -> expOfLn,
        LnOfExp -> lnOfExp,
        AtOne -> atOne,
        Multiplicative -> multiplicative
      )

      // Each statement checked against the text a person reads it by, as `Root` and `Continuity`
      // do: a development that built something other than what it says must not be handed out.
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
    } yield new Logarithm(theory, notation, logic, facts)
  }

  /* ================================================================== the exponential's sign */

  /**
   * [[Positive]]. `exp x` is `exp (x / 2) * exp (x / 2)`, a square, so it is not negative; and it
   * is not zero, because `exp x * exp (0 - x) = 1`.
   */
  private def exponentialPositive(steps: Steps): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    for {
      exp <- Parser.term(theory, notation, "exp", Type.fun(Reals, Reals))
      halves <- ringEquation("x / 2 + x / 2", "x:real")
      split <- at(transcendental.fact(Transcendental.Addition), "x / 2", "x / 2")
      square <- Conv.apTerm(exp, halves).flatMap(Conv.sym).flatMap(Conv.trans(_, split))
      nonNegative <- at(magnitude.order.fact(Order.SquareNonNegative), "exp (x / 2)")
      atLeastZero <- at(lemma("!a:real b:real. a = b ==> 0 <= b ==> 0 <= a"), "exp x", "exp (x / 2) * exp (x / 2)")
        .flatMap(mp(_, Right(square), Right(nonNegative)))
      reciprocal <- at(transcendental.fact(Transcendental.Reciprocal), "x:real")
      cases <- at(magnitude.order.fact(Order.LeCases), "0:real", "exp x").flatMap(mp(_, Right(atLeastZero)))
      goal <- proposition("0 < exp x")
      strict <- assume("0 < exp x")
      zero <- for {
        equal <- assume("0 = exp x")
        moved <- Conv.sym(equal).flatMap(rewrite(_, reciprocal))
        absurd <- at(lemma("!b:real. 0 * b = 1 ==> F"), "exp (0 - x)").flatMap(mp(_, Right(moved)))
        result <- rules.falsityElim(goal, absurd)
      } yield result
      result <- rules.disjElim(cases, strict, zero).flatMap(rules.gen(x, _))
    } yield result
  }

  /* ============================================================= the series, at a positive t */

  /**
   * Open `exp t` as the limit of its partial sums and hand `body` the convergence and the value.
   *
   * The two existentials are the absolute convergence `EXP_ABSOLUTE` names and the sum it then
   * converges to; `body` gets `converges (Sum e) A` and `exp t = A` and must conclude something
   * that mentions neither `A` nor the magnitude's sum, which is what closes them again.
   */
  private def withLimit(
    steps: Steps,
    t: String,
    body: (Term, Kernel.Thm, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val p = Term.variable("P", Reals)
    val a = Term.variable("A", Reals)
    for {
      point <- real(t)
      terms <- Parser.term(theory, notation,
        s"\\i:num. Power ($t) i / real_of_num (NUM_FACT i)", Type.fun(Numbers, Reals))
      magnitudes <- transcendental.fact(Transcendental.AbsolutelyConvergent).flatMap(rules.spec(point, _))
      assumedP <- instanceAt(magnitudes, p).flatMap(s => LogicError.lift(Kernel.assume(s)))
      converging <- limit.fact(Limit.Absolute)
        .flatMap(rules.specAll(_, List(terms, p)))
        .flatMap(opened)
        .flatMap(rules.mp(_, assumedP))
      assumedA <- instanceAt(converging, a).flatMap(s => LogicError.lift(Kernel.assume(s)))

      unfolded <- transcendental.definition(Transcendental.Exponential)
        .flatMap(Conv.unfold(_, List(point)))
        .flatMap(equation => rightOf(equation).flatMap(Conv.betaNormalise).flatMap(Conv.trans(equation, _)))
      limited <- rightOf(unfolded)
      sequence <- limited match {
        case App(_, inner) => Right(inner)
        case other         => Left(NotOfForm("a limit of a sequence", other))
      }
      partial <- sidesOf(assumedA.conclusion).map(_._1)
      zero <- number("0:num")
      eventually <- limit.fact(Limit.Eventually)
        .flatMap(rules.specAll(_, List(partial, sequence, a, zero)))
        .flatMap(opened)
      premise <- logic.destImp(eventually.conclusion).toRight(NotOfForm("an implication", eventually.conclusion))
      stripped <- Logic.stripForall(premise._1)
      index <- stripped._1.headOption.toRight(NotOfForm("a claim about every index", premise._1))
      inner <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      pointwise <- LogicError.lift(Term.app(partial, index)).map(Kernel.refl)
      everywhere <- rules.disch(inner._1, pointwise).flatMap(rules.gen(index, _))
      towards <- mp(eventually, Right(everywhere), Right(assumedA))
      named <- limit.fact(Limit.ValueOfConverges)
        .flatMap(rules.specAll(_, List(sequence, a)))
        .flatMap(rules.mp(_, towards))
      value <- Conv.trans(unfolded, named)

      concluded <- body(terms, assumedA, value)
      withoutA <- rules.existsElim(converging, a, concluded)
      result <- rules.existsElim(magnitudes, p, withoutA)
    } yield result
  }

  /** `|- 0 + 1 <= real_of_num (NUM_FACT i)`: a factorial is at least one, on the reals. */
  private def factorialAtLeastOne(steps: Steps, index: Term): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      positive <- coding.fact(Coding.FactorialPositive).flatMap(rules.spec(index, _))
      sides <- sidesOf(positive.conclusion)
      embedded <- peano.fact(Peano.EmbedsStrictOrder)
        .flatMap(rules.specAll(_, List(sides._1, sides._2)))
        .flatMap(rules.mp(_, positive))
      zero <- peano.fact(Peano.EmbedsZero)
      result <- rewrite(zero, embedded)
    } yield result
  }

  /**
   * `|- !i. Power t i / F i = Power t i * v /\ F i * v = 1 /\ 0 < v` at `v = inv (F i)`, which
   * is every fact about a term of the series the bounds below use. Returned as three theorems.
   */
  private def reciprocalOfFactorial(
    steps: Steps,
    t: String,
    index: Term
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm)] = {
    import steps.*
    for {
      atLeastOne <- factorialAtLeastOne(steps, index)
      factorial <- sidesOf(atLeastOne.conclusion).map(_._2)
      positive <- lemma("!f:real. 0 + 1 <= f ==> 0 < f")
        .flatMap(rules.spec(factorial, _))
        .flatMap(rules.mp(_, atLeastOne))
      nonZero <- magnitude.order.fact(Order.NonZero).flatMap(rules.spec(factorial, _)).flatMap(rules.mp(_, positive))
      cancels <- reals.axiom("MUL_INVERSE").flatMap(rules.spec(factorial, _)).flatMap(rules.mp(_, nonZero))
      inversePositive <- magnitude.order.fact(Order.InversePositive)
        .flatMap(rules.spec(factorial, _)).flatMap(rules.mp(_, positive))
      power <- Parser.term(theory, notation, "Power", Type.fun(Reals, Type.fun(Numbers, Reals)))
      base <- real(t)
      powerAt <- LogicError.lift(Term.app(power, base).flatMap(Term.app(_, index)))
      quotient <- Parser.term(theory, notation, "(1:real) / 1", Reals).flatMap {
        case App(App(divide, _), _) => LogicError.lift(Term.app(divide, powerAt).flatMap(Term.app(_, factorial)))
        case other                  => Left(NotOfForm("a quotient", other))
      }
      inverse <- sidesOf(inversePositive.conclusion).map(_._2)
      product <- Parser.term(theory, notation, "(1:real) * 1", Reals).flatMap {
        case App(App(times, _), _) => LogicError.lift(Term.app(times, powerAt).flatMap(Term.app(_, inverse)))
        case other                 => Left(NotOfForm("a product", other))
      }
      asProduct <- LogicError.lift(Term.eq(quotient, product)).flatMap(ring.prove)
    } yield (asProduct, cancels, inversePositive, atLeastOne)
  }

  /**
   * [[AboveLine]]: at a positive `x` every term is positive, so the partial sums increase, and the
   * one with two terms is `1 + x`; `Limit.CONVERGES_GE` puts that under the limit.
   */
  private def exponentialAboveLine(steps: Steps): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    val i = Term.variable("i", Numbers)
    val n = Term.variable("n", Numbers)
    for {
      hypothesis <- proposition("0 < x:real")
      positive <- LogicError.lift(Kernel.assume(hypothesis))
      concluded <- withLimit(steps, "x:real", (terms, converges, value) =>
        for {
          powerPositive <- series.fact(Series.PowerPositive)
            .flatMap(rules.spec(x, _)).flatMap(rules.mp(_, positive)).flatMap(rules.spec(i, _))
          parts <- reciprocalOfFactorial(steps, "x:real", i)
          (asProduct, cancels, inversePositive, _) = parts
          productSides <- rightOf(asProduct).flatMap(sidesOf)
          termNonNegative <- lemma("!p:real v:real. 0 < p ==> 0 < v ==> 0 <= p * v")
            .flatMap(rules.specAll(_, List(productSides._1, productSides._2)))
            .flatMap(rules.mp(_, powerPositive)).flatMap(rules.mp(_, inversePositive))
            .flatMap(theorem => Conv.sym(asProduct).flatMap(rewrite(_, theorem)))
            .flatMap(rules.gen(i, _))
          grows <- limit.fact(Limit.Grows)
            .flatMap(rules.spec(terms, _)).flatMap(opened).flatMap(rules.mp(_, termNonNegative))
          two <- number("SUC (SUC 0)")
          fromTwo <- rules.specAll(grows, List(two, n))
          sum <- Parser.term(theory, notation, "Sum", Type.fun(Type.fun(Numbers, Reals), Type.fun(Numbers, Reals)))
          twoTerms <- LogicError.lift(Term.app(sum, terms).flatMap(Term.app(_, two)))
          recurrences <- Vector(
            series.fact(Series.AtSuccessor), series.fact(Series.AtZero),
            series.fact(Series.PowerAtZero), series.fact(Series.PowerAtSuccessor),
            coding.fact(Coding.FactorialAtZero), coding.fact(Coding.FactorialAtSuccessor),
            peano.fact(Peano.MulAtZero), peano.fact(Peano.MulAtSuccessor),
            peano.fact(Peano.AddAtZero), peano.fact(Peano.ZeroPlus),
            peano.fact(Peano.EmbedsSuccessor), peano.fact(Peano.EmbedsZero)
          ).foldRight[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
            case (next, rest) => next.flatMap(theorem => rest.map(theorem +: _))
          }.flatMap(Rewrite.Rule.all(logic, _))
          walked <- Rewrite.rewrite(recurrences, twoTerms)
          walkedValue <- rightOf(walked)
          line <- real("1 + x:real")
          closes <- LogicError.lift(Term.eq(walkedValue, line)).flatMap(ring.prove)
          atTwo <- Conv.trans(walked, closes)
          guard <- Parser.proposition(theory, notation, "NUM_LE (SUC (SUC 0)) (n:num)")
          assumedGuard <- LogicError.lift(Kernel.assume(guard))
          fromGuard <- rules.mp(fromTwo, assumedGuard).flatMap(rewrite(atTwo, _))
          later <- rules.disch(guard, fromGuard).flatMap(rules.gen(n, _))
          partial <- sidesOf(converges.conclusion).map(_._1)
          limitValue <- sidesOf(converges.conclusion).map(_._2)
          bound <- limit.fact(Limit.AboveBound)
            .flatMap(rules.specAll(_, List(partial, limitValue, line, two)))
            .flatMap(opened)
            .flatMap(rules.mp(_, converges))
            .flatMap(rules.mp(_, later))
          result <- Conv.sym(value).flatMap(rewrite(_, bound))
        } yield result)
      result <- rules.disch(hypothesis, concluded).flatMap(rules.gen(x, _))
    } yield result
  }

  /**
   * [[SmallAbove]]: each term is at most `x^i`, since `i! >= 1`, and the geometric series at a
   * ratio of at most a half sums to at most `1 + 2 x`; `Limit.CONVERGES_LE` carries the bound to
   * the limit.
   */
  private def exponentialSmallAbove(steps: Steps): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    val i = Term.variable("i", Numbers)
    val n = Term.variable("n", Numbers)
    for {
      positiveStatement <- proposition("0 < x:real")
      smallStatement <- proposition("x:real <= 1 / 2")
      positive <- LogicError.lift(Kernel.assume(positiveStatement))
      small <- LogicError.lift(Kernel.assume(smallStatement))
      concluded <- withLimit(steps, "x:real", (terms, converges, value) =>
        for {
          powerPositive <- series.fact(Series.PowerPositive)
            .flatMap(rules.spec(x, _)).flatMap(rules.mp(_, positive)).flatMap(rules.spec(i, _))
          parts <- reciprocalOfFactorial(steps, "x:real", i)
          (asProduct, cancels, inversePositive, atLeastOne) = parts
          productSides <- rightOf(asProduct).flatMap(sidesOf)
          factorial <- sidesOf(atLeastOne.conclusion).map(_._2)
          termBelow <- lemma("!p:real f:real v:real. 0 < p ==> 0 + 1 <= f ==> f * v = 1 ==> 0 < v ==> p * v <= p")
            .flatMap(rules.specAll(_, List(productSides._1, factorial, productSides._2)))
            .flatMap(rules.mp(_, powerPositive)).flatMap(rules.mp(_, atLeastOne))
            .flatMap(rules.mp(_, cancels)).flatMap(rules.mp(_, inversePositive))
            .flatMap(theorem => Conv.sym(asProduct).flatMap(rewrite(_, theorem)))
            .flatMap(rules.gen(i, _))
          powers <- Parser.term(theory, notation, "\\i:num. Power (x:real) i", Type.fun(Numbers, Reals))
          dominated <- series.fact(Series.Monotone)
            .flatMap(rules.specAll(_, List(terms, powers)))
            .flatMap(opened)
            .flatMap(rules.mp(_, termBelow))
            .flatMap(rules.spec(n, _))
          geometric <- series.fact(Series.Geometric).flatMap(rules.specAll(_, List(x, n)))
          powerAtN <- series.fact(Series.PowerPositive)
            .flatMap(rules.spec(x, _)).flatMap(rules.mp(_, positive)).flatMap(rules.spec(n, _))
          partialAtN <- sidesOf(dominated.conclusion)
          geometricSum <- sidesOf(dominated.conclusion).map(_._2)
          powerTerm <- sidesOf(powerAtN.conclusion).map(_._2)
          underLine <- lemma(
              "!x:real s:real p:real. 0 < x ==> x <= 1 / 2 ==> (x - 1) * s = p - 1 ==> 0 < p ==> s <= 1 + 2 * x")
            .flatMap(rules.specAll(_, List(x, geometricSum, powerTerm)))
            .flatMap(mp(_, Right(positive), Right(small), Right(geometric), Right(powerAtN)))
          line <- real("1 + 2 * x:real")
          every <- lemma("!a:real b:real c:real. a <= b ==> b <= c ==> a <= c")
            .flatMap(rules.specAll(_, List(partialAtN._1, geometricSum, line)))
            .flatMap(mp(_, Right(dominated), Right(underLine)))
          guard <- Parser.proposition(theory, notation, "NUM_LE 0 (n:num)")
          later <- rules.disch(guard, every).flatMap(rules.gen(n, _))
          zero <- number("0:num")
          partial <- sidesOf(converges.conclusion).map(_._1)
          limitValue <- sidesOf(converges.conclusion).map(_._2)
          bound <- limit.fact(Limit.BelowBound)
            .flatMap(rules.specAll(_, List(partial, limitValue, line, zero)))
            .flatMap(opened)
            .flatMap(rules.mp(_, converges))
            .flatMap(rules.mp(_, later))
          result <- Conv.sym(value).flatMap(rewrite(_, bound))
        } yield result)
      result <- rules.disch(smallStatement, concluded)
        .flatMap(rules.disch(positiveStatement, _))
        .flatMap(rules.gen(x, _))
    } yield result
  }

  /* =================================================================== the second order at zero */

  /**
   * [[NearLine]]: the partial sums from two terms on stay within `h * h` of the two-term sum
   * `1 + h`, and `Limit.CONVERGES_LE` and `CONVERGES_GE` carry that to `exp h`.
   *
   * The tail after two terms is `Transcendental.EXP_TAIL_GEOMETRIC` at two, which holds for either
   * sign of `h` because `2 * abs h <= 2`: each term is at most `(1/2)^z` times the first of the
   * tail, `h * h / 2`, and the geometric sum is under two. So one argument covers both signs, where
   * [[NearOne]] went through the reflection `exp h * exp (0 - h) = 1`. The first of the tail is
   * computed as a numerator and a denominator walked separately and put back by congruence, since a
   * quotient walked whole leaves its denominator under `inv`, where the ring does not look.
   */
  private def exponentialNearLine(steps: Steps): Either[LogicError, Kernel.Thm] = {
    import steps.*
    def sequence(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, Type.fun(Numbers, Reals))
    val h = Term.variable("h", Reals)
    val d = Term.variable("d", Numbers)
    val v = Term.variable("v", Numbers)
    val two = "SUC (SUC 0)"
    val terms = "\\i:num. Power (h:real) i / real_of_num (NUM_FACT i)"
    val shifted = s"\\u:num. Power (h:real) ($two + u) / real_of_num (NUM_FACT ($two + u))"
    val first = s"Power (h:real) ($two) / real_of_num (NUM_FACT ($two))"
    val magnitudes = s"\\z:num. abs (Power (h:real) ($two + z) / real_of_num (NUM_FACT ($two + z)))"
    val halves = s"\\z:num. Power (1 / 2) z * abs ($first)"

    for {
      hypothesis <- proposition("abs (h:real) <= 1 / 2")
      small <- LogicError.lift(Kernel.assume(hypothesis))

      /* ------------------------------------------ the numbers the recurrences settle */
      recurrences <- Vector(
        series.fact(Series.AtSuccessor), series.fact(Series.AtZero),
        series.fact(Series.PowerAtZero), series.fact(Series.PowerAtSuccessor),
        coding.fact(Coding.FactorialAtZero), coding.fact(Coding.FactorialAtSuccessor),
        peano.fact(Peano.MulAtZero), peano.fact(Peano.MulAtSuccessor),
        peano.fact(Peano.AddAtZero), peano.fact(Peano.AddAtSuccessor), peano.fact(Peano.ZeroPlus),
        peano.fact(Peano.EmbedsSuccessor), peano.fact(Peano.EmbedsZero)
      ).foldRight[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
        case (next, rest) => next.flatMap(theorem => rest.map(theorem +: _))
      }.flatMap(Rewrite.Rule.all(logic, _))
      sequenceT <- sequence(terms)
      twoTerms <- settle(steps, recurrences, s"Sum ($terms) ($two)", "1 + h:real")
      numerator <- settle(steps, recurrences, s"Power (h:real) ($two)", "h:real * h")
      denominator <- settle(steps, recurrences, s"real_of_num (NUM_FACT ($two))", "2:real")
      firstTerm <- real(first)
      divide <- firstTerm match {
        case App(App(op, _), _) => Right(op)
        case other => Left(NotOfForm("a quotient", other))
      }
      firstValue <- Conv.apTerm(divide, numerator).flatMap(t => LogicError.lift(Kernel.mkComb(t, denominator)))
      twoReal <- settle(steps, recurrences, s"real_of_num ($two)", "2:real")

      /* ------------------------------------------------- the tail after two terms */
      ratio <- at(lemma("!A:real R:real. A <= 1 / 2 ==> R = 2 ==> 2 * A <= R"), "abs (h:real)", s"real_of_num ($two)")
        .flatMap(mp(_, Right(small), Right(twoReal)))
      twoNumber <- number(two)
      geometricTail <- transcendental.fact(Transcendental.TailIsGeometric)
        .flatMap(rules.specAll(_, List(h, twoNumber))).flatMap(rules.mp(_, ratio))
      magnitudesT <- sequence(magnitudes)
      halvesT <- sequence(halves)
      dominated <- series.fact(Series.Monotone)
        .flatMap(rules.specAll(_, List(magnitudesT, halvesT))).flatMap(opened)
        .flatMap(rules.mp(_, geometricTail)).flatMap(rules.spec(d, _))

      shiftedT <- sequence(shifted)
      absSum <- limit.fact(Limit.SumOfMagnitudes)
        .flatMap(rules.specAll(_, List(shiftedT, d))).flatMap(opened)
      reindexed <- series.fact(Series.Reindex)
        .flatMap(rules.specAll(_, List(sequenceT, twoNumber, d))).flatMap(opened)

      /* ------------------------------ the geometric sum is at most twice its first term */
      scaledForm <- sequence(s"\\z:num. abs ($first) * Power (1 / 2) z + 0")
      pointwise <- {
        val z = Term.variable("z", Numbers)
        for {
          lhs <- LogicError.lift(Term.app(halvesT, z)).flatMap(Conv.betaNormalise).flatMap(rightOf)
          rhs <- LogicError.lift(Term.app(scaledForm, z)).flatMap(Conv.betaNormalise).flatMap(rightOf)
          equal <- LogicError.lift(Term.eq(lhs, rhs)).flatMap(ring.prove)
          result <- rules.gen(z, equal)
        } yield result
      }
      congruent <- series.fact(Series.Congruence)
        .flatMap(rules.specAll(_, List(halvesT, scaledForm))).flatMap(opened)
        .flatMap(rules.mp(_, pointwise)).flatMap(rules.spec(d, _))
      constant <- real(s"abs ($first)")
      powersT <- sequence("\\z:num. Power (1 / 2) z")
      zerosT <- sequence("\\z:num. (0:real)")
      linear <- series.fact(Series.Linear)
        .flatMap(rules.specAll(_, List(constant, powersT, zerosT, d))).flatMap(opened)
      zeroReal <- real("0:real")
      zeroSum <- series.fact(Series.Constant).flatMap(rules.specAll(_, List(zeroReal, d)))
      half <- real("1 / 2")
      geometric <- series.fact(Series.Geometric).flatMap(rules.specAll(_, List(half, d)))
      halfNonNeg <- lemma("(0:real) <= 1 / 2")
      powerNonNeg <- at(limit.fact(Limit.PowerNonNegative), "1 / 2")
        .flatMap(rules.mp(_, halfNonNeg)).flatMap(rules.spec(d, _))

      /* --------------------------------------------- the tail is within h * h of nothing */
      sa <- real(s"Sum ($shifted) d")
      sm <- real(s"Sum ($magnitudes) d")
      sh <- real(s"Sum ($halves) d")
      sl <- real(s"Sum (\\z:num. abs ($first) * Power (1 / 2) z + 0) d")
      g <- real("Sum (\\z:num. Power (1 / 2) z) d")
      zs <- real("Sum (\\z:num. (0:real)) d")
      w <- real("real_of_num d")
      p <- real("Power (1 / 2) d")
      sv <- real(s"Sum ($terms) ($two + d)")
      s2 <- real(s"Sum ($terms) ($two)")
      firstNonNeg <- at(lemma("!F:real h:real. F = h * h / 2 ==> 0 <= F"), first, "h:real").flatMap(mp(_, Right(firstValue)))
      cIs <- at(magnitude.fact(Magnitude.OfNonNegative), first).flatMap(mp(_, Right(firstNonNeg)))
      gBound <- lemma("!G:real P:real. (1 / 2 - 1) * G = P - 1 ==> 0 <= P ==> G <= 2")
        .flatMap(rules.specAll(_, List(g, p))).flatMap(mp(_, Right(geometric), Right(powerNonNeg)))
      cNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), first)
      shBound <- lemma("!SH:real SL:real C:real G:real Z:real W:real. SH = SL ==> SL = C * G + Z ==> Z = W * 0 ==> G <= 2 ==> 0 <= C ==> SH <= 2 * C")
        .flatMap(rules.specAll(_, List(sh, sl, constant, g, zs, w)))
        .flatMap(mp(_, Right(congruent), Right(linear), Right(zeroSum), Right(gBound), Right(cNonNeg)))
      above <- at(magnitude.fact(Magnitude.AbsAbove), s"Sum ($shifted) d")
      belowNeg <- at(magnitude.fact(Magnitude.AbsAboveNegation), s"Sum ($shifted) d")
      c <- real(s"abs ($first)")
      absSa <- real(s"abs (Sum ($shifted) d)")
      hh <- real("h:real * h / 2")
      tailUp <- lemma("!SA:real B:real SM:real SH:real C:real T:real. SA <= B ==> B <= SM ==> SM <= SH ==> SH <= 2 * C ==> C = T ==> SA <= 2 * T")
        .flatMap(rules.specAll(_, List(sa, absSa, sm, sh, c, hh)))
        .flatMap(mp(_, Right(above), Right(absSum), Right(dominated), Right(shBound), Conv.trans(cIs, firstValue)))
      tailDown <- lemma("!SA:real B:real SM:real SH:real C:real T:real. -SA <= B ==> B <= SM ==> SM <= SH ==> SH <= 2 * C ==> C = T ==> -SA <= 2 * T")
        .flatMap(rules.specAll(_, List(sa, absSa, sm, sh, c, hh)))
        .flatMap(mp(_, Right(belowNeg), Right(absSum), Right(dominated), Right(shBound), Conv.trans(cIs, firstValue)))
      upper <- lemma("!SA:real Sv:real S2:real h:real. SA = Sv - S2 ==> S2 = 1 + h ==> SA <= 2 * (h * h / 2) ==> Sv <= 1 + h + h * h")
        .flatMap(rules.specAll(_, List(sa, sv, s2, h))).flatMap(mp(_, Right(reindexed), Right(twoTerms), Right(tailUp)))
      lower <- lemma("!SA:real Sv:real S2:real h:real. SA = Sv - S2 ==> S2 = 1 + h ==> -SA <= 2 * (h * h / 2) ==> 1 + h - h * h <= Sv")
        .flatMap(rules.specAll(_, List(sa, sv, s2, h))).flatMap(mp(_, Right(reindexed), Right(twoTerms), Right(tailDown)))

      /* ------------------------------------------------- at every index from two on */
      orderDefinition <- peano.definition(Peano.NonStrictOrder)
      sumOf <- Parser.term(theory, notation, s"Sum ($terms)", Type.fun(Numbers, Reals))
      everyIndex <- {
        def fromTwo(bound: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            guard <- Parser.proposition(theory, notation, s"NUM_LE ($two) (v:num)")
            assumedGuard <- LogicError.lift(Kernel.assume(guard))
            unfolded <- Conv.unfold(orderDefinition, List(twoNumber, v))
              .flatMap(eq => rightOf(eq).flatMap(Conv.betaNormalise).flatMap(Conv.trans(eq, _)))
            witness <- LogicError.lift(Kernel.eqMp(unfolded, assumedGuard))
            body <- Parser.proposition(theory, notation, s"$two + (d:num) = v")
            assumedBody <- LogicError.lift(Kernel.assume(body))
            atV <- Conv.apTerm(sumOf, assumedBody)
            // `Sum t (2 + d)` is `Sum t v` by the witness; the bound is carried across by rewriting.
            rewritten <- rewrite(atV, bound)
            eliminated <- rules.existsElim(witness, d, rewritten)
            result <- rules.disch(guard, eliminated).flatMap(rules.gen(v, _))
          } yield result
        for { up <- fromTwo(upper); down <- fromTwo(lower) } yield (up, down)
      }
      converges <- transcendental.fact(Transcendental.ExponentialConverges).flatMap(rules.spec(h, _))
      line <- real("1 + h:real + h * h")
      floor <- real("1 + h:real - h * h")
      expH <- real("exp (h:real)")
      atMost <- limit.fact(Limit.BelowBound).flatMap(rules.specAll(_, List(sumOf, expH, line, twoNumber))).flatMap(opened)
        .flatMap(mp(_, Right(converges), Right(everyIndex._1)))
      atLeast <- limit.fact(Limit.AboveBound).flatMap(rules.specAll(_, List(sumOf, expH, floor, twoNumber))).flatMap(opened)
        .flatMap(mp(_, Right(converges), Right(everyIndex._2)))
      cases <- at(magnitude.fact(Magnitude.AbsCases), "exp (h:real) - 1 - h")
      itself <- assume("abs (exp (h:real) - 1 - h) = exp h - 1 - h").flatMap(eq =>
        at(lemma("!A:real E:real h:real. A = E - 1 - h ==> E <= 1 + h + h * h ==> A <= h * h"), "abs (exp (h:real) - 1 - h)", "exp (h:real)", "h:real")
          .flatMap(mp(_, Right(eq), Right(atMost))))
      negated <- assume("abs (exp (h:real) - 1 - h) = -(exp h - 1 - h)").flatMap(eq =>
        at(lemma("!A:real E:real h:real. A = -(E - 1 - h) ==> 1 + h - h * h <= E ==> A <= h * h"), "abs (exp (h:real) - 1 - h)", "exp (h:real)", "h:real")
          .flatMap(mp(_, Right(eq), Right(atLeast))))
      estimate <- rules.disjElim(cases, itself, negated)
      result <- rules.disch(hypothesis, estimate).flatMap(rules.gen(h, _))
    } yield result
  }

  /** `|- text = value`, by walking `text` with `recurrences` and closing the gap with `Ring`. */
  private def settle(steps: Steps, recurrences: Vector[Rewrite.Rule], text: String, value: String): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      term <- real(text)
      walked <- Rewrite.rewrite(recurrences, term)
      walkedValue <- rightOf(walked)
      target <- real(value)
      closes <- LogicError.lift(Term.eq(walkedValue, target)).flatMap(ring.prove)
      joined <- Conv.trans(walked, closes)
    } yield joined
  }

  /* ===================================================================== the estimate at zero */

  /** [[NearOne]], by the sign of `h`: the two bounds above, and below zero their reflection. */
  private def exponentialNearOne(
    steps: Steps,
    aboveLine: Kernel.Thm,
    smallAbove: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val h = Term.variable("h", Reals)
    for {
      hypothesis <- proposition("abs (h:real) <= 1 / 2")
      small <- LogicError.lift(Kernel.assume(hypothesis))
      goal <- proposition("abs (exp (h:real) - 1) <= 2 * abs h")
      magnitudeNonNegative <- at(magnitude.fact(Magnitude.AbsNonNegative), "h:real")

      positiveCase <- for {
        sign <- assume("0 < h:real")
        magnitudeIs <- at(magnitude.fact(Magnitude.OfNonNegative), "h:real")
          .flatMap(mp(_, at(lemma("!h:real. 0 < h ==> 0 <= h"), "h:real").flatMap(mp(_, Right(sign)))))
        below <- at(Right(aboveLine), "h:real").flatMap(mp(_, Right(sign)))
        bounded <- at(lemma("!m:real h:real. m = h ==> m <= 1 / 2 ==> h <= 1 / 2"), "abs (h:real)", "h:real")
          .flatMap(mp(_, Right(magnitudeIs), Right(small)))
        above <- at(Right(smallAbove), "h:real").flatMap(mp(_, Right(sign), Right(bounded)))
        distanceIs <- at(magnitude.fact(Magnitude.OfNonNegative), "exp (h:real) - 1")
          .flatMap(mp(_, at(lemma("!h:real e:real. 1 + h <= e ==> 0 < h ==> 0 <= e - 1"), "h:real", "exp (h:real)")
            .flatMap(mp(_, Right(below), Right(sign)))))
        result <- at(
          lemma("!d:real m:real e:real h:real. d = e - 1 ==> m = h ==> e <= 1 + 2 * h ==> d <= 2 * m"),
          "abs (exp (h:real) - 1)", "abs (h:real)", "exp (h:real)", "h:real")
          .flatMap(mp(_, Right(distanceIs), Right(magnitudeIs), Right(above)))
      } yield result

      zeroCase <- for {
        same <- assume("0 = h:real")
        exp <- Parser.term(theory, notation, "exp", Type.fun(Reals, Reals))
        atZero <- transcendental.fact(Transcendental.ExponentialAtZero)
        value <- Conv.apTerm(exp, same).flatMap(Conv.sym).flatMap(Conv.trans(_, atZero))
        distanceIs <- at(magnitude.fact(Magnitude.OfNonNegative), "exp (h:real) - 1")
          .flatMap(mp(_, at(lemma("!e:real. e = 1 ==> 0 <= e - 1"), "exp (h:real)").flatMap(mp(_, Right(value)))))
        result <- at(
          lemma("!d:real m:real e:real. d = e - 1 ==> e = 1 ==> 0 <= m ==> d <= 2 * m"),
          "abs (exp (h:real) - 1)", "abs (h:real)", "exp (h:real)")
          .flatMap(mp(_, Right(distanceIs), Right(value), Right(magnitudeNonNegative)))
      } yield result

      negativeCase <- for {
        sign <- assume("h:real < 0")
        magnitudeIs <- at(magnitude.fact(Magnitude.OfNonPositive), "h:real")
          .flatMap(mp(_, at(lemma("!h:real. h < 0 ==> h <= 0"), "h:real").flatMap(mp(_, Right(sign)))))
        reflected <- at(lemma("!h:real. h < 0 ==> 0 < 0 - h"), "h:real").flatMap(mp(_, Right(sign)))
        reflectedSmall <- at(lemma("!m:real h:real. m = -h ==> m <= 1 / 2 ==> 0 - h <= 1 / 2"), "abs (h:real)", "h:real")
          .flatMap(mp(_, Right(magnitudeIs), Right(small)))
        below <- at(Right(aboveLine), "0 - h:real").flatMap(mp(_, Right(reflected)))
        above <- at(Right(smallAbove), "0 - h:real").flatMap(mp(_, Right(reflected), Right(reflectedSmall)))
        reciprocal <- at(transcendental.fact(Transcendental.Reciprocal), "h:real")
        atMostOne <- at(
          lemma("!f:real e:real t:real. f * e = 1 ==> 1 + t <= e ==> 0 < t ==> f - 1 <= 0"),
          "exp (h:real)", "exp (0 - h:real)", "0 - h:real")
          .flatMap(mp(_, Right(reciprocal), Right(below), Right(reflected)))
        distanceIs <- at(magnitude.fact(Magnitude.OfNonPositive), "exp (h:real) - 1").flatMap(mp(_, Right(atMostOne)))
        // Two lemmas and not one: with all seven hypotheses at once `Linarith` stops at its bound on
        // facts, which it reports as saying nothing either way. The product the argument needs,
        // `(1 - f) * (e - 1) >= 0`, is the whole of the first; the second is linear.
        shortfall <- at(
          lemma("!f:real e:real t:real. f * e = 1 ==> 1 + t <= e ==> 0 < t ==> f - 1 <= 0 ==> 1 - f <= e - 1"),
          "exp (h:real)", "exp (0 - h:real)", "0 - h:real")
          .flatMap(mp(_, Right(reciprocal), Right(below), Right(reflected), Right(atMostOne)))
        result <- at(
          lemma("!d:real m:real f:real e:real h:real. d = -(f - 1) ==> m = -h ==> " +
            "1 - f <= e - 1 ==> e <= 1 + 2 * (0 - h) ==> d <= 2 * m"),
          "abs (exp (h:real) - 1)", "abs (h:real)", "exp (h:real)", "exp (0 - h:real)", "h:real")
          .flatMap(mp(_, Right(distanceIs), Right(magnitudeIs), Right(shortfall), Right(above)))
      } yield result

      trichotomy <- at(reals.axiom("LT_TOTAL"), "0:real", "h:real")
      rest <- assume("0 = h:real \\/ h:real < 0").flatMap(rules.disjElim(_, zeroCase, negativeCase))
      cases <- rules.disjElim(trichotomy, positiveCase, rest)
      result <- rules.disch(hypothesis, cases).flatMap(rules.gen(h, _))
    } yield result
  }

  /* ========================================================================= continuity */

  /**
   * [[Continuous]]. At tolerance `e` the radius is `min (1/2) w` with `w * (2 exp x + 1) = e`, so
   * that inside it `abs (exp y - exp x) = exp x * abs (exp (y - x) - 1) <= 2 exp x abs (y - x)`,
   * which is under `e`. The reciprocal enters as a term whose only property used is `MUL_INVERSE`,
   * which is `Root`'s arrangement.
   */
  private def exponentialContinuous(
    steps: Steps,
    positive: Kernel.Thm,
    nearOne: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    val e = Term.variable("e", Reals)
    val y = Term.variable("y", Reals)
    val c = "2 * exp (x:real) + 1"
    val w = s"(e:real) * inv ($c)"
    val d = s"min (1 / 2) ($w)"
    for {
      exp <- Parser.term(theory, notation, "exp", Type.fun(Reals, Reals))
      tolerance <- proposition("0 < e:real")
      assumedTolerance <- LogicError.lift(Kernel.assume(tolerance))
      valuePositive <- rules.spec(x, positive)
      cPositive <- at(lemma("!p:real. 0 < p ==> 0 < 2 * p + 1"), "exp (x:real)").flatMap(mp(_, Right(valuePositive)))
      cTerm <- real(c)
      cancels <- magnitude.order.fact(Order.NonZero).flatMap(rules.spec(cTerm, _)).flatMap(rules.mp(_, cPositive))
        .flatMap(nonZero => reals.axiom("MUL_INVERSE").flatMap(rules.spec(cTerm, _)).flatMap(rules.mp(_, nonZero)))
      wTimesC <- at(lemma("!e:real c:real v:real. 0 < e ==> c * v = 1 ==> (e * v) * c = e"), "e:real", c, s"inv ($c)")
        .flatMap(mp(_, Right(assumedTolerance), Right(cancels)))
      wPositive <- at(lemma("!e:real c:real w:real. 0 < e ==> 0 < c ==> w * c = e ==> 0 < w"), "e:real", c, w)
        .flatMap(mp(_, Right(assumedTolerance), Right(cPositive), Right(wTimesC)))

      radiusCases <- at(magnitude.fact(Magnitude.MinCases), "1 / 2", w)
      atHalf <- assume(s"$d = 1 / 2")
        .flatMap(eq => at(lemma("!r:real. r = 1 / 2 ==> 0 < r"), d).flatMap(mp(_, Right(eq))))
      atW <- assume(s"$d = $w")
        .flatMap(eq => at(lemma("!r:real w:real. r = w ==> 0 < w ==> 0 < r"), d, w).flatMap(mp(_, Right(eq), Right(wPositive))))
      radiusPositive <- rules.disjElim(radiusCases, atHalf, atW)
      belowHalf <- at(magnitude.fact(Magnitude.MinBelowLeft), "1 / 2", w)
      belowW <- at(magnitude.fact(Magnitude.MinBelowRight), "1 / 2", w)

      near <- proposition(s"abs ((y:real) - x) < $d")
      assumedNear <- LogicError.lift(Kernel.assume(near))
      small <- at(lemma("!a:real r:real. a < r ==> r <= 1 / 2 ==> a <= 1 / 2"), "abs ((y:real) - x)", d)
        .flatMap(mp(_, Right(assumedNear), Right(belowHalf)))
      underW <- at(lemma("!a:real r:real w:real. a < r ==> r <= w ==> a < w"), "abs ((y:real) - x)", d, w)
        .flatMap(mp(_, Right(assumedNear), Right(belowW)))
      estimate <- at(Right(nearOne), "(y:real) - x").flatMap(mp(_, Right(small)))

      sum <- ringEquation("(x:real) + ((y:real) - x)", "y:real")
      addition <- at(transcendental.fact(Transcendental.Addition), "x:real", "(y:real) - x")
      product <- Conv.apTerm(exp, sum).flatMap(Conv.sym).flatMap(Conv.trans(_, addition))
      // `exp y - exp x = exp x * (exp (y - x) - 1)`, by congruence and `Ring`: an equation is not
      // asked of `Linarith`, for the reason `Root` records.
      minus <- Parser.term(theory, notation, "(1:real) - 1", Reals).flatMap {
        case App(App(operator, _), _) => Right(operator)
        case unexpected               => Left(NotOfForm("a difference", unexpected))
      }
      valueAtX <- real("exp (x:real)")
      difference <- Conv.apTerm(minus, product).flatMap(Conv.apThm(_, valueAtX))
        .flatMap(first => ringEquation("exp (x:real) * exp ((y:real) - x) - exp x", "exp (x:real) * (exp ((y:real) - x) - 1)")
          .flatMap(Conv.trans(first, _)))
      split <- at(magnitude.fact(Magnitude.Multiplicative), "exp (x:real)", "exp ((y:real) - x) - 1")
      factorIs <- at(magnitude.fact(Magnitude.OfNonNegative), "exp (x:real)")
        .flatMap(mp(_, at(lemma("!p:real. 0 < p ==> 0 <= p"), "exp (x:real)").flatMap(mp(_, Right(valuePositive)))))
      splitAtValue <- rewrite(factorIs, split)
      // Three lemmas of four hypotheses rather than one of seven, for `Linarith`'s bound on facts:
      // the two products by `exp x` first, then a step that is linear in them.
      p = "exp (x:real)"
      q = "abs (exp ((y:real) - x) - 1)"
      a = "abs ((y:real) - x)"
      scaled <- at(lemma("!p:real q:real a:real. 0 < p ==> q <= 2 * a ==> p * q <= 2 * (p * a)"), p, q, a)
        .flatMap(mp(_, Right(valuePositive), Right(estimate)))
      shifted <- at(lemma("!p:real a:real w:real. 0 < p ==> a < w ==> p * a < p * w"), p, a, w)
        .flatMap(mp(_, Right(valuePositive), Right(underW)))
      underTolerance <- at(
        lemma("!p:real q:real a:real w:real e:real. p * q <= 2 * (p * a) ==> p * a < p * w ==> " +
          "w * (2 * p + 1) = e ==> 0 < w ==> p * q < e"),
        p, q, a, w, "e:real")
        .flatMap(mp(_, Right(scaled), Right(shifted), Right(wTimesC), Right(wPositive)))
      abs <- Parser.term(theory, notation, "abs", Type.fun(Reals, Reals))
      distance <- Conv.apTerm(abs, difference).flatMap(Conv.trans(_, splitAtValue))
      bound <- Conv.sym(distance).flatMap(rewrite(_, underTolerance))

      everyPoint <- rules.disch(near, bound).flatMap(rules.gen(y, _))
      radius <- rules.conjIntro(radiusPositive, everyPoint)
      dTerm <- real(d)
      witnessed <- existential(
        "?d:real. 0 < d /\\ (!y:real. abs ((y:real) - x) < d ==> abs (exp y - exp x) < e:real)")
        .flatMap(rules.existsIntro(_, dTerm, radius))
      statement <- rules.disch(tolerance, witnessed).flatMap(rules.gen(e, _))

      unfolded <- continuity.definition(Continuity.Continuous)
        .flatMap(Conv.unfold(_, List(exp, x)))
        .flatMap(equation => rightOf(equation).flatMap(Conv.betaNormalise).flatMap(Conv.trans(equation, _)))
      folded <- Conv.sym(unfolded).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, statement)))
      result <- rules.gen(x, folded)
    } yield result
  }

  /* ================================================================= order and injectivity */

  /** [[StrictlyIncreasing]]: `exp b = exp a * exp (b - a)`, and the second factor is above one. */
  private def exponentialIncreasing(
    steps: Steps,
    positive: Kernel.Thm,
    aboveLine: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    for {
      exp <- Parser.term(theory, notation, "exp", Type.fun(Reals, Reals))
      hypothesis <- proposition("(a:real) < b")
      ordered <- LogicError.lift(Kernel.assume(hypothesis))
      gap <- at(lemma("!a:real b:real. a < b ==> 0 < b - a"), "a:real", "b:real").flatMap(mp(_, Right(ordered)))
      sum <- ringEquation("(a:real) + ((b:real) - a)", "b:real")
      addition <- at(transcendental.fact(Transcendental.Addition), "a:real", "(b:real) - a")
      product <- Conv.apTerm(exp, sum).flatMap(Conv.sym).flatMap(Conv.trans(_, addition))
      factor <- at(Right(aboveLine), "(b:real) - a").flatMap(mp(_, Right(gap)))
      base <- rules.spec(a, positive)
      result <- at(
        lemma("!r:real p:real q:real s:real. r = p * q ==> 0 < p ==> 1 + s <= q ==> 0 < s ==> p < r"),
        "exp (b:real)", "exp (a:real)", "exp ((b:real) - a)", "(b:real) - a")
        .flatMap(mp(_, Right(product), Right(base), Right(factor), Right(gap)))
        .flatMap(rules.disch(hypothesis, _))
        .flatMap(rules.genAll(_, List(a, b)))
    } yield result
  }

  /** [[Injective]], from strict monotonicity by trichotomy. */
  private def exponentialInjective(steps: Steps, increasing: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    for {
      hypothesis <- proposition("exp (a:real) = exp b")
      same <- LogicError.lift(Kernel.assume(hypothesis))
      goal <- proposition("(a:real) = b")
      below <- for {
        ordered <- assume("(a:real) < b")
        strict <- at(Right(increasing), "a:real", "b:real").flatMap(mp(_, Right(ordered)))
        absurd <- at(lemma("!u:real v:real. u < v ==> u = v ==> F"), "exp (a:real)", "exp (b:real)")
          .flatMap(mp(_, Right(strict), Right(same)))
        result <- rules.falsityElim(goal, absurd)
      } yield result
      equal <- assume("(a:real) = b")
      above <- for {
        ordered <- assume("(b:real) < a")
        strict <- at(Right(increasing), "b:real", "a:real").flatMap(mp(_, Right(ordered)))
        absurd <- at(lemma("!u:real v:real. v < u ==> u = v ==> F"), "exp (a:real)", "exp (b:real)")
          .flatMap(mp(_, Right(strict), Right(same)))
        result <- rules.falsityElim(goal, absurd)
      } yield result
      trichotomy <- at(reals.axiom("LT_TOTAL"), "a:real", "b:real")
      rest <- assume("(a:real) = b \\/ (b:real) < a").flatMap(rules.disjElim(_, equal, above))
      result <- rules.disjElim(trichotomy, below, rest)
        .flatMap(rules.disch(hypothesis, _))
        .flatMap(rules.genAll(_, List(a, b)))
    } yield result
  }

  /* ========================================================================== onto the positives */

  /**
   * [[Onto]]. At a `y` of at least one the intermediate value theorem on `[0, y]`, where the
   * exponential is `1` at the left end and at least `1 + y` at the right; below one, the same at
   * `inv y`, and `exp (0 - x) = y` from `exp x * exp (0 - x) = 1`.
   */
  private def exponentialOnto(
    steps: Steps,
    aboveLine: Kernel.Thm,
    continuous: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val y = Term.variable("y", Reals)
    val x = Term.variable("x", Reals)
    val z = Term.variable("z", Reals)

    /** `|- 1 <= target ==> ?x. exp x = target`, at a target given as text. */
    def fromOne(target: String): Either[LogicError, Kernel.Thm] =
      for {
        exp <- Parser.term(theory, notation, "exp", Type.fun(Reals, Reals))
        hypothesis <- proposition(s"1 <= $target")
        atLeastOne <- LogicError.lift(Kernel.assume(hypothesis))
        targetTerm <- real(target)
        zero <- real("0:real")
        theorem <- continuity.fact(Continuity.IntermediateValue)
          .flatMap(rules.specAll(_, List(exp, zero, targetTerm, targetTerm)))
        ordered <- at(lemma("!y:real. 1 <= y ==> 0 <= y"), target).flatMap(mp(_, Right(atLeastOne)))
        inside <- proposition(s"0 <= x:real /\\ x <= $target")
        everywhere <- rules.spec(x, continuous).flatMap(rules.disch(inside, _)).flatMap(rules.gen(x, _))
        leftEnd <- transcendental.fact(Transcendental.ExponentialAtZero).flatMap(atZero =>
          at(lemma("!e:real y:real. e = 1 ==> 1 <= y ==> e <= y"), "exp 0", target)
            .flatMap(mp(_, Right(atZero), Right(atLeastOne))))
        positiveTarget <- at(lemma("!y:real. 1 <= y ==> 0 < y"), target).flatMap(mp(_, Right(atLeastOne)))
        rightEnd <- at(Right(aboveLine), target).flatMap(mp(_, Right(positiveTarget)))
          .flatMap(line => at(lemma("!y:real e:real. 1 + y <= e ==> 0 < y ==> y <= e"), target, s"exp ($target)")
            .flatMap(mp(_, Right(line), Right(positiveTarget))))
        crossing <- mp(theorem, Right(ordered), Right(everywhere), Right(leftEnd), Right(rightEnd))
        body <- instanceAt(crossing, x)
        assumedBody <- LogicError.lift(Kernel.assume(body))
        value <- rules.conjElim2(assumedBody).flatMap(rules.conjElim2)
        found <- existential(s"?x:real. exp x = $target").flatMap(rules.existsIntro(_, x, value))
        eliminated <- rules.existsElim(crossing, x, found)
        result <- rules.disch(hypothesis, eliminated)
      } yield result

    for {
      hypothesis <- proposition("0 < y:real")
      positive <- LogicError.lift(Kernel.assume(hypothesis))
      goal <- proposition("?x:real. exp x = y")

      atLeastOne <- for {
        cases <- assume("(y:real) = 1 \\/ 1 < y")
        equal <- assume("(y:real) = 1").flatMap(eq => at(lemma("!y:real. y = 1 ==> 1 <= y"), "y:real").flatMap(mp(_, Right(eq))))
        greater <- assume("1 < y:real").flatMap(gt => at(lemma("!y:real. 1 < y ==> 1 <= y"), "y:real").flatMap(mp(_, Right(gt))))
        joined <- rules.disjElim(cases, equal, greater)
        result <- fromOne("y:real").flatMap(rules.mp(_, joined))
      } yield result

      belowOne <- for {
        under <- assume("(y:real) < 1")
        nonZero <- magnitude.order.fact(Order.NonZero).flatMap(rules.spec(y, _)).flatMap(rules.mp(_, positive))
        cancels <- reals.axiom("MUL_INVERSE").flatMap(rules.spec(y, _)).flatMap(rules.mp(_, nonZero))
        inversePositive <- magnitude.order.fact(Order.InversePositive).flatMap(rules.spec(y, _)).flatMap(rules.mp(_, positive))
        aboveOne <- at(lemma("!y:real v:real. y * v = 1 ==> 0 < y ==> y < 1 ==> 0 < v ==> 1 <= v"), "y:real", "inv (y:real)")
          .flatMap(mp(_, Right(cancels), Right(positive), Right(under), Right(inversePositive)))
        reflected <- fromOne("inv (y:real)").flatMap(rules.mp(_, aboveOne))
        body <- instanceAt(reflected, z)
        assumedBody <- LogicError.lift(Kernel.assume(body))
        reciprocal <- at(transcendental.fact(Transcendental.Reciprocal), "z:real")
        // `exp (0 - z) = y`, by a chain of congruences rather than a procedure: `Linarith`
        // is not asked an equation here, for the reason `Root` records.
        other <- real("exp (0 - z:real)")
        times <- Parser.term(theory, notation, "(1:real) * 1", Reals).flatMap {
          case App(App(product, _), _) => Right(product)
          case unexpected              => Left(NotOfForm("a product", unexpected))
        }
        unit <- ringEquation("exp (0 - z:real)", "1 * exp (0 - z:real)")
        expanded <- Conv.sym(cancels).flatMap(Conv.apTerm(times, _)).flatMap(Conv.apThm(_, other))
        regrouped <- ringEquation("((y:real) * inv y) * exp (0 - z:real)", "y * (inv y * exp (0 - z:real))")
        substituted <- for {
          moved <- Conv.sym(assumedBody)
          byY <- real("y:real").flatMap(yt => LogicError.lift(Term.app(times, yt)))
          inner <- Conv.apTerm(times, moved).flatMap(Conv.apThm(_, other))
          outer <- Conv.apTerm(byY, inner)
        } yield outer
        byY <- real("y:real").flatMap(yt => LogicError.lift(Term.app(times, yt)))
        closed <- Conv.apTerm(byY, reciprocal)
        last <- ringEquation("(y:real) * 1", "y:real")
        chain <- Conv.trans(unit, expanded)
          .flatMap(Conv.trans(_, regrouped))
          .flatMap(Conv.trans(_, substituted))
          .flatMap(Conv.trans(_, closed))
          .flatMap(Conv.trans(_, last))
        witness <- real("0 - z:real")
        found <- existential("?x:real. exp x = y:real").flatMap(rules.existsIntro(_, witness, chain))
        result <- rules.existsElim(reflected, z, found)
      } yield result

      // `disjElim` discharges each disjunct itself: the second case is proved under exactly the
      // assumption `LT_TOTAL`'s second disjunct names.
      trichotomy <- at(reals.axiom("LT_TOTAL"), "y:real", "1:real")
      settled <- rules.disjElim(trichotomy, belowOne, atLeastOne)
      result <- rules.disch(hypothesis, settled).flatMap(rules.gen(y, _))
    } yield result
  }

  /* =============================================================================== the logarithm */

  /** [[ExpOfLn]]: the choice in `ln`'s definition, at a predicate [[Onto]] says is satisfiable. */
  private def exponentialOfLogarithm(steps: Steps, onto: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val y = Term.variable("y", Reals)
    for {
      exp <- Parser.term(theory, notation, "exp", Type.fun(Reals, Reals))
      hypothesis <- proposition("0 < y:real")
      positive <- LogicError.lift(Kernel.assume(hypothesis))
      existential <- rules.spec(y, onto).flatMap(rules.mp(_, positive))
      chosen <- classical.witness(existential).flatMap(opened)
      unfolded <- transcendental.definition(Transcendental.Logarithm)
        .flatMap(Conv.unfold(_, List(y)))
        .flatMap(equation => rightOf(equation).flatMap(Conv.betaNormalise).flatMap(Conv.trans(equation, _)))
      carried <- Conv.apTerm(exp, unfolded)
      value <- Conv.trans(carried, chosen)
      result <- rules.disch(hypothesis, value).flatMap(rules.gen(y, _))
    } yield result
  }

  /** [[LnOfExp]]: `exp (ln (exp x)) = exp x`, and the exponential is injective. */
  private def logarithmOfExponential(
    steps: Steps,
    positive: Kernel.Thm,
    injective: Kernel.Thm,
    expOfLn: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    for {
      valuePositive <- rules.spec(x, positive)
      value <- at(Right(expOfLn), "exp (x:real)").flatMap(mp(_, Right(valuePositive)))
      result <- at(Right(injective), "ln (exp (x:real))", "x:real")
        .flatMap(mp(_, Right(value)))
        .flatMap(rules.gen(x, _))
    } yield result
  }

  /** [[AtOne]]: [[LnOfExp]] at zero, read through `exp 0 = 1`. */
  private def logarithmAtOne(steps: Steps, lnOfExp: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      atZero <- at(Right(lnOfExp), "0:real")
      value <- transcendental.fact(Transcendental.ExponentialAtZero)
      result <- rewrite(value, atZero)
    } yield result
  }

  /** [[Multiplicative]]: both sides have exponential `a * b`, and the exponential is injective. */
  private def logarithmOfProduct(
    steps: Steps,
    injective: Kernel.Thm,
    expOfLn: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    for {
      exp <- Parser.term(theory, notation, "exp", Type.fun(Reals, Reals))
      aStatement <- proposition("0 < a:real")
      bStatement <- proposition("0 < b:real")
      aPositive <- LogicError.lift(Kernel.assume(aStatement))
      bPositive <- LogicError.lift(Kernel.assume(bStatement))
      productPositive <- at(lemma("!a:real b:real. 0 < a ==> 0 < b ==> 0 < a * b"), "a:real", "b:real")
        .flatMap(mp(_, Right(aPositive), Right(bPositive)))
      atProduct <- at(Right(expOfLn), "(a:real) * b").flatMap(mp(_, Right(productPositive)))
      addition <- at(transcendental.fact(Transcendental.Addition), "ln (a:real)", "ln (b:real)")
      atA <- at(Right(expOfLn), "a:real").flatMap(mp(_, Right(aPositive)))
      atB <- at(Right(expOfLn), "b:real").flatMap(mp(_, Right(bPositive)))
      times <- Parser.term(theory, notation, "(1:real) * 1", Reals).flatMap {
        case App(App(product, _), _) => Right(product)
        case unexpected              => Left(NotOfForm("a product", unexpected))
      }
      lnB <- real("exp (ln (b:real))")
      aTerm <- real("a:real")
      byA <- LogicError.lift(Term.app(times, aTerm))
      values <- Conv.apTerm(times, atA).flatMap(Conv.apThm(_, lnB))
        .flatMap(first => Conv.apTerm(byA, atB).flatMap(Conv.trans(first, _)))
      sumSide <- Conv.trans(addition, values)
      same <- Conv.sym(sumSide).flatMap(Conv.trans(atProduct, _))
      result <- at(Right(injective), "ln ((a:real) * b)", "ln (a:real) + ln (b:real)")
        .flatMap(mp(_, Right(same)))
        .flatMap(rules.disch(bStatement, _))
        .flatMap(rules.disch(aStatement, _))
        .flatMap(rules.genAll(_, List(a, b)))
    } yield result
  }
}
