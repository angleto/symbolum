package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A procedure that decides whether a series converges, over a named fragment, and refuses outside
 * it saying which kind of outside.
 *
 * == It cannot be complete over every series, and the reason is not a missing lemma ==
 *
 * For any decidable predicate `P` on `num`, the summand `COND (?j. NUM_LE j i /\ P j) 1 0` gives a
 * series that diverges exactly when `?j. P j`. A procedure answering every convergence question
 * would answer every `Pi-0-1` question, so what is decided has to be a fragment, and the rest has
 * to be refused rather than guessed.
 *
 * == The fragment ==
 *
 * The summand is read as a lambda over the index, and its body as one of:
 *
 *  - a constant free of the index that LINARITH shows is not zero, whose series diverges by the
 *    term test (`Sum (\i. 1)` is the case); the zero series converges and is refused, for want of
 *    a fact about a sum of zeros rather than for want of an answer;
 *  - `Power q i`, the geometric series, decided in **both** directions when the sign of `q` and its
 *    magnitude against one are decided by LINARITH: `Limit.SUM_GEOMETRIC_CONVERGES` below one, with
 *    the value `inv (1 - q)`, and `Limit.SUM_GEOMETRIC_DIVERGES` at one and above;
 *  - `Power t i / real_of_num (NUM_FACT i)`, the exponential's series, which converges at every `t`
 *    whatever `t` is, to `exp t`;
 *  - the cosine's and the sine's series in the spelling `Transcendental.COS_CONVERGES` states, to
 *    `cos x` and `sin x`;
 *  - `c * g i` for any of those, with `c` free of the index: a convergence carries the factor into
 *    the value, and a divergence carries it where LINARITH shows `~(c = 0)`.
 *
 * On that fragment it is complete where the numbers are numerals, **except at zero**: a geometric
 * ratio that is a numeral has a sign and a magnitude LINARITH decides, so every such series is
 * answered one way or the other, but a zero constant or a zero factor in front of a divergent
 * series gives a series that converges and is refused, because saying so wants a fact about a sum
 * of zeros this procedure does not carry. `0 * Power 3 i` is the case `ConvergenceSpec` holds. A
 * symbolic ratio is answered where its sign and magnitude follow with no hypotheses, which is
 * rarely, and refused otherwise, naming the ratio.
 *
 * == Three refusals, and they are kept apart ==
 *
 *  - The summand is not in the fragment, and the refusal names it: nothing was learned.
 *  - The summand is a rational function of the index, which is where the ratio of consecutive terms
 *    tends to **one**: the ratio test says nothing there, deciding that class wants Raabe's or
 *    Gauss's test and the p-series under them, and the refusal says so rather than calling the
 *    summand unreadable. Also nothing learned, and a different next move.
 *  - The procedure proved the opposite of the goal, which is `Denied`, carrying the theorem: a
 *    decided answer, and the only one of the three that is.
 *
 * == Why closed forms rather than the ratio test ==
 *
 * `Limit.SUM_RATIO_TEST` is the obvious engine and it is not used. Applying it means proving
 * `abs (f (SUC n)) <= r * abs (f n)` at a **symbolic** `n` for the summand in hand, which for the
 * exponential's series is a rewrite of `POWER_SUC`, of `NUM_FACT` at a successor, of `real_of_num`
 * across a product and a cancellation of a reciprocal, all before LINARITH sees anything, and a
 * different sequence of those for every shape. The closed forms need none of it: every shape here
 * already has a published theorem saying what its series does. Widening the fragment to the
 * hypergeometric terms is the work the ratio test is for, and it is recorded as a gap rather than
 * started here.
 *
 * == What it does not do ==
 *
 * It never proposes a value for a series it has not read, and it asks the algebra half nothing:
 * `core` has no notion of a series or of a limit, so there is nothing there to propose with.
 */
final class Convergence private (
  logic: Logic,
  theory: Theory,
  notation: Notation,
  linarith: Linarith,
  ring: Ring,
  field: Field,
  facts: Convergence.Facts
) {
  import Convergence.*

  private val rules = logic.rules

  /** Whether `goal` is a question this procedure is asked: a convergence or a divergence of a series. */
  def reads(goal: Term): Boolean = Convergence.goalOf(logic, goal).isDefined

  /** The theorem that is `goal`, or a refusal saying which of the three it is. */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    Convergence.goalOf(logic, goal) match {
      case None => Left(NotOfForm(Expected, goal))
      case Some(question) =>
        decide(question.series).flatMap(answer => settle(goal, question, answer))
    }

  /** The same, from text read against the theory this procedure was built over. */
  def prove(text: String): Either[LogicError, Kernel.Thm] =
    Parser.proposition(theory, notation, text).flatMap(prove)

  /** What the series does, with the theorem that says so. */
  private def decide(series: Term): Either[LogicError, Answer] =
    series match {
      case App(_, summand @ Abs(_, _)) =>
        val index = Conv.freshVariable("i", numbers, Term.freeVariables(summand))
        for {
          opened <- LogicError.lift(Term.app(summand, index))
          body <- Term.betaReduce(opened).toRight(NotOfForm("a summand that is a lambda", summand))
          shape <- shapeOf(index, body)
          answer <- answerFor(shape)
        } yield answer
      case App(_, summand) =>
        Left(NotOfForm("a summand written as a lambda over the index", summand))
      case other => Left(NotOfForm("a series", other))
    }

  /** The summand's body read against the fragment, or the refusal that names why it is not in it. */
  private def shapeOf(index: FVar, body: Term): Either[LogicError, Shape] = {
    def read(pattern: String, name: String): Option[Term] =
      (for {
        written <- Parser.term(theory, notation, pattern, values).toOption
        placed <- Term.substitute(Map(Term.variable("i", numbers) -> index), written).toOption
        parameter = Term.variable(name, values)
        found <- Matching.matchTerm(Set(parameter), placed, body)
        bound <- found.terms.get(parameter)
        if !Term.occursFree(index, bound)
      } yield bound)

    def plain: Option[Shape] =
      read("Power (q:real) (i:num)", "q").map(Shape.Geometric.apply)
        .orElse(read("Power (t:real) (i:num) / real_of_num (NUM_FACT (i:num))", "t").map(Shape.Exponential.apply))
        .orElse(read(Trigonometric.cosineTerm("i:num"), "x").map(Shape.Cosine.apply))
        .orElse(read(Trigonometric.sineTerm("i:num"), "x").map(Shape.Sine.apply))

    val scaled: Option[Shape] = body match {
      case App(App(times, factor), rest)
          if Parser.term(theory, notation, "(a:real) * (b:real)", values).toOption.exists {
            case App(App(symbol, _), _) => symbol == times
            case _                      => false
          } && !Term.occursFree(index, factor) =>
        shapeOf(index, rest).toOption.map(inner => Shape.Scaled(factor, inner))
      case _ => None
    }

    // A summand free of the index. Read last so that `c * Power q i` is not mistaken for one, which
    // it cannot be anyway, and first among the refusals' alternatives because it is the cheapest.
    val constant: Option[Shape] =
      if (Term.occursFree(index, body)) None else Some(Shape.Constant(body))

    plain.orElse(scaled).orElse(constant).toRight(
      if (ratioTendsToOne(index, body)) NotOfForm(RatioTendsToOne, body)
      else NotOfForm(Summands, body)
    )
  }

  /**
   * Whether the index occurs in `body` only inside `real_of_num`, which is what a rational function
   * of the index looks like here: `inv (real_of_num (SUC i))`, `real_of_num i * real_of_num i`.
   */
  private def ratioTendsToOne(index: FVar, body: Term): Boolean = {
    val embedding = Parser.term(theory, notation, "real_of_num").toOption
    def outside(term: Term): Boolean = term match {
      case App(fn, _) if embedding.contains(fn) => false
      case App(fn, arg)                         => outside(fn) || outside(arg)
      case Abs(_, inner)                        => outside(inner)
      case other                                => other == index
    }
    Term.occursFree(index, body) && !outside(body)
  }

  /** The theorem a recognised shape is answered with. */
  private def answerFor(shape: Shape): Either[LogicError, Answer] =
    shape match {
      case Shape.Geometric(q) =>
        magnitude(q).flatMap {
          case Left(below) =>
            rules.spec(q, facts.geometricConverges).flatMap(rules.mp(_, below)).map(Answer.Converges.apply)
          case Right(atLeast) =>
            rules.spec(q, facts.geometricDiverges).flatMap(rules.mp(_, atLeast)).map(Answer.Diverges.apply)
        }
      case Shape.Constant(value) =>
        // The term test at the constant's own magnitude, from index zero. Only a non-zero constant
        // is answered: the zero series converges, and saying so wants a fact about a sum of zeros
        // this procedure does not carry, so it is refused rather than guessed.
        for {
          equation <- signOf(value).left.map(_ => NotOfForm("a constant summand whose sign LINARITH decides", value))
          positive <- through(equation, "\\x:real. 0 < x")
            .left
            .map(_ => NotOfForm("a constant summand LINARITH shows is not zero", value))
          size <- Limit.destructEquation(equation).map(_._1)
          summand <- LogicError.lift(Term.abs(Conv.freshVariable("i", numbers, Term.freeVariables(value)), value))
          indexZero <- Parser.term(theory, notation, "ZERO", numbers)
          instance <- rules
            .specAll(facts.termTest, List(summand, size, indexZero))
            .flatMap(Limit.normalised)
            .flatMap(rules.mp(_, positive))
          premise <- logic.destImp(instance.conclusion).map(_._1).toRight(NotOfForm("an implication", instance.conclusion))
          stripped <- Logic.stripForall(premise)
          guard <- logic.destImp(stripped._2).toRight(NotOfForm("a guarded bound", stripped._2))
          index <- stripped._1.headOption.toRight(NotOfForm("a bound at every index", premise))
          bound <- linarith.prove(guard._2).flatMap(rules.disch(guard._1, _)).flatMap(rules.gen(index, _))
          diverging <- rules.mp(instance, bound)
        } yield Answer.Diverges(diverging)
      case Shape.Exponential(t) => rules.spec(t, facts.exponentialConverges).map(Answer.Converges.apply)
      case Shape.Cosine(x)      => rules.spec(x, facts.cosineConverges).map(Answer.Converges.apply)
      case Shape.Sine(x)        => rules.spec(x, facts.sineConverges).map(Answer.Converges.apply)
      case Shape.Scaled(c, inner) =>
        answerFor(inner).flatMap {
          case Answer.Converges(theorem) =>
            for {
              parts <- Limit.convergenceOf(theorem)
              summand <- summandOf(parts._1)
              scaled <- rules
                .specAll(facts.scaleConverges, List(summand, c, parts._2))
                .flatMap(Limit.normalised)
                .flatMap(rules.mp(_, theorem))
            } yield Answer.Converges(scaled)
          case Answer.Diverges(theorem) =>
            for {
              series <- theorem.conclusion match {
                case App(_, s) => Right(s)
                case other     => Left(NotOfForm("a divergence", other))
              }
              summand <- summandOf(series)
              nonZero <- LogicError
                .lift(Term.eq(c, zero))
                .flatMap(logic.mkNot)
                .flatMap(linarith.prove)
                .left
                .map(_ => NotOfForm("a constant factor LINARITH shows is not zero", c))
              scaled <- rules
                .specAll(facts.scaleDiverges, List(summand, c))
                .flatMap(Limit.normalised)
                .flatMap(rules.mp(_, nonZero))
                .flatMap(rules.mp(_, theorem))
            } yield Answer.Diverges(scaled)
        }
    }

  /**
   * `abs q < 1` on the left or `1 <= abs q` on the right, decided through the sign of `q`.
   *
   * LINARITH reads `abs q` as an atom, so the sign is decided first and `abs` is rewritten away by
   * `ABS_OF_NONNEG` or `ABS_OF_NONPOS`; what is left is a comparison of `q` or `-q` with one, and
   * the answer is carried back to `abs q` by the same equation.
   */
  private def magnitude(q: Term): Either[LogicError, Either[Kernel.Thm, Kernel.Thm]] =
    signOf(q)
      .left
      .map(_ => NotOfForm("a geometric ratio whose sign LINARITH decides", q))
      .flatMap { equation =>
        through(equation, "\\x:real. x < 1") match {
          case Right(below) => Right(Left(below))
          case Left(_) =>
            through(equation, "\\x:real. 1 <= x")
              .map(Right(_))
              .left
              .map(_ => NotOfForm("a geometric ratio whose magnitude LINARITH compares with one", q))
        }
      }

  /** `predicate` applied to `value` and reduced, where `predicate` is a lambda written as text. */
  private def comparison(text: String, value: Term): Either[LogicError, Term] =
    Parser
      .term(theory, notation, text, Type.fun(values, Type.Bool))
      .flatMap(predicate => LogicError.lift(Term.app(predicate, value)))
      .flatMap(Conv.betaNormalise)
      .flatMap(Limit.rightOf)

  /** `abs q = q` or `abs q = -q`, whichever sign of `q` LINARITH decides. */
  private def signOf(q: Term): Either[LogicError, Kernel.Thm] =
    comparison("\\x:real. 0 <= x", q)
      .flatMap(linarith.prove)
      .flatMap(nonNegative => rules.spec(q, facts.ofNonNegative).flatMap(rules.mp(_, nonNegative)))
      .orElse(
        comparison("\\x:real. x <= 0", q)
          .flatMap(linarith.prove)
          .flatMap(nonPositive => rules.spec(q, facts.ofNonPositive).flatMap(rules.mp(_, nonPositive))))

  /**
   * A comparison about `abs q`, proved with `abs q` as an atom and the sign's equation as its
   * hypothesis, rather than proved about `q` and rewritten back: rewriting `1` into `abs 1` would
   * also rewrite the bound, since at `q = 1` the ratio and the bound are the same term.
   */
  private def through(equation: Kernel.Thm, text: String): Either[LogicError, Kernel.Thm] =
    for {
      size <- Limit.destructEquation(equation).map(_._1)
      claim <- comparison(text, size)
      implication <- logic.mkImp(equation.conclusion, claim)
      proved <- linarith.prove(implication)
      result <- rules.mp(proved, equation)
    } yield result

  /** The answer, set against what was asked. */
  private def settle(goal: Term, question: Question, answer: Answer): Either[LogicError, Kernel.Thm] =
    (question, answer) match {
      case (Question.Exists(_), Answer.Converges(theorem)) =>
        for {
          parts <- Limit.convergenceOf(theorem)
          predicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
          packed <- rules.existsIntro(predicate, parts._2, theorem)
          result <- sameAs(goal, packed)
        } yield result

      case (Question.To(_, wanted), Answer.Converges(theorem)) =>
        Limit.convergenceOf(theorem).flatMap { case (_, found) =>
          if (found == wanted) sameAs(goal, theorem)
          else
            LogicError
              .lift(Term.eq(found, wanted))
              .flatMap(valueEquation)
              .flatMap(Limit.rewriteWith(_, theorem))
              .flatMap(sameAs(goal, _))
              .left
              .map(_ => NotEqualTo(wanted, found))
        }

      case (Question.Diverges(_), Answer.Diverges(theorem)) => sameAs(goal, theorem)

      case (_, Answer.Converges(theorem)) => Left(Denied(goal, theorem.conclusion, Name))
      case (_, Answer.Diverges(theorem))  => Left(Denied(goal, theorem.conclusion, Name))
    }

  /**
   * `found = wanted` between two values, by RING and failing that by `Field` with every condition it
   * charges discharged by LINARITH: the value of a geometric series is a reciprocal, `inv (1 - q)`,
   * and a caller writes the number it is, which only a cancellation reaches. A condition LINARITH
   * cannot discharge leaves the two values unidentified, which is what the caller is told.
   */
  private def valueEquation(equation: Term): Either[LogicError, Kernel.Thm] =
    ring.prove(equation).orElse(
      field.prove(equation).flatMap(proved =>
        proved.hypotheses.foldLeft[Either[LogicError, Kernel.Thm]](Right(proved)) { (carried, condition) =>
          carried.flatMap(theorem =>
            linarith.prove(condition).flatMap(met => rules.disch(condition, theorem).flatMap(rules.mp(_, met))))
        }))

  private def sameAs(goal: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    if (theorem.conclusion == goal) Right(theorem)
    else Left(NotOfForm(s"a proof of ${Show.show(notation, goal)}", theorem.conclusion))

  private val zero: Term = Parser.term(theory, notation, "0:real", values).fold(
    error => throw new IllegalStateException(s"the reals do not read zero: ${error.message}"),
    identity)
}

object Convergence {

  /** The procedure's name, as a refusal carrying a decision reports it. */
  val Name: String = "Convergence"

  /** What a goal has to be for this procedure to be asked it. */
  val Expected: String =
    "a convergence or a divergence of a series: ?l. converges (Sum f) l, " +
      "converges (Sum f) v, or diverges (Sum f)"

  /** The summands this procedure reads, as a refusal names them. */
  val Summands: String =
    "a summand this procedure reads: a non-zero constant, Power q i, " +
      "Power t i / real_of_num (NUM_FACT i), the cosine's or the sine's term, " +
      "or a constant times one of those"

  /** The refusal at a rational function of the index, which is not the refusal of an unread summand. */
  val RatioTendsToOne: String =
    "a summand whose ratio of consecutive terms tends to something other than one; this one is " +
      "a rational function of the index, where it tends to one and no ratio test decides anything"

  private val values: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  /** The theorems it answers with, named so that a missing one is a refusal to build. */
  final case class Facts(
    termTest: Kernel.Thm,
    geometricConverges: Kernel.Thm,
    geometricDiverges: Kernel.Thm,
    scaleConverges: Kernel.Thm,
    scaleDiverges: Kernel.Thm,
    exponentialConverges: Kernel.Thm,
    cosineConverges: Kernel.Thm,
    sineConverges: Kernel.Thm,
    ofNonNegative: Kernel.Thm,
    ofNonPositive: Kernel.Thm
  )

  /** The three questions, each about the series it names. */
  enum Question(val series: Term):
    case Exists(about: Term) extends Question(about)
    case To(about: Term, value: Term) extends Question(about)
    case Diverges(about: Term) extends Question(about)

  private enum Answer:
    case Converges(theorem: Kernel.Thm)
    case Diverges(theorem: Kernel.Thm)

  private enum Shape:
    case Constant(value: Term)
    case Geometric(ratio: Term)
    case Exponential(argument: Term)
    case Cosine(argument: Term)
    case Sine(argument: Term)
    case Scaled(factor: Term, inner: Shape)

  /**
   * The question a goal asks, read by the names of the constants and nothing else.
   *
   * Static and over a `Logic` alone, because `Prove.addressOf` asks it before any procedure is
   * built, and it must answer the same thing the procedure will: a goal this reads is one the
   * procedure is asked.
   */
  def goalOf(logic: Logic, goal: Term): Option[Question] = {
    def seriesIn(term: Term): Option[Term] = term match {
      case App(Const(Series.SumName, _), _) => Some(term)
      case _                            => None
    }
    def convergence(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(Limit.Converges, _), sequence), value) => seriesIn(sequence).map(_ -> value)
      case _                                                    => None
    }
    goal match {
      case App(Const(Limit.Diverges, _), sequence) => seriesIn(sequence).map(Question.Diverges.apply)
      case _ =>
        convergence(goal)
          .map { case (series, value) => Question.To(series, value) }
          .orElse(
            logic.destExistsPredicate(goal).flatMap {
              case predicate @ Abs(binder, _) =>
                val value = Conv.freshVariable("l", binder, Term.freeVariables(goal))
                Term
                  .app(predicate, value)
                  .toOption
                  .flatMap(Term.betaReduce)
                  .flatMap(convergence)
                  .collect { case (series, `value`) => Question.Exists(series) }
              case _ => None
            })
    }
  }

  /** Over the standard chain. */
  lazy val standard: Convergence =
    construct(Chain.standard).fold(error => throw new IllegalStateException(error.message), identity)

  /** Over a chain, reading in its widest signature, which is where every constant it names is. */
  def construct(chain: Chain): Either[LogicError, Convergence] =
    for {
      linarith <- Linarith.construct(chain.order)
      field <- Field.construct(chain.arithmetic)
      facts <- for {
        termTest <- chain.limit.fact(Limit.TermTest)
        geometricConverges <- chain.limit.fact(Limit.GeometricConverges)
        geometricDiverges <- chain.limit.fact(Limit.GeometricDiverges)
        scaleConverges <- chain.limit.fact(Limit.ScaleConverges)
        scaleDiverges <- chain.limit.fact(Limit.ScaleDiverges)
        exponentialConverges <- chain.transcendental.fact(Transcendental.ExponentialConverges)
        cosineConverges <- chain.transcendental.fact(Transcendental.CosineConverges)
        sineConverges <- chain.transcendental.fact(Transcendental.SineConverges)
        ofNonNegative <- chain.magnitude.fact(Magnitude.OfNonNegative)
        ofNonPositive <- chain.magnitude.fact(Magnitude.OfNonPositive)
      } yield Facts(
        termTest, geometricConverges, geometricDiverges, scaleConverges, scaleDiverges, exponentialConverges,
        cosineConverges, sineConverges, ofNonNegative, ofNonPositive)
    } yield new Convergence(
      chain.logic, chain.widest.theory, chain.widest.notation, linarith, chain.ring, field, facts)

  /** The summand of `Sum f`, which is `f`. */
  private def summandOf(series: Term): Either[LogicError, Term] = series match {
    case App(_, summand) => Right(summand)
    case other           => Left(NotOfForm("the partial sums of a series", other))
  }
}
