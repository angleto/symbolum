package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * `exp 1` is not a ratio of naturals: Fourier's proof, which `Transcendental` publishes as
 * [[Transcendental.ExponentialOneIrrational]].
 *
 * Not a development: it declares nothing, and the one fact it derives is published under a name
 * `Transcendental` declares, the arrangement `Trigonometric` has for the squared identity.
 *
 * == The argument ==
 *
 * Write `f i` for the series' term `1 / i!` and suppose `exp 1 = p / q` with `0 < q`. Run the
 * argument at `b = q + 1` and call `S` the partial sum `f 0 + ... + f b`. Three facts, and then
 * nothing is left:
 *
 *  - `b! * S` is a natural. By induction on `b`: at zero it is one, and one index along it is
 *    `(n + 1) * k + 1` when it was `k`, because `(n + 1)! * f (n + 1)` is one. No quotient
 *    `b! / i!` is ever formed, which is the usual statement of this step and a fact about
 *    divisibility this argument does not need.
 *  - `b! * exp 1` is a natural, because `q` divides `b!` (`Coding.NUM_FACT_DIVIDES`), so it is
 *    `c * p` where `b! = q * c`.
 *  - `b! * (exp 1 - S)` lies strictly between zero and one. Above zero because the next partial
 *    sum is already `S + f (b + 1)` and the partial sums never pass the limit
 *    (`Limit.SUM_BELOW_LIMIT`). Below one because the tail from `b + 1` on is under a geometric
 *    series of ratio one half (`Transcendental.EXP_TAIL_GEOMETRIC` at `x = 1`), so
 *    `exp 1 - S <= 2 * f (b + 1)`, and `b! * 2 * f (b + 1)` is `2 / (b + 1)`, which is `2 / (q + 2)`.
 *
 * So `c * p` is a natural strictly between the natural `k = b! * S` and `k + 1`, which
 * `Peano.NUM_LT_TOTAL` and the embedding's two order facts refuse.
 *
 * == Why `q + 1` and not `q` ==
 *
 * The textbook runs it at `q` and bounds the tail by a geometric series of ratio `1 / (q + 1)`,
 * which ends at `1 / q`. At `q = 1` that is one, and the argument survives only because the
 * comparison of the tail with the geometric series is strict term by term, which a limit then
 * has to preserve. The ratio this library already has is one half, from
 * an index where `2 <= i`, and at `q` it ends at `2 / (q + 1)`, which is one at `q = 1`. Moving
 * the argument one index along costs nothing, since `q` divides `(q + 1)!` as well as `q!`, and
 * ends at `2 / (q + 2) <= 2 / 3`: the strict inequality comes from a margin rather than from a
 * strict limit comparison, which is the step this library would have had to build.
 *
 * `tools/verify/perturb-exp-one-irrational.sh` takes that margin away and watches the last step
 * refuse, and takes the doubling out of the tail bound and watches the bound refuse.
 *
 * == Stated over a variable series first ==
 *
 * The derivation is about an `f` and an `e` given three facts: the partial sums of `f` converge to
 * `e`, `i! * f i = 1`, and the tail bound in the shape `EXP_TAIL_GEOMETRIC` has at one. Only the
 * end specialises it at the exponential's own series and `exp 1`. That keeps every intermediate
 * term small, so `Linarith` meets atoms such as `f (SUC (SUC q))` rather than the quotient they
 * stand for, which it refuses by name; and it makes the three facts the argument uses the whole of
 * what it knows about the series, which a reader can check against the statement above.
 *
 * == How each step is decided ==
 *
 * `settle` is the one place anything is decided, and it is `Linarith` on the implication from the
 * facts handed to it to the goal. Every product it has to form is one of two of those facts, which
 * is why several steps below are split in two where one would read more naturally: a hypothesis
 * multiplied by an atom that is not itself a hypothesis is outside what it multiplies. Where the
 * step is an equation between products, it is a rewrite with the facts and then `Ring`.
 *
 * == What it costs ==
 *
 * No axiom and no constant. What it rests on, measured when it landed and asserted in
 * `TranscendentalSpec`: of the chain's three axioms it reaches choice, through `exp` being a limit
 * named by `select`, and infinity, through `num`, and not eta; and all sixteen laws of the reals,
 * `COMPLETENESS` among them through the series' convergence.
 */
private[theories] object Fourier {

  private val values: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  /** What the derivation takes from the developments under it. */
  final case class Pieces(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    limit: Limit,
    series: Series,
    peano: Peano,
    coding: Coding,
    induct: Induct,
    exponentialConverges: Kernel.Thm,
    tailIsGeometric: Kernel.Thm
  )

  // The five names every text below is written over, each carrying its type so that no text is
  // ambiguous: `<` and `+` are `num`'s as well as the reals', and a free name nothing constrains
  // is refused rather than guessed.
  private val F = "(f:num->real)"
  private val E = "(e:real)"
  private val P = "(p:num)"
  private val Q = "(q:num)"

  /** The denominator the argument is run at, one past the ratio's own. */
  private val B = s"SUC $Q"

  /** The first index of the tail, which is one past the last term of the partial sum. */
  private val N0 = s"SUC ($B)"

  private val Cancels = s"!i:num. real_of_num (NUM_FACT i) * $F i = 1"
  private val Tail =
    s"!m:num. 2 * abs 1 <= real_of_num m ==> (!j:num. abs ($F (m + j)) <= Power (1 / 2) j * abs ($F m))"
  private val Converges = s"converges (Sum $F) $E"
  private val Claim = s"$E = real_of_num $P / real_of_num $Q"
  private val Positive = s"0 < $Q"

  private final case class Steps(held: Pieces) {
    import held.*
    val rules: Rules = logic.rules

    def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)
    def real(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, values)
    def natural(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, numbers)
    def assume(text: String): Either[LogicError, Kernel.Thm] =
      proposition(text).flatMap(statement => LogicError.lift(Kernel.assume(statement)))

    def terms(texts: Seq[String], typed: String => Either[LogicError, Term]): Either[LogicError, List[Term]] =
      texts.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, text) =>
        for { done <- acc; term <- typed(text) } yield done :+ term
      }

    /** A theorem specialised at terms of type `num`. */
    def atNumbers(theorem: Either[LogicError, Kernel.Thm], arguments: String*): Either[LogicError, Kernel.Thm] =
      for { proved <- theorem; args <- terms(arguments, natural); result <- rules.specAll(proved, args) } yield result

    /** A theorem specialised at terms given with their types, beta-reduced afterwards. */
    def atTerms(theorem: Either[LogicError, Kernel.Thm], arguments: Either[LogicError, Term]*): Either[LogicError, Kernel.Thm] =
      for {
        proved <- theorem
        args <- arguments.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, next) =>
          for { done <- acc; term <- next } yield done :+ term
        }
        specialised <- rules.specAll(proved, args)
        result <- opened(specialised)
      } yield result

    def mp(implication: Either[LogicError, Kernel.Thm], premises: Either[LogicError, Kernel.Thm]*): Either[LogicError, Kernel.Thm] =
      premises.foldLeft(implication) { (acc, premise) =>
        for { current <- acc; proved <- premise; next <- rules.mp(current, proved) } yield next
      }

    def conj(left: Either[LogicError, Kernel.Thm], right: Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for { l <- left; r <- right; both <- rules.conjIntro(l, r) } yield both

    def opened(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv.betaNormalise(theorem.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    /**
     * The goal, from the facts, by `Linarith`: the implication from their conclusions to the goal
     * is proved once and detached against them. Nothing is decided anywhere else.
     */
    def settle(goal: Term, facts: Either[LogicError, Kernel.Thm]*): Either[LogicError, Kernel.Thm] =
      for {
        proved <- facts.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (acc, next) =>
          for { done <- acc; fact <- next } yield done :+ fact
        }
        implication <- proved.foldRight[Either[LogicError, Term]](Right(goal)) { (fact, acc) =>
          acc.flatMap(logic.mkImp(fact.conclusion, _))
        }
        general <- linarith.prove(implication)
        result <- proved.foldLeft[Either[LogicError, Kernel.Thm]](Right(general)) { (acc, fact) =>
          acc.flatMap(rules.mp(_, fact))
        }
      } yield result

    def settle(goal: String, facts: Either[LogicError, Kernel.Thm]*): Either[LogicError, Kernel.Thm] =
      proposition(goal).flatMap(settle(_, facts*))

    /** The goal rewritten with the equations given, and what is left closed by `close`. */
    def byRewriting(goal: Term, equations: Either[LogicError, Kernel.Thm]*)(
      close: Term => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        proved <- equations.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, next) =>
          for { done <- acc; fact <- next } yield done :+ fact
        }
        rewrites <- Rewrite.Rule.all(logic, proved)
        result <- Induct.afterRewriting(rewrites, goal)(close)
      } yield result

    def rewritten(theorem: Either[LogicError, Kernel.Thm], equations: Either[LogicError, Kernel.Thm]*): Either[LogicError, Kernel.Thm] =
      for {
        target <- theorem
        proved <- equations.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, next) =>
          for { done <- acc; fact <- next } yield done :+ fact
        }
        rewrites <- Rewrite.Rule.all(logic, proved)
        result <- Rewrite.inTheorem(rewrites, target)
      } yield result

    def generalised(variable: String, typed: Type, theorem: Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      theorem.flatMap(rules.gen(Term.variable(variable, typed), _))

    def discharged(text: String, theorem: Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for { statement <- proposition(text); proved <- theorem; result <- rules.disch(statement, proved) } yield result

    /** The body of an existential, at a witness, from a proof of that instance. */
    def introduced(existential: Term, witness: Either[LogicError, Term], body: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        predicate <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
        chosen <- witness
        result <- rules.existsIntro(predicate, chosen, body)
      } yield result

    /** The instance of an existential's predicate at a term, beta-reduced. */
    def instance(existential: Term, witness: Term): Either[LogicError, Term] =
      for {
        predicate <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
        applied <- LogicError.lift(Term.app(predicate, witness))
        reduced <- Conv.betaNormalise(applied)
        right <- Term.destEq(reduced.conclusion).map(_._2).toRight(NotOfForm("an equation", reduced.conclusion))
      } yield right
  }

  def prove(pieces: Pieces): Either[LogicError, Kernel.Thm] = {
    val steps = Steps(pieces)
    import steps.*
    import pieces.*

    val reals = limit.magnitude.order.ring.reals
    val magnitude = limit.magnitude

    val converging = assume(Converges)
    val unit = assume(Cancels)
    val tail = assume(Tail)
    val positive = assume(Positive)
    val claim = assume(Claim)

    val zeroEmbeds = peano.fact(Peano.EmbedsZero)
    val successorEmbeds = peano.fact(Peano.EmbedsSuccessor)
    val productEmbeds = peano.fact(Peano.EmbedsProduct)
    val factorialSuccessor = coding.fact(Coding.FactorialAtSuccessor)

    // Every term of the series is positive: its factorial is at least one and the two multiply to one.
    val termPositive: Either[LogicError, Kernel.Thm] = {
      val index = "i:num"
      val atLeastOne = mp(atNumbers(peano.fact(Peano.EmbedsStrictOrder), "0", s"NUM_FACT $index"),
        atNumbers(coding.fact(Coding.FactorialPositive), index))
      generalised("i", numbers,
        settle(s"0 < $F $index", zeroEmbeds, atLeastOne, atNumbers(unit, index)))
    }
    val termNonNegative: Either[LogicError, Kernel.Thm] =
      generalised("i", numbers, settle(s"0 <= $F i", atNumbers(termPositive, "i:num")))

    val function = Parser.term(theory, notation, F, Type.fun(numbers, values))

    // Below: the partial sum one past the argument's, which is the argument's plus a positive term.
    val sumsBelow = mp(atTerms(limit.belowLimit, function, real(E)), termNonNegative, converging)
    val lower = settle(s"Sum $F ($N0) + $F ($N0) <= $E",
      atNumbers(sumsBelow, s"SUC ($N0)"),
      atTerms(series.fact(Series.AtSuccessor), function, natural(N0)))

    // Above: the tail from `N0` on is under twice its first term.
    val tailApplies = {
      val one = settle("(0:real) <= 1")
      val absOne = mp(atTerms(magnitude.fact(Magnitude.OfNonNegative), real("1:real")), one)
      settle(s"2 * abs 1 <= real_of_num ($N0)",
        absOne,
        atNumbers(successorEmbeds, B),
        atNumbers(successorEmbeds, Q),
        atNumbers(peano.fact(Peano.EmbedsNonNegative), Q))
    }
    val pointwise: Either[LogicError, Kernel.Thm] = {
      val j = "j:num"
      val first = mp(atTerms(magnitude.fact(Magnitude.OfNonNegative), real(s"$F ($N0)")),
        atNumbers(termNonNegative, N0))
      val bound = rewritten(atNumbers(mp(atNumbers(tail, N0), tailApplies), j), first)
      val above = atTerms(magnitude.fact(Magnitude.AbsAbove), real(s"$F ($N0 + $j)"))
      generalised("j", numbers,
        settle(s"$F ($N0 + $j) <= Power (1 / 2) $j * $F ($N0)", above, bound))
    }
    val shifted = Parser.term(theory, notation, s"\\j:num. $F ($N0 + j)", Type.fun(numbers, values))
    val halves = Parser.term(theory, notation, "\\j:num. Power ((1:real) / 2) j", Type.fun(numbers, values))
    val scaledHalves = Parser.term(theory, notation, s"\\j:num. Power ((1:real) / 2) j * $F ($N0)", Type.fun(numbers, values))

    val stretch: Either[LogicError, Kernel.Thm] = {
      val n = "n:num"
      val monotone = atNumbers(mp(atTerms(series.fact(Series.Monotone), shifted, scaledHalves), pointwise), n)
      val reindexed = atTerms(series.fact(Series.Reindex), function, natural(N0), natural(n))
      val scaled = atTerms(series.fact(Series.ScaledRight), real(s"$F ($N0)"), halves, natural(n))
      val geometric = atTerms(series.fact(Series.Geometric), real("(1:real) / 2"), natural(n))
      val powerNonNegative = atNumbers(mp(atTerms(limit.fact(Limit.PowerNonNegative), real("(1:real) / 2")),
        settle("(0:real) <= 1 / 2")), n)
      val sumOfHalves = settle(s"Sum (\\j:num. Power ((1:real) / 2) j) $n <= 2", geometric, powerNonNegative)
      generalised("n", numbers,
        settle(s"Sum $F ($N0 + $n) <= Sum $F ($N0) + 2 * $F ($N0)",
          monotone, reindexed, scaled, sumOfHalves, atNumbers(termNonNegative, N0)))
    }
    val everySum: Either[LogicError, Kernel.Thm] = {
      val m = "m:num"
      val later = rewritten(atNumbers(peano.fact(Peano.AtMostSum), m, N0), atNumbers(peano.fact(Peano.AddCommutative), m, N0))
      val grows = mp(atNumbers(mp(atTerms(limit.grows, function), termNonNegative), m, s"$N0 + $m"), later)
      val bounded = settle(s"Sum $F $m <= Sum $F ($N0) + 2 * $F ($N0)", grows, atNumbers(stretch, m))
      generalised("m", numbers, discharged(s"0 <= $m", bounded))
    }
    val upper = mp(atTerms(limit.belowBound, Parser.term(theory, notation, s"Sum $F", Type.fun(numbers, values)),
      real(E), real(s"Sum $F ($N0) + 2 * $F ($N0)"), natural("0")), converging, everySum)

    // The partial sum times the factorial of its last index is a natural, by induction on that index.
    val integral: Either[LogicError, Kernel.Thm] = {
      val statement = s"!n:num. ?k:num. real_of_num (NUM_FACT n) * Sum $F (SUC n) = real_of_num k"
      val sumAtSuccessor = series.fact(Series.AtSuccessor)
      proposition(statement).flatMap { stated =>
        induct.proveBy(
          stated,
          base =>
            for {
              one <- natural("SUC 0")
              body <- instance(base, one)
              proved <- byRewriting(body,
                coding.fact(Coding.FactorialAtZero), atTerms(sumAtSuccessor, function, natural("0")),
                series.fact(Series.AtZero), successorEmbeds, zeroEmbeds) { goal =>
                  settle(goal, rewritten(atNumbers(unit, "0"), coding.fact(Coding.FactorialAtZero), successorEmbeds, zeroEmbeds))
                }
              result <- introduced(base, Right(one), proved)
            } yield result,
          step => {
            val n = step.variable
            val k = Term.variable("k", numbers)
            for {
              hypothesisBody <- instance(step.hypothesis.conclusion, k)
              assumed <- LogicError.lift(Kernel.assume(hypothesisBody))
              witness <- Parser.term(theory, notation, s"SUC (SUC ${n.name} * k)", numbers)
              body <- instance(step.goal, witness)
              back <- Conv.sym(assumed)
              atSuccessor <- natural(s"SUC ${n.name}")
              proved <- byRewriting(body,
                factorialSuccessor, atTerms(sumAtSuccessor, function, Right(atSuccessor)),
                productEmbeds, successorEmbeds, Right(back)) { goal =>
                  settle(goal, rewritten(atTerms(unit, Right(atSuccessor)), factorialSuccessor, productEmbeds, successorEmbeds))
                }
              introducedHere <- introduced(step.goal, Right(witness), proved)
              result <- rules.existsElim(step.hypothesis, k, introducedHere)
            } yield result
          }
        )
      }
    }

    // The ratio's denominator divides the factorial the argument is run at.
    val divides = mp(atNumbers(coding.fact(Coding.FactorialDivides), Q, B),
      conj(positive, atNumbers(peano.fact(Peano.AtMostSuccessor), Q)))
    val multiple = mp(atNumbers(coding.modular.fact(Modular.DividesElim), Q, s"NUM_FACT ($B)"), divides)

    // The claim, cleared of its division.
    val division = reals.definition(Real.Division)
    val asProduct = rewritten(claim, division)
    val qPositive = settle(s"0 < real_of_num $Q", zeroEmbeds, mp(atNumbers(peano.fact(Peano.EmbedsStrictOrder), "0", Q), positive))
    val qNonZero = settle(s"~(real_of_num $Q = 0)", qPositive)
    val reciprocal = mp(atTerms(reals.axiom("MUL_INVERSE"), real(s"real_of_num $Q")), qNonZero)
    val cleared = settle(s"$E * real_of_num $Q = real_of_num $P",
      asProduct, reciprocal, qPositive, atNumbers(peano.fact(Peano.EmbedsNonNegative), P))

    val c = Term.variable("c", numbers)
    val k = Term.variable("k", numbers)
    val factorial = s"real_of_num (NUM_FACT ($B))"
    val sum = s"Sum $F ($N0)"
    val term = s"$F ($N0)"
    val scaled = s"real_of_num (c * $P)"

    val absurd: Either[LogicError, Kernel.Thm] =
      for {
        multipleBody <- multiple.flatMap(m => instance(m.conclusion, c))
        isMultiple <- LogicError.lift(Kernel.assume(multipleBody))
        integerExists <- atNumbers(integral, B)
        integerBody <- instance(integerExists.conclusion, k)
        isInteger <- LogicError.lift(Kernel.assume(integerBody))

        // The factorial times the claimed value is the natural `c * p`.
        timesValue <- proposition(s"$factorial * $E = $scaled").flatMap { goal =>
          byRewriting(goal, Right(isMultiple), productEmbeds, cleared.flatMap(Conv.sym)) { rest =>
            series.ring.prove(rest)
          }
        }

        factorialPositive <- settle(s"0 < $factorial", zeroEmbeds,
          mp(atNumbers(peano.fact(Peano.EmbedsStrictOrder), "0", s"NUM_FACT ($B)"),
            atNumbers(coding.fact(Coding.FactorialPositive), B)))
        termPositiveHere <- atNumbers(termPositive, N0)
        product <- settle(s"0 < $factorial * $term", Right(factorialPositive), Right(termPositiveHere))
        atLeastThree <- settle(s"3 <= real_of_num ($N0)",
          atNumbers(successorEmbeds, B), atNumbers(successorEmbeds, Q), zeroEmbeds,
          mp(atNumbers(peano.fact(Peano.EmbedsStrictOrder), "0", Q), positive))
        unitAtN0 <- rewritten(atNumbers(unit, N0), atNumbers(factorialSuccessor, B), productEmbeds)
        small <- settle(s"3 * ($factorial * $term) <= 1", Right(unitAtN0), Right(atLeastThree), Right(product))
        above <- settle(s"$factorial * $sum < $factorial * $E", Right(factorialPositive), lower, Right(product))
        below <- settle(s"$factorial * $E < $factorial * $sum + 1", Right(factorialPositive), upper, Right(small))
        embedded <- atNumbers(productEmbeds, "c:num", P)
        pastInteger <- settle(s"real_of_num k < $scaled", Right(isInteger), Right(timesValue), Right(above))
        beforeNext <- settle(s"$scaled < real_of_num k + 1", Right(isInteger), Right(timesValue), Right(below))

        // No natural lies strictly between `k` and `k + 1`.
        trichotomy <- atNumbers(peano.fact(Peano.Trichotomy), "k:num", s"c * $P")
        lessCase <- for {
          assumed <- assume(s"k < c * $P")
          step <- mp(atNumbers(peano.fact(Peano.EmbedsStrictOrder), "k:num", s"c * $P"), Right(assumed))
          result <- settle("F", Right(step), Right(beforeNext))
        } yield result
        equalCase <- for {
          assumed <- assume(s"k = c * $P")
          embedding <- Parser.term(theory, notation, "real_of_num", Type.fun(numbers, values))
          congruent <- Conv.apTerm(embedding, assumed)
          result <- settle("F", Right(congruent), Right(pastInteger))
        } yield result
        greaterCase <- for {
          assumed <- assume(s"c * $P < k")
          step <- mp(atNumbers(peano.fact(Peano.EmbedsStrictOrder), s"c * $P", "k:num"), Right(assumed))
          result <- settle("F", Right(step), Right(pastInteger))
        } yield result
        rest <- assume(s"k = c * $P \\/ c * $P < k").flatMap(rules.disjElim(_, equalCase, greaterCase))
        split <- rules.disjElim(trichotomy, lessCase, rest)
        withoutInteger <- rules.existsElim(integerExists, k, split)
        withoutMultiple <- multiple.flatMap(rules.existsElim(_, c, withoutInteger))
      } yield withoutMultiple

    val general: Either[LogicError, Kernel.Thm] =
      for {
        refuted <- absurd
        claimed <- proposition(Claim)
        negated <- rules.notIntro(claimed, refuted)
        inRatio <- generalised("p", numbers, generalised("q", numbers, discharged(Positive, Right(negated))))
        closed <- generalised("f", Type.fun(numbers, values), generalised("e", values,
          discharged(Converges, discharged(Cancels, discharged(Tail, Right(inRatio))))))
      } yield closed

    // The general argument at the exponential's own series.
    val seriesTerms = Parser.term(theory, notation, "\\i:num. Power (1:real) i / real_of_num (NUM_FACT i)", Type.fun(numbers, values))
    val unitHere: Either[LogicError, Kernel.Thm] = {
      val index = "i:num"
      val factorialText = s"real_of_num (NUM_FACT $index)"
      val atLeastOne = mp(atNumbers(peano.fact(Peano.EmbedsStrictOrder), "0", s"NUM_FACT $index"),
        atNumbers(coding.fact(Coding.FactorialPositive), index))
      val nonZero = settle(s"~($factorialText = 0)", zeroEmbeds, atLeastOne)
      val inverse = mp(atTerms(reals.axiom("MUL_INVERSE"), real(factorialText)), nonZero)
      generalised("i", numbers,
        proposition(s"$factorialText * (Power (1:real) $index / $factorialText) = 1").flatMap { goal =>
          byRewriting(goal, division, series.fact(Series.PowerOfOne)) { rest => settle(rest, inverse) }
        })
    }
    for {
      closed <- general
      atSeries <- atTerms(Right(closed), seriesTerms, real("exp 1"))
      convergesHere <- atTerms(Right(exponentialConverges), real("1:real"))
      one <- real("1:real")
      tailHere <- rules.specPrefix(tailIsGeometric, List(one))
      unitProved <- unitHere
      result <- rules.mp(atSeries, convergesHere).flatMap(rules.mp(_, unitProved)).flatMap(rules.mp(_, tailHere))
    } yield result
  }
}
