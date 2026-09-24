package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The sine and the cosine squared and added, which is one: `sin x * sin x + cos x * cos x = 1`.
 *
 * Proved here from the two series and nothing about the circle, which is the only route this
 * repository has: `sin` and `cos` are their own power series and meet `exp` only through a square
 * root of minus one, which no type here provides. So what joins them is the Cauchy product, taken
 * once at the cosine's series against itself and once at the sine's against itself, and an
 * identity between the two products' terms that is the binomial theorem at `(x, -x)` read by
 * parity.
 *
 * == The cancellation, which is the whole of the arithmetic ==
 *
 * Write `e j` for the exponential's term `x^j / j!` and `P k` for `(0 - 1)^k`. The cosine's `k`th
 * term is `P k * e (2k)` and the sine's is `P k * e (2k + 1)`. `Transcendental.EXP_CONVOLUTION`
 * at `x` and `0 - x`, at an even length `N = 2(m + 1)`, says the convolution
 * `g j = e j * h (N - j)`, with `h` the term at `0 - x`, sums to `(x - x)^N / N! = 0`. Split by
 * parity with `Series.SUM_EVEN_ODD`, the even places are `P (m + 1)` times the cosine's product
 * term at `m + 1`, because `h (2d) = e (2d)` (`Series.POWER_NEG_DOUBLE`) and the two signs of a
 * cosine pair multiply to `P (m + 1)`; the odd places are `P (m + 1)` times the sine's product
 * term at `m`, because `h (2d + 1) = -e (2d + 1)` supplies the one sign the sine pair lacks. So the
 * cosine's product term at `m + 1` and the sine's at `m` add to zero, and the cosine's at zero is
 * one.
 *
 * **Nothing in that is divided and no index is subtracted without a bound in front of it.** Every
 * `NUM_SUB` met here is `NUM_SUB K u` with `u` below `SUC K`, handed over by
 * `Series.SUM_CONGRUENCE_BELOW`, so `Peano.NUM_SUB_ADD` turns it into an addition and
 * `Peano.NUM_ADD_SUB` takes the addition back apart at the place the parity needs.
 *
 * == The limits, which are bookkeeping ==
 *
 * The two series converge absolutely because their magnitudes are under the exponential's at the
 * even and the odd places, and those two together are the exponential's own partial sums at an
 * even length, which `Transcendental.EXP_ABSOLUTE` bounds. `Limit.SUM_CAUCHY_PRODUCT` then gives
 * the two products, and the cancellation says the cosine's partial sums **one index along** plus
 * the sine's are one at every index. `Limit.CONVERGES_SHIFT` is what makes "one index along" a
 * statement about a limit.
 */
private[theories] object Trigonometric {

  private val values: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  /** The exponential's term at an index written as text, which both series are built from. */
  private def exponentialTerm(index: String): String =
    "(Power (x:real) (" + index + ") / real_of_num (NUM_FACT (" + index + ")))"

  /** The cosine's term at `k`, in the additive spelling of the even index. */
  def cosineTerm(k: String): String =
    "Power (0 - 1) (" + k + ") * " + exponentialTerm("NUM_ADD (" + k + ") (" + k + ")")

  /** The sine's term at `k`, the odd index being the successor of the even one. */
  def sineTerm(k: String): String =
    "Power (0 - 1) (" + k + ") * " + exponentialTerm("SUC (NUM_ADD (" + k + ") (" + k + "))")

  private val CosineTermsText: String = "\\k:num. " + cosineTerm("k")
  private val SineTermsText: String = "\\k:num. " + sineTerm("k")

  /** What the derivation takes from the developments under it. */
  final case class Pieces(
    logic: Logic,
    linarith: Linarith,
    semiring: Semiring,
    theory: Theory,
    notation: Notation,
    limit: Limit,
    series: Series,
    peano: Peano,
    coding: Coding,
    sineDefinition: Kernel.Thm,
    cosineDefinition: Kernel.Thm,
    exponentialAbsolute: Kernel.Thm,
    exponentialConvolution: Kernel.Thm
  )

  def prove(pieces: Pieces): Either[LogicError, Map[String, Kernel.Thm]] =
    for {
      cosineAbsolute <- absolutelyConvergent(pieces, cosineTerm, odd = false)
      sineAbsolute <- absolutelyConvergent(pieces, sineTerm, odd = true)
      squared <- pythagoras(pieces, cosineAbsolute, sineAbsolute)
    } yield Map(
      Transcendental.CosineAbsolute -> cosineAbsolute,
      Transcendental.SineAbsolute -> sineAbsolute,
      Transcendental.Pythagoras -> squared
    )

  /* ======================================================================== small conversions */

  private def opened(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv
      .betaNormalise(theorem.conclusion)
      .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

  private def normal(term: Term): Either[LogicError, Term] =
    Conv.betaNormalise(term).flatMap(rightOf)

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))

  private def sidesOf(term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(_, left), right) => Right((left, right))
    case other                    => Left(NotOfForm("two arguments of one operator", other))
  }

  private def operatorOf(term: Term): Either[LogicError, Term] = term match {
    case App(App(operator, _), _) => Right(operator)
    case other                    => Left(NotOfForm("a binary application", other))
  }

  private def applied(function: Term, argument: Term): Either[LogicError, Term] =
    LogicError.lift(Term.app(function, argument)).flatMap(normal)

  /** `|- left = right` by rewriting each side with its own ground equations and `Ring` between. */
  private def byRewritingThenRing(
    pieces: Pieces,
    left: Term,
    right: Term,
    leftEquations: Vector[Kernel.Thm],
    rightEquations: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      leftRules <- Rewrite.Rule.all(pieces.logic, leftEquations)
      rightRules <- Rewrite.Rule.all(pieces.logic, rightEquations)
      leftMoved <- Rewrite.rewrite(leftRules, left)
      rightMoved <- Rewrite.rewrite(rightRules, right)
      leftNew <- rightOf(leftMoved)
      rightNew <- rightOf(rightMoved)
      middle <- LogicError.lift(Term.eq(leftNew, rightNew)).flatMap(pieces.series.ring.prove)
      result <- Conv
        .trans(leftMoved, middle)
        .flatMap(theorem => Conv.sym(rightMoved).flatMap(Conv.trans(theorem, _)))
    } yield result

  /* ============================================================ absolute convergence of each */

  /**
   * `Transcendental.COS_ABSOLUTE` or `SIN_ABSOLUTE`, one derivation read at two parities.
   *
   * Each term's magnitude is at most the exponential's at its index, since `abs ((0 - 1)^k)` is at
   * most `1^k`. The partial sums of those are the exponential's magnitudes at the even or the odd
   * places, which with the other parity make the exponential's partial sum at an even length
   * (`Series.SUM_EVEN_ODD`), and that is under the limit `EXP_ABSOLUTE` names. So the partial sums
   * increase and are bounded, and `Limit.MONOTONE_CONVERGES` closes it, which is the route
   * `EXP_ABSOLUTE` itself takes.
   */
  private def absolutelyConvergent(
    pieces: Pieces,
    term: String => String,
    odd: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val rules = pieces.logic.rules
    val theory = pieces.theory
    val notation = pieces.notation
    val linarith = pieces.linarith
    val magnitude = pieces.limit.magnitude
    val x = Term.variable("x", values)
    val k = Term.variable("k", numbers)
    val n = Term.variable("n", numbers)
    val i = Term.variable("i", numbers)
    val q = Term.variable("Q", values)
    val sequence = Type.fun(numbers, values)
    val magnitudesText = "\\k:num. abs (" + term("k") + ")"
    val indexText = if (odd) "SUC (NUM_ADD k k)" else "NUM_ADD k k"

    for {
      magnitudes <- Parser.term(theory, notation, magnitudesText, sequence)
      termAtK <- Parser.term(theory, notation, term("k:num"), values)
      signAndTerm <- sidesOf(termAtK)
      (sign, exponential) = signAndTerm
      absolute <- Parser.term(
        theory, notation, "\\i:num. abs " + exponentialTerm("i"), sequence)
      atThisParity <- Parser.term(
        theory, notation, "\\k:num. abs " + exponentialTerm(indexText), sequence)
      minusOne <- Parser.term(theory, notation, "(0:real) - 1", values)
      one <- Parser.term(theory, notation, "1:real", values)

      absNonNegative <- magnitude.fact(Magnitude.AbsNonNegative)

      /* ------------------------------------ one term under the exponential's term at its index */

      split <- magnitude
        .fact(Magnitude.Multiplicative)
        .flatMap(rules.specAll(_, List(sign, exponential)))
      splitSides <- Term.destEq(split.conclusion).toRight(NotOfForm("an equation", split.conclusion))
      minusOneMagnitude <- magnitude
        .fact(Magnitude.OfNonPositive)
        .flatMap(rules.spec(minusOne, _))
        .flatMap(theorem => linarith.prove("(0:real) - 1 <= 0").flatMap(rules.mp(theorem, _)))
      atMostOne <- leftOf(minusOneMagnitude).flatMap(value =>
        linarith
          .prove("!a:real. a = -((0:real) - 1) ==> a <= 1")
          .flatMap(rules.spec(value, _))
          .flatMap(rules.mp(_, minusOneMagnitude)))
      signBounded <- pieces.limit
        .fact(Limit.PowerOfAMagnitude)
        .flatMap(rules.specAll(_, List(minusOne, one, k)))
        .flatMap(rules.mp(_, atMostOne))
      powerOfOne <- pieces.series.fact(Series.PowerOfOne).flatMap(rules.spec(k, _))
      signUnderOne <- onRight(powerOfOne, signBounded)
      signMagnitude <- sidesOf(signUnderOne.conclusion).map(_._1)
      termMagnitude <- rules.spec(exponential, absNonNegative)
      termMagnitudeTerm <- sidesOf(termMagnitude.conclusion).map(_._2)
      scaled <- magnitude.order
        .fact(Order.MultiplyLe)
        .flatMap(rules.specAll(_, List(termMagnitudeTerm, signMagnitude, one)))
        .flatMap(rules.mp(_, termMagnitude))
        .flatMap(rules.mp(_, signUnderOne))
      pointwise <- linarith
        .prove("!a:real. !b:real. !c:real. a = b ==> b <= 1 * c ==> a <= c")
        .flatMap(rules.specAll(_, List(splitSides._1, splitSides._2, termMagnitudeTerm)))
        .flatMap(rules.mp(_, split))
        .flatMap(rules.mp(_, scaled))
        .flatMap(rules.gen(k, _))

      /* ------------------------------------------------ the partial sums, under the exponential's */

      dominated <- pieces.series
        .fact(Series.Monotone)
        .flatMap(rules.specAll(_, List(magnitudes, atThisParity)))
        .flatMap(opened)
        .flatMap(rules.mp(_, pointwise))
        .flatMap(rules.spec(n, _))

      exponentialAtX <- rules.spec(x, pieces.exponentialAbsolute)
      bodyAtQ <- pieces.logic
        .destExistsPredicate(exponentialAtX.conclusion)
        .toRight(NotOfForm("an existential", exponentialAtX.conclusion))
        .flatMap(predicate => applied(predicate, q))
      assumedQ <- LogicError.lift(Kernel.assume(bodyAtQ))

      exponentialAtI <- Parser.term(theory, notation, exponentialTerm("i:num"), values)
      everyTermNonNegative <- rules.spec(exponentialAtI, absNonNegative).flatMap(rules.gen(i, _))
      belowQ <- pieces.limit
        .fact(Limit.BelowLimit)
        .flatMap(rules.specAll(_, List(absolute, q)))
        .flatMap(opened)
        .flatMap(rules.mp(_, everyTermNonNegative))
        .flatMap(rules.mp(_, assumedQ))
      doubled <- Parser.term(theory, notation, "NUM_ADD (n:num) (n:num)", numbers)
      evenLength <- rules.spec(doubled, belowQ)

      halves <- pieces.series
        .fact(Series.EvenOdd)
        .flatMap(rules.specAll(_, List(absolute, n)))
        .flatMap(opened)
      halvesSides <- rightOf(halves).flatMap(sidesOf)
      (evenSum, oddSum) = halvesSides
      other = if (odd) evenSum else oddSum
      otherTerms <- other match {
        case App(App(_, function), _) => Right(function)
        case unexpected               => Left(NotOfForm("a partial sum", unexpected))
      }
      otherIndex = if (odd) "NUM_ADD i i" else "SUC (NUM_ADD i i)"
      otherTermAtI <- Parser.term(theory, notation, exponentialTerm(otherIndex), values)
      otherPointwise <- rules.spec(otherTermAtI, absNonNegative).flatMap(rules.gen(i, _))
      otherNonNegative <- pieces.series
        .fact(Series.NonNegative)
        .flatMap(rules.spec(otherTerms, _))
        .flatMap(opened)
        .flatMap(rules.mp(_, otherPointwise))
        .flatMap(rules.spec(n, _))

      thisSum <- sidesOf(dominated.conclusion)
      length <- sidesOf(evenLength.conclusion).map(_._1)
      // The even-odd split has the even sum first, so which summand is this parity's decides the
      // order the linear step is stated in.
      order = if (odd) "d = c + b" else "d = b + c"
      bound <- linarith
        .prove(
          "!a:real. !b:real. !c:real. !d:real. !q:real. " +
            "a <= b ==> 0 <= c ==> " + order + " ==> d <= q ==> a <= q")
        .flatMap(rules.specAll(_, List(thisSum._1, thisSum._2, other, length, q)))
        .flatMap(rules.mp(_, dominated))
        .flatMap(rules.mp(_, otherNonNegative))
        .flatMap(rules.mp(_, halves))
        .flatMap(rules.mp(_, evenLength))
        .flatMap(rules.gen(n, _))

      /* --------------------------------------------------------- increasing, bounded, convergent */

      recurrence <- pieces.series
        .fact(Series.AtSuccessor)
        .flatMap(rules.specAll(_, List(magnitudes, n)))
        .flatMap(opened)
      recurrenceSides <- Term
        .destEq(recurrence.conclusion)
        .toRight(NotOfForm("an equation", recurrence.conclusion))
      summands <- sidesOf(recurrenceSides._2)
      termNonNegative <- summands._2 match {
        case App(_, inner) => rules.spec(inner, absNonNegative)
        case unexpected    => Left(NotOfForm("a magnitude", unexpected))
      }
      increasing <- linarith
        .prove("!p:real. !q:real. !t:real. q = p + t ==> 0 <= t ==> p <= q")
        .flatMap(rules.specAll(_, List(summands._1, recurrenceSides._1, summands._2)))
        .flatMap(rules.mp(_, recurrence))
        .flatMap(rules.mp(_, termNonNegative))
        .flatMap(rules.gen(n, _))

      partial <- Parser.term(theory, notation, "Sum (" + magnitudesText + ")", sequence)
      boundClaim <- Parser.proposition(
        theory, notation, "?b:real. !n:num. Sum (" + magnitudesText + ") n <= b")
      boundPredicate <- pieces.logic
        .destExistsPredicate(boundClaim)
        .toRight(NotOfForm("an existential quantification", boundClaim))
      bounded <- rules.existsIntro(boundPredicate, q, bound)
      converging <- pieces.limit
        .fact(Limit.MonotoneConverges)
        .flatMap(rules.spec(partial, _))
        .flatMap(opened)
        .flatMap(rules.mp(_, increasing))
        .flatMap(rules.mp(_, bounded))
      closed <- rules.existsElim(exponentialAtX, q, converging)
      result <- rules.gen(x, closed)
    } yield result
  }

  private def onRight(equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    theorem.conclusion match {
      case App(App(relation, left), _) =>
        for {
          context <- LogicError.lift(Term.app(relation, left))
          congruence <- Conv.apTerm(context, equation)
          result <- LogicError.lift(Kernel.eqMp(congruence, theorem))
        } yield result
      case other => Left(NotOfForm("a comparison", other))
    }

  /* ======================================================================== the cancellation */

  /** The binary operator of a sample term, read off it rather than named. */
  private def operatorIn(pieces: Pieces, sample: String, ty: Type): Either[LogicError, Term] =
    Parser.term(pieces.theory, pieces.notation, sample, ty).flatMap(operatorOf)

  /** The function of a sample application, read off it rather than named. */
  private def functionIn(pieces: Pieces, sample: String, ty: Type): Either[LogicError, Term] =
    Parser.term(pieces.theory, pieces.notation, sample, ty).flatMap {
      case App(function, _) => Right(function)
      case other            => Left(NotOfForm("an application", other))
    }

  /** The summand of `Sum f n`. */
  private def summandOf(sum: Term): Either[LogicError, Term] = sum match {
    case App(App(_, summand), _) => Right(summand)
    case other                   => Left(NotOfForm("a partial sum", other))
  }

  /**
   * `|- Sum f bound = Sum g bound` from `Series.SUM_CONGRUENCE_BELOW`, the termwise equation at
   * each index below the bound supplied by `termwise`, which is handed the index and `u < bound`.
   */
  private def congruentBelow(
    pieces: Pieces,
    f: Term,
    g: Term,
    bound: Term,
    termwise: (Term, Kernel.Thm, Term) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = pieces.logic.rules
    val u = Term.variable("u", numbers)
    for {
      congruence <- pieces.series
        .fact(Series.CongruenceBelow)
        .flatMap(rules.specAll(_, List(f, g, bound)))
        .flatMap(opened)
      lessThan <- operatorIn(pieces, "NUM_LT (0:num) 0", Type.Bool)
      below <- LogicError.lift(Term.app(lessThan, u).flatMap(Term.app(_, bound)))
      assumedBelow <- LogicError.lift(Kernel.assume(below))
      left <- applied(f, u)
      right <- applied(g, u)
      goal <- LogicError.lift(Term.eq(left, right))
      atIndex <- termwise(u, assumedBelow, goal)
      everyIndex <- rules.disch(below, atIndex).flatMap(rules.gen(u, _))
      result <- rules.mp(congruence, everyIndex)
    } yield result
  }

  /**
   * One even place: `c u * c (K - u) = P K * g (u + u)` for `u < SUC K`, with `K = SUC m`.
   *
   * `d = K - u` is the partner index and `d + u = K` is all that is known about it. From that the
   * convolution's index `(K + K) - (u + u)` is `d + d`, which is `Peano.NUM_ADD_SUB` after the
   * semiring has regrouped `(d + u) + (d + u)`; the partner's term at `0 - x` is its term at `x`
   * by `Series.POWER_NEG_DOUBLE`; and the sign `P K` is `P d * P u` by `Series.POWER_ADD`. What
   * is left is an identity of the ring in six atoms.
   */
  private def evenPlace(
    pieces: Pieces,
    u: Term,
    below: Kernel.Thm,
    goal: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = pieces.logic.rules
    val theory = pieces.theory
    val notation = pieces.notation
    val x = Term.variable("x", values)
    val dText = "NUM_SUB (SUC (m:num)) (u:num)"

    for {
      k <- Parser.term(theory, notation, "SUC (m:num)", numbers)
      d <- Parser.term(theory, notation, dText, numbers)
      doubledU <- Parser.term(theory, notation, "NUM_ADD (u:num) (u:num)", numbers)
      doubledD <- Parser.term(theory, notation, "NUM_ADD (" + dText + ") (" + dText + ")", numbers)
      regrouped <- Parser.term(
        theory, notation,
        "NUM_ADD (NUM_ADD (" + dText + ") (" + dText + ")) (NUM_ADD (u:num) (u:num))", numbers)
      add <- operatorIn(pieces, "NUM_ADD (0:num) 0", numbers)
      subtract <- operatorIn(pieces, "NUM_SUB (0:num) 0", numbers)
      sign <- functionIn(pieces, "Power ((0:real) - 1) (0:num)", values)
      minusOne <- Parser.term(theory, notation, "(0:real) - 1", values)

      atMost <- pieces.peano
        .fact(Peano.AtMostBelowSuccessor)
        .flatMap(rules.specAll(_, List(k, u)))
        .flatMap(rules.mp(_, below))
      partner <- pieces.peano
        .fact(Peano.MinusThenPlus)
        .flatMap(rules.specAll(_, List(k, u)))
        .flatMap(rules.mp(_, atMost))
        .flatMap(Conv.sym)

      doubledK <- Conv.apTerm(add, partner).flatMap(Conv.apThm(_, k)).flatMap(first =>
        Parser.term(theory, notation, "NUM_ADD (" + dText + ") (u:num)", numbers)
          .flatMap(du => LogicError.lift(Term.app(add, du)))
          .flatMap(context => Conv.apTerm(context, partner))
          .flatMap(Conv.trans(first, _)))
      semiring <- rightOf(doubledK).flatMap(pieces.semiring.prove(_, regrouped))
      takenApart <- pieces.peano.fact(Peano.SumMinus).flatMap(rules.specAll(_, List(doubledD, doubledU)))
      index <- Conv
        .trans(doubledK, semiring)
        .flatMap(Conv.apTerm(subtract, _))
        .flatMap(Conv.apThm(_, doubledU))
        .flatMap(Conv.trans(_, takenApart))

      signs <- pieces.series
        .fact(Series.PowerOfSum)
        .flatMap(rules.specAll(_, List(minusOne, d, u)))
        .flatMap(split => Conv.apTerm(sign, partner).flatMap(Conv.trans(_, split)))
      negated <- pieces.series.fact(Series.NegatedDouble).flatMap(rules.specAll(_, List(x, d)))

      sides <- Term.destEq(goal).toRight(NotOfForm("an equation", goal))
      result <- byRewritingThenRing(
        pieces, sides._1, sides._2, Vector.empty, Vector(index, signs, negated))
    } yield result
  }

  /**
   * One odd place: `s u * s (m - u) = P (SUC m) * g (SUC (u + u))` for `u < SUC m`.
   *
   * The same argument as `evenPlace` one step along. The convolution's index is
   * `SUC (d + d)`, the partner's term at `0 - x` is `(0 - x)` times its even part and therefore
   * minus its term at `x`, and that one sign is exactly what `P (SUC m) = (0 - 1) * P d * P u`
   * has and the sine pair's `P u * P d` lacks.
   */
  private def oddPlace(
    pieces: Pieces,
    u: Term,
    below: Kernel.Thm,
    goal: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = pieces.logic.rules
    val theory = pieces.theory
    val notation = pieces.notation
    val x = Term.variable("x", values)
    val m = Term.variable("m", numbers)
    val dText = "NUM_SUB (m:num) (u:num)"

    for {
      d <- Parser.term(theory, notation, dText, numbers)
      doubledD <- Parser.term(theory, notation, "NUM_ADD (" + dText + ") (" + dText + ")", numbers)
      oddU <- Parser.term(theory, notation, "SUC (NUM_ADD (u:num) (u:num))", numbers)
      oddD <- Parser.term(theory, notation, "SUC (NUM_ADD (" + dText + ") (" + dText + "))", numbers)
      length <- Parser.term(theory, notation, "NUM_ADD (SUC (m:num)) (SUC (m:num))", numbers)
      apart <- Parser.term(
        theory, notation,
        "NUM_ADD (SUC (NUM_ADD (" + dText + ") (" + dText + "))) (SUC (NUM_ADD (u:num) (u:num)))",
        numbers)
      regrouped <- Parser.term(
        theory, notation,
        "NUM_ADD (NUM_ADD (" + dText + ") (" + dText + ")) (NUM_ADD (u:num) (u:num))", numbers)
      add <- operatorIn(pieces, "NUM_ADD (0:num) 0", numbers)
      subtract <- operatorIn(pieces, "NUM_SUB (0:num) 0", numbers)
      successor <- functionIn(pieces, "SUC (0:num)", numbers)
      sign <- functionIn(pieces, "Power ((0:real) - 1) (0:num)", values)
      times <- operatorIn(pieces, "(1:real) * 1", values)
      minusOne <- Parser.term(theory, notation, "(0:real) - 1", values)
      minusX <- Parser.term(theory, notation, "0 - (x:real)", values)

      atMost <- pieces.peano
        .fact(Peano.AtMostBelowSuccessor)
        .flatMap(rules.specAll(_, List(m, u)))
        .flatMap(rules.mp(_, below))
      partner <- pieces.peano
        .fact(Peano.MinusThenPlus)
        .flatMap(rules.specAll(_, List(m, u)))
        .flatMap(rules.mp(_, atMost))
        .flatMap(Conv.sym)

      successorRules <- Vector(Peano.AddAtSuccessor, Peano.SuccessorPlus)
        .map(pieces.peano.fact)
        .foldRight[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
          case (next, rest) => next.flatMap(one => rest.map(one +: _))
        }
        .flatMap(Rewrite.Rule.all(pieces.logic, _))
      lengthOpened <- Rewrite.rewrite(successorRules, length)
      apartOpened <- Rewrite.rewrite(successorRules, apart)

      doubledM <- Conv.apTerm(add, partner).flatMap(Conv.apThm(_, m)).flatMap(first =>
        Parser.term(theory, notation, "NUM_ADD (" + dText + ") (u:num)", numbers)
          .flatMap(du => LogicError.lift(Term.app(add, du)))
          .flatMap(context => Conv.apTerm(context, partner))
          .flatMap(Conv.trans(first, _)))
      semiring <- rightOf(doubledM).flatMap(pieces.semiring.prove(_, regrouped))
      inner <- Conv
        .trans(doubledM, semiring)
        .flatMap(Conv.apTerm(successor, _))
        .flatMap(Conv.apTerm(successor, _))
      lengthApart <- Conv
        .trans(lengthOpened, inner)
        .flatMap(theorem => Conv.sym(apartOpened).flatMap(Conv.trans(theorem, _)))
      takenApart <- pieces.peano.fact(Peano.SumMinus).flatMap(rules.specAll(_, List(oddD, oddU)))
      index <- Conv
        .apTerm(subtract, lengthApart)
        .flatMap(Conv.apThm(_, oddU))
        .flatMap(Conv.trans(_, takenApart))

      powerStep <- pieces.series.fact(Series.PowerAtSuccessor)
      signs <- for {
        step <- rules.specAll(powerStep, List(minusOne, m))
        split <- pieces.series
          .fact(Series.PowerOfSum)
          .flatMap(rules.specAll(_, List(minusOne, d, u)))
          .flatMap(theorem => Conv.apTerm(sign, partner).flatMap(Conv.trans(_, theorem)))
        byMinusOne <- LogicError.lift(Term.app(times, minusOne))
        carried <- Conv.apTerm(byMinusOne, split)
        joined <- Conv.trans(step, carried)
      } yield joined
      negated <- pieces.series.fact(Series.NegatedDouble).flatMap(rules.specAll(_, List(x, d)))
      partnerAtMinus <- for {
        step <- rules.specAll(powerStep, List(minusX, doubledD))
        byMinusX <- LogicError.lift(Term.app(times, minusX))
        carried <- Conv.apTerm(byMinusX, negated)
        joined <- Conv.trans(step, carried)
      } yield joined
      partnerAtX <- rules.specAll(powerStep, List(x, doubledD))

      sides <- Term.destEq(goal).toRight(NotOfForm("an equation", goal))
      result <- byRewritingThenRing(
        pieces, sides._1, sides._2, Vector(partnerAtX), Vector(index, signs, partnerAtMinus))
    } yield result
  }

  /**
   * `|- !m. C (SUC m) + S m = 0`, where `C` and `S` are the Cauchy products' terms, read off the
   * theorems that produced them so the statement is theirs and not a copy.
   */
  private def cancellation(pieces: Pieces, cosines: Term, sines: Term): Either[LogicError, Kernel.Thm] = {
    val rules = pieces.logic.rules
    val theory = pieces.theory
    val notation = pieces.notation
    val ring = pieces.series.ring
    val x = Term.variable("x", values)
    val m = Term.variable("m", numbers)
    val u = Term.variable("u", numbers)

    for {
      k <- Parser.term(theory, notation, "SUC (m:num)", numbers)
      afterK <- Parser.term(theory, notation, "SUC (SUC (m:num))", numbers)
      length <- Parser.term(theory, notation, "NUM_ADD (SUC (m:num)) (SUC (m:num))", numbers)
      minusX <- Parser.term(theory, notation, "0 - (x:real)", values)
      sign <- Parser.term(theory, notation, "Power ((0:real) - 1) (SUC (m:num))", values)
      evenIndex <- Parser.term(theory, notation, "NUM_ADD (u:num) (u:num)", numbers)
      oddIndex <- Parser.term(theory, notation, "SUC (NUM_ADD (u:num) (u:num))", numbers)
      plus <- operatorIn(pieces, "(1:real) + 1", values)
      times <- operatorIn(pieces, "(1:real) * 1", values)
      zero <- Parser.term(theory, notation, "0:real", values)

      convolution <- rules.specAll(pieces.exponentialConvolution, List(x, minusX, length))
      convolutionSum <- leftOf(convolution)
      g <- summandOf(convolutionSum)

      evens <- applied(g, evenIndex).flatMap(body => LogicError.lift(Term.abs(u, body)))
      odds <- applied(g, oddIndex).flatMap(body => LogicError.lift(Term.abs(u, body)))

      scaledEvens <- pieces.series
        .fact(Series.Scaled)
        .flatMap(rules.specAll(_, List(sign, evens, afterK)))
        .flatMap(opened)
      scaledOdds <- pieces.series
        .fact(Series.Scaled)
        .flatMap(rules.specAll(_, List(sign, odds, k)))
        .flatMap(opened)

      cosineAtK <- applied(cosines, k)
      sineAtM <- applied(sines, m)
      cosinePairs <- summandOf(cosineAtK)
      sinePairs <- summandOf(sineAtM)
      evenTarget <- leftOf(scaledEvens).flatMap(summandOf)
      oddTarget <- leftOf(scaledOdds).flatMap(summandOf)

      sameEvens <- congruentBelow(pieces, cosinePairs, evenTarget, afterK, evenPlace(pieces, _, _, _))
      sameOdds <- congruentBelow(pieces, sinePairs, oddTarget, k, oddPlace(pieces, _, _, _))
      cosineScaled <- Conv.trans(sameEvens, scaledEvens)
      sineScaled <- Conv.trans(sameOdds, scaledOdds)

      evenStep <- pieces.series
        .fact(Series.AtSuccessor)
        .flatMap(rules.specAll(_, List(evens, k)))
        .flatMap(opened)
      halves <- pieces.series
        .fact(Series.EvenOdd)
        .flatMap(rules.specAll(_, List(g, k)))
        .flatMap(opened)
      lastStep <- pieces.series
        .fact(Series.AtSuccessor)
        .flatMap(rules.specAll(_, List(g, length)))
        .flatMap(opened)

      /* ------------------------------------------ the whole convolution is `(x - x)^N / N! = 0` */

      cancelled <- Parser.term(theory, notation, "(x:real) + (0 - (x:real))", values)
        .flatMap(sum => LogicError.lift(Term.eq(sum, zero)))
        .flatMap(ring.prove)
      lengthIsSuccessor <- pieces.peano
        .fact(Peano.AddAtSuccessor)
        .flatMap(rules.specAll(_, List(k, m)))
      beforeLength <- Parser.term(theory, notation, "NUM_ADD (SUC (m:num)) (m:num)", numbers)
      zeroPower <- pieces.series
        .fact(Series.PowerAtSuccessor)
        .flatMap(rules.specAll(_, List(zero, beforeLength)))
      value <- rightOf(convolution)
      vanishes <- byRewritingThenRing(
        pieces, value, zero, Vector(cancelled, lengthIsSuccessor, zeroPower), Vector.empty)
      wholeIsZero <- Conv.trans(convolution, vanishes)

      /* ------------------------------------------------------- the two products add to nothing */

      evenLong <- leftOf(evenStep)
      evenShort <- rightOf(evenStep).flatMap(sidesOf).map(_._1)
      lastTerm <- rightOf(evenStep).flatMap(sidesOf).map(_._2)
      halfSum <- leftOf(halves)
      oddSum <- rightOf(halves).flatMap(sidesOf).map(_._2)
      wholeSum <- leftOf(lastStep)
      linear <- pieces.linarith
        .prove(
          "!a:real. !b:real. !c:real. !d:real. !e:real. !f:real. " +
            "a = b + c ==> d = b + e ==> f = d + c ==> f = 0 ==> a + e = 0")
        .flatMap(rules.specAll(_, List(evenLong, evenShort, lastTerm, halfSum, oddSum, wholeSum)))
        .flatMap(rules.mp(_, evenStep))
        .flatMap(rules.mp(_, halves))
        .flatMap(rules.mp(_, lastStep))
        .flatMap(rules.mp(_, wholeIsZero))

      added <- Conv
        .apTerm(plus, cosineScaled)
        .flatMap(first => LogicError.lift(Kernel.mkComb(first, sineScaled)))
      factored <- rightOf(added).flatMap(product =>
        leftOf(linear).flatMap(total =>
          LogicError.lift(Term.app(times, sign).flatMap(Term.app(_, total)))
            .flatMap(right => LogicError.lift(Term.eq(product, right)))
            .flatMap(ring.prove)))
      bySign <- LogicError.lift(Term.app(times, sign))
      zeroed <- Conv.apTerm(bySign, linear)
      annihilated <- rightOf(zeroed)
        .flatMap(product => LogicError.lift(Term.eq(product, zero)))
        .flatMap(ring.prove)
      result <- Conv
        .trans(added, factored)
        .flatMap(Conv.trans(_, zeroed))
        .flatMap(Conv.trans(_, annihilated))
        .flatMap(rules.gen(m, _))
    } yield result
  }

  /** `|- C 0 = 1`: the cosine's product term at zero is its first term squared, `1 * 1`. */
  private def cosineProductAtZero(pieces: Pieces, cosines: Term): Either[LogicError, Kernel.Thm] =
    for {
      zero <- Parser.term(pieces.theory, pieces.notation, "0:num", numbers)
      one <- Parser.term(pieces.theory, pieces.notation, "1:real", values)
      atZero <- applied(cosines, zero)
      equations <- Vector(
        pieces.series.fact(Series.AtSuccessor),
        pieces.series.fact(Series.AtZero),
        pieces.series.fact(Series.PowerAtZero),
        pieces.peano.fact(Peano.ZeroMinus),
        pieces.peano.fact(Peano.AddAtZero),
        pieces.peano.fact(Peano.EmbedsSuccessor),
        pieces.peano.fact(Peano.EmbedsZero),
        pieces.coding.fact(Coding.FactorialAtZero)
      ).foldRight[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
        case (next, rest) => next.flatMap(theorem => rest.map(theorem +: _))
      }
      result <- byRewritingThenRing(pieces, atZero, one, equations, Vector.empty)
    } yield result

  /* ====================================================================== the identity itself */

  /**
   * The series under a definition, in the spelling the rest of this file uses.
   *
   * The definitions write the index `NUM_MUL 2 k` and `NUM_ADD (NUM_MUL 2 k) 1`, which is what a
   * reader of the series expects; the induction under `Series.SUM_EVEN_ODD` closes on `k + k` and
   * `SUC (k + k)`. **Two passes and not one**: `NUM_ONE_SUC` rewrites the `1` inside the numeral
   * `2`, so with it in the first pass the doubling rule would never see a `2` to match, which is
   * the trap `Transcendental.construct` records for the cosine's value at zero.
   */
  private def respelled(pieces: Pieces, definition: Kernel.Thm, x: Term): Either[LogicError, Kernel.Thm] =
    for {
      unfolded <- Conv.unfold(definition, List(x))
      doubling <- pieces.semiring
        .prove("NUM_MUL 2 (k:num) = NUM_ADD k k")
        .flatMap(pieces.logic.rules.gen(Term.variable("k", numbers), _))
      first <- Rewrite.Rule.all(pieces.logic, Vector(doubling))
      successor <- Vector(
        pieces.peano.fact(Peano.NumeralOneIsSuccessorOfZero),
        pieces.peano.fact(Peano.AddAtSuccessor),
        pieces.peano.fact(Peano.AddAtZero)
      ).foldRight[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
        case (next, rest) => next.flatMap(theorem => rest.map(theorem +: _))
      }
      second <- Rewrite.Rule.all(pieces.logic, successor)
      once <- Rewrite.inTheorem(first, unfolded)
      twice <- Rewrite.inTheorem(second, once)
    } yield twice

  /**
   * `|- sequence converges to value` for the sequence a definition writes, from the convergence of
   * the partial sums: they differ by an eta step, and `Limit.CONVERGES_EVENTUALLY` at index zero
   * is what `Transcendental`'s addition theorem uses for the same gap.
   */
  private def carried(
    pieces: Pieces,
    partial: Term,
    sequence: Term,
    value: Term,
    convergence: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = pieces.logic.rules
    for {
      zero <- Parser.term(pieces.theory, pieces.notation, "0:num", numbers)
      instance <- pieces.limit
        .fact(Limit.Eventually)
        .flatMap(rules.specAll(_, List(partial, sequence, value, zero)))
        .flatMap(opened)
      premise <- pieces.logic
        .destImp(instance.conclusion)
        .toRight(NotOfForm("an implication", instance.conclusion))
      stripped <- Logic.stripForall(premise._1)
      index <- stripped._1.headOption.toRight(NotOfForm("a claim about every index", premise._1))
      inner <- pieces.logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      pointwise <- LogicError.lift(Term.app(partial, index)).map(Kernel.refl)
      everywhere <- rules.disch(inner._1, pointwise).flatMap(rules.gen(index, _))
      result <- rules.mp(instance, everywhere).flatMap(rules.mp(_, convergence))
    } yield result
  }

  /** The body of an existential at a chosen witness, ready to be assumed. */
  private def instanceAt(pieces: Pieces, existential: Kernel.Thm, witness: Term): Either[LogicError, Term] =
    pieces.logic
      .destExistsPredicate(existential.conclusion)
      .toRight(NotOfForm("an existential quantification", existential.conclusion))
      .flatMap(predicate => applied(predicate, witness))

  /**
   * `Transcendental.SIN_COS_SQUARED`, which is everything above put in one order.
   *
   * Four existentials are opened: `P` and `Q` are the sums of the two series' magnitudes, `A` and
   * `B` the two sums themselves, and the theorem says `cos x` is `A` and `sin x` is `B` without
   * saying what either is.
   */
  private def pythagoras(
    pieces: Pieces,
    cosineAbsolute: Kernel.Thm,
    sineAbsolute: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = pieces.logic.rules
    val theory = pieces.theory
    val notation = pieces.notation
    val ring = pieces.series.ring
    val x = Term.variable("x", values)
    val n = Term.variable("n", numbers)
    val p = Term.variable("P", values)
    val q = Term.variable("Q", values)
    val a = Term.variable("A", values)
    val b = Term.variable("B", values)
    val sequence = Type.fun(numbers, values)

    for {
      cosineTerms <- Parser.term(theory, notation, CosineTermsText, sequence)
      sineTerms <- Parser.term(theory, notation, SineTermsText, sequence)

      /* ------------------------------------ the four existentials, opened from the outside in */

      cosineMagnitudes <- rules.spec(x, cosineAbsolute)
      sineMagnitudes <- rules.spec(x, sineAbsolute)
      assumedP <- instanceAt(pieces, cosineMagnitudes, p).flatMap(t => LogicError.lift(Kernel.assume(t)))
      assumedQ <- instanceAt(pieces, sineMagnitudes, q).flatMap(t => LogicError.lift(Kernel.assume(t)))
      absoluteFact <- pieces.limit.fact(Limit.Absolute)
      cosineConverges <- rules
        .specAll(absoluteFact, List(cosineTerms, p))
        .flatMap(opened)
        .flatMap(rules.mp(_, assumedP))
      sineConverges <- rules
        .specAll(absoluteFact, List(sineTerms, q))
        .flatMap(opened)
        .flatMap(rules.mp(_, assumedQ))
      assumedA <- instanceAt(pieces, cosineConverges, a).flatMap(t => LogicError.lift(Kernel.assume(t)))
      assumedB <- instanceAt(pieces, sineConverges, b).flatMap(t => LogicError.lift(Kernel.assume(t)))

      /* ---------------------------------------------------------------- the two Cauchy products */

      cauchy <- pieces.limit.fact(Limit.Cauchy)
      cosineProduct <- rules
        .specAll(cauchy, List(cosineTerms, cosineTerms, a, a, p, p))
        .flatMap(opened)
        .flatMap(rules.mp(_, assumedP))
        .flatMap(rules.mp(_, assumedP))
        .flatMap(rules.mp(_, assumedA))
        .flatMap(rules.mp(_, assumedA))
      sineProduct <- rules
        .specAll(cauchy, List(sineTerms, sineTerms, b, b, q, q))
        .flatMap(opened)
        .flatMap(rules.mp(_, assumedQ))
        .flatMap(rules.mp(_, assumedQ))
        .flatMap(rules.mp(_, assumedB))
        .flatMap(rules.mp(_, assumedB))
      cosinePartials <- sidesOf(cosineProduct.conclusion).map(_._1)
      sinePartials <- sidesOf(sineProduct.conclusion).map(_._1)
      cosines <- cosinePartials match {
        case App(_, terms) => Right(terms)
        case other         => Left(NotOfForm("the partial sums of a series", other))
      }
      sines <- sinePartials match {
        case App(_, terms) => Right(terms)
        case other         => Left(NotOfForm("the partial sums of a series", other))
      }

      cancelling <- cancellation(pieces, cosines, sines)
      atZero <- cosineProductAtZero(pieces, cosines)

      /* ------------------------------ one index along, the partial sums add to one everywhere */

      shift <- pieces.series
        .fact(Series.Shift)
        .flatMap(rules.specAll(_, List(cosines, n)))
        .flatMap(opened)
      shifted <- leftOf(shift).flatMap(summandOf)
      additive <- pieces.series
        .fact(Series.Additive)
        .flatMap(rules.specAll(_, List(shifted, sines, n)))
        .flatMap(opened)
      summed <- leftOf(additive).flatMap(summandOf)
      nothing <- Parser.term(theory, notation, "\\i:num. (0:real)", sequence)
      congruent <- pieces.series
        .fact(Series.Congruence)
        .flatMap(rules.specAll(_, List(summed, nothing)))
        .flatMap(opened)
        .flatMap(rules.mp(_, cancelling))
        .flatMap(rules.spec(n, _))
      ofZero <- pieces.series.fact(Series.OfZero).flatMap(rules.spec(n, _))

      shiftedSum <- leftOf(shift)
      longer <- rightOf(shift).flatMap(sidesOf).map(_._1)
      first <- rightOf(shift).flatMap(sidesOf).map(_._2)
      summedSum <- leftOf(additive)
      sineSum <- rightOf(additive).flatMap(sidesOf).map(_._2)
      zeroSum <- rightOf(congruent)
      one <- pieces.linarith
        .prove(
          "!x:real. !y:real. !c:real. !z:real. !w:real. !o:real. " +
            "x = y - c ==> z = x + w ==> z = o ==> o = 0 ==> c = 1 ==> y + w = 1")
        .flatMap(rules.specAll(_, List(shiftedSum, longer, first, summedSum, sineSum, zeroSum)))
        .flatMap(rules.mp(_, shift))
        .flatMap(rules.mp(_, additive))
        .flatMap(rules.mp(_, congruent))
        .flatMap(rules.mp(_, ofZero))
        .flatMap(rules.mp(_, atZero))
        .flatMap(rules.gen(n, _))

      /* ----------------------------------------------- and so the two limits add to one as well */

      squareA <- sidesOf(cosineProduct.conclusion).map(_._2)
      squareB <- sidesOf(sineProduct.conclusion).map(_._2)
      cosineShifted <- pieces.limit
        .fact(Limit.Shifted)
        .flatMap(rules.specAll(_, List(cosinePartials, squareA)))
        .flatMap(opened)
        .flatMap(rules.mp(_, cosineProduct))
      shiftedSequence <- sidesOf(cosineShifted.conclusion).map(_._1)
      together <- pieces.limit
        .fact(Limit.Added)
        .flatMap(rules.specAll(_, List(shiftedSequence, sinePartials, squareA, squareB)))
        .flatMap(opened)
        .flatMap(rules.mp(_, cosineShifted))
        .flatMap(rules.mp(_, sineProduct))
      togetherSequence <- sidesOf(together.conclusion).map(_._1)
      total <- sidesOf(together.conclusion).map(_._2)
      ones <- Parser.term(theory, notation, "\\n:num. (1:real)", sequence)
      realOne <- Parser.term(theory, notation, "1:real", values)
      zero <- Parser.term(theory, notation, "0:num", numbers)
      eventually <- pieces.limit
        .fact(Limit.Eventually)
        .flatMap(rules.specAll(_, List(togetherSequence, ones, total, zero)))
        .flatMap(opened)
      premise <- pieces.logic
        .destImp(eventually.conclusion)
        .toRight(NotOfForm("an implication", eventually.conclusion))
      stripped <- Logic.stripForall(premise._1)
      index <- stripped._1.headOption.toRight(NotOfForm("a claim about every index", premise._1))
      inner <- pieces.logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      atIndex <- rules.spec(index, one)
      everywhere <- rules.disch(inner._1, atIndex).flatMap(rules.gen(index, _))
      towardsOne <- rules.mp(eventually, everywhere).flatMap(rules.mp(_, together))
      constant <- pieces.limit.fact(Limit.Constant).flatMap(rules.spec(realOne, _))
      squaresAddToOne <- pieces.limit
        .fact(Limit.Unique)
        .flatMap(rules.specAll(_, List(ones, total, realOne)))
        .flatMap(rules.mp(_, towardsOne))
        .flatMap(rules.mp(_, constant))

      /* ----------------------------------------------- the two values, and the identity at them */

      cosineAtX <- respelled(pieces, pieces.cosineDefinition, x)
      sineAtX <- respelled(pieces, pieces.sineDefinition, x)
      cosineValue <- valueOf(pieces, cosineAtX, cosineTerms, a, assumedA)
      sineValue <- valueOf(pieces, sineAtX, sineTerms, b, assumedB)

      claim <- Parser.term(theory, notation, "sin (x:real) * sin (x:real) + cos (x:real) * cos (x:real)", values)
      valueRules <- Rewrite.Rule.all(pieces.logic, Vector(sineValue, cosineValue))
      atValues <- Rewrite.rewrite(valueRules, claim)
      reordered <- rightOf(atValues).flatMap(term =>
        LogicError.lift(Term.eq(term, total)).flatMap(ring.prove))
      whole <- Conv
        .trans(atValues, reordered)
        .flatMap(Conv.trans(_, squaresAddToOne))

      /* ------------------------------------------- and the four existentials closed, inside out */

      withoutB <- rules.existsElim(sineConverges, b, whole)
      withoutA <- rules.existsElim(cosineConverges, a, withoutB)
      withoutQ <- rules.existsElim(sineMagnitudes, q, withoutA)
      result <- rules.existsElim(cosineMagnitudes, p, withoutQ).flatMap(rules.gen(x, _))
    } yield result
  }

  /** `|- f x = value` from the respelled definition and the convergence of its partial sums. */
  private def valueOf(
    pieces: Pieces,
    respelledDefinition: Kernel.Thm,
    terms: Term,
    value: Term,
    convergence: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      limited <- rightOf(respelledDefinition)
      sequence <- limited match {
        case App(_, inner) => Right(inner)
        case other         => Left(NotOfForm("a limit of a sequence", other))
      }
      partial <- sidesOf(convergence.conclusion).map(_._1)
      _ <- sequence match {
        case Abs(_, App(sums, _)) if sums == partial => Right(())
        case other => Left(NotOfForm("the partial sums the convergence is about", other))
      }
      towards <- carried(pieces, partial, sequence, value, convergence)
      named <- pieces.limit
        .fact(Limit.ValueOfConverges)
        .flatMap(pieces.logic.rules.specAll(_, List(sequence, value)))
        .flatMap(pieces.logic.rules.mp(_, towards))
      result <- Conv.trans(respelledDefinition, named)
    } yield result
}
