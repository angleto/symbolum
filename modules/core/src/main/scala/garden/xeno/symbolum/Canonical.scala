package garden.xeno.symbolum

import scala.annotation.tailrec
import scala.collection.immutable.VectorMap
import garden.xeno.symbolum.SimplificationRule._

/**
 * Smart constructors that build expressions already in canonical form.
 *
 * Every function here takes children that are themselves canonical and returns a canonical
 * result. That contract is what replaced the previous design, in which each node's `simplify`
 * re-simplified the nodes it built: `Div` factored a `-1` out of a negative numerator, `Mul`
 * folded it straight back in, and the two called each other until the stack ran out. Constructors
 * that terminate by construction cannot do that, and the call graph below has no cycle:
 *
 * {{{
 *   sum      ─┐
 *   product  ─┼─> sumDivFree <──> mulDivFree   (mutual, but only through `distribute`,
 *   quotient ─┘        │              │         which strictly reduces the number of
 *   power    ──────────┴──> mulCore <─┘         sum-valued factors)
 *                              │
 *                          fromFraction ──> mulCore
 * }}}
 *
 * == Canonical form ==
 *
 *  - `Num` is normalised by [[Rational]]; `Sub` and `Neg` never survive;
 *  - a sum has at least two terms, no nested sum, at most one numeric term and it sorts last;
 *  - a product has at least two factors, no nested product, no quotient factor, and at most one
 *    numeric factor, which sorts first;
 *  - a quotient has exactly two operands and neither is itself a quotient;
 *  - a coefficient that is a fraction lives in a quotient, not in a product: `n/2`, never
 *    `1/2 * n`. One spelling per value is the point; two spellings is what stopped `2 * (n/4)`
 *    and `n/2` from being recognised as the same term.
 *
 * == Div-free intermediate ==
 *
 * The `…DivFree` functions work on expressions with no quotient node, carrying a fractional
 * coefficient inside a product instead. Sums are built there, and [[fromFraction]] performs the
 * single step that moves every coefficient denominator down into one quotient at the end. Doing
 * it once, at the end, is what puts `n/2 + 1/4` over the common denominator without a separate
 * merging pass that could disagree with the rest of the pipeline.
 */
object Canonical {

  private val Zero: Num = Num(0)
  private val One: Num = Num(1)
  private val MinusOne: Num = Num(-1)

  /* ---------------------------------------------------------------- numbers */

  private def numAdd(a: Num, b: Num): Num = Num.fromFraction(Rational.add(a.fraction, b.fraction))
  private def numMul(a: Num, b: Num): Num = Num.fromFraction(Rational.multiply(a.fraction, b.fraction))
  private def numDiv(a: Num, b: Num): Num = Num.fromFraction(Rational.divide(a.fraction, b.fraction))

  private def isZero(e: Expr): Boolean = e match {
    case n: Num => n.numerator == 0.0
    case _ => false
  }

  private def isOne(e: Expr): Boolean = e match {
    case n: Num => n.numerator == 1.0 && n.denominator == 1.0
    case _ => false
  }

  /* ------------------------------------------------- coefficients and bases */

  /**
   * Split a canonical term into its numeric coefficient and the rest.
   *
   * `3*n/2` yields `(3/2, n)`, `7` yields `(7, 1)`, `cos(x)` yields `(1, cos(x))`. Like-term
   * collection groups on the second component, so this is the function that decides which terms
   * count as alike.
   */
  def splitCoefficient(e: Expr): (Num, Expr) = e match {
    case n: Num => (n, One)

    case Mul(factors) =>
      factors.head match {
        case c: Num => (c, mulOfFactors(factors.tail))
        case _ => (One, e)
      }

    case Div(Vector(numerator, denominator: Num)) =>
      val (coefficient, base) = splitCoefficient(numerator)
      (numDiv(coefficient, denominator), base)

    // A symbolic denominator stays in the base, and the coefficient is the numerator's. Matching
    // only the numeric denominator above made `3/x` a term with coefficient one and base `3/x`,
    // so `3/x + 1/x` was two unlike terms and never collected to `4/x`; the same blindness sent a
    // quotient into the div-free pipeline, which then built `2 * 27/x^3`, a product containing a
    // quotient, which this form forbids.
    case Div(Vector(numerator, denominator)) =>
      val (coefficient, base) = splitCoefficient(numerator)
      (coefficient, Div(Vector(base, denominator)))

    case _ => (One, e)
  }

  /** The factors of a base, as produced by [[splitCoefficient]]. */
  private def factorsOf(base: Expr): Vector[Expr] = base match {
    case Mul(factors) => factors
    case n: Num if isOne(n) => Vector.empty
    case other => Vector(other)
  }

  /** Rebuild a product from bare factors, without re-running any rule. */
  private def mulOfFactors(factors: Vector[Expr]): Expr =
    factors.length match {
      case 0 => One
      case 1 => factors.head
      case _ => Mul(factors)
    }

  /**
   * Split a canonical expression into numerator and denominator.
   *
   * The denominator is `1` for anything that is not a quotient or a fractional literal. Neither
   * component is itself a quotient, which is what lets [[product]] and [[quotient]] combine
   * fractions with one multiplication each instead of recursing.
   */
  private def asFraction(e: Expr)(implicit config: SimplificationConfig): (Expr, Expr) = e match {
    case Div(Vector(numerator, denominator)) => (numerator, denominator)
    // Taking a literal apart is numeric folding, and the whole fraction pipeline below is gated
    // on the same rule. Splitting here while the rest stayed put made a product and a sum
    // disagree about where the denominator of 1/5 belongs.
    case Num(numerator, denominator)
      if denominator != 1.0 && config.isEnabled(CombineNumericLiterals) =>
      (Num(numerator), Num(denominator))
    case _ => (e, One)
  }

  /** Rewrite a quotient by a numeric denominator as a fractional coefficient. */
  private def asDivFree(e: Expr)(implicit config: SimplificationConfig): Expr = e match {
    case Div(Vector(numerator, denominator: Num)) if config.isEnabled(CombineNumericLiterals) =>
      scaleDivFree(numDiv(One, denominator), numerator)
    case other => other
  }

  /* ---------------------------------------------------------------- products */

  /**
   * Build a product from canonical factors.
   *
   * @throws ExpansionLimitExceededError if distributing would exceed `config.maxExpansionTerms`
   */
  def product(factors: Vector[Expr])(implicit config: SimplificationConfig): Expr = {
    val flattened = flattenProducts(factors)
    if (flattened.exists(isZero)) Zero
    else {
      val parts = flattened.map(asFraction)
      val numerator = mulDivFree(parts.map(_._1))
      val denominators = parts.map(_._2).filterNot(isOne)
      if (denominators.isEmpty) fromFraction(numerator, One)
      else fromFraction(numerator, mulDivFree(denominators))
    }
  }

  /** Build a quotient from a canonical numerator and denominator. */
  def quotient(numerator: Expr, denominator: Expr)(implicit config: SimplificationConfig): Expr = {
    val (topNumerator, topDenominator) = asFraction(numerator)
    val (bottomNumerator, bottomDenominator) = asFraction(denominator)
    fromFraction(
      multiplyParts(Vector(topNumerator, bottomDenominator)),
      multiplyParts(Vector(topDenominator, bottomNumerator))
    )
  }

  /**
   * Multiply the parts of a fraction, dropping the `1`s [[asFraction]] supplies for a side that
   * has none.
   *
   * Those `1`s are an artefact of the split, not part of the expression. Passing them through
   * meant that with [[SimplificationRule.RemoveIdentity]] disabled every pass added another
   * factor of one: `x/3` became `1 * x / (1 * 3)`, then `1 * 1 * x / (1 * 1 * 3)`, so
   * simplification never settled. Not introducing them is the fix; removing them afterwards would
   * be the rule the caller had switched off.
   */
  private def multiplyParts(parts: Vector[Expr])(implicit config: SimplificationConfig): Expr = {
    val present = parts.filterNot(isOne)
    if (present.isEmpty) One else mulDivFree(present)
  }

  private def flattenProducts(factors: Vector[Expr]): Vector[Expr] =
    factors.flatMap {
      case Mul(inner) => inner
      case other => Vector(other)
    }

  /**
   * Multiply quotient-free factors, distributing over sums where the rules ask for it.
   *
   * The result is quotient-free except where a factor carried a symbolic denominator that
   * [[asFraction]] could not peel; [[fromFraction]] absorbs that case.
   */
  private def mulDivFree(factors: Vector[Expr])(implicit config: SimplificationConfig): Expr = {
    // Flattened before the cosine search, which looks at the factors it is given: a cosine still
    // nested inside a product went unseen, the pair was rewritten a pass later than it should
    // have been, and simplification was not idempotent.
    val flattened = flattenProducts(factors)
    val cosineReduced =
      if (config.isEnabled(ProductOfCosToSumOfCos)) productOfCosines(flattened) else flattened

    val sums = cosineReduced.count {
      case Add(_) => true
      case _ => false
    }

    if (sums > 0 && cosineReduced.length > 1 && config.isEnabled(DistributeProduct))
      distribute(cosineReduced)
    else
      mulCore(cosineReduced)
  }

  /**
   * Distribute a product over the sums among its factors.
   *
   * Every combination is a product of terms, and a term of a canonical sum is never itself a
   * sum, so the recursive call cannot distribute again: this recursion is one level deep.
   */
  private def distribute(factors: Vector[Expr])(implicit config: SimplificationConfig): Expr = {
    val termSets = factors.map {
      case Add(terms) => terms
      case other => Vector(other)
    }

    val estimatedTerms = termSets.foldLeft(1L)((acc, set) => acc * set.length)
    if (estimatedTerms > config.maxExpansionTerms)
      throw ExpansionLimitExceededError(estimatedTerms, config.maxExpansionTerms)

    val combinations = termSets.foldLeft(Vector(Vector.empty[Expr])) { (acc, set) =>
      acc.flatMap(prefix => set.map(prefix :+ _))
    }

    // Through `product` rather than `mulDivFree`: a term of one of the sums can be a quotient, and
    // `mulDivFree` takes its factors as they come, so three copies of `3/x` folded into
    // `(3/x)^3`. `product` splits each factor into numerator and denominator first, so the same
    // three give `27/x^3`.
    //
    // The recursion this opens is one level deep, for the reason stated above: a term of a
    // canonical sum is never a sum, so the inner `product` has no sum among its factors and
    // cannot distribute again.
    sumDivFree(combinations.map(combination => product(combination)))
  }

  /**
   * Apply `cos(A)*cos(B) = (cos(A-B) + cos(A+B))/2` to the first pair of cosine factors.
   *
   * Only the first pair is rewritten; the caller re-enters with one fewer cosine, so a product of
   * many cosines unwinds one pair at a time and terminates.
   */
  private def productOfCosines(factors: Vector[Expr])(implicit config: SimplificationConfig): Vector[Expr] = {
    val cosines = factors.zipWithIndex.collect { case (c: Cos, index) => (c, index) }
    if (cosines.length < 2) factors
    else {
      val ((firstCos, first), (secondCos, second)) = (cosines(0), cosines(1))
      val difference = sum(Vector(firstCos.argument, negate(secondCos.argument)))
      val total = sum(Vector(firstCos.argument, secondCos.argument))

      // Returned as factors rather than as a ready-made quotient: a quotient here would sit
      // inside the product the caller is still assembling, and a product containing a quotient is
      // not canonical. As a coefficient of one half it descends into the denominator along with
      // every other fractional coefficient. The two cosines go through `Cos.simplified` because
      // equal arguments make the difference zero, and `cos(0)` has to fold in this pass.
      val replacement = Vector[Expr](
        Num(1, 2),
        sum(Vector(Cos.simplified(difference), Cos.simplified(total)))
      )
      val remaining = factors.indices.filter(i => i != first && i != second).map(factors).toVector
      productOfCosines(replacement ++ remaining)
    }
  }

  /**
   * Assemble a product from factors that need no further rewriting.
   *
   * Numeric factors fold into a single leading coefficient, equal bases fold into powers, and
   * the remaining factors are sorted so that two spellings of one product are one expression.
   */
  private def mulCore(factors: Vector[Expr])(implicit config: SimplificationConfig): Expr = {
    val flattened = flattenProducts(factors)
    if (flattened.exists(isZero)) Zero
    else {
      val (numerics, others) = flattened.partitionMap {
        case n: Num => Left(n)
        case other => Right(other)
      }

      val coefficient =
        if (config.isEnabled(CombineNumericLiterals)) numerics.foldLeft(One)(numMul)
        else One

      val keptNumerics =
        if (config.isEnabled(CombineNumericLiterals)) Vector.empty[Expr]
        else if (config.isEnabled(RemoveIdentity)) numerics.filterNot(isOne)
        else numerics

      if (isZero(coefficient)) Zero
      else {
        val sorted = (keptNumerics ++ combinePowers(others)).sorted(ExprOrder.forProduct)
        val all = if (isOne(coefficient)) sorted else coefficient +: sorted

        all.length match {
          case 0 => One
          case 1 => all.head
          case _ => Mul(all)
        }
      }
    }
  }

  /**
   * Fold repeated factors into powers: `x * x` becomes `x^2`.
   *
   * Without this, `x * (x - 3)` expands to `Mul(x, x) - 3*x`, which no caller matching on
   * `Pow(x, 2)` recognises as a quadratic.
   */
  private def combinePowers(factors: Vector[Expr])(implicit config: SimplificationConfig): Vector[Expr] = {
    if (!config.isEnabled(CollectLikeTerms) || factors.length < 2) factors
    else {
      val (exponents, opaque) =
        factors.foldLeft((VectorMap.empty[Expr, Num], Vector.empty[Expr])) {
          case ((seen, kept), Pow(base, exponent: Num)) =>
            (seen.updated(base, numAdd(seen.getOrElse(base, Zero), exponent)), kept)
          case ((seen, kept), other @ Pow(_, _)) =>
            (seen, kept :+ other)
          case ((seen, kept), other) =>
            (seen.updated(other, numAdd(seen.getOrElse(other, Zero), One)), kept)
        }

      val rebuilt = exponents.toVector.flatMap { case (base, exponent) =>
        if (isZero(exponent)) Vector.empty[Expr]
        else if (isOne(exponent)) Vector(base)
        else Vector(Pow(base, exponent))
      }

      rebuilt ++ opaque
    }
  }

  /* ------------------------------------------------------------------- sums */

  /** Build a sum from canonical terms. */
  def sum(terms: Vector[Expr])(implicit config: SimplificationConfig): Expr =
    fromFraction(sumDivFree(flattenSums(terms).map(asDivFree)), One)

  private def flattenSums(terms: Vector[Expr])(implicit config: SimplificationConfig): Vector[Expr] = {
    val flattened = terms.flatMap {
      case Add(inner) => inner
      case other => Vector(other)
    }
    if (config.isEnabled(RemoveIdentity)) flattened.filterNot(isZero) else flattened
  }

  /**
   * Assemble a sum from quotient-free terms, collecting like terms.
   *
   * Grouping runs through an insertion-ordered map and the result is sorted afterwards, so the
   * same input always produces the same output. The previous implementation grouped through a
   * hash map and emitted terms in iteration order, which made simplification non-reproducible.
   */
  private def sumDivFree(terms: Vector[Expr])(implicit config: SimplificationConfig): Expr = {
    val flattened = flattenSums(terms)
    if (flattened.isEmpty) Zero
    else {
      val combined =
        if (config.isEnabled(CollectLikeTerms)) collectLikeTerms(flattened)
        else if (config.isEnabled(CombineNumericLiterals)) combineNumericTerms(flattened)
        else flattened

      // Scaling a term whose base is a sum distributes it, so collection can hand back a term that
      // is itself a sum, and `flattened` by construction contains none. One more round settles it:
      // those terms come from a distributed product and none of them has a sum for a base, so the
      // second round cannot produce another.
      if (combined.exists(_.isInstanceOf[Add])) sumDivFree(combined)
      else {
        val sorted = combined.sorted(ExprOrder.forSum)
        sorted.length match {
          case 0 => Zero
          case 1 => sorted.head
          case _ => Add(sorted)
        }
      }
    }
  }

  /**
   * Group terms by their base and add the coefficients, in the order the bases first appeared.
   *
   * `VectorMap` rather than `mutable.LinkedHashMap`, and the insertion order is the whole reason
   * either is here: the note above [[sumDivFree]] records what a hash map once did to
   * reproducibility. The two agree on it, and they agree for the same reason: writing a key that is
   * already present leaves its position alone and replaces only the value. That was checked rather
   * than assumed before the swap, over the whole expression corpus: every grouping this function
   * and [[combinePowers]] produce, and every canonical form built on them, came out identical.
   *
   * What it does not cover: `VectorMap` is not a drop-in for a `LinkedHashMap` that has entries
   * **removed** from it, where the two do differ. Neither of these two ever removes one.
   */
  private def collectLikeTerms(terms: Vector[Expr])(implicit config: SimplificationConfig): Vector[Expr] = {
    val coefficients = terms.foldLeft(VectorMap.empty[Expr, Num]) { (seen, term) =>
      val (coefficient, base) = splitCoefficient(term)
      seen.updated(base, numAdd(seen.getOrElse(base, Zero), coefficient))
    }
    coefficients.toVector
      .map { case (base, coefficient) => scaleDivFree(coefficient, base) }
      .filterNot(isZero)
  }

  private def combineNumericTerms(terms: Vector[Expr])(implicit config: SimplificationConfig): Vector[Expr] = {
    val (numerics, others) = terms.partitionMap {
      case n: Num => Left(n)
      case other => Right(other)
    }
    if (numerics.isEmpty) others
    else {
      val total = numerics.foldLeft(Zero)(numAdd)
      if (isZero(total)) others else total +: others
    }
  }

  /**
   * Multiply a base by a coefficient, keeping a fractional coefficient inside the product.
   *
   * The multiplication goes through [[mulDivFree]] rather than [[mulCore]] so that a coefficient
   * meeting a sum is distributed straight away. Scaling a sum and leaving the product intact left
   * `4 * (5*x - 3)` sitting in a numerator, which the next pass would then distribute, making
   * simplification non-idempotent, and `fullSimplify` do in two passes what belongs in one.
   */
  private def scaleDivFree(coefficient: Num, base: Expr)(implicit config: SimplificationConfig): Expr =
    if (isZero(coefficient)) Zero
    else if (isOne(base)) coefficient
    else if (isOne(coefficient)) base
    else base match {
      // A base that is a quotient is scaled in its numerator, and reassembled through [[quotient]]
      // rather than by building the node directly. Multiplying the coefficient into the factor
      // list instead put the quotient among the factors of a product, which this form forbids;
      // building the node directly skipped the numeric cancellation, which left `10/(5 * y)` for
      // the next pass to turn into `2/y`, so simplification was still not idempotent.
      case Div(Vector(numerator, denominator)) =>
        quotient(scaleDivFree(coefficient, numerator), denominator)

      case _ => mulDivFree(coefficient +: factorsOf(base))
    }

  /* ------------------------------------------------------- fraction assembly */

  /**
   * Reduce a numerator over a denominator to the canonical quotient.
   *
   * This is the single place where a fraction becomes a `Div`, and it performs, in order:
   *  1. moving every fractional coefficient in the numerator down into the denominator, which is
   *     what puts a sum over its least common denominator;
   *  2. folding the denominator into an inexact coefficient, which has no fraction to preserve;
   *  3. cancelling the numeric content shared by numerator and denominator, repeatedly;
   *  4. cancelling factors shared by both sides;
   *  5. giving each term of a sum its own denominator, where the rules ask for that instead of
   *     one common denominator.
   */
  private def fromFraction(numerator: Expr, denominator: Expr)
                          (implicit config: SimplificationConfig): Expr = {
    if (isZero(denominator)) throw DivisionByZeroError(s"$numerator divided by $denominator")
    if (isZero(numerator)) Zero
    else {
      val (lifted, scaledDenominator) = {
        val factor =
          if (!config.isEnabled(CombineNumericLiterals)) 1.0
          else numerator match {
            // Scaling a sum to the least common denominator of its terms is the merge itself, so it
            // waits for the rule. Doing it anyway and splitting the terms apart again afterwards
            // multiplied every inexact constant by the denominator and divided it back, which does
            // not return the same double.
            case Add(_) if !config.isEnabled(MergeFractionsCommonDenom) => 1.0
            case other => coefficientDenominator(other)
          }
        if (factor == 1.0) (numerator, denominator)
        else (scaleByWhole(numerator, factor), mulCore(Vector(denominator, Num(factor))))
      }

      // An inexact coefficient has no fraction worth preserving: 0.8775/2 is simply 0.4388, and
      // keeping the 2 in a denominator gives one value two spellings, which is how the same
      // expression came out as `0.8775 * (y - 2)/2` from one route and `0.4388 * (y - 2)` from
      // another. Exact coefficients keep their quotient form: `n/2`, not `0.5 * n`.
      val (folded, foldedDenominator) = (lifted, scaledDenominator) match {
        case (numeratorExpr, divisor: Num)
          if config.isEnabled(CombineNumericLiterals) && hasInexactCoefficient(numeratorExpr) =>
          val (coefficient, base) = splitCoefficient(numeratorExpr)
          (scaleDivFree(numDiv(coefficient, divisor), base), One)
        case unchanged => unchanged
      }

      val (reducedNumerator, reducedDenominator) =
        cancelCommonFactors(cancelNumericContent(folded, foldedDenominator))

      (reducedNumerator, reducedDenominator) match {
        case (n: Num, d: Num) if config.isEnabled(CombineNumericLiterals) => numDiv(n, d)

        // A fractional coefficient is always spelled as a quotient. That is the canonical form,
        // not an optional rule. What MergeFractionsCommonDenom governs is whether the terms of a
        // sum share one denominator or each keep their own. This runs after the reductions above,
        // not before them: a numerator that only becomes a sum once its content has been cancelled
        // would otherwise be split on one pass and merged on the next. It also runs before the
        // divide-by-one case, because a sum with no denominator of its own can still have terms
        // that carry one.
        case (Add(terms), d) if !config.isEnabled(MergeFractionsCommonDenom) =>
          quotientPerTerm(terms, d)

        case (n, d) if isOne(d) => n
        case (n, d) => Div(Vector(n, d))
      }
    }
  }

  /**
   * Divide each term of a sum by the denominator separately.
   *
   * This is what a sum looks like when the terms are not brought over a common denominator:
   * `n/2 + 1/4` rather than `(2*n + 1)/4`.
   */
  private def quotientPerTerm(terms: Vector[Expr], denominator: Expr)
                             (implicit config: SimplificationConfig): Expr = {
    // Through `quotient`, not `fromFraction`: a term may itself be a quotient, and `fromFraction`
    // expects a numerator that is not one. Handing it a quotient produced `cos(x)/4/5` on one
    // pass and `cos(x)/(4 * 5)` on the next.
    val quotients = terms.map(term => quotient(term, denominator))

    // Dividing through can turn one term into a sum of its own, so the terms are gathered and
    // collected again; without it `(3 * (x + 1/5) + 1)/3` came out as `x + 1/5 + 1/3`, with two
    // numeric terms that the next pass then added together.
    val flattened = flattenSums(quotients)
    val collected =
      if (config.isEnabled(CollectLikeTerms)) collectLikeTerms(flattened)
      else if (config.isEnabled(CombineNumericLiterals)) combineNumericTerms(flattened)
      else flattened

    // Collection puts a fractional coefficient back inside a product, so each term is given its
    // own denominator once more. Flattening first guarantees no term is a sum, which is what
    // stops this from re-entering the branch that called it.
    val perTerm = flattenSums(collected).map(term => quotient(term, One))

    // Zero terms go only where RemoveIdentity says so; dropping them here regardless made
    // `x + 0` simplify to `x` under a configuration with no rules enabled at all.
    val kept = if (config.isEnabled(RemoveIdentity)) perTerm.filterNot(isZero) else perTerm
    val sorted = kept.sorted(ExprOrder.forSum)
    sorted.length match {
      case 0 => Zero
      case 1 => sorted.head
      case _ => Add(sorted)
    }
  }

  /** True if the leading coefficient of `e` is a double outside the exact rational regime. */
  private def hasInexactCoefficient(e: Expr): Boolean = {
    val coefficient = splitCoefficient(e)._1
    coefficient.denominator == 1.0 && !Rational.isWhole(coefficient.numerator)
  }

  /** Least common multiple of the coefficient denominators appearing in `e`. */
  private def coefficientDenominator(e: Expr): Double = e match {
    case Add(terms) => terms.map(t => splitCoefficient(t)._1.denominator).reduce(Rational.lcm)
    case other => splitCoefficient(other)._1.denominator
  }

  /** Multiply through by a whole number, keeping the expression quotient-free. */
  private def scaleByWhole(e: Expr, factor: Double)(implicit config: SimplificationConfig): Expr = {
    val multiplier = Num(factor)
    e match {
      case Add(terms) => sumDivFree(terms.map(scaleByWhole(_, factor)))
      case other =>
        val (coefficient, base) = splitCoefficient(other)
        scaleDivFree(numMul(coefficient, multiplier), base)
    }
  }

  /**
   * Divide numerator and denominator by the largest whole number dividing both.
   *
   * Only whole coefficients participate: with a fractional coefficient still present the greatest
   * common divisor is not an integer and cancelling it would move the fraction rather than remove
   * it. Step 1 of [[fromFraction]] has already cleared those when the rules allow.
   */
  @tailrec
  private def cancelNumericContent(numerator: Expr, denominator: Expr)
                                  (implicit config: SimplificationConfig): (Expr, Expr) = {
    val unreduced = (numerator, denominator)
    if (!config.isEnabled(SimplifyFractions)) unreduced
    else {
      val (denominatorCoefficient, denominatorBase) = splitCoefficient(denominator)
      if (denominatorCoefficient.denominator != 1.0) unreduced
      else {
        val divisor = Rational.gcd(wholeContent(numerator), denominatorCoefficient.numerator)
        if (divisor <= 1.0) unreduced
        else {
          // Repeated, not once: dividing through re-collects the numerator, and a term that was
          // exact can absorb an inexact one and leave a content the first look could not see.
          // `9*(5*x - 29) - 92.6` over 45 cancels a 9, becomes `5*x - 39.3`, and only then shows
          // the 5. Each round divides a positive whole denominator by more than one, so this ends.
          val scale = Num(1.0 / divisor)
          cancelNumericContent(
            scaleByWhole(numerator, 1.0 / divisor),
            scaleDivFree(numMul(denominatorCoefficient, scale), denominatorBase)
          )
        }
      }
    }
  }

  /** Greatest whole number dividing every coefficient of `e`, or 0 when there is none. */
  private def wholeContent(e: Expr): Double = e match {
    case Add(terms) => terms.map(wholeContent).reduce(Rational.gcd)
    case other =>
      val coefficient = splitCoefficient(other)._1
      // Whole, not merely denominator-free: `gcd` is the integer Euclidean algorithm, and running
      // it on 0.8775 returns a number that means nothing and cancels the wrong amount.
      if (coefficient.denominator == 1.0 && Rational.isWhole(coefficient.numerator))
        math.abs(coefficient.numerator)
      else 0.0
  }

  /** Drop factors present on both sides of a quotient. */
  private def cancelCommonFactors(fraction: (Expr, Expr))
                                 (implicit config: SimplificationConfig): (Expr, Expr) = {
    val (numerator, denominator) = fraction
    if (!config.isEnabled(CancelCommonFactors)) fraction
    else {
      val numeratorFactors = factorsOf(splitCoefficient(numerator)._2)
      val denominatorFactors = factorsOf(splitCoefficient(denominator)._2)
      val shared = numeratorFactors.filter(denominatorFactors.contains)
      if (shared.isEmpty) fraction
      else {
        val (numeratorCoefficient, _) = splitCoefficient(numerator)
        val (denominatorCoefficient, _) = splitCoefficient(denominator)
        val keptNumerator = removeFirstEach(numeratorFactors, shared)
        val keptDenominator = removeFirstEach(denominatorFactors, shared)
        (scaleDivFree(numeratorCoefficient, mulOfFactors(keptNumerator)),
         scaleDivFree(denominatorCoefficient, mulOfFactors(keptDenominator)))
      }
    }
  }

  private def removeFirstEach(from: Vector[Expr], remove: Vector[Expr]): Vector[Expr] =
    remove.foldLeft(from) { (remaining, item) =>
      val index = remaining.indexOf(item)
      if (index < 0) remaining else remaining.patch(index, Nil, 1)
    }

  /* ------------------------------------------------------------------ powers */

  /** Build a power from a canonical base and exponent. */
  def power(base: Expr, exponent: Expr)(implicit config: SimplificationConfig): Expr =
    (base, exponent) match {
      case (_, e: Num) if isZero(e) => One
      case (b, e: Num) if isOne(e) => b
      case (b: Num, _) if isOne(b) => One
      case (b: Num, e: Num) if isZero(b) && e.value > 0 => Zero

      case (b: Num, e: Num) if config.isEnabled(CombineNumericLiterals) =>
        numericPower(b, e).getOrElse(Pow(b, e))

      case (Pow(innerBase, innerExponent), outerExponent) =>
        power(innerBase, product(Vector(innerExponent, outerExponent)))

      case (b, e: Num) if e.value < 0 =>
        quotient(One, power(b, Num(-e.numerator, e.denominator)))

      case (Div(Vector(numerator, denominator)), e) =>
        quotient(power(numerator, e), power(denominator, e))

      case (Add(terms), e: Num)
        if config.isEnabled(DistributeProduct) && e.denominator == 1.0 && e.numerator > 1.0 =>
        Pow.expandedSum(terms, e.numerator.toInt).getOrElse(Pow(base, exponent))

      case (Mul(factors), e: Num) if config.isEnabled(DistributeProduct) =>
        product(factors.map(power(_, e)))

      case _ => Pow(base, exponent)
    }

  /**
   * Evaluate a numeric power.
   *
   * A whole exponent stays exact. A fractional one is evaluated in floating point when the base
   * is non-negative, which is how `Solve` obtains the square root in the quadratic formula; the
   * result is no longer an exact rational and `4^(1/2)` is `2.0`, not `2`. A negative base with a
   * fractional exponent has no real value and is left symbolic.
   */
  private def numericPower(base: Num, exponent: Num): Option[Num] =
    if (exponent.denominator == 1.0 && math.abs(exponent.numerator) <= 1024.0)
      Rational.power(base.fraction, exponent.numerator.toInt).map(Num.fromFraction)
    else if (base.value >= 0.0) {
      val result = math.pow(base.value, exponent.value)
      if (result.isNaN || result.isInfinite) None else Some(Num(result))
    } else None

  /* --------------------------------------------------------------- negation */

  /** Negate a canonical expression. */
  def negate(e: Expr)(implicit config: SimplificationConfig): Expr =
    product(Vector(MinusOne, e))

  /**
   * Factor a common factor out of a sum: `a*b + a*c` becomes `a*(b + c)`.
   *
   * Inert while [[SimplificationRule.DistributeProduct]] is enabled, because the two rules invert
   * each other and running both never reaches a fixpoint. Distribution wins because it is the one
   * in the default rule set.
   */
  def factorCommonTerms(e: Expr)(implicit config: SimplificationConfig): Expr = {
    if (!config.isEnabled(FactorCommonTerms) || config.isEnabled(DistributeProduct)) e
    else e match {
      case Add(terms) if terms.length > 1 =>
        val factorSets = terms.map(t => factorsOf(splitCoefficient(t)._2))
        val shared = factorSets.head.filter(candidate => factorSets.tail.forall(_.contains(candidate)))
        if (shared.isEmpty) e
        else {
          val common = shared.head
          val remainders = terms.zip(factorSets).map { case (term, factors) =>
            val (coefficient, _) = splitCoefficient(term)
            scaleDivFree(coefficient, mulOfFactors(removeFirstEach(factors, Vector(common))))
          }
          // The remaining sum is factored again rather than left for the next pass. One common
          // factor was pulled per call until 2026-09-12, so two terms sharing two factors needed
          // two passes and `simplify` was NOT idempotent, which its own docstring promised and
          // `CanonicalFormSpec` found with a generated case after some thousands of others:
          // `(-4/5^3 * y * x)^1 + -(x * y) * (-6 - x)` came back as
          // `x * (-125 * y * (-x - 6) - 4 * y)/125` and then moved `y` out on the second pass.
          //
          // Pulling all of `shared` at once instead would be WRONG, and that is why this recurses.
          // `shared` is built with `contains` and carries no multiplicity, so for `x*x*y + x*y` it
          // is `[x, x, y]`, and removing all of it from the second term would take an `x` that is
          // not there and give `2*x*x*y` for `x*y*(x + 1)`. Recursing recomputes the shared set
          // against the actual remainders, so each step removes exactly what every term has.
          //
          // It terminates because every step removes one factor from every term and a term holds
          // finitely many.
          product(Vector(common, factorCommonTerms(sum(remainders))))
        }

      // A sum over a common denominator is still a sum, and its numerator can still be factored.
      // Matching only on `Add` meant `(3*cos(x) + x*cos(x))/3` was left alone on one pass and
      // factored on the next, once the quotient had been taken apart again.
      case Div(Vector(numerator, denominator)) =>
        val factored = factorCommonTerms(numerator)
        if (factored == numerator) e else quotient(factored, denominator)

      case other => other
    }
  }
}
