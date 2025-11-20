package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/**
 * Multiplication expression.
 *
 * Represents an n-ary product: a * b * c * ...
 * Supports distribution over sums and product-to-sum transformations for cosines.
 *
 * @param factors Vector of expressions to multiply
 * @throws IllegalArgumentException if factors is empty
 *
 * @example {{{
 *   Mul(Vector(Num(2), Var("x")))             // 2 * x
 *   Mul(Vector(Num(1, 2), Num(1, 3)))         // (1/2) * (1/3) → 1/6
 *   Mul(Vector(a, Add(Vector(b, c))))         // a * (b + c) → a*b + a*c (when expanded)
 * }}}
 */
final case class Mul(factors: Vector[Expr]) extends Expr {
  require(factors.nonEmpty, "Multiplication requires at least one factor")

  override val precedence: Int = 2

  /**
   * Evaluates by multiplying all factors.
   *
   * @param variables Map of variable names to values
   * @return Product of all factor evaluations
   */
  def eval(variables: Map[String, Double]): Double =
    factors.map(_.eval(variables)).product

  /**
   * Applies symbol replacement to all factors.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Multiplication with replaced factors
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Mul(factors.map(_.replaceSymbol(sym, repl)))

  /**
   * Expands the multiplication by distributing over sums.
   *
   * For example: a * (b + c) → a*b + a*c
   *
   * @param config Simplification configuration (includes expansion limits)
   * @return Expanded expression
   * @throws ExpansionLimitExceededError if expansion would exceed maxExpansionTerms
   *
   * @note Time Complexity: O(k^n) where k is average terms per Add, n is number of Adds
   * @note This is the critical method that needs expansion limiting to prevent OOM
   */
  override def expand(implicit config: SimplificationConfig): Expr = {
    val expandedFactors: Vector[Expr] = factors.map(_.expand(config))

    // First try product-to-sum transformation if enabled
    if (config.isEnabled(ProductOfCosToSumOfCos)) {
      productToSumCosines(expandedFactors)(config) match {
        case Some((transformed, remaining)) =>
          if (remaining.isEmpty)
            transformed.expand(config)
          else
            Mul(transformed +: remaining).expand(config)
        case None =>
          expandDistribute(expandedFactors)(config)
      }
    } else {
      expandDistribute(expandedFactors)(config)
    }
  }

  /**
   * Distributes products over sums with expansion limit checking.
   *
   * Transforms: (a+b) * (c+d) → a*c + a*d + b*c + b*d
   *
   * @param expandedFactors Factors that have already been expanded
   * @param config Simplification configuration
   * @return Distributed expression or unexpanded Mul if limit would be exceeded
   * @throws ExpansionLimitExceededError if expansion would exceed maxExpansionTerms
   *
   * @note Prevents combinatorial explosion by checking term count before expanding
   */
  private def expandDistribute(expandedFactors: Vector[Expr])(implicit config: SimplificationConfig): Expr = {
    // Convert each factor to a set of terms (Add becomes multiple terms, others become single term)
    val termSets: Vector[Vector[Expr]] = expandedFactors.map {
      case Add(terms) => terms
      case other => Vector(other)
    }

    val hasAddition = termSets.exists(_.length > 1)
    if (!hasAddition || !config.isEnabled(DistributeProduct))
      return Mul(expandedFactors).simplify(config)

    /* CRITICAL: Check expansion limit before computing cartesian product */
    val estimatedTerms = termSets.map(_.length.toLong).product

    if (estimatedTerms > config.maxExpansionTerms) {
      // Expansion would exceed limit - return unexpanded form
      throw ExpansionLimitExceededError(estimatedTerms, config.maxExpansionTerms)
    }

    /* Safe to expand - compute cartesian product */
    val combinations: List[List[Expr]] = cartesianProduct(termSets.map(_.toList).toList)

    /* Build a product for every combination and simplify */
    val distributedTerms: Vector[Expr] =
      combinations.map { factorList =>
        Mul(factorList.toVector).simplify(config)
      }.toVector

    Add(distributedTerms).simplify(config)
  }

  /**
   * Computes the cartesian product of lists.
   *
   * For example: [[a,b], [c,d]] → [[a,c], [a,d], [b,c], [b,d]]
   *
   * @param lists List of lists to compute cartesian product of
   * @return All combinations
   *
   * @note Time Complexity: O(product of list lengths)
   */
  private def cartesianProduct[T](lists: List[List[T]]): List[List[T]] = lists match {
    case Nil => List(Nil)
    case head :: tail =>
      for {
        element <- head
        rest <- cartesianProduct(tail)
      } yield element :: rest
  }

  /**
   * Applies product-to-sum transformation for cosines.
   *
   * Transforms: cos(A) * cos(B) → (1/2) * [cos(A-B) + cos(A+B)]
   *
   * @param factors Factors to search for cosine pair
   * @param config Simplification configuration
   * @return Some((transformed, remaining)) if a pair was found, None otherwise
   *
   * @note Only transforms the first pair found, allowing iterative application
   */
  private def productToSumCosines(factors: Vector[Expr])(implicit config: SimplificationConfig):
      Option[(Expr, Vector[Expr])] = {
    // Find the first pair of Cos terms
    val cosineIndices = factors.zipWithIndex.collect {
      case (Cos(_), idx) => idx
    }

    if (cosineIndices.length >= 2) {
      val index1 = cosineIndices(0)
      val index2 = cosineIndices(1)

      // Safe pattern matching - we know these are Cos because we filtered them
      val (argA, argB) = (factors(index1), factors(index2)) match {
        case (Cos(a), Cos(b)) => (a, b)
        case _ => return None  // Defensive: should never happen
      }

      // Build: 1/2 * [cos(A - B) + cos(A + B)]
      val halfCoefficient = Num(1, 2)
      val difference = Sub(Vector(argA, argB)).simplify(config)
      val sum = Add(Vector(argA, argB)).simplify(config)
      val cosineSum = Add(Vector(
        Cos(difference),
        Cos(sum)
      ))

      // Keep all other factors except the two cosines we used
      val remainingFactors = factors.zipWithIndex.collect {
        case (expr, i) if i != index1 && i != index2 => expr
      }

      Some((Mul(Vector(halfCoefficient, cosineSum)).simplify(config), remainingFactors))
    } else {
      None
    }
  }

  /**
   * Simplifies the multiplication expression.
   *
   * Transformations applied:
   * 1. Flatten nested multiplications: Mul(a, Mul(b, c)) → Mul(a, b, c)
   * 2. Remove identity elements (1)
   * 3. Check for zero (short-circuit to 0)
   * 4. Aggressively expand products containing sums
   * 5. Merge divisions
   * 6. Apply product-to-sum for cosines
   * 7. Combine numeric factors
   *
   * @param config Simplification configuration
   * @return Simplified expression
   *
   * @note Time Complexity: O(n) where n is the number of factors
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplifiedFactors = factors.map(_.simplify(config))
    val one = Num(1.0)

    /* Flatten nested multiplications: Mul(a, Mul(b, c)) → Mul(a, b, c) */
    val flattened = if (config.isEnabled(FlattenOperations)) {
      simplifiedFactors.flatMap {
        case Mul(innerFactors) => innerFactors
        case other => Vector(other)
      }
    } else {
      simplifiedFactors
    }

    /* Remove identity elements (1) */
    val withoutOnes = if (config.isEnabled(RemoveIdentity)) {
      flattened.filterNot(_ == one)
    } else {
      flattened
    }

    /* Check for zero - short circuit */
    if (withoutOnes.contains(Num(0.0))) {
      return Num(0.0)
    }

    /* AGGRESSIVE EXPANSION: If we have a product with an Add term, expand it immediately
     * This prevents large nested blocks like: cos(A) * (B + C + D + ...)
     * We want: cos(A) * B + cos(A) * C + cos(A) * D + ...
     * This is crucial for breaking down large Collatz expressions */
    if (config.isEnabled(DistributeProduct)) {
      val containsAdd = withoutOnes.exists(_.isInstanceOf[Add])
      if (containsAdd && withoutOnes.length > 1) {
        // Expand this product immediately and return the expanded form
        // This may throw ExpansionLimitExceededError if too many terms
        return Mul(withoutOnes).expand(config)
      }
    }

    /* Merge numeric factors with divisions */
    /* Transform: Num(a) * Div(b, c) → Div(Mul(Num(a), b), c) */
    /* This allows 3 * (x/2) to become (3*x)/2 for better simplification */
    val withMergedDivs = if (config.isEnabled(FlattenOperations)) {
      val (numFactors, nonNumFactors) = withoutOnes.partition(_.isInstanceOf[Num])
      val (divisions, otherFactors) = nonNumFactors.partition(_.isInstanceOf[Div])

      if (divisions.length >= 2) {
        // Multiple divisions: merge them all into one
        val divisionPairs = divisions.collect { case Div(Vector(numerator, denominator)) => (numerator, denominator) }
        val allNumerators = divisionPairs.map(_._1)
        val allDenominators = divisionPairs.map(_._2)

        val combinedNumerator = if (allNumerators.length == 1) {
          allNumerators.head
        } else {
          Mul(allNumerators).simplify(config)
        }

        val combinedDenominator = if (allDenominators.length == 1) {
          allDenominators.head
        } else {
          Mul(allDenominators).simplify(config)
        }

        val mergedDivision = Div(Vector(combinedNumerator, combinedDenominator)).simplify(config)

        // Combine with numeric factors and other factors
        val result = mergedDivision +: (numFactors ++ otherFactors)
        if (result.length == 1) return result.head
        result

      } else if (numFactors.nonEmpty && divisions.nonEmpty) {
        // Single division with numeric factors: merge into numerator
        val numericProduct = if (numFactors.length == 1) numFactors.head else Mul(numFactors).simplify(config)

        val mergedDivisions = divisions.map {
          case Div(Vector(numerator, denominator)) =>
            Div(Vector(Mul(Vector(numericProduct, numerator)).simplify(config), denominator))
          case d => d  // Defensive: shouldn't happen
        }

        // Return merged divisions plus other factors
        mergedDivisions ++ otherFactors

      } else {
        withoutOnes
      }
    } else {
      withoutOnes
    }

    /* Try product-to-sum transformation for cosines */
    if (config.isEnabled(ProductOfCosToSumOfCos)) {
      productToSumCosines(withMergedDivs)(config) match {
        case Some((transformed, remaining)) =>
          // Multiply with remaining factors and recursively simplify
          if (remaining.isEmpty)
            return transformed
          else {
            // Combine remaining factors with the transformed expression
            // The transformed is "1/2 * (cos(a-b) + cos(a+b))"
            // We want remaining * 1/2 * (cos(a-b) + cos(a+b))
            transformed match {
              case Mul(Vector(halfCoefficient, sumExpr)) =>
                // Combine remaining factors with the half factor
                val allCoefficients = halfCoefficient +: remaining
                val finalCoefficient = if (allCoefficients.length == 1) allCoefficients(0)
                else Mul(allCoefficients).simplify(config)
                return Mul(Vector(finalCoefficient, sumExpr)).simplify(config)
              case _ =>
                return Mul(transformed +: remaining).simplify(config)
            }
          }

        case None =>
        // Fall through to numeric simplification
      }
    }

    /* Split into numeric and symbolic parts */
    val (numericFactors, symbolicFactors) = withMergedDivs.partition(_.isInstanceOf[Num])

    /* Combine all numeric factors using multiplyFractions */
    val numericPart = if (config.isEnabled(CombineNumericLiterals) && numericFactors.nonEmpty) {
      numericFactors.collect { case n: Num => n }
        .reduce(Num.multiplyFractions)
        .simplify(config)
    } else {
      one
    }

    /* Build final result */
    val combinedFactors: Vector[Expr] =
      if (numericPart == one) {
        // No numeric factors to combine, keep both numeric and symbolic factors
        numericFactors ++ symbolicFactors
      } else {
        // Combined numeric factors into numericPart, add symbolic factors
        Vector(numericPart) ++ symbolicFactors
      }

    combinedFactors.length match {
      case 0 => Num(1.0)
      case 1 => combinedFactors(0)
      case _ => Mul(combinedFactors)
    }
  }

  override def toString: String = {
    // Group numeric coefficients first for cleaner output
    val (numericFactors, symbolicFactors) = factors.partition(_.isInstanceOf[Num])

    val parts = if (numericFactors.nonEmpty) {
      // Show numeric coefficients first (without extra parens)
      numericFactors.map(_.toString) ++ symbolicFactors.map(e => showWithParens(e, this))
    } else {
      factors.map(e => showWithParens(e, this))
    }

    parts.mkString(" * ")
  }
}
