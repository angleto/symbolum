package symbolicas

import scala.annotation.tailrec
import symbolicas.{SimplificationConfig, SimplificationRule, MathUtils}
import SimplificationRule._

/* ============================================================================
 * n-ary composites - Addition
 * ========================================================================== */
final case class Add(exprs: Array[Expr]) extends Expr {
  override val precedence: Int = 1

  /* -------------------------------------------------------------------------
   * Try to merge a sum of "fractions" into a single common denominator
   * Uses least common denominator (LCD) to combine fractions efficiently.
   *
   * Example: 1/2 + 1/3 → (3 + 2)/6 → 5/6
   * ----------------------------------------------------------------------- */
  private def mergeFractionsLCD(terms: Seq[Expr])(implicit config: SimplificationConfig): Option[Expr] = {
    /* Attempt to peel "numerator / integerDenominator" out of a term        */
    def asFraction(e: Expr): Option[(Expr, Int)] = e match {
      case Num(num, den) if MathUtils.isWhole(den) =>
        Some((Num(num).simplify(config), den.toInt))

      case Div(Array(numExpr, Num(denNum, denDen)))
        if denDen == 1.0 && MathUtils.isWhole(denNum) =>
        Some((numExpr, denNum.toInt))

      case _ => None
    }

    val extracted = terms.map(asFraction)

    /* Only proceed if we succeeded for every single term and we really
       *have* at least two fractions                                    */
    if (extracted.forall(_.isDefined) && terms.length > 1) {
      val fracs = extracted.map(_.get)
      val denominators = fracs.map(_._2)
      val commonDenominator = denominators.reduce(MathUtils.lcm)

      if (commonDenominator == 1) {
        None // nothing to do
      } else {
        /* scale every numerator so that it matches the common denominator    */
        val scaledNumerators = fracs.map { case (numExpr, den) =>
          val factor = commonDenominator / den
          if (factor == 1) numExpr
          else Mul(Array(numExpr, Num(factor))).simplify(config)
        }

        val combinedNumerator = Add(scaledNumerators.toArray).simplify(config)
        Some(Div(Array(combinedNumerator, Num(commonDenominator))).simplify(config))
      }
    } else None
  }

  /* -------------------------------------------------------------------------
   * Collect like terms: x + 2*x + 3*y → 3*x + 3*y
   * Look for terms that differ only by a numeric coefficient.
   * IMPORTANT: Preserves fraction representation.
   *
   * Example: 1/2*x + 1/3*x → (3/6 + 2/6)*x → 5/6*x
   * ----------------------------------------------------------------------- */
  private def collectLikeTerms(terms: Seq[Expr])(implicit config: SimplificationConfig): Seq[Expr] = {
    // Extract coefficient and base for each term
    // Returns Num to preserve fractions, not Double
    def extractCoeffAndBase(e: Expr): (Num, Expr) = e match {
      case n @ Num(_, _) => (n, Num(1))
      case Mul(Array(n @ Num(_, _), rest @ _*)) if rest.nonEmpty =>
        (n, if (rest.length == 1) rest.head else Mul(rest.toArray))
      case other => (Num(1), other)
    }

    // Group terms by their base expression (as string for simplicity)
    val grouped = terms.groupBy { term =>
      val (_, base) = extractCoeffAndBase(term)
      base.toString
    }

    // For each group, sum up coefficients as fractions
    grouped.map { case (_, group) =>
      val coeffsAndBases = group.map(extractCoeffAndBase)
      val totalCoeff = coeffsAndBases.map(_._1).reduce(MathUtils.addFractions).simplify(config)
      val base = coeffsAndBases.head._2

      if (base == Num(1)) {
        totalCoeff
      } else if (totalCoeff == Num(1)) {
        base
      } else if (totalCoeff == Num(0)) {
        Num(0)
      } else {
        Mul(Array(totalCoeff, base)).simplify(config)
      }
    }.toSeq
  }

  /* -------------------------------------------------------------------------
   * Factor common denominators: a/d + b/d → (a + b)/d
   * Recognizes denominators in Num(a, d), Mul([Num(a, d), ...]), Div([num, den]).
   *
   * Example: 2/3 + 5/3 → (2 + 5)/3 → 7/3
   * Example: x/2 + y/2 → (x + y)/2
   * ----------------------------------------------------------------------- */
  private def factorCommonDenominator(terms: Seq[Expr])(implicit config: SimplificationConfig): Option[Expr] = {
    if (terms.length < 2) return None

    // Extract numerator and denominator from a term
    // Returns Some((numerator, denominator_value)) or None
    def extractDenominator(e: Expr): Option[(Expr, Double)] = e match {
      case Num(n, d) if d != 1.0 => Some((Num(n), d))

      case Mul(Array(Num(n, d), rest @ _*)) if d != 1.0 && rest.nonEmpty =>
        val numerator = if (rest.length == 1) {
          Mul(Array(Num(n), rest.head))
        } else {
          Mul(Array(Num(n)) ++ rest)
        }
        Some((numerator, d))

      case Div(Array(num, Num(denN, denD))) =>
        val denValue = denN / denD
        Some((num, denValue))

      case _ => None
    }

    // Try to extract denominators from all terms
    val extracted = terms.map(extractDenominator)

    // Only proceed if all terms have denominators
    if (!extracted.forall(_.isDefined)) return None

    val pairs = extracted.map(_.get)
    val denominators = pairs.map(_._2)

    // Check if all denominators are the same
    val firstDen = denominators.head
    val tolerance = 1e-10
    if (!denominators.forall(d => math.abs(d - firstDen) < tolerance)) return None

    // All denominators are the same! Factor it out
    val numerators = pairs.map(_._1)
    val combinedNumerator = Add(numerators.toArray).simplify(config)

    Some(Div(Array(combinedNumerator, Num(firstDen))).simplify(config))
  }

  /* -------------------------------------------------------------------------
   * Factor common terms: a*b + a*c → a*(b + c)
   * This is a simplified version - looks for common factors in products.
   *
   * Example: 2*x + 3*x → x*(2 + 3) → 5*x
   * Example: x*y + x*z → x*(y + z)
   * ----------------------------------------------------------------------- */
  private def factorCommonTerms(terms: Seq[Expr])(implicit config: SimplificationConfig): Expr = {
    if (terms.length < 2) return Add(terms.toArray)

    // Helper to get factors of a term
    def getFactors(e: Expr): Seq[Expr] = e match {
      case Mul(factors) => factors.toSeq
      case other => Seq(other)
    }

    // Find common factors across all terms
    val allFactors = terms.map(getFactors)
    val firstFactors = allFactors.head.toSet

    // Find factors common to all terms
    val commonFactors = firstFactors.filter { factor =>
      allFactors.tail.forall(_.exists(_.toString == factor.toString))
    }

    if (commonFactors.isEmpty) {
      Add(terms.toArray)
    } else {
      // Extract one common factor
      val commonFactor = commonFactors.head

      // Remove common factor from each term
      val remainders = terms.map { term =>
        val factors = getFactors(term).filterNot(_.toString == commonFactor.toString)
        factors.length match {
          case 0 => Num(1)
          case 1 => factors.head
          case _ => Mul(factors.toArray)
        }
      }

      // Build: commonFactor * (remainder1 + remainder2 + ...)
      Mul(Array(commonFactor, Add(remainders.toArray))).simplify(config)
    }
  }

  /* ========================================================================
   * PUBLIC API
   * ====================================================================== */

  /**
   * Evaluate this addition expression numerically.
   * @param vars mapping from variable names to their numeric values
   * @return the numeric sum of all terms
   */
  def eval(vars: Map[String, Double]): Double =
    exprs.map(_.eval(vars)).sum

  /**
   * Replace all occurrences of a symbol with another expression.
   * @param sym the symbol name to replace
   * @param repl the expression to substitute
   * @return a new Add expression with substitutions applied
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Add(exprs.map(_.replaceSymbol(sym, repl)))

  /**
   * Expand this addition expression.
   * Recursively expands all child expressions and flattens nested additions.
   *
   * Example: (a + b) + c → a + b + c
   * Note: Child expressions (like Mul or Div) will distribute during their expansion
   *
   * @param config simplification configuration (controls which rules apply)
   * @return expanded and flattened expression
   */
  override def expand(implicit config: SimplificationConfig): Expr = {
    // Expand all child expressions and flatten any nested additions
    val expandedChildren = exprs.map(_.expand(config))
    val flattened = expandedChildren.flatMap {
      case Add(innerExprs) => innerExprs
      case other => Array(other)
    }
    Add(flattened).simplify(config)
  }

  /**
   * Simplify this addition expression using algebraic rules.
   *
   * Simplification pipeline (applied sequentially):
   *   1. Simplify all child expressions
   *   2. Flatten nested additions:  (a + b) + c → a + b + c
   *   3. Remove identity elements:  a + 0 → a
   *   4. Merge fractions (LCD):     1/2 + 1/3 → 5/6
   *   5. Collect like terms:        2*x + 3*x → 5*x
   *   6. Factor common denominators: a/d + b/d → (a+b)/d
   *   7. Factor common terms:       a*b + a*c → a*(b+c)
   *   8. Merge divisions:           x/2 + y/2 → (x+y)/2
   *   9. Combine numeric literals:  2 + 3 → 5
   *
   * Which rules are applied depends on the SimplificationConfig.
   *
   * @param config simplification configuration controlling which rules to apply
   * @return simplified expression
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    // ========================================================================
    // PHASE 1: STRUCTURAL NORMALIZATION
    // Simplify children, flatten structure, remove identities
    // ========================================================================

    val simplified = exprs.map(_.simplify(config))
    val zero = Num(0)

    /* Flatten nested additions: Add(a, Add(b, c)) => Add(a, b, c) */
    val flattened = if (config.isEnabled(FlattenOperations)) {
      simplified.flatMap {
        case Add(innerExprs) => innerExprs
        case other => Array(other)
      }
    } else {
      simplified
    }

    /* Remove zeros */
    val noZeros = if (config.isEnabled(RemoveIdentity)) {
      flattened.filterNot(_ == zero)
    } else {
      flattened
    }

    if (noZeros.isEmpty) return Num(0)

    // ========================================================================
    // PHASE 2: FRACTION OPERATIONS
    // Apply fraction-specific simplifications
    // ========================================================================

    /* Try to merge fractions with LCD if enabled */
    if (config.isEnabled(MergeFractionsLCD)) {
      mergeFractionsLCD(noZeros)(config) match {
        case Some(merged) => return merged
        case None => // continue to next phase
      }
    }

    // ========================================================================
    // PHASE 3: ALGEBRAIC SIMPLIFICATIONS
    // Collect like terms and factor common expressions
    // ========================================================================

    /* Collect like terms: 2*x + 3*x → 5*x */
    val afterLikeTerms: Array[Expr] = if (config.isEnabled(CollectLikeTerms)) {
      collectLikeTerms(noZeros)(config).toArray
    } else {
      noZeros
    }

    /* Factor common denominators: a/d + b/d → (a+b)/d */
    /* This should happen before factorCommonTerms for better simplification */
    if (config.isEnabled(MergeFractionsCommonDenom) && afterLikeTerms.length > 1) {
      factorCommonDenominator(afterLikeTerms)(config) match {
        case Some(factored) => return factored
        case None => // continue to next phase
      }
    }

    /* Factor common terms: a*b + a*c → a*(b+c) */
    if (config.isEnabled(FactorCommonTerms) && afterLikeTerms.length > 1) {
      val factored = factorCommonTerms(afterLikeTerms)(config)
      if (factored != Add(afterLikeTerms)) {
        return factored
      }
    }

    // ========================================================================
    // PHASE 4: DIVISION MERGING
    // Merge multiple division expressions with common or compatible denominators
    // ========================================================================

    /* Merge divisions with common denominators */
    /* Transform: Div([a, c]) + Div([b, c]) → Div([Add([a, b]), c]) */
    /* Also handles mixed Div and Num by finding LCD */
    val afterDivMerge: Array[Expr] = if (config.isEnabled(MergeFractionsCommonDenom)) {
      val (divs, nonDivs) = afterLikeTerms.partition(_.isInstanceOf[Div])
      val (nums, others) = nonDivs.partition(_.isInstanceOf[Num])

      // Convert Num to Div for uniform handling (only if we have Divs to merge with)
      val numsAsDivs = if (divs.nonEmpty && nums.nonEmpty) {
        nums.collect {
          case Num(n, d) => Div(Array(Num(n), Num(d)))
        }
      } else {
        Array.empty[Expr]
      }

      val allDivs = divs ++ numsAsDivs

      if (allDivs.length >= 2) {
        // Extract all (numerator, denominator) pairs
        val divPairs = allDivs.collect { case Div(Array(num, den)) => (num, den) }

        // Extract denominator values (assuming they're Num)
        val denValues = divPairs.map(_._2).collect {
          case Num(n, d) => n / d
        }

        if (denValues.nonEmpty && denValues.length == divPairs.length) {
          // All denominators are numeric, we can find LCD
          val lcd = denValues.reduce(MathUtils.lcmDouble)

          // Convert all divs to have LCD as denominator
          val normalizedPairs = divPairs.map { case (num, den) =>
            den match {
              case Num(dn, dd) =>
                val denValue = dn / dd
                val multiplier = lcd / denValue
                val newNum = if (multiplier == 1.0) {
                  num
                } else {
                  Mul(Array(Num(multiplier), num)).simplify(config)
                }
                (newNum, Num(lcd))
              case _ => (num, den)  // Can't normalize non-numeric denominator
            }
          }

          // Group by denominator
          val grouped = normalizedPairs.groupBy(_._2.toString)

          val mergedDivs = grouped.flatMap { case (_, pairs) =>
            if (pairs.length == 1) {
              val (num, den) = pairs.head
              Some(Div(Array(num, den)))
            } else {
              val den = pairs.head._2
              val numerators = pairs.map(_._1)
              val mergedNumerator = Add(numerators.toArray).simplify(config)

              mergedNumerator match {
                case Num(0, _) => None
                case _ => Some(Div(Array(mergedNumerator, den)).simplify(config))
              }
            }
          }.toArray

          mergedDivs ++ others ++ (if (numsAsDivs.isEmpty) nums else Array.empty[Expr])
        } else {
          // Some denominators are not numeric, fall back to grouping by exact match
          val grouped = divPairs.groupBy(_._2.toString)
          val mergedDivs = grouped.flatMap { case (_, pairs) =>
            if (pairs.length == 1) {
              val (num, den) = pairs.head
              Some(Div(Array(num, den)))
            } else {
              val den = pairs.head._2
              val numerators = pairs.map(_._1)
              val mergedNumerator = Add(numerators.toArray).simplify(config)
              mergedNumerator match {
                case Num(0, _) => None
                case _ => Some(Div(Array(mergedNumerator, den)).simplify(config))
              }
            }
          }.toArray
          mergedDivs ++ others ++ (if (numsAsDivs.isEmpty) nums else Array.empty[Expr])
        }
      } else if (allDivs.length == 1) {
        allDivs ++ others ++ (if (numsAsDivs.isEmpty) nums else Array.empty[Expr])
      } else {
        afterLikeTerms
      }
    } else {
      afterLikeTerms
    }

    // ========================================================================
    // PHASE 5: NUMERIC LITERAL COMBINATION
    // Combine all numeric constants into a single value
    // ========================================================================

    /* Combine numeric literals: 2 + 3 + x → 5 + x */
    if (config.isEnabled(CombineNumericLiterals)) {
      val (nums, others) = afterDivMerge.partition(_.isInstanceOf[Num])

      /* For common denominator merging */
      if (config.isEnabled(MergeFractionsCommonDenom) && nums.nonEmpty) {
        val numericSum: Array[Expr] =
          nums
            .collect { case Num(n, d) => (n, d) }
            .groupBy(_._2) // group by denominator
            .map { case (den, pairs) =>
              val sumNum = pairs.map(_._1).sum
              Num(sumNum, den).simplify(config): Expr
            }
            .toArray
            .filterNot(_ == zero)

        val combined: Array[Expr] = numericSum ++ others

        combined.length match {
          case 0 => Num(0)
          case 1 => combined(0)
          case _ => Add(combined)
        }
      } else {
        // Just sum all numerics into one - preserve fractions
        val numSum = if (nums.nonEmpty) {
          nums.collect { case n @ Num(_, _) => n }
            .reduce(MathUtils.addFractions)
            .simplify(config)
        } else {
          Num(0)
        }

        val combined: Array[Expr] = (if (numSum != Num(0)) Array[Expr](numSum) else Array.empty[Expr]) ++ others

        combined.length match {
          case 0 => Num(0)
          case 1 => combined(0)
          case _ => Add(combined)
        }
      }
    } else {
      afterDivMerge.length match {
        case 0 => Num(0)
        case 1 => afterDivMerge(0)
        case _ => Add(afterDivMerge)
      }
    }
  }

  override def toString: String = {
    if (exprs.isEmpty) return "0"

    val first = showWithParens(exprs.head, this)
    val rest = exprs.tail.map {
      case Neg(inner) => s"- ${showWithParens(inner, this)}"

      case Num(n, d) if n < 0 =>
        val positive = Num(-n, d)
        s"- ${showWithParens(positive, this)}"

      case Mul(Array(Num(n, d), rest @ _*)) if n < 0 && rest.nonEmpty =>
        // Handle negative coefficient in multiplication: -2*x becomes "- 2*x"
        val positiveCoeff = Num(-n, d)
        val positiveMul = if (rest.length == 1) {
          Mul(Array(positiveCoeff, rest.head))
        } else {
          Mul(Array(positiveCoeff) ++ rest)
        }
        s"- ${showWithParens(positiveMul, this)}"

      case Div(Array(Num(n, d), den)) if n < 0 =>
        // Handle negative numerator in division: -a/b becomes "- a/b"
        val positiveNum = Num(-n, d)
        s"- ${showWithParens(Div(Array(positiveNum, den)), this)}"

      case Div(Array(Mul(Array(Num(n, d), rest @ _*)), den)) if n < 0 && rest.nonEmpty =>
        // Handle negative coefficient in numerator: (-2*x)/y becomes "- (2*x)/y"
        val positiveCoeff = Num(-n, d)
        val positiveMul = if (rest.length == 1) {
          Mul(Array(positiveCoeff, rest.head))
        } else {
          Mul(Array(positiveCoeff) ++ rest)
        }
        s"- ${showWithParens(Div(Array(positiveMul, den)), this)}"

      case Div(Array(Add(addTerms), den)) =>
        // Check if all terms in numerator are negative - if so, factor out the negative
        val allNegative = addTerms.forall {
          case Num(n, _) => n < 0
          case Mul(Array(Num(n, _), _ @ _*)) => n < 0
          case _ => false
        }

        if (allNegative && addTerms.length > 1) {
          // Factor out -1 from all terms
          val positiveTerms = addTerms.map {
            case Num(n, d) => Num(-n, d)
            case Mul(Array(Num(n, d), rest @ _*)) =>
              if (rest.length == 1) Mul(Array(Num(-n, d), rest.head))
              else Mul(Array(Num(-n, d)) ++ rest)
            case other => other
          }
          val positiveAdd = Add(positiveTerms)
          s"- ${showWithParens(Div(Array(positiveAdd, den)), this)}"
        } else {
          s"+ ${showWithParens(Div(Array(Add(addTerms), den)), this)}"
        }

      case e => s"+ ${showWithParens(e, this)}"
    }

    (first +: rest).mkString(" ")
  }
}
