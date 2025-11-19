package symbolicas

import scala.annotation.tailrec
import symbolicas.{SimplificationConfig, SimplificationRule, Num, NumericConstants}
import SimplificationRule._
import NumericConstants._

/**
 * Addition expression.
 *
 * Represents an n-ary sum: a + b + c + ...
 * Supports fraction merging, like term collection, and common factor extraction.
 *
 * @param terms Vector of expressions to add
 * @throws IllegalArgumentException if terms is empty
 *
 * @example {{{
 *   Add(Vector(Var("x"), Num(2)))           // x + 2
 *   Add(Vector(Num(1, 2), Num(1, 3)))       // 1/2 + 1/3
 *   Add(Vector(Var("x"), Mul(Vector(Num(2), Var("x")))))  // x + 2*x → 3*x (when simplified)
 * }}}
 */
final case class Add(terms: Vector[Expr]) extends Expr {
  require(terms.nonEmpty, "Addition requires at least one term")

  override val precedence: Int = 1

  /* -------------------------------------------------------------------------
   * Try to merge a sum of "fractions" into a single common denominator using LCD
   * ----------------------------------------------------------------------- */
  private def mergeFractionsLCD(termSeq: Seq[Expr])(implicit config: SimplificationConfig): Option[Expr] = {

    /* Attempt to extract numerator and integer denominator from a term */
    def asFraction(e: Expr): Option[(Expr, Int)] = e match {
      case Num(numerator, denominator) if Num.isWhole(denominator) =>
        Some((Num(numerator).simplify(config), denominator.toInt))

      case Div(Vector(numeratorExpr, Num(denNumerator, denDenominator)))
        if denDenominator == 1.0 && Num.isWhole(denNumerator) =>
        Some((numeratorExpr, denNumerator.toInt))

      case _ => None
    }

    val extracted = termSeq.map(asFraction)

    /* Only proceed if we succeeded for every single term and have at least two fractions */
    if (extracted.forall(_.isDefined) && termSeq.length > 1) {
      val fractions = extracted.map(_.get)
      val denominators = fractions.map(_._2)

      // Use Num.lcm for Int denominators (convert to Double for compatibility)
      val commonDenominator = denominators.reduce((a, b) => Num.lcm(a.toDouble, b.toDouble).toInt)

      if (commonDenominator == 1) {
        None // nothing to do
      } else {
        /* Scale every numerator to match the common denominator */
        val scaledNumerators = fractions.map { case (numeratorExpr, denom) =>
          val scaleFactor = commonDenominator / denom
          if (scaleFactor == 1) numeratorExpr
          else Mul(Vector(numeratorExpr, Num(scaleFactor))).simplify(config)
        }

        val combinedNumerator = Add(scaledNumerators.toVector).simplify(config)
        Some(Div(Vector(combinedNumerator, Num(commonDenominator))).simplify(config))
      }
    } else None
  }

  /* -------------------------------------------------------------------------
   * Collect like terms: x + 2*x + 3*y → 3*x + 3*y
   * IMPORTANT: Preserves fraction representation using Num.addFractions
   * ----------------------------------------------------------------------- */
  private def collectLikeTerms(termSeq: Seq[Expr])(implicit config: SimplificationConfig): Seq[Expr] = {

    /* Extract coefficient and base for each term */
    def extractCoeffAndBase(e: Expr): (Num, Expr) = e match {
      case n @ Num(_, _) => (n, Num(1))
      case Mul(Vector(n: Num, rest @ _*)) if rest.nonEmpty =>
        (n, if (rest.length == 1) rest.head else Mul(rest))
      case other => (Num(1), other)
    }

    // Group terms by their base expression
    // With Vector, we now have structural equality!
    val grouped = termSeq.groupBy { term =>
      extractCoeffAndBase(term)._2
    }

    // For each group, sum up coefficients using Num.addFractions
    grouped.map { case (base, group) =>
      val coefficientsAndBases = group.map(extractCoeffAndBase)
      val totalCoefficient = coefficientsAndBases.map(_._1).reduce(Num.addFractions).simplify(config)

      if (base == Num(1)) {
        totalCoefficient
      } else if (totalCoefficient == Num(1)) {
        base
      } else if (totalCoefficient == Num(0)) {
        Num(0)
      } else {
        Mul(Vector(totalCoefficient, base)).simplify(config)
      }
    }.toSeq
  }

  /* -------------------------------------------------------------------------
   * Factor common denominators: a/d + b/d → (a + b)/d
   * ----------------------------------------------------------------------- */
  private def factorCommonDenominator(termSeq: Seq[Expr])(implicit config: SimplificationConfig): Option[Expr] = {
    if (termSeq.length < 2) return None

    /* Extract numerator and denominator from a term */
    def extractDenominator(e: Expr): Option[(Expr, Double)] = e match {
      case Num(numerator, denominator) if denominator != 1.0 => Some((Num(numerator), denominator))

      case Mul(Vector(Num(numerator, denominator), rest @ _*)) if denominator != 1.0 && rest.nonEmpty =>
        val numeratorExpr = if (rest.length == 1) {
          Mul(Vector(Num(numerator), rest.head))
        } else {
          Mul(Vector(Num(numerator)) ++ rest)
        }
        Some((numeratorExpr, denominator))

      case Div(Vector(numerator, Num(denNumerator, denDenominator))) =>
        val denominatorValue = denNumerator / denDenominator
        Some((numerator, denominatorValue))

      case _ => None
    }

    // Try to extract denominators from all terms
    val extracted = termSeq.map(extractDenominator)
    if (!extracted.forall(_.isDefined)) return None

    val pairs = extracted.map(_.get)
    val denominators = pairs.map(_._2)

    // Check if all denominators are the same (within tolerance)
    val firstDenominator = denominators.head
    if (!denominators.forall(d => math.abs(d - firstDenominator) < TOLERANCE)) return None

    // All denominators are the same! Factor it out
    val numerators = pairs.map(_._1)
    val combinedNumerator = Add(numerators.toVector).simplify(config)

    Some(Div(Vector(combinedNumerator, Num(firstDenominator))).simplify(config))
  }

  /* -------------------------------------------------------------------------
   * Factor common terms: a*b + a*c → a*(b + c)
   * NOTE: Disabled when it would create large nested blocks (for Collatz expressions)
   * ----------------------------------------------------------------------- */
  private def factorCommonTerms(termSeq: Seq[Expr])(implicit config: SimplificationConfig): Expr = {
    if (termSeq.length < 2) return Add(termSeq.toVector)

    /* Get factors of a term */
    def getFactors(e: Expr): Seq[Expr] = e match {
      case Mul(factors) => factors
      case other => Seq(other)
    }

    // Find common factors across all terms
    val allFactorSets = termSeq.map(getFactors)
    val firstFactors = allFactorSets.head.toSet

    // With Vector, we now have proper structural equality!
    val commonFactors = firstFactors.filter { factor =>
      allFactorSets.tail.forall(_.exists(_ == factor))
    }

    if (commonFactors.isEmpty) {
      Add(termSeq.toVector)
    } else {
      // Extract one common factor
      val commonFactor = commonFactors.head

      // Remove common factor from each term
      val remainders = termSeq.map { term =>
        val factors = getFactors(term).filterNot(_ == commonFactor)
        factors.length match {
          case 0 => Num(1)
          case 1 => factors.head
          case _ => Mul(factors.toVector)
        }
      }

      // IMPORTANT: Don't factor if DistributeProduct is enabled and we'd create a nested block
      // This prevents oscillation between expansion and factoring
      if (config.isEnabled(DistributeProduct) && remainders.length > 1) {
        Add(termSeq.toVector)
      } else {
        Mul(Vector(commonFactor, Add(remainders.toVector))).simplify(config)
      }
    }
  }

  /* ---------------- Public API -------------------------------------------- */

  /**
   * Evaluates by summing all terms.
   *
   * @param variables Map of variable names to values
   * @return Sum of all term evaluations
   */
  def eval(variables: Map[String, Double]): Double =
    terms.map(_.eval(variables)).sum

  /**
   * Applies symbol replacement to all terms.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Addition with replaced terms
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Add(terms.map(_.replaceSymbol(sym, repl)))

  /**
   * Expands all child expressions and flattens nested additions.
   *
   * @param config Simplification configuration
   * @return Expanded expression
   */
  override def expand(implicit config: SimplificationConfig): Expr = {
    // Expand all child expressions
    val expandedChildren = terms.map(_.expand(config))

    // Flatten any nested additions
    val flattened = expandedChildren.flatMap {
      case Add(innerTerms) => innerTerms
      case other => Vector(other)
    }

    Add(flattened).simplify(config)
  }

  /**
   * Simplifies the addition expression.
   *
   * This is a complex method applying multiple transformations in sequence.
   * See IMPROVEMENT_PLAN.md for refactoring suggestions.
   *
   * @param config Simplification configuration
   * @return Simplified expression
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplifiedTerms = terms.map(_.simplify(config))
    val zero = Num(0)

    /* Flatten nested additions: Add(a, Add(b, c)) => Add(a, b, c) */
    val flattened = if (config.isEnabled(FlattenOperations)) {
      simplifiedTerms.flatMap {
        case Add(innerTerms) => innerTerms
        case other => Vector(other)
      }
    } else {
      simplifiedTerms
    }

    /* Remove zeros */
    val noZeros = if (config.isEnabled(RemoveIdentity)) {
      flattened.filterNot(_ == zero)
    } else {
      flattened
    }

    if (noZeros.isEmpty) return Num(0)

    /* Try to merge fractions with LCD if enabled */
    if (config.isEnabled(MergeFractionsLCD)) {
      mergeFractionsLCD(noZeros)(config) match {
        case Some(merged) => return merged
        case None => // continue
      }
    }

    /* Collect like terms if enabled */
    val afterLikeTerms: Vector[Expr] = if (config.isEnabled(CollectLikeTerms)) {
      collectLikeTerms(noZeros)(config).toVector
    } else {
      noZeros
    }

    /* Factor common denominators if enabled */
    if (config.isEnabled(MergeFractionsCommonDenom) && afterLikeTerms.length > 1) {
      factorCommonDenominator(afterLikeTerms)(config) match {
        case Some(factored) => return factored
        case None => // continue
      }
    }

    /* Factor common terms if enabled */
    if (config.isEnabled(FactorCommonTerms) && afterLikeTerms.length > 1) {
      val factored = factorCommonTerms(afterLikeTerms)(config)
      if (factored != Add(afterLikeTerms)) {
        return factored
      }
    }

    /* Merge divisions with common denominators (complex logic continues here) */
    val afterDivMerge: Vector[Expr] = if (config.isEnabled(MergeFractionsCommonDenom)) {
      val (divisions, nonDivisions) = afterLikeTerms.partition(_.isInstanceOf[Div])
      val (numerics, others) = nonDivisions.partition(_.isInstanceOf[Num])

      // Convert Num to Div for uniform handling (only if we have Divs to merge with)
      val numericsAsDivs = if (divisions.nonEmpty && numerics.nonEmpty) {
        numerics.collect {
          case Num(numerator, denominator) => Div(Vector(Num(numerator), Num(denominator)))
        }
      } else {
        Vector.empty[Expr]
      }

      val allDivisions = divisions ++ numericsAsDivs

      if (allDivisions.length >= 2) {
        // Extract all (numerator, denominator) pairs
        val divisionPairs = allDivisions.collect { case Div(Vector(num, den)) => (num, den) }

        // Extract denominator values (assuming they're Num)
        val denominatorValues = divisionPairs.map(_._2).collect {
          case Num(numerator, denominator) => numerator / denominator
        }

        if (denominatorValues.nonEmpty && denominatorValues.length == divisionPairs.length) {
          // All denominators are numeric, we can find LCD
          val lcd = denominatorValues.reduce(Num.lcm)

          // Convert all divisions to have LCD as denominator
          val normalizedPairs = divisionPairs.map { case (numerator, denominator) =>
            denominator match {
              case Num(denNumerator, denDenominator) =>
                val denominatorValue = denNumerator / denDenominator
                val multiplier = lcd / denominatorValue
                val newNumerator = if (multiplier == 1.0) {
                  numerator
                } else {
                  Mul(Vector(Num(multiplier), numerator)).simplify(config)
                }
                (newNumerator, Num(lcd))
              case _ => (numerator, denominator)  // Can't normalize non-numeric denominator
            }
          }

          // Group by denominator (now we have structural equality with Vector!)
          val grouped = normalizedPairs.groupBy(_._2)

          val mergedDivisions = grouped.flatMap { case (_, pairs) =>
            if (pairs.length == 1) {
              val (numerator, denominator) = pairs.head
              Some(Div(Vector(numerator, denominator)))
            } else {
              val denominator = pairs.head._2
              val numerators = pairs.map(_._1)
              val mergedNumerator = Add(numerators).simplify(config)

              mergedNumerator match {
                case Num(0, _) => None
                case _ => Some(Div(Vector(mergedNumerator, denominator)).simplify(config))
              }
            }
          }.toVector

          mergedDivisions ++ others ++ (if (numericsAsDivs.isEmpty) numerics else Vector.empty[Expr])
        } else {
          // Some denominators are not numeric, fall back to grouping by exact match
          val grouped = divisionPairs.groupBy(_._2)
          val mergedDivisions = grouped.flatMap { case (_, pairs) =>
            if (pairs.length == 1) {
              val (numerator, denominator) = pairs.head
              Some(Div(Vector(numerator, denominator)))
            } else {
              val denominator = pairs.head._2
              val numerators = pairs.map(_._1)
              val mergedNumerator = Add(numerators).simplify(config)
              mergedNumerator match {
                case Num(0, _) => None
                case _ => Some(Div(Vector(mergedNumerator, denominator)).simplify(config))
              }
            }
          }.toVector
          mergedDivisions ++ others ++ (if (numericsAsDivs.isEmpty) numerics else Vector.empty[Expr])
        }
      } else if (allDivisions.length == 1) {
        allDivisions ++ others ++ (if (numericsAsDivs.isEmpty) numerics else Vector.empty[Expr])
      } else {
        afterLikeTerms
      }
    } else {
      afterLikeTerms
    }

    /* Combine numeric literals */
    if (config.isEnabled(CombineNumericLiterals)) {
      val (numerics, others) = afterDivMerge.partition(_.isInstanceOf[Num])

      /* For common denominator merging */
      if (config.isEnabled(MergeFractionsCommonDenom) && numerics.nonEmpty) {
        val numericSum: Vector[Expr] =
          numerics
            .collect { case Num(numerator, denominator) => (numerator, denominator) }
            .groupBy(_._2) // group by denominator
            .map { case (denominator, pairs) =>
              val sumNumerator = pairs.map(_._1).sum
              Num(sumNumerator, denominator).simplify(config): Expr
            }
            .toVector
            .filterNot(_ == zero)

        val combined: Vector[Expr] = numericSum ++ others

        combined.length match {
          case 0 => Num(0)
          case 1 => combined(0)
          case _ => Add(combined)
        }
      } else {
        // Just sum all numerics using Num.addFractions
        val numericSum = if (numerics.nonEmpty) {
          numerics.collect { case n: Num => n }
            .reduce(Num.addFractions)
            .simplify(config)
        } else {
          Num(0)
        }

        val combined: Vector[Expr] =
          (if (numericSum != Num(0)) Vector[Expr](numericSum) else Vector.empty[Expr]) ++ others

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

  /**
   * Pretty-prints the addition with proper sign handling.
   *
   * Displays negative terms with minus signs instead of "+ -".
   */
  override def toString: String = {
    if (terms.isEmpty) return "0"

    val first = showWithParens(terms.head, this)
    val rest = terms.tail.map {
      case Neg(inner) => s"- ${showWithParens(inner, this)}"

      case Num(numerator, denominator) if numerator < 0 =>
        val positive = Num(-numerator, denominator)
        s"- ${showWithParens(positive, this)}"

      case Mul(Vector(Num(numerator, denominator), rest @ _*)) if numerator < 0 && rest.nonEmpty =>
        val positiveCoefficient = Num(-numerator, denominator)
        val positiveMul = if (rest.length == 1) {
          Mul(Vector(positiveCoefficient, rest.head))
        } else {
          Mul(Vector(positiveCoefficient) ++ rest)
        }
        s"- ${showWithParens(positiveMul, this)}"

      case Div(Vector(Num(numerator, denominator), den)) if numerator < 0 =>
        val positiveNumerator = Num(-numerator, denominator)
        s"- ${showWithParens(Div(Vector(positiveNumerator, den)), this)}"

      case Div(Vector(Mul(Vector(Num(numerator, denominator), rest @ _*)), den)) if numerator < 0 && rest.nonEmpty =>
        val positiveCoefficient = Num(-numerator, denominator)
        val positiveMul = if (rest.length == 1) {
          Mul(Vector(positiveCoefficient, rest.head))
        } else {
          Mul(Vector(positiveCoefficient) ++ rest)
        }
        s"- ${showWithParens(Div(Vector(positiveMul, den)), this)}"

      case Div(Vector(Add(addTerms), den)) =>
        // Check if all terms in numerator are negative
        val allNegative = addTerms.forall {
          case Num(n, _) => n < 0
          case Mul(Vector(Num(n, _), _ @ _*)) => n < 0
          case _ => false
        }

        if (allNegative && addTerms.length > 1) {
          // Factor out -1 from all terms
          val positiveTerms = addTerms.map {
            case Num(numerator, denominator) => Num(-numerator, denominator)
            case Mul(Vector(Num(numerator, denominator), rest @ _*)) =>
              if (rest.length == 1) Mul(Vector(Num(-numerator, denominator), rest.head))
              else Mul(Vector(Num(-numerator, denominator)) ++ rest)
            case other => other
          }
          val positiveAdd = Add(positiveTerms)
          s"- ${showWithParens(Div(Vector(positiveAdd, den)), this)}"
        } else {
          s"+ ${showWithParens(Div(Vector(Add(addTerms), den)), this)}"
        }

      case e => s"+ ${showWithParens(e, this)}"
    }

    (first +: rest).mkString(" ")
  }
}
