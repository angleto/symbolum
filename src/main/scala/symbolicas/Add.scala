package symbolicas

import scala.annotation.tailrec
import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/* ============================================================================
 * n-ary composites - Addition
 * ========================================================================== */
final case class Add(exprs: Array[Expr]) extends Expr {
  override val precedence: Int = 1

  /* -------------------------------------------------------------------------
   * Try to merge a sum of "fractions" into a single common denominator
   * ----------------------------------------------------------------------- */
  private def mergeFractionsLCD(terms: Seq[Expr])(implicit config: SimplificationConfig): Option[Expr] = {

    /* helpers -------------------------------------------------------------- */
    def isWhole(d: Double): Boolean = (d % 1.0) == 0.0

    @tailrec
    def gcd(a: Int, b: Int): Int = if (b == 0) a.abs else gcd(b, a % b)

    def lcm(a: Int, b: Int): Int = (a / gcd(a, b)) * b

    /* Attempt to peel "numerator / integerDenominator" out of a term        */
    def asFraction(e: Expr): Option[(Expr, Int)] = e match {
      case Num(num, den) if isWhole(den) =>
        Some((Num(num).simplify(config), den.toInt))

      case Div(Array(numExpr, Num(denNum, denDen)))
        if denDen == 1.0 && isWhole(denNum) =>
        Some((numExpr, denNum.toInt))

      case _ => None
    }

    val extracted = terms.map(asFraction)

    /* Only proceed if we succeeded for every single term and we really
       *have* at least two fractions                                    */
    if (extracted.forall(_.isDefined) && terms.length > 1) {
      val fracs = extracted.map(_.get)
      val denominators = fracs.map(_._2)
      val commonDenominator = denominators.reduce(lcm)

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
   * Look for terms that differ only by a numeric coefficient
   * IMPORTANT: Preserves fraction representation
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

    // Helper to add two Num values as fractions
    def addFractions(a: Num, b: Num): Num = {
      // a/b + c/d = (ad + bc) / bd
      val newNum = a.numerator * b.denominator + b.numerator * a.denominator
      val newDen = a.denominator * b.denominator
      Num(newNum, newDen)
    }

    // Group terms by their base expression (as string for simplicity)
    val grouped = terms.groupBy { term =>
      val (_, base) = extractCoeffAndBase(term)
      base.toString
    }

    // For each group, sum up coefficients as fractions
    grouped.map { case (_, group) =>
      val coeffsAndBases = group.map(extractCoeffAndBase)
      val totalCoeff = coeffsAndBases.map(_._1).reduce(addFractions).simplify(config)
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
   * Factor common terms: a*b + a*c → a*(b + c)
   * This is a simplified version - looks for common factors in products
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

  /* ---------------- public part ------------------------------------------ */
  def eval(vars: Map[String, Double]): Double =
    exprs.map(_.eval(vars)).sum

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Add(exprs.map(_.replaceSymbol(sym, repl)))

  override def expand(implicit config: SimplificationConfig): Expr = {
    // Expand all child expressions and flatten any nested additions
    val expandedChildren = exprs.map(_.expand(config))
    val flattened = expandedChildren.flatMap {
      case Add(innerExprs) => innerExprs
      case other => Array(other)
    }
    Add(flattened).simplify(config)
  }

  def simplify(implicit config: SimplificationConfig): Expr = {
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

    /* Try to merge fractions with LCD if enabled */
    if (config.isEnabled(MergeFractionsLCD)) {
      mergeFractionsLCD(noZeros)(config) match {
        case Some(merged) => return merged
        case None => // continue
      }
    }

    /* Collect like terms if enabled */
    val afterLikeTerms: Array[Expr] = if (config.isEnabled(CollectLikeTerms)) {
      collectLikeTerms(noZeros)(config).toArray
    } else {
      noZeros
    }

    /* Factor common terms if enabled */
    if (config.isEnabled(FactorCommonTerms) && afterLikeTerms.length > 1) {
      val factored = factorCommonTerms(afterLikeTerms)(config)
      if (factored != Add(afterLikeTerms)) {
        return factored
      }
    }

    /* Merge divisions with common denominators ---------------------------- */
    /* Transform: Div([a, c]) + Div([b, c]) → Div([Add([a, b]), c])        */
    val afterDivMerge: Array[Expr] = if (config.isEnabled(MergeFractionsCommonDenom)) {
      val (divs, nonDivs) = afterLikeTerms.partition(_.isInstanceOf[Div])

      if (divs.length >= 2) {
        // Group divisions by their denominator (as string for simplicity)
        val grouped = divs.collect { case Div(Array(num, den)) => (num, den) }
          .groupBy(_._2.toString)

        val mergedDivs = grouped.flatMap { case (_, pairs) =>
          if (pairs.length == 1) {
            // Single div with this denominator, keep as-is
            val (num, den) = pairs.head
            Some(Div(Array(num, den)))
          } else {
            // Multiple divs with same denominator, merge them
            val den = pairs.head._2  // All have same denominator
            val numerators = pairs.map(_._1)
            val mergedNumerator = Add(numerators.toArray).simplify(config)

            // Only create a Div if the numerator is non-zero
            mergedNumerator match {
              case Num(0, _) => None
              case _ => Some(Div(Array(mergedNumerator, den)).simplify(config))
            }
          }
        }.toArray

        mergedDivs ++ nonDivs
      } else {
        afterLikeTerms
      }
    } else {
      afterLikeTerms
    }

    /* Combine numeric literals */
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
            .reduce { (a, b) =>
              // Add fractions: a/b + c/d = (ad + bc) / bd
              val newNum = a.numerator * b.denominator + b.numerator * a.denominator
              val newDen = a.denominator * b.denominator
              Num(newNum, newDen)
            }
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
      case e => s"+ ${showWithParens(e, this)}"
    }

    (first +: rest).mkString(" ")
  }
}
