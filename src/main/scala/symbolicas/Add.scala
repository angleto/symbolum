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
   * ----------------------------------------------------------------------- */
  private def collectLikeTerms(terms: Seq[Expr])(implicit config: SimplificationConfig): Seq[Expr] = {
    // Extract coefficient and base for each term
    def extractCoeffAndBase(e: Expr): (Double, Expr) = e match {
      case Num(n, d) => (n/d, Num(1))
      case Mul(Array(Num(n, d), rest @ _*)) if rest.nonEmpty =>
        (n/d, if (rest.length == 1) rest.head else Mul(rest.toArray))
      case other => (1.0, other)
    }

    // Group terms by their base expression (as string for simplicity)
    val grouped = terms.groupBy { term =>
      val (_, base) = extractCoeffAndBase(term)
      base.toString
    }

    // For each group, sum up coefficients
    grouped.map { case (_, group) =>
      val coeffsAndBases = group.map(extractCoeffAndBase)
      val totalCoeff = coeffsAndBases.map(_._1).sum
      val base = coeffsAndBases.head._2

      if (base == Num(1)) {
        Num(totalCoeff)
      } else if (totalCoeff == 1.0) {
        base
      } else if (totalCoeff == 0.0) {
        Num(0)
      } else {
        Mul(Array(Num(totalCoeff), base)).simplify(config)
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
    val afterLikeTerms = if (config.isEnabled(CollectLikeTerms)) {
      collectLikeTerms(noZeros)(config)
    } else {
      noZeros
    }

    /* Factor common terms if enabled */
    if (config.isEnabled(FactorCommonTerms) && afterLikeTerms.length > 1) {
      val factored = factorCommonTerms(afterLikeTerms)(config)
      if (factored != Add(afterLikeTerms.toArray)) {
        return factored
      }
    }

    /* Combine numeric literals */
    if (config.isEnabled(CombineNumericLiterals)) {
      val (nums, others) = afterLikeTerms.partition(_.isInstanceOf[Num])

      /* For common denominator merging */
      if (config.isEnabled(MergeFractionsCommonDenom) && nums.nonEmpty) {
        val numericSum: Array[Expr] =
          nums
            .collect { case Num(n, d) => (n, d) }
            .groupBy(_._2) // group by denominator
            .map { case (den, pairs) =>
              val sumNum = pairs.map(_._1).sum
              Num(sumNum, den).simplify(config)
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
        // Just sum all numerics into one
        val numSum = nums.collect { case Num(n, d) => n/d }.sum
        val combined = (if (numSum != 0.0) Seq(Num(numSum)) else Seq()) ++ others

        combined.length match {
          case 0 => Num(0)
          case 1 => combined(0)
          case _ => Add(combined.toArray)
        }
      }
    } else {
      afterLikeTerms.length match {
        case 0 => Num(0)
        case 1 => afterLikeTerms(0)
        case _ => Add(afterLikeTerms.toArray)
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
      case e => s"+ ${showWithParens(e, this)}"
    }

    (first +: rest).mkString(" ")
  }
}
