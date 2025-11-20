package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/**
 * Division expression.
 *
 * Represents a chain of divisions: a / b / c / ...
 * Multi-operand divisions are flattened to a / (b * c * d) during simplification.
 *
 * @param operands Vector of expressions (dividend and divisors)
 * @throws IllegalArgumentException if operands has fewer than 2 elements
 *
 * @example {{{
 *   Div(Vector(Num(6), Num(2)))      // 6 / 2 → 3
 *   Div(Vector(Num(1, 2), Num(1, 3)))  // (1/2) / (1/3) → 3/2
 *   Div(Vector(a, b, c))             // a / b / c → a / (b * c)
 * }}}
 */
final case class Div(operands: Vector[Expr]) extends Expr {
  require(operands.length >= 2,
    s"Division requires at least 2 operands (dividend and divisor), got ${operands.length}")

  override val precedence: Int = 2

  /**
   * Evaluates division by computing a / b / c / ... = a / (b * c * ...)
   *
   * @param variables Map of variable names to values
   * @return Numerical result of the division
   * @throws DivisionByZeroError if any divisor evaluates to zero
   */
  def eval(variables: Map[String, Double]): Double = {
    val values = operands.map(_.eval(variables))
    values.tail.foreach { divisor =>
      if (divisor == 0.0)
        throw DivisionByZeroError(this.toString)
    }
    values.reduce(_ / _)
  }

  /**
   * Applies symbol replacement to all operands.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Division with replaced operands
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Div(operands.map(_.replaceSymbol(sym, repl)))

  /**
   * Expands the division expression.
   *
   * If the numerator is an Add and distribution is enabled, distributes:
   * (a + b + c) / d → a/d + b/d + c/d
   *
   * @param config Simplification configuration
   * @return Expanded expression
   *
   * @note Time Complexity: O(n) where n is total number of nodes
   */
  override def expand(implicit config: SimplificationConfig): Expr = {
    // Expand children first
    val expandedChildren = operands.map(_.expand(config))

    // If numerator is an Add and denominator is simple, distribute
    expandedChildren match {
      case Vector(Add(addTerms), denominator) if config.isEnabled(DistributeProduct) =>
        // Distribute: (a + b + c) / d → a/d + b/d + c/d
        // This allows further simplification by merging common denominators
        val distributedTerms = addTerms.map { term =>
          Div(Vector(term, denominator)).simplify(config)
        }
        Add(distributedTerms).simplify(config)

      case _ =>
        Div(expandedChildren).simplify(config)
    }
  }

  /**
   * Helper to build a simplified product from a sequence of expressions.
   *
   * @param expressions Expressions to multiply
   * @param config Simplification configuration
   * @return Product expression (or single element if only one)
   */
  private def buildProduct(expressions: Seq[Expr])(implicit config: SimplificationConfig): Expr =
    expressions.length match {
      case 0 => Num(1)
      case 1 => expressions.head
      case _ => Mul(expressions.toVector).simplify(config)
    }

  /**
   * Helper to check if an expression has a negative coefficient.
   *
   * @param expr Expression to check
   * @return True if the expression has a negative leading coefficient
   */
  private def hasNegativeCoefficient(expr: Expr): Boolean = expr match {
    case Num(n, _) if n < 0 => true
    case Mul(factors) if factors.nonEmpty =>
      factors.head match {
        case Num(n, _) if n < 0 => true
        case _ => false
      }
    case _ => false
  }

  /**
   * Helper to negate an expression by flipping the sign of its coefficient.
   *
   * @param expr Expression to negate
   * @param config Simplification configuration
   * @return Expression with negated coefficient
   */
  private def negateCoefficient(expr: Expr)(implicit config: SimplificationConfig): Expr = expr match {
    case Num(n, d) => Num(-n, d)
    case Mul(factors) if factors.nonEmpty =>
      factors.head match {
        case Num(n, d) =>
          val negatedNum = Num(-n, d)
          if (factors.tail.isEmpty) negatedNum
          else Mul(negatedNum +: factors.tail).simplify(config)
        case _ =>
          // No numeric coefficient, prepend -1
          Mul(Num(-1) +: factors).simplify(config)
      }
    case _ =>
      // No numeric coefficient, multiply by -1
      Mul(Vector(Num(-1), expr)).simplify(config)
  }

  /**
   * Simplifies the division expression.
   *
   * Transformations applied:
   * 1. Flatten multi-operand divisions: a / b / c → a / (b * c)
   * 2. Nested divisions: (a / b) / c → a / (b * c)
   * 3. Inverted divisions: a / (b / c) → (a * c) / b
   * 4. Numeric divisions: (a/b) / (c/d) → (a*d) / (b*c)
   * 5. Division by one: a / 1 → a
   * 6. Merge numeric factors
   * 7. Factor negative numerators: (-a - b) / c → -(a + b) / c
   *
   * @param config Simplification configuration
   * @return Simplified expression
   *
   * @note Time Complexity: O(n) where n is the number of operands
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    /* Simplify every child first */
    val simplifiedOperands = operands.map(_.simplify(config))

    /* 1) Flatten multi-operand: a / b / c / d → a / (b * c * d) */
    if (config.isEnabled(FlattenOperations) && simplifiedOperands.length > 2) {
      val numerator = simplifiedOperands.head
      val denominatorProduct = buildProduct(simplifiedOperands.tail)(config)
      return Div(Vector(numerator, denominatorProduct)).simplify(config)
    }

    /* Now we have at most two operands */
    simplifiedOperands match {
      /* 2) Nested division in numerator: (a / b) / c → a / (b * c) */
      case Vector(Div(Vector(innerNum, innerDen)), outerDen) if config.isEnabled(FlattenOperations) =>
        val newDenominator = buildProduct(Seq(innerDen, outerDen))(config)
        Div(Vector(innerNum, newDenominator)).simplify(config)

      /* 3) Nested division in denominator: a / (b / c) → (a * c) / b */
      case Vector(numerator, Div(Vector(innerDen1, innerDen2))) if config.isEnabled(FlattenOperations) =>
        val newNumerator = buildProduct(Seq(numerator, innerDen2))(config)
        Div(Vector(newNumerator, innerDen1)).simplify(config)

      /* 4) Both operands are Num: compute directly using fraction division */
      case Vector(dividend: Num, divisor: Num) if config.isEnabled(CombineNumericLiterals) =>
        Num.divideFractions(dividend, divisor).simplify(config)

      /* 5) Division by one */
      case Vector(numerator, Num(1, 1)) if config.isEnabled(RemoveIdentity) =>
        numerator

      /* 6) Numerator is Mul with Num factors, denominator is Num: merge them */
      case Vector(Mul(factors), denominator: Num) if config.isEnabled(CombineNumericLiterals) =>
        val (numFactors, symbolicFactors) = factors.partition(_.isInstanceOf[Num])
        if (numFactors.nonEmpty) {
          // Merge all Num factors in numerator using multiplyFractions
          val numeratorProduct = numFactors.collect { case n: Num => n }
            .reduce(Num.multiplyFractions)

          // Divide the merged numerator by the denominator
          val mergedFraction = Num.divideFractions(numeratorProduct, denominator).simplify(config)

          if (symbolicFactors.isEmpty) {
            mergedFraction
          } else if (mergedFraction == Num(1)) {
            // Coefficient is 1, return just the symbolic part
            if (symbolicFactors.length == 1) symbolicFactors.head
            else Mul(symbolicFactors).simplify(config)
          } else {
            // Both numeric and symbolic parts remain
            Mul(mergedFraction +: symbolicFactors).simplify(config)
          }
        } else {
          Div(Vector(Mul(factors), denominator))
        }

      /* 7) Denominator is Mul with multiple Num factors: merge them */
      case Vector(numerator, Mul(factors)) if config.isEnabled(FlattenOperations) =>
        val (numFactors, symbolicFactors) = factors.partition(_.isInstanceOf[Num])
        if (numFactors.length >= 2) {
          val mergedDenominator = numFactors.collect { case n: Num => n }
            .reduce(Num.multiplyFractions)
            .simplify(config)

          val newDenominator = if (symbolicFactors.isEmpty) {
            mergedDenominator
          } else if (symbolicFactors.length == 1) {
            Mul(Vector(mergedDenominator, symbolicFactors.head)).simplify(config)
          } else {
            Mul(mergedDenominator +: symbolicFactors).simplify(config)
          }
          Div(Vector(numerator, newDenominator)).simplify(config)
        } else {
          Div(Vector(numerator, Mul(factors)))
        }

      /* 8) Numerator is Add of Divs with same denominator: ((a/d + b/d + ...) / e) → (a+b+...) / (d*e) */
      case Vector(Add(addTerms), outerDenominator) if config.isEnabled(MergeFractionsCommonDenom) =>
        val allDivs = addTerms.forall(_.isInstanceOf[Div])
        if (allDivs && addTerms.length > 1) {
          val divTerms = addTerms.collect { case Div(Vector(n, d)) => (n, d) }

          // Check if all have the same denominator (using structural equality from Vector)
          val firstDenominator = divTerms.head._2
          val allSameDenominator = divTerms.tail.forall(_._2 == firstDenominator)

          if (allSameDenominator) {
            // All have same denominator: (a/d + b/d + ...) / e = (a+b+...) / (d*e)
            val numerators = divTerms.map(_._1)
            val sumOfNumerators = Add(numerators).simplify(config)
            val combinedDenominator = buildProduct(Seq(firstDenominator, outerDenominator))(config)
            Div(Vector(sumOfNumerators, combinedDenominator)).simplify(config)
          } else {
            Div(Vector(Add(addTerms), outerDenominator))
          }
        } else {
          Div(Vector(Add(addTerms), outerDenominator))
        }

      /* 9) Numerator is Add with all negative terms: factor out -1 */
      case Vector(Add(addTerms), denominator) if config.isEnabled(CombineNumericLiterals) =>
        // Check if all terms have negative coefficients
        if (addTerms.nonEmpty && addTerms.forall(hasNegativeCoefficient)) {
          // Factor out -1 from all terms
          val negatedTerms = addTerms.map(negateCoefficient)
          val positiveNumerator = Add(negatedTerms).simplify
          // Return -(positive_numerator / denominator)
          Mul(Vector(Num(-1), Div(Vector(positiveNumerator, denominator)))).simplify
        } else {
          Div(Vector(Add(addTerms), denominator))
        }

      /* Default: no simplification possible */
      case Vector(numerator, denominator) =>
        Div(Vector(numerator, denominator))

      case _ =>
        Div(simplifiedOperands)
    }
  }

  override def toString: String = {
    if (operands.length == 2) {
      val numerator = operands(0)
      val denominator = operands(1)

      // For cleaner output, add parentheses to denominators when needed
      val numeratorStr = if (numerator.precedence < this.precedence)
        s"($numerator)"
      else
        numerator.toString

      val denominatorStr = if (denominator.precedence <= this.precedence)
        s"($denominator)"
      else
        denominator.toString

      s"$numeratorStr/$denominatorStr"
    } else {
      operands.map(e => showWithParens(e, this)).mkString(" / ")
    }
  }
}
