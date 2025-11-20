package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._
import scala.annotation.tailrec

/**
 * Power/Exponentiation expression.
 *
 * Represents base^exponent.
 * Supports algebraic simplification, binomial expansion for small integer exponents,
 * and various power laws.
 *
 * @param base The base expression
 * @param exponent The exponent expression
 * @throws IllegalArgumentException if both base and exponent are zero (0^0 is undefined)
 *
 * @example {{{
 *   Pow(Var("x"), Num(2))              // x^2
 *   Pow(Num(2), Num(3))                // 2^3 → 8
 *   Pow(Var("x"), Num(0))              // x^0 → 1
 *   Pow(Add(Vector(Var("x"), Num(1))), Num(2))  // (x+1)^2 → x^2 + 2*x + 1 (when expanded)
 * }}}
 */
final case class Pow(base: Expr, exponent: Expr) extends Expr {
  require(!(base == Num(0) && exponent == Num(0)), "0^0 is undefined")

  override val precedence: Int = 3

  /**
   * Evaluate the power numerically.
   *
   * @param variables Map of variable names to values
   * @return base^exponent evaluated numerically
   */
  def eval(variables: Map[String, Double]): Double = {
    val b = base.eval(variables)
    val e = exponent.eval(variables)
    math.pow(b, e)
  }

  /**
   * Apply symbol replacement to base and exponent.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Power with replaced base and exponent
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Pow(base.replaceSymbol(sym, repl), exponent.replaceSymbol(sym, repl))

  /**
   * Expand the power expression.
   *
   * For integer exponents on sums, applies binomial expansion:
   * (a+b)^n = Σ C(n,k) * a^(n-k) * b^k
   *
   * @param config Simplification configuration
   * @return Expanded expression
   *
   * @note Only expands for small positive integer exponents (n ≤ 10) to avoid combinatorial explosion
   */
  override def expand(implicit config: SimplificationConfig): Expr = {
    val expandedBase = base.expand(config)
    val expandedExponent = exponent.expand(config)

    (expandedBase, expandedExponent) match {
      // Binomial expansion for (a+b)^n where n is small positive integer
      case (Add(terms), Num(n)) if n == n.toInt && n > 0 && n <= 10 && config.isEnabled(DistributeProduct) =>
        binomialExpansion(terms, n.toInt)(config)

      // Distribute power over multiplication: (a*b)^n → a^n * b^n
      case (Mul(factors), exp: Num) if config.isEnabled(DistributeProduct) =>
        val poweredFactors = factors.map(f => Pow(f, exp).simplify(config))
        Mul(poweredFactors).simplify(config)

      case _ =>
        Pow(expandedBase, expandedExponent).simplify(config)
    }
  }

  /**
   * Compute binomial expansion of (a1 + a2 + ... + an)^k.
   *
   * For two terms: (a+b)^n = Σ C(n,i) * a^i * b^(n-i)
   * For multiple terms: Uses multinomial theorem
   *
   * @param terms Terms in the sum
   * @param n Positive integer exponent
   * @param config Simplification configuration
   * @return Expanded sum
   */
  private def binomialExpansion(terms: Vector[Expr], n: Int)(implicit config: SimplificationConfig): Expr = {
    if (terms.length == 1) {
      // Single term: just raise to power
      Pow(terms.head, Num(n)).simplify(config)
    } else if (terms.length == 2) {
      // Binomial theorem: (a+b)^n
      val a = terms(0)
      val b = terms(1)
      val expandedTerms = (0 to n).map { k =>
        val coeff = binomialCoefficient(n, k)
        val termA = if (n - k == 0) Num(1) else if (n - k == 1) a else Pow(a, Num(n - k)).simplify(config)
        val termB = if (k == 0) Num(1) else if (k == 1) b else Pow(b, Num(k)).simplify(config)

        if (coeff == 1) {
          Mul(Vector(termA, termB)).simplify(config)
        } else {
          Mul(Vector(Num(coeff), termA, termB)).simplify(config)
        }
      }.toVector

      Add(expandedTerms).simplify(config)
    } else {
      // Multinomial expansion for 3+ terms: convert to (first + rest)^n and recurse
      val first = terms.head
      val rest = Add(terms.tail)
      binomialExpansion(Vector(first, rest), n)(config)
    }
  }

  /**
   * Compute binomial coefficient C(n, k) = n! / (k! * (n-k)!)
   *
   * @param n Total
   * @param k Chosen
   * @return C(n, k)
   */
  private def binomialCoefficient(n: Int, k: Int): Int = {
    if (k > n) 0
    else if (k == 0 || k == n) 1
    else {
      // Use the recursive formula: C(n,k) = C(n-1,k-1) + C(n-1,k)
      // But for efficiency, use iterative calculation
      val kk = math.min(k, n - k) // Take advantage of symmetry
      (1 to kk).foldLeft(1) { (acc, i) =>
        acc * (n - i + 1) / i
      }
    }
  }

  /**
   * Simplify the power expression.
   *
   * Applies various power laws:
   * 1. x^0 → 1
   * 2. x^1 → x
   * 3. 0^x → 0 (for x > 0)
   * 4. 1^x → 1
   * 5. (a^b)^c → a^(b*c)
   * 6. Numeric evaluation when both base and exponent are numbers
   * 7. Negative exponent: a^(-b) → 1/(a^b)
   *
   * @param config Simplification configuration
   * @return Simplified expression
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplifiedBase = base.simplify(config)
    val simplifiedExponent = exponent.simplify(config)

    (simplifiedBase, simplifiedExponent) match {
      // x^0 → 1 (for any non-zero x)
      case (_, Num(0)) => Num(1)

      // x^1 → x
      case (b, Num(1)) => b

      // 0^x → 0 (for positive x)
      case (Num(0), Num(e)) if e > 0 => Num(0)

      // 1^x → 1
      case (Num(1), _) => Num(1)

      // Numeric: a^b where both are numbers
      case (Num(b), Num(e)) if config.isEnabled(CombineNumericLiterals) =>
        // Only compute if exponent is reasonable
        if (e.abs <= 100 && e == e.toInt) {
          val result = math.pow(b, e)
          if (!result.isNaN && !result.isInfinite) Num(result)
          else Pow(Num(b), Num(e))
        } else if (e.abs <= 10) {
          val result = math.pow(b, e)
          if (!result.isNaN && !result.isInfinite) Num(result)
          else Pow(Num(b), Num(e))
        } else {
          Pow(Num(b), Num(e))
        }

      // (a^b)^c → a^(b*c)
      case (Pow(innerBase, innerExp), outerExp) =>
        val newExponent = Mul(Vector(innerExp, outerExp)).simplify(config)
        Pow(innerBase, newExponent).simplify(config)

      // (a*b)^n → a^n * b^n (if DistributeProduct enabled)
      case (Mul(factors), exp) if config.isEnabled(DistributeProduct) =>
        val poweredFactors = factors.map(f => Pow(f, exp).simplify(config))
        Mul(poweredFactors).simplify(config)

      // Negative exponent: a^(-b) → 1/(a^b)
      case (b, Num(e)) if e < 0 =>
        Div(Vector(Num(1), Pow(b, Num(-e)).simplify(config))).simplify(config)

      // Fractional exponent on numeric: sqrt, etc.
      case (Num(b), Num(e)) if b >= 0 =>
        val result = math.pow(b, e)
        if (!result.isNaN && !result.isInfinite) Num(result)
        else Pow(Num(b), Num(e))

      // No simplification possible
      case _ =>
        Pow(simplifiedBase, simplifiedExponent)
    }
  }

  override def toString: String = {
    val baseStr = if (base.precedence < this.precedence) s"($base)" else base.toString
    val expStr = if (exponent.precedence < this.precedence) s"($exponent)" else exponent.toString
    s"$baseStr^$expStr"
  }
}
