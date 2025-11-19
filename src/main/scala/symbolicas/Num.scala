package symbolicas

import scala.annotation.tailrec
import symbolicas.{SimplificationConfig, SimplificationRule}
import symbolicas.NumericConstants._
import SimplificationRule._

/**
 * Numeric literal expression with fraction support.
 *
 * Represents a rational number as numerator/denominator.
 * Both values are stored as doubles but are typically integer values.
 *
 * @param numerator The numerator of the fraction
 * @param denominator The denominator of the fraction (must be non-zero)
 *
 * @throws IllegalArgumentException if denominator is zero, NaN, or infinite
 * @throws IllegalArgumentException if numerator is NaN or infinite
 *
 * @example {{{
 *   Num(3)        // Represents 3
 *   Num(1, 2)     // Represents 1/2
 *   Num(4, 6)     // Can be simplified to 2/3
 * }}}
 */
final case class Num(numerator: Double, denominator: Double = 1.0) extends Expr {
  require(!numerator.isNaN, s"Numerator cannot be NaN")
  require(!numerator.isInfinity, s"Numerator cannot be infinite")
  require(!denominator.isNaN, s"Denominator cannot be NaN")
  require(!denominator.isInfinity, s"Denominator cannot be infinite")
  require(denominator != 0.0, s"Denominator cannot be zero")

  override val precedence: Int = 4

  def eval(vars: Map[String, Double]): Double = numerator / denominator

  def replaceSymbol(sym: String, repl: Expr): Expr = this

  /**
   * Simplifies this numeric fraction by dividing by GCD.
   *
   * @param config Simplification configuration
   * @return Simplified Num with reduced fraction
   *
   * @note Time Complexity: O(log(min(n, d))) where n is numerator, d is denominator
   * @note Space Complexity: O(1)
   */
  def simplify(implicit config: SimplificationConfig): Num = {
    if (denominator == 1.0) this
    else if (config.isEnabled(SimplifyFractions)) {
      val g = Num.gcd(numerator, denominator)
      Num(numerator / g, denominator / g)
    } else {
      this
    }
  }

  override def toString: String = {
    if (denominator == 1.0) {
      if (Num.isWhole(numerator))
        s"${numerator.toInt}"
      else
        s"$numerator"
    } else {
      if (Num.isWhole(numerator) && Num.isWhole(denominator))
        s"${numerator.toInt}/${denominator.toInt}"
      else
        s"$numerator/$denominator"
    }
  }
}

/**
 * Companion object with fraction arithmetic utilities.
 *
 * Consolidates all numeric operations on fractions to avoid code duplication.
 */
object Num {

  /**
   * Computes the greatest common divisor using Euclidean algorithm.
   *
   * @param a First number
   * @param b Second number
   * @return GCD of a and b
   *
   * @note Time Complexity: O(log(min(a, b)))
   * @note Thread-safe (pure function)
   */
  def gcd(a: Double, b: Double): Double = {
    @tailrec
    def loop(x: Double, y: Double): Double =
      if (math.abs(y) < TOLERANCE) x
      else loop(y, x % y)

    loop(math.abs(a), math.abs(b))
  }

  /**
   * Computes the least common multiple.
   *
   * @param a First number
   * @param b Second number
   * @return LCM of a and b
   *
   * @note Time Complexity: O(log(min(a, b)))
   */
  def lcm(a: Double, b: Double): Double = {
    if (a == 0.0 || b == 0.0) 0.0
    else math.abs(a * b) / gcd(a, b)
  }

  /**
   * Adds two fractions: a/b + c/d = (ad + bc) / bd
   *
   * @param a First fraction
   * @param b Second fraction
   * @return Sum as a new Num (not simplified)
   *
   * @example {{{
   *   Num.addFractions(Num(1, 2), Num(1, 3)) // Returns Num(5, 6)
   * }}}
   */
  def addFractions(a: Num, b: Num): Num = {
    val newNumerator = a.numerator * b.denominator + b.numerator * a.denominator
    val newDenominator = a.denominator * b.denominator
    Num(newNumerator, newDenominator)
  }

  /**
   * Multiplies two fractions: (a/b) * (c/d) = (ac) / (bd)
   *
   * @param a First fraction
   * @param b Second fraction
   * @return Product as a new Num (not simplified)
   */
  def multiplyFractions(a: Num, b: Num): Num = {
    val newNumerator = a.numerator * b.numerator
    val newDenominator = a.denominator * b.denominator
    Num(newNumerator, newDenominator)
  }

  /**
   * Divides two fractions: (a/b) / (c/d) = (ad) / (bc)
   *
   * @param a First fraction (dividend)
   * @param b Second fraction (divisor)
   * @return Quotient as a new Num (not simplified)
   * @throws IllegalArgumentException if divisor numerator is zero
   */
  def divideFractions(a: Num, b: Num): Num = {
    require(b.numerator != 0.0, "Cannot divide by zero")
    val newNumerator = a.numerator * b.denominator
    val newDenominator = a.denominator * b.numerator
    Num(newNumerator, newDenominator)
  }

  /**
   * Checks if a double represents a whole number.
   *
   * @param d The number to check
   * @return true if d is within TOLERANCE of an integer
   *
   * @example {{{
   *   Num.isWhole(3.0)           // true
   *   Num.isWhole(3.0000000001)  // true (within tolerance)
   *   Num.isWhole(3.5)           // false
   * }}}
   */
  def isWhole(d: Double): Boolean =
    math.abs(d % 1.0) < TOLERANCE

  /**
   * Creates a Num from an integer.
   *
   * @param n The integer value
   * @return Num representing the integer
   */
  def apply(n: Int): Num = Num(n.toDouble, 1.0)

  /**
   * Creates a Num from a long.
   *
   * @param n The long value
   * @return Num representing the long
   */
  def apply(n: Long): Num = Num(n.toDouble, 1.0)
}
