package symbolicas

import scala.annotation.tailrec
import symbolicas.{SimplificationConfig, SimplificationRule}
import symbolicas.NumericConstants._
import SimplificationRule._

/**
 * Represents a numeric literal with optional fractional representation.
 *
 * Internally stores values as numerator/denominator to preserve exact fractions
 * and avoid floating-point precision issues during symbolic computation.
 *
 * @param numerator the numerator value
 * @param denominator the denominator value (defaults to 1.0 for whole numbers)
 *
 * @example {{{
 * val half = Num(1, 2)        // represents 1/2
 * val three = Num(3)          // represents 3
 * val twoThirds = Num(2, 3)   // represents 2/3
 * }}}
 */
final case class Num(numerator: Double, denominator: Double = 1.0)
  extends Expr {

  override val precedence: Int = 4

  def eval(vars: Map[String, Double]): Double = numerator / denominator

  def replaceSymbol(sym: String, repl: Expr): Expr = this

  /**
   * Simplifies the fraction to lowest terms if SimplifyFractions rule is enabled.
   *
   * Uses GCD to reduce the fraction. For example, 4/6 becomes 2/3.
   *
   * @param config simplification configuration
   * @return simplified numeric expression
   */
  def simplify(implicit config: SimplificationConfig): Num = {
    if (denominator == 1.0) this
    else if (config.isEnabled(SimplifyFractions)) {
      val (simpleNum, simpleDen) = MathUtils.simplifyFraction(numerator, denominator)
      Num(simpleNum, simpleDen)
    } else {
      this
    }
  }

  override def toString: String = {
    if (denominator == 1.0) {
      if (MathUtils.isWhole(numerator))
        s"${numerator.toInt}"
      else
        s"$numerator"
    } else {
      if (MathUtils.isWhole(numerator) && MathUtils.isWhole(denominator))
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
