package symbolicas

import scala.annotation.tailrec

/**
 * Common mathematical utilities for symbolic expression manipulation.
 * Centralizes shared arithmetic operations to avoid code duplication.
 */
object MathUtils {

  /**
   * Check if a double value represents a whole number.
   * @param d the value to check
   * @return true if d is a whole number (no fractional part)
   */
  def isWhole(d: Double): Boolean = (d % 1.0) == 0.0

  /**
   * Compute the greatest common divisor of two integers.
   * @param a first integer
   * @param b second integer
   * @return the GCD of a and b
   */
  @tailrec
  def gcd(a: Int, b: Int): Int =
    if (b == 0) a.abs else gcd(b, a % b)

  /**
   * Compute the greatest common divisor of two doubles.
   * Assumes the doubles represent integer values.
   * @param a first value
   * @param b second value
   * @return the GCD of a and b
   */
  @tailrec
  def gcdDouble(a: Double, b: Double): Double = {
    val tolerance = 1e-10
    if (math.abs(b) < tolerance) math.abs(a)
    else gcdDouble(b, a % b)
  }

  /**
   * Compute the least common multiple of two integers.
   * @param a first integer
   * @param b second integer
   * @return the LCM of a and b
   */
  def lcm(a: Int, b: Int): Int =
    if (a == 0 || b == 0) 0
    else (a / gcd(a, b)) * b

  /**
   * Compute the least common multiple of two doubles.
   * Assumes the doubles represent integer values.
   * @param a first value
   * @param b second value
   * @return the LCM of a and b
   */
  def lcmDouble(a: Double, b: Double): Double =
    if (a == 0.0 || b == 0.0) 0.0
    else math.abs(a * b) / gcdDouble(a, b)

  /**
   * Add two fractions represented as Num objects.
   * Implements: a/b + c/d = (ad + bc) / bd
   * @param a first fraction
   * @param b second fraction
   * @return the sum as a new Num
   */
  def addFractions(a: Num, b: Num): Num = {
    val newNum = a.numerator * b.denominator + b.numerator * a.denominator
    val newDen = a.denominator * b.denominator
    Num(newNum, newDen)
  }

  /**
   * Multiply two fractions represented as Num objects.
   * Implements: (a/b) * (c/d) = (ac) / (bd)
   * @param a first fraction
   * @param b second fraction
   * @return the product as a new Num
   */
  def multiplyFractions(a: Num, b: Num): Num = {
    val newNum = a.numerator * b.numerator
    val newDen = a.denominator * b.denominator
    Num(newNum, newDen)
  }

  /**
   * Divide two fractions represented as Num objects.
   * Implements: (a/b) / (c/d) = (ad) / (bc)
   * @param a first fraction (dividend)
   * @param b second fraction (divisor)
   * @return the quotient as a new Num
   */
  def divideFractions(a: Num, b: Num): Num = {
    val newNum = a.numerator * b.denominator
    val newDen = a.denominator * b.numerator
    Num(newNum, newDen)
  }

  /**
   * Simplify a fraction by dividing both numerator and denominator by their GCD.
   * @param numerator the numerator
   * @param denominator the denominator
   * @return a tuple (simplified_numerator, simplified_denominator)
   */
  def simplifyFraction(numerator: Double, denominator: Double): (Double, Double) = {
    if (denominator == 1.0) {
      (numerator, denominator)
    } else {
      val g = gcdDouble(numerator, denominator)
      (numerator / g, denominator / g)
    }
  }
}
