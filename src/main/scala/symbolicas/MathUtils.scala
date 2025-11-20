package symbolicas

import scala.annotation.tailrec

/**
 * Mathematical utility functions used across the symbolic algebra system.
 *
 * Provides common mathematical operations like GCD, LCM, and fraction manipulation
 * that are shared by multiple expression types.
 */
object MathUtils {

  /**
   * Check if a double value represents a whole number.
   *
   * @param d the value to check
   * @return true if d is a whole number (no fractional part)
   */
  def isWhole(d: Double): Boolean = (d % 1.0) == 0.0

  /**
   * Compute the greatest common divisor of two integers.
   *
   * @param a first integer
   * @param b second integer
   * @return GCD of a and b
   */
  @tailrec
  def gcdInt(a: Int, b: Int): Int = {
    if (b == 0) a.abs else gcdInt(b, a % b)
  }

  /**
   * Compute the greatest common divisor of two doubles.
   * Intended for use with integers stored as doubles.
   *
   * @param a first value
   * @param b second value
   * @return GCD of a and b
   */
  @tailrec
  def gcdDouble(a: Double, b: Double): Double = {
    val tolerance = 1e-10
    if (math.abs(b) < tolerance) math.abs(a)
    else gcdDouble(b, a % b)
  }

  /**
   * Compute the least common multiple of two integers.
   *
   * @param a first integer
   * @param b second integer
   * @return LCM of a and b
   */
  def lcmInt(a: Int, b: Int): Int = {
    if (a == 0 || b == 0) 0
    else (a / gcdInt(a, b)) * b
  }

  /**
   * Compute the least common multiple of two doubles.
   * Intended for use with integers stored as doubles.
   *
   * @param a first value
   * @param b second value
   * @return LCM of a and b
   */
  def lcmDouble(a: Double, b: Double): Double = {
    if (a == 0.0 || b == 0.0) 0.0
    else math.abs(a * b) / gcdDouble(a, b)
  }

  /**
   * Add two fractions represented as (numerator, denominator) pairs.
   *
   * Formula: a/b + c/d = (a*d + b*c) / (b*d)
   *
   * @param a first fraction (numerator, denominator)
   * @param b second fraction (numerator, denominator)
   * @return resulting fraction (numerator, denominator)
   */
  def addFractions(a: (Double, Double), b: (Double, Double)): (Double, Double) = {
    val (aN, aD) = a
    val (bN, bD) = b
    val newNum = aN * bD + bN * aD
    val newDen = aD * bD
    (newNum, newDen)
  }

  /**
   * Multiply two fractions represented as (numerator, denominator) pairs.
   *
   * Formula: (a/b) * (c/d) = (a*c) / (b*d)
   *
   * @param a first fraction (numerator, denominator)
   * @param b second fraction (numerator, denominator)
   * @return resulting fraction (numerator, denominator)
   */
  def multiplyFractions(a: (Double, Double), b: (Double, Double)): (Double, Double) = {
    val (aN, aD) = a
    val (bN, bD) = b
    (aN * bN, aD * bD)
  }

  /**
   * Divide two fractions represented as (numerator, denominator) pairs.
   *
   * Formula: (a/b) / (c/d) = (a*d) / (b*c)
   *
   * @param a first fraction (numerator, denominator)
   * @param b second fraction (numerator, denominator)
   * @return resulting fraction (numerator, denominator)
   */
  def divideFractions(a: (Double, Double), b: (Double, Double)): (Double, Double) = {
    val (aN, aD) = a
    val (bN, bD) = b
    (aN * bD, aD * bN)
  }

  /**
   * Simplify a fraction by dividing both numerator and denominator by their GCD.
   *
   * @param numerator the numerator
   * @param denominator the denominator
   * @return simplified fraction (numerator, denominator)
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
