package garden.xeno.symbolum

import scala.annotation.tailrec

/**
 * Exact arithmetic on rational numbers held as a numerator/denominator pair of `Double`s.
 *
 * This is the single home for fraction arithmetic in the library: [[Num]] stores the pair and
 * every operation that combines two numeric literals goes through here.
 *
 * == Representation ==
 *
 * A pair is ''normalised'' when it satisfies exactly one of:
 *  - `(v, 1.0)` where `v` is any finite double: the inexact regime, used for the irrational
 *    results of `sin`, `exp` and friends;
 *  - `(p, q)` with `q > 1`, both whole and coprime: the exact regime.
 *
 * Zero always normalises to `(0.0, 1.0)` and the sign always lives in the numerator.
 *
 * Normalising at construction is what makes structural equality on expressions usable: `2/4` and
 * `1/2` are one value and must be one object, otherwise like-term collection and fixpoint
 * detection silently miss matches. That was the defect this type was introduced to remove.
 *
 * == Exactness limit ==
 *
 * A double represents integers exactly up to 2^53. Beyond that a whole double is no longer
 * reliably the integer it prints as, so an operation whose numerator or denominator would leave
 * [[ExactLimit]] falls back to the inexact regime and keeps a plain quotient: the result stays
 * correct to within double precision but stops being exact. `BigInt` was rejected because [[Num]]
 * must also carry irrational values, which no integer pair can hold; a two-regime `Double` pair
 * covers both without a second numeric type.
 *
 * What this does not cover: overflow is silent, so a computation that repeatedly multiplies
 * denominators degrades to floating point without saying so.
 */
object Rational {

  /** Largest magnitude at which a `Double` still represents every integer exactly (2^53). */
  final val ExactLimit: Double = 9007199254740992.0

  /** A fraction as a (numerator, denominator) pair. */
  type Fraction = (Double, Double)

  /** True if `d` is a finite whole number. */
  def isWhole(d: Double): Boolean = d.isFinite && d % 1.0 == 0.0

  /** True if the pair can be handled by exact integer arithmetic. */
  def isExact(numerator: Double, denominator: Double): Boolean =
    isWhole(numerator) && isWhole(denominator) &&
      math.abs(numerator) <= ExactLimit && math.abs(denominator) <= ExactLimit

  /**
   * Greatest common divisor of two whole doubles, by the Euclidean algorithm.
   *
   * `%` on whole doubles below [[ExactLimit]] is exact, so no tolerance is needed here. An
   * earlier version compared against 1e-10, which made `gcd` disagree with itself for values a
   * hair away from an integer.
   */
  @tailrec
  def gcd(a: Double, b: Double): Double =
    if (b == 0.0) math.abs(a) else gcd(b, a % b)

  /** Least common multiple of two whole doubles. Zero with either operand zero. */
  def lcm(a: Double, b: Double): Double =
    if (a == 0.0 || b == 0.0) 0.0 else math.abs(a / gcd(a, b) * b)

  /**
   * Reduce a fraction to the normalised representation described above.
   *
   * @throws IllegalArgumentException if the denominator is zero
   */
  def normalize(numerator: Double, denominator: Double): Fraction = {
    require(denominator != 0.0, "denominator must not be zero")
    if (!isExact(numerator, denominator)) {
      val quotient = numerator / denominator
      // Collapse -0.0: it compares equal to 0.0 but hashes differently, and these pairs are used
      // as map keys when like terms are grouped.
      (if (quotient == 0.0) 0.0 else quotient, 1.0)
    }
    else if (numerator == 0.0) (0.0, 1.0)
    else {
      val sign = if (denominator < 0.0) -1.0 else 1.0
      val n = sign * numerator
      val d = sign * denominator
      val g = gcd(n, d)
      (n / g, d / g)
    }
  }

  /** Numeric value of a fraction. */
  def value(f: Fraction): Double = f._1 / f._2

  /**
   * Sum of two fractions.
   *
   * Scaling to the least common multiple rather than to the product of the denominators keeps
   * the intermediate numerator small, which is what keeps repeated sums inside [[ExactLimit]].
   */
  def add(a: Fraction, b: Fraction): Fraction =
    if (!isExact(a._1, a._2) || !isExact(b._1, b._2)) (value(a) + value(b), 1.0)
    else {
      val d = lcm(a._2, b._2)
      normalize(a._1 * (d / a._2) + b._1 * (d / b._2), d)
    }

  /**
   * Product of two fractions.
   *
   * Cross-cancelling before multiplying keeps both parts small for the same reason as [[add]].
   */
  def multiply(a: Fraction, b: Fraction): Fraction =
    if (!isExact(a._1, a._2) || !isExact(b._1, b._2)) (value(a) * value(b), 1.0)
    else {
      val g1 = gcd(a._1, b._2)
      val g2 = gcd(b._1, a._2)
      normalize((a._1 / g1) * (b._1 / g2), (a._2 / g2) * (b._2 / g1))
    }

  /**
   * Quotient of two fractions.
   *
   * @throws DivisionByZeroError if the divisor is zero
   */
  def divide(a: Fraction, b: Fraction): Fraction = {
    if (b._1 == 0.0) throw DivisionByZeroError(s"${a._1}/${a._2} divided by zero")
    multiply(a, (b._2, b._1))
  }

  /**
   * Raise a fraction to an integer power, exactly where possible.
   *
   * Returns `None` when the result would leave the exact regime, so the caller can decide
   * between a floating-point approximation and leaving the power symbolic.
   */
  def power(a: Fraction, exponent: Int): Option[Fraction] = {
    if (!isExact(a._1, a._2)) None
    else if (exponent == 0) Some((1.0, 1.0))
    else {
      val n = math.pow(a._1, math.abs(exponent).toDouble)
      val d = math.pow(a._2, math.abs(exponent).toDouble)
      if (!isExact(n, d)) None
      else if (exponent > 0) Some(normalize(n, d))
      else if (n == 0.0) throw DivisionByZeroError(s"zero raised to $exponent")
      else Some(normalize(d, n))
    }
  }
}
