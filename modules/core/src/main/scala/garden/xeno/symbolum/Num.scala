package garden.xeno.symbolum

/**
 * A numeric literal, held as a fraction.
 *
 * Every instance is normalised by [[Rational]] at construction, so `Num(6, 8)` and `Num(3, 4)` are
 * the same object and `Num(3, -4)` carries its sign in the numerator. Two literals of equal value
 * are therefore equal, which is what lets the simplifier group like terms by structural equality
 * instead of by an approximate comparison that had to be tuned per call site.
 *
 * Construction goes through the companion; there is no public constructor, because a `Num` that
 * skipped normalisation would compare unequal to its own reduced form and quietly defeat term
 * collection.
 *
 * @param numerator   normalised numerator, carrying the sign
 * @param denominator normalised denominator, always positive
 *
 * @example {{{
 * Num(1, 2)   // 1/2
 * Num(3)      // 3
 * Num(6, 8)   // 3/4
 * Num(0.5)    // 0.5, held inexactly with denominator 1
 * }}}
 */
final class Num private (val numerator: Double, val denominator: Double) extends Expr {

  override val precedence: Int = 4

  /** This literal as a fraction pair, for [[Rational]]. */
  def fraction: Rational.Fraction = (numerator, denominator)

  /** This literal as a plain double. */
  def value: Double = numerator / denominator

  def eval(variables: Map[String, Double]): Double = value

  def replaceSymbol(sym: String, repl: Expr): Expr = this

  override def equals(other: Any): Boolean = other match {
    case that: Num => numerator == that.numerator && denominator == that.denominator
    case _ => false
  }

  override def hashCode(): Int =
    31 * java.lang.Double.hashCode(numerator) + java.lang.Double.hashCode(denominator)

  override def toString: String = {
    def show(d: Double): String = if (Rational.isWhole(d)) d.toLong.toString else d.toString
    if (denominator == 1.0) show(numerator) else s"${show(numerator)}/${show(denominator)}"
  }
}

object Num {

  /**
   * A literal for `numerator / denominator`, reduced to lowest terms.
   *
   * @throws IllegalArgumentException if the denominator is zero
   */
  def apply(numerator: Double, denominator: Double): Num = {
    val (n, d) = Rational.normalize(numerator, denominator)
    new Num(n, d)
  }

  /** A literal for a plain value. */
  def apply(value: Double): Num = apply(value, 1.0)

  /** A literal for a whole number. */
  def apply(value: Int): Num = apply(value.toDouble, 1.0)

  /** A literal for a whole number. */
  def apply(value: Long): Num = apply(value.toDouble, 1.0)

  /** A literal from a [[Rational]] fraction pair. */
  def fromFraction(f: Rational.Fraction): Num = apply(f._1, f._2)

  def unapply(n: Num): Option[(Double, Double)] = Some((n.numerator, n.denominator))
}
