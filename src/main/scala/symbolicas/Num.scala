package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
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