package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule, MathUtils}
import SimplificationRule._

final case class Num(numerator: Double, denominator: Double = 1.0)
  extends Expr {

  override val precedence: Int = 4

  def eval(vars: Map[String, Double]): Double = numerator / denominator

  def replaceSymbol(sym: String, repl: Expr): Expr = this

  /**
   * Simplify this numeric literal by reducing the fraction to lowest terms.
   * Uses GCD to eliminate common factors from numerator and denominator.
   *
   * Examples:
   *   - Num(6, 9) → Num(2, 3)
   *   - Num(4, 2) → Num(2, 1)
   *   - Num(5, 1) → Num(5, 1) (already simplified)
   */
  def simplify(implicit config: SimplificationConfig): Num = {
    if (denominator == 1.0) this
    else if (config.isEnabled(SimplifyFractions)) {
      val (simplifiedNum, simplifiedDen) = MathUtils.simplifyFraction(numerator, denominator)
      Num(simplifiedNum, simplifiedDen)
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