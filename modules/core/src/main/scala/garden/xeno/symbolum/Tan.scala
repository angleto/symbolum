package garden.xeno.symbolum

import garden.xeno.symbolum.SimplificationRule._

/**
 * The tangent function.
 *
 * @param argument the angle
 */
final case class Tan(argument: Expr) extends Expr {

  override val precedence: Int = 4

  def eval(variables: Map[String, Double]): Double = math.tan(argument.eval(variables))

  def replaceSymbol(sym: String, repl: Expr): Expr = Tan(argument.replaceSymbol(sym, repl))

  override def toString: String = s"tan($argument)"
}

object Tan {

  /**
   * Simplify `tan(argument)` for an already-simplified argument.
   *
   * Tangent is odd, like sine. It is not rewritten as `sin/cos`: the previous implementation did
   * that whenever [[SimplificationRule.DistributeProduct]] was enabled, which is a rule about
   * products over sums and says nothing about tangent, and the rewrite made `tan(x).expand`
   * return a quotient no caller had asked for.
   */
  private[symbolum] def simplified(argument: Expr)(implicit config: SimplificationConfig): Expr = {
    val (negated, magnitude) = Trigonometry.splitSign(argument)
    val core = magnitude match {
      case n: Num if n.numerator == 0.0 => Num(0)
      case n: Num if config.isEnabled(CombineNumericLiterals) => Num(math.tan(n.value))
      case other => Tan(other)
    }
    if (negated) Canonical.negate(core) else core
  }
}
