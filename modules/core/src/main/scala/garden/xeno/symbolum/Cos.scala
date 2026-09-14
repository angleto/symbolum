package garden.xeno.symbolum

import garden.xeno.symbolum.SimplificationRule._

/**
 * The cosine function.
 *
 * @param argument the angle
 */
final case class Cos(argument: Expr) extends Expr {

  override val precedence: Int = 4

  def eval(variables: Map[String, Double]): Double = math.cos(argument.eval(variables))

  def replaceSymbol(sym: String, repl: Expr): Expr = Cos(argument.replaceSymbol(sym, repl))

  override def toString: String = s"cos($argument)"
}

object Cos {

  /**
   * Simplify `cos(argument)` for an already-simplified argument.
   *
   * Cosine is even, so a negated argument loses its sign rather than moving it outside as sine's
   * does. The sign comes off before the magnitude is tested for being numeric, so that `cos(-4)`
   * is evaluated in the same pass that removes the sign.
   */
  private[symbolum] def simplified(argument: Expr)(implicit config: SimplificationConfig): Expr =
    Trigonometry.splitSign(argument)._2 match {
      case n: Num if n.numerator == 0.0 => Num(1)
      case n: Num if config.isEnabled(CombineNumericLiterals) => Num(math.cos(n.value))
      case other => Cos(other)
    }
}
