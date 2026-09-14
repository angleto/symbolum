package garden.xeno.symbolum

import garden.xeno.symbolum.SimplificationRule._

/**
 * The sine function.
 *
 * @param argument the angle
 */
final case class Sin(argument: Expr) extends Expr {

  override val precedence: Int = 4

  def eval(variables: Map[String, Double]): Double = math.sin(argument.eval(variables))

  def replaceSymbol(sym: String, repl: Expr): Expr = Sin(argument.replaceSymbol(sym, repl))

  override def toString: String = s"sin($argument)"
}

object Sin {

  /**
   * Simplify `sin(argument)` for an already-simplified argument.
   *
   * `sin(0) = 0` and `sin(-x) = -sin(x)` hold for every argument. Evaluating a numeric argument
   * leaves the exact rationals behind, so it is tied to
   * [[SimplificationRule.CombineNumericLiterals]] like every other numeric fold.
   */
  private[symbolum] def simplified(argument: Expr)(implicit config: SimplificationConfig): Expr = {
    // The sign comes off first so that the magnitude is tested for being numeric afterwards.
    // Testing before, as an earlier version did, left sin(-4) as sin(4) negated but unevaluated,
    // and the next pass evaluated it: simplification that is not idempotent.
    val (negated, magnitude) = Trigonometry.splitSign(argument)
    val core = magnitude match {
      case n: Num if n.numerator == 0.0 => Num(0)
      case n: Num if config.isEnabled(CombineNumericLiterals) => Num(math.sin(n.value))
      case other => Sin(other)
    }
    if (negated) Canonical.negate(core) else core
  }
}
