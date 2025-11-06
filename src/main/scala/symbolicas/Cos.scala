package symbolicas

import SimplificationRule._

/* ============================================================================
 * unary composites
 * ========================================================================== */
final case class Cos(expr: Expr) extends Expr {
  override val precedence: Int = 4

  def eval(vars: Map[String, Double]): Double =
    math.cos(expr.eval(vars))

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Cos(expr.replaceSymbol(sym, repl))

  override def expand: Expr = Cos(expr.expand)

  override def expand(implicit config: SimplificationConfig): Expr = Cos(expr.expand(config))

  def simplify(implicit config: SimplificationConfig): Expr = Cos(expr.simplify(config))

  override def toString: String = s"cos($expr)"
}

/* ------------------------------------------------------------------------- */
final case class Neg(expr: Expr) extends Expr {
  override val precedence: Int = 3

  def eval(vars: Map[String, Double]): Double =
    -expr.eval(vars)

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Neg(expr.replaceSymbol(sym, repl))

  override def expand: Expr = Neg(expr.expand).simplify

  override def expand(implicit config: SimplificationConfig): Expr =
    Neg(expr.expand(config)).simplify(config)

  def simplify(implicit config: SimplificationConfig): Expr = {
    val s = expr.simplify(config)
    s match {
      case Num(n, d) => Num(-n, d)
      case Neg(inner) if config.isEnabled(SimplifyDoubleNegative) =>
        inner  // double negative: --x = x
      case Neg(inner) =>
        Neg(inner)  // keep double negative if rule disabled
      case _ => Neg(s)
    }
  }

  override def toString: String =
    s"-${showWithParens(expr, this)}"
}
