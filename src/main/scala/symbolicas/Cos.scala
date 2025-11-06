package symbolicas ;

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

  def simplify: Expr = Cos(expr.simplify)

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

  def simplify: Expr = {
    val s = expr.simplify
    s match {
      case Num(n, d) => Num(-n, d)
      case Neg(inner) => inner  // double negative: --x = x
      case _ => Neg(s)
    }
  }

  override def toString: String =
    s"-${showWithParens(expr, this)}"
}
