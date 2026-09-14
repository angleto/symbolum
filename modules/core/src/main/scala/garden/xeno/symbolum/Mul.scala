package garden.xeno.symbolum

/**
 * An n-ary product.
 *
 * @param factors the factors; at least one
 *
 * @example {{{
 * Mul(Vector(Num(2), Var("x")))              // 2 * x
 * Mul(Vector(Num(2), Div(Vector(Var("n"), Num(4))))).simplify  // n/2
 * }}}
 */
final case class Mul(factors: Vector[Expr]) extends Expr {
  require(factors.nonEmpty, "Multiplication requires at least one factor")

  override val precedence: Int = 2

  def eval(variables: Map[String, Double]): Double =
    factors.foldLeft(1.0)((acc, f) => acc * f.eval(variables))

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Mul(factors.map(_.replaceSymbol(sym, repl)))

  override def toString: String = {
    val rendered = factors.map(f => showWithParens(f, this))
    factors.head match {
      case Num(-1.0, 1.0) if factors.length > 1 => s"-${rendered.tail.mkString(" * ")}"
      case _ => rendered.mkString(" * ")
    }
  }
}
