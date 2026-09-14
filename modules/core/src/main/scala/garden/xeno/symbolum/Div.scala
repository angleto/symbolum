package garden.xeno.symbolum

/**
 * A chain of divisions, read left to right: `a / b / c`.
 *
 * Simplification reassociates it into a single quotient, `a / (b * c)`.
 *
 * @param operands the dividend followed by its divisors; at least two
 *
 * @example {{{
 * Div(Vector(Num(6), Num(2)))                       // 6/2, simplifies to 3
 * Div(Vector(Var("n"), Num(2), Num(4), Num(8)))     // n/2/4/8, simplifies to n/64
 * }}}
 */
final case class Div(operands: Vector[Expr]) extends Expr {
  require(operands.length >= 2,
    s"Division requires at least 2 operands (dividend and divisor), got ${operands.length}")

  override val precedence: Int = 2

  /**
   * @throws DivisionByZeroError if any divisor evaluates to zero
   */
  def eval(variables: Map[String, Double]): Double =
    operands.map(_.eval(variables)).reduceLeft { (dividend, divisor) =>
      if (divisor == 0.0) throw DivisionByZeroError(this.toString)
      dividend / divisor
    }

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Div(operands.map(_.replaceSymbol(sym, repl)))

  override def toString: String = {
    def render(e: Expr, parenthesiseAtSamePrecedence: Boolean): String = {
      val needsParens =
        if (parenthesiseAtSamePrecedence) e.precedence <= precedence else e.precedence < precedence
      if (needsParens) s"($e)" else e.toString
    }
    operands match {
      case Vector(numerator, denominator) =>
        s"${render(numerator, false)}/${render(denominator, true)}"
      case _ =>
        operands.map(e => showWithParens(e, this)).mkString(" / ")
    }
  }
}
