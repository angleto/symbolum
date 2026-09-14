package garden.xeno.symbolum

/**
 * A chain of subtractions, read left to right: `a - b - c`.
 *
 * This is input sugar. Simplification rewrites it as a sum with negated terms and no `Sub` node
 * survives, so every rule about sums applies to it without a second set of cases.
 *
 * @param expressions the minuend followed by its subtrahends; at least one
 */
final case class Sub(expressions: Vector[Expr]) extends Expr {
  require(expressions.nonEmpty, "Subtraction requires at least one operand")

  override val precedence: Int = 1

  def eval(variables: Map[String, Double]): Double =
    expressions.map(_.eval(variables)).reduceLeft(_ - _)

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Sub(expressions.map(_.replaceSymbol(sym, repl)))

  override def toString: String =
    expressions.map(e => showWithParens(e, this)).mkString(" - ")
}
