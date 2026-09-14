package garden.xeno.symbolum

/**
 * Arithmetic negation.
 *
 * Like [[Sub]] this is input sugar: simplification folds it into a `-1` coefficient and no `Neg`
 * node survives, which is why `-(-x)` collapses to `x` without a rule of its own. It previously
 * lived in `Cos.scala`, where nothing about it belonged.
 *
 * @param argument the expression to negate
 */
final case class Neg(argument: Expr) extends Expr {

  override val precedence: Int = 3

  def eval(variables: Map[String, Double]): Double = -argument.eval(variables)

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Neg(argument.replaceSymbol(sym, repl))

  override def toString: String = s"-${showWithParens(argument, this)}"
}
