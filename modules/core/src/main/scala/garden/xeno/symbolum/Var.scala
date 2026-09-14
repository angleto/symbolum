package garden.xeno.symbolum

/**
 * A symbolic variable.
 *
 * @param name the identifier, for example `"x"`, `"n"` or `"pi"`
 *
 * @example {{{
 * val x = Var("x")
 * Add(Vector(x, Num(1))).eval(Map("x" -> 5.0))  // 6.0
 * }}}
 */
final case class Var(name: String) extends Expr {
  require(name.trim.nonEmpty, "Variable name cannot be blank")

  override val precedence: Int = 4

  /**
   * @throws UndefinedVariableError if `variables` has no value for this variable
   */
  def eval(variables: Map[String, Double]): Double =
    variables.getOrElse(name, throw UndefinedVariableError(name, variables.keySet))

  def replaceSymbol(sym: String, repl: Expr): Expr =
    if (name == sym) repl else this

  override def toString: String = name
}
