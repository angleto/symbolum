package symbolicas

import symbolicas.SimplificationConfig

/**
 * Variable expression.
 *
 * Represents a symbolic variable such as 'x', 'n', 'pi', etc.
 *
 * @param name The name of the variable
 * @throws IllegalArgumentException if name is empty or contains only whitespace
 *
 * @example {{{
 *   Var("x")    // Variable x
 *   Var("n")    // Variable n
 *   Var("pi")   // Constant pi (conventionally)
 * }}}
 */
final case class Var(name: String) extends Expr {
  require(name.nonEmpty, "Variable name cannot be empty")
  require(name.trim.nonEmpty, "Variable name cannot be only whitespace")

  override val precedence: Int = 4

  /**
   * Evaluates the variable by looking up its value in the variable map.
   *
   * @param variables Map of variable names to values
   * @return The numeric value assigned to this variable
   * @throws UndefinedVariableError if the variable is not defined in the map
   */
  def eval(variables: Map[String, Double]): Double =
    variables.getOrElse(name,
      throw UndefinedVariableError(name, variables.keySet)
    )

  /**
   * Replaces this variable if its name matches the target symbol.
   *
   * @param sym Symbol name to replace
   * @param repl Replacement expression
   * @return The replacement expression if name matches sym, otherwise this variable
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    if (name == sym) repl else this

  /**
   * Variables are already in simplest form.
   *
   * @param config Simplification configuration (unused for variables)
   * @return This variable unchanged
   */
  def simplify(implicit config: SimplificationConfig): Var = this

  override def toString: String = name
}
