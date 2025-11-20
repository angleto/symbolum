package symbolicas

import symbolicas.SimplificationConfig

/**
 * Represents a symbolic variable in algebraic expressions.
 *
 * Variables are atomic expressions that stand for unknown or parameterized values.
 * They can be evaluated numerically by providing a value mapping, or manipulated
 * symbolically through algebraic operations.
 *
 * Variables cannot be simplified further - they are already in simplest form.
 *
 * @param name the variable identifier (e.g., "x", "n", "alpha")
 *
 * @example {{{
 * val x = Var("x")
 * val expr = Add(Array(x, Num(1)))  // represents: x + 1
 *
 * // Evaluate with x = 5
 * expr.eval(Map("x" -> 5.0))  // returns 6.0
 *
 * // Substitute x with another expression
 * val y = Var("y")
 * expr.replaceSymbol("x", Mul(Array(Num(2), y)))  // returns: 2*y + 1
 * }}}
 */
final case class Var(name: String) extends Expr {
  require(name.nonEmpty, "Variable name cannot be empty")
  require(name.trim.nonEmpty, "Variable name cannot be only whitespace")

    /**
     * Evaluate this variable numerically.
     *
     * @param vars map from variable names to values
     * @return the numeric value assigned to this variable
     * @throws Exception if this variable is not defined in the map
     */
    def eval(vars: Map[String, Double]): Double =
            vars.getOrElse(name,
            throw new Exception(s"Variable $name not defined")
    )

    /**
     * Replace this variable if it matches the given symbol.
     *
     * @param sym the variable name to replace
     * @param repl the replacement expression
     * @return `repl` if this variable's name matches `sym`, otherwise `this`
     */
    def replaceSymbol(sym: String, repl: Expr): Expr =
            if (name == sym) repl else this

    /**
     * Simplify this variable.
     *
     * Variables are already in simplest form, so this returns the variable unchanged.
     *
     * @param config simplification configuration (ignored for variables)
     * @return this variable
     */
    def simplify(implicit config: SimplificationConfig): Var = this

  override def toString: String = name
}
