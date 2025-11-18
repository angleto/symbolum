package symbolicas

import symbolicas.SimplificationConfig

/* ============================================================================
 * Atomic expressions - Variables
 * ========================================================================== */
final case class Var(name: String) extends Expr {
    override val precedence: Int = 4

    /**
     * Evaluate this variable by looking up its value.
     * @param vars mapping from variable names to their numeric values
     * @return the numeric value associated with this variable
     * @throws Exception if the variable is not defined in the map
     */
    def eval(vars: Map[String, Double]): Double =
            vars.getOrElse(name,
            throw new Exception(s"Variable $name not defined")
    )

    /**
     * Replace this variable if it matches the given symbol.
     * @param sym the symbol name to replace
     * @param repl the expression to substitute
     * @return the replacement expression if name matches sym, otherwise this
     */
    def replaceSymbol(sym: String, repl:Expr): Expr =
            if (name == sym) repl else this

    /**
     * Simplify this variable (identity operation).
     * Variables cannot be simplified further.
     * @param config simplification configuration (unused)
     * @return this variable unchanged
     */
    def simplify(implicit config: SimplificationConfig): Var = this

    override def toString: String = name
}

