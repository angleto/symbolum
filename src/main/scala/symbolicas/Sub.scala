package symbolicas

import scala.Array
import symbolicas.SimplificationConfig

/* ============================================================================
 * n-ary composites - Subtraction
 * ========================================================================== */

final case class Sub(exprs: Array[Expr]) extends Expr {
    override val precedence: Int = 1

    /**
     * Evaluate this subtraction expression numerically.
     * @param vars mapping from variable names to their numeric values
     * @return the numeric difference of all terms
     */
    def eval(vars: Map[String, Double]): Double =
            exprs.map(_.eval(vars)).reduce(_ - _)

    /**
     * Replace all occurrences of a symbol with another expression.
     * @param sym the symbol name to replace
     * @param repl the expression to substitute
     * @return a new Sub expression with substitutions applied
     */
    def replaceSymbol(sym: String, repl:Expr): Expr =
    Sub(exprs.map(_.replaceSymbol(sym, repl)))

    /**
     * Expand this subtraction expression.
     * Converts to addition with negation, then expands.
     *
     * Example: (a - b) → a + (-b)
     *
     * @param config simplification configuration (controls which rules apply)
     * @return expanded expression
     */
    override def expand(implicit config: SimplificationConfig): Expr = {
        // Convert to addition with negation and expand
        if (exprs.isEmpty) Num(0)
        else {
            val head = exprs.head.expand(config)
            val tail = exprs.tail.map(e => Neg(e.expand(config)))
            Add(Array(head) ++ tail).expand(config)
        }
    }

    /**
     * Simplify this subtraction expression.
     * Delegates to Add by converting: a - b - c → a + (-b) + (-c)
     *
     * @param config simplification configuration
     * @return simplified expression
     */
    def simplify(implicit config: SimplificationConfig): Expr =
        if (exprs.isEmpty) Num(0)
        else {
            val head = exprs.head
            val tail = exprs.tail
            Add(Array(head) ++ tail.map(e => Neg(e))).simplify(config)
        }

    override def toString: String =
            exprs.map(_.toString).mkString(" - ")
}
