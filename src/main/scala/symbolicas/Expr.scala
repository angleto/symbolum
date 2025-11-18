package symbolicas

import scala.annotation.tailrec
import scala.language.implicitConversions
import symbolicas.SimplificationConfig

/**
 * Base trait for all symbolic expressions.
 * Provides core operations: evaluation, symbol replacement, expansion, and simplification.
 */
trait Expr {
  /**
   * Precedence level for pretty printing with parentheses.
   * Lower values bind less tightly (require more parentheses).
   */
  def precedence: Int = 10

  /**
   * Evaluate this expression numerically given variable values.
   * @param variables mapping from variable names to their numeric values
   * @return the numeric result of evaluating this expression
   */
  def eval(variables: Map[String, Double]): Double

  /**
   * Replace all occurrences of a symbol with another expression.
   * @param sym the symbol name to replace
   * @param repl the expression to substitute
   * @return a new expression with substitutions applied
   */
  def replaceSymbol(sym: String, repl: Expr): Expr

  /**
   * Expand this expression by distributing products over sums.
   * Default implementation returns the expression unchanged (identity).
   *
   * @param config Simplification configuration controlling which rules to apply (defaults to Default)
   * @return expanded expression
   */
  def expand(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr = this

  /**
   * Algebraic simplification (single pass) with configurable rules.
   * Each expression type implements its own simplification strategy.
   *
   * @param config Simplification configuration controlling which rules to apply (defaults to Default)
   * @return simplified expression
   */
  def simplify(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr

  /**
   * Full simplification: repeatedly apply expand+simplify until fixpoint.
   * This ensures complete optimization of the expression.
   * @param config Simplification configuration controlling which rules to apply
   * @param maxIter Maximum iterations (default 100)
   */
  def fullSimplify(implicit config: SimplificationConfig = SimplificationConfig.Default,
                   maxIter: Int = 100): Expr = {
    @tailrec
    def loop(expr: Expr, iterationsLeft: Int, previousStr: String): Expr = {
      if (iterationsLeft <= 0) {
        // Safety limit reached - return what we have
        return expr
      }

      // Ultra-aggressive multi-pass for deeply nested expressions:
      // expand → simplify → expand → simplify → expand → simplify → simplify
      // The triple expand ensures distribution of products over sums at all nesting levels
      val step1 = expr.expand(config)
      val step2 = step1.simplify(config)
      val step3 = step2.expand(config)  // Second expand catches newly exposed structure
      val step4 = step3.simplify(config)
      val step5 = step4.expand(config)  // Third expand for deeply nested Mul(Cos(...), Add(...))
      val step6 = step5.simplify(config)
      val step7 = step6.simplify(config)  // Double simplify for cascading effects

      val currentStr = step7.toString

      // Check if we've reached a fixpoint
      if (currentStr == previousStr) {
        step7
      } else {
        loop(step7, iterationsLeft - 1, currentStr)
      }
    }

    // Initial multi-pass to normalize deeply nested input
    val step0 = this.simplify(config)
    val step1 = step0.expand(config)
    val initial = step1.simplify(config)
    loop(initial, maxIter, initial.toString)
  }

  /* -------- helper for pretty printing ------------------------------------ */
  protected def showWithParens(child: Expr, parent: Expr): String =
    if (child.precedence < parent.precedence) s"(${child.toString})"
    else child.toString
}
