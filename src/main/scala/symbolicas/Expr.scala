package symbolicas

import scala.annotation.tailrec
import scala.language.implicitConversions
import symbolicas.SimplificationConfig

trait Expr {
  /** Precedence used only for pretty printing */
  def precedence: Int = 10

  /** Evaluate numerically */
  def eval(variables: Map[String, Double]): Double

  /** Replace a given symbol by another expression */
  def replaceSymbol(sym: String, repl: Expr): Expr

  /**
   * Expand – distributes products over sums
   * @param config Simplification configuration controlling which rules to apply (defaults to Default)
   */
  def expand(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr = this

  /**
   * Algebraic simplification (single pass) with configurable rules.
   * @param config Simplification configuration controlling which rules to apply (defaults to Default)
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

      // Apply expand → simplify → simplify again
      val step1 = expr.expand(config)
      val step2 = step1.simplify(config)
      val step3 = step2.simplify(config)  // Double simplify to catch cascading simplifications

      val currentStr = step3.toString

      // Check if we've reached a fixpoint
      if (currentStr == previousStr) {
        step3
      } else {
        loop(step3, iterationsLeft - 1, currentStr)
      }
    }

    // Initial pass: simplify first to normalize the input
    val initial = this.simplify(config)
    loop(initial, maxIter, initial.toString)
  }

  /* -------- helper for pretty printing ------------------------------------ */
  protected def showWithParens(child: Expr, parent: Expr): String =
    if (child.precedence < parent.precedence) s"(${child.toString})"
    else child.toString
}
