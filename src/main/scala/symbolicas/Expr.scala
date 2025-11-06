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
   * Full simplification: repeatedly apply simplify+expand until fixpoint.
   * This ensures complete optimization of the expression.
   * @param config Simplification configuration controlling which rules to apply
   * @param maxIter Maximum iterations (default 100)
   */
  def fullSimplify(implicit config: SimplificationConfig = SimplificationConfig.Default,
                   maxIter: Int = 100): Expr = {
    @tailrec
    def loop(expr: Expr, iterationsLeft: Int): Expr = {
      if (iterationsLeft <= 0) return expr // safety limit

      val step1 = expr.simplify(config)
      val step2 = step1.expand(config)
      val step3 = step2.simplify(config)

      // Check if we've reached a fixpoint
      if (step3.toString == expr.toString) {
        step3
      } else {
        loop(step3, iterationsLeft - 1)
      }
    }
    loop(this, maxIter)
  }

  /* -------- helper for pretty printing ------------------------------------ */
  protected def showWithParens(child: Expr, parent: Expr): String =
    if (child.precedence < parent.precedence) s"(${child.toString})"
    else child.toString
}
