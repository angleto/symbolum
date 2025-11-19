package symbolicas

import scala.annotation.tailrec
import scala.language.implicitConversions
import symbolicas.SimplificationConfig
import symbolicas.NumericConstants._

/**
 * Base trait for all symbolic expressions.
 *
 * This is a sealed trait, meaning all implementations must be in this file or package.
 * This enables exhaustive pattern matching with compiler verification.
 *
 * All expressions are immutable and support the following operations:
 * - eval: Numerical evaluation with variable substitution
 * - simplify: Single-pass algebraic simplification
 * - expand: Distribution of products over sums
 * - fullSimplify: Iterative simplification to fixpoint
 * - replaceSymbol: Symbol substitution
 *
 * @note Thread Safety: All expressions are immutable and thread-safe.
 * @note Implementations: Add, Mul, Div, Sub, Num, Var, Cos, Neg
 */
sealed trait Expr {
  /** Precedence used only for pretty printing */
  def precedence: Int = 10

  /**
   * Evaluate numerically.
   *
   * @param variables Map of variable names to their numerical values
   * @return Numerical result of evaluation
   * @throws ExpressionError if a required variable is undefined or if division by zero occurs
   */
  def eval(variables: Map[String, Double]): Double

  /**
   * Replace a given symbol by another expression.
   *
   * @param sym Symbol name to replace
   * @param repl Replacement expression
   * @return New expression with symbol replaced
   */
  def replaceSymbol(sym: String, repl: Expr): Expr

  /**
   * Expand – distributes products over sums.
   *
   * @param config Simplification configuration controlling which rules to apply (defaults to Default)
   * @return Expanded expression
   *
   * @note Time Complexity: O(n) for most expressions, O(k^n) for cartesian product expansion
   */
  def expand(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr = this

  /**
   * Algebraic simplification (single pass) with configurable rules.
   *
   * @param config Simplification configuration controlling which rules to apply (defaults to Default)
   * @return Simplified expression
   *
   * @note Time Complexity: Varies by expression type, typically O(n) to O(n log n)
   */
  def simplify(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr

  /**
   * Full simplification: repeatedly apply expand+simplify until fixpoint.
   * This ensures complete optimization of the expression.
   *
   * @param config Simplification configuration controlling which rules to apply
   * @param maxIter Maximum iterations (default from NumericConstants.MAX_ITERATIONS)
   * @return Fully simplified expression
   *
   * @note Time Complexity: O(k * f(n)) where k is iterations to fixpoint, f(n) is simplify cost
   * @note Guaranteed to terminate due to maxIter limit
   */
  def fullSimplify(implicit config: SimplificationConfig = SimplificationConfig.Default,
                   maxIter: Int = MAX_ITERATIONS): Expr = {
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
