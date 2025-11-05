package collatz ;

import scala.annotation.tailrec ;
import scala.language.implicitConversions ;

trait Expr {
  /** Precedence used only for pretty printing */
  def precedence: Int = 10

  /** Evaluate numerically */
  def eval(variables: Map[String, Double]): Double

  /** Replace a given symbol by another expression */
  def replaceSymbol(sym: String, repl: Expr): Expr

  /** Expand – currently a stub for future work */
  def expand: Expr = this

  /** Algebraic simplification (single pass) */
  def simplify: Expr

  /**
   * Full simplification: repeatedly apply simplify+expand until fixpoint.
   * This ensures complete optimization of the expression.
   */
  def fullSimplify: Expr = {
    @tailrec
    def loop(expr: Expr, maxIter: Int = 100): Expr = {
      if (maxIter <= 0) return expr // safety limit

      val step1 = expr.simplify
      val step2 = step1.expand
      val step3 = step2.simplify

      // Check if we've reached a fixpoint
      if (step3.toString == expr.toString) {
        step3
      } else {
        loop(step3, maxIter - 1)
      }
    }
    loop(this)
  }

  /* -------- helper for pretty printing ------------------------------------ */
  protected def showWithParens(child: Expr, parent: Expr): String =
    if (child.precedence < parent.precedence) s"(${child.toString})"
    else child.toString
}
