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

  /** Algebraic simplification */
  def simplify: Expr

  /* -------- helper for pretty printing ------------------------------------ */
  protected def showWithParens(child: Expr, parent: Expr): String =
    if (child.precedence < parent.precedence) s"(${child.toString})"
    else child.toString
}
