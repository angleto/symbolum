package symbolicas

import symbolicas.SimplificationConfig

/**
 * Subtraction expression.
 *
 * Represents a chain of subtractions: a - b - c - ...
 * Internally converted to addition with negation during simplification.
 *
 * @param expressions Vector of expressions to subtract (first - rest)
 * @throws IllegalArgumentException if expressions is empty
 *
 * @example {{{
 *   Sub(Vector(a, b))       // a - b
 *   Sub(Vector(a, b, c))    // a - b - c (equivalent to a - b - c)
 * }}}
 *
 * @note This is a convenience class. During simplification, it's converted to:
 *       Sub(Vector(a, b, c)) → Add(Vector(a, Neg(b), Neg(c)))
 */
final case class Sub(expressions: Vector[Expr]) extends Expr {
  require(expressions.nonEmpty, "Subtraction requires at least one operand")

  override val precedence: Int = 1

  /**
   * Evaluates by computing the first element minus all remaining elements.
   *
   * @param variables Map of variable names to values
   * @return Numerical result of a - b - c - ...
   */
  def eval(variables: Map[String, Double]): Double =
    expressions.map(_.eval(variables)).reduce(_ - _)

  /**
   * Applies symbol replacement to all sub-expressions.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Subtraction with replaced sub-expressions
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Sub(expressions.map(_.replaceSymbol(sym, repl)))

  /**
   * Expands by converting to addition with negation.
   *
   * @param config Simplification configuration
   * @return Expanded expression
   *
   * @note Time Complexity: O(n) where n is the number of sub-expressions
   */
  override def expand(implicit config: SimplificationConfig): Expr = {
    if (expressions.isEmpty) Num(0)
    else {
      val head = expressions.head.expand(config)
      val tail = expressions.tail.map(e => Neg(e.expand(config)))
      Add(head +: tail).expand(config)
    }
  }

  /**
   * Simplifies by converting to addition with negation.
   *
   * Transformation: Sub(a, b, c) → Add(a, Neg(b), Neg(c))
   *
   * @param config Simplification configuration
   * @return Simplified expression (typically an Add)
   *
   * @note Time Complexity: O(n) where n is the number of sub-expressions
   */
  def simplify(implicit config: SimplificationConfig): Expr =
    if (expressions.isEmpty) Num(0)
    else {
      val head = expressions.head
      val tail = expressions.tail
      Add(head +: tail.map(e => Neg(e))).simplify(config)
    }

  override def toString: String =
    expressions.map(_.toString).mkString(" - ")
}
