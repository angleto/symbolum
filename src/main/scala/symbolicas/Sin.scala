package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/**
 * Sine trigonometric function.
 *
 * Represents sin(argument).
 * Supports various trigonometric identities and simplifications.
 *
 * @param argument The expression inside the sine function
 *
 * @example {{{
 *   Sin(Num(0))                    // sin(0) → 0
 *   Sin(Var("x"))                  // sin(x)
 *   Sin(Neg(Var("x")))             // sin(-x) → -sin(x)
 *   Sin(Mul(Vector(Num(2), Var("x"))))  // sin(2x)
 * }}}
 */
final case class Sin(argument: Expr) extends Expr {
  override val precedence: Int = 4

  /**
   * Evaluate sine numerically.
   *
   * @param variables Map of variable names to values
   * @return sin(argument) evaluated numerically
   */
  def eval(variables: Map[String, Double]): Double =
    math.sin(argument.eval(variables))

  /**
   * Apply symbol replacement to the argument.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Sine with replaced argument
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Sin(argument.replaceSymbol(sym, repl))

  /**
   * Expand the sine expression by expanding its argument.
   *
   * @param config Simplification configuration
   * @return Sine with expanded argument
   */
  override def expand(implicit config: SimplificationConfig): Expr =
    Sin(argument.expand(config)).simplify(config)

  /**
   * Simplify the sine expression.
   *
   * Applies trigonometric identities:
   * 1. sin(0) → 0
   * 2. sin(-x) → -sin(x) (odd function)
   * 3. Numeric evaluation for numeric arguments
   * 4. Simplify argument first
   *
   * @param config Simplification configuration
   * @return Simplified expression
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplifiedArg = argument.simplify(config)

    simplifiedArg match {
      // sin(0) = 0
      case Num(0, _) => Num(0)

      // sin(numeric) = evaluate
      case Num(x, _) if config.isEnabled(CombineNumericLiterals) =>
        Num(math.sin(x))

      // sin(-x) = -sin(x) (odd function)
      case Neg(inner) =>
        Neg(Sin(inner).simplify(config)).simplify(config)

      // sin(Sub(...)) with single negative term
      case Sub(Vector(Num(0, _), inner)) =>
        Neg(Sin(inner).simplify(config)).simplify(config)

      // Default: keep as Sin with simplified argument
      case _ =>
        Sin(simplifiedArg)
    }
  }

  override def toString: String = s"sin($argument)"
}
