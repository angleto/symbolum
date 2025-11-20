package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/**
 * Tangent trigonometric function.
 *
 * Represents tan(argument) = sin(argument) / cos(argument).
 * Supports various trigonometric identities and simplifications.
 *
 * @param argument The expression inside the tangent function
 *
 * @example {{{
 *   Tan(Num(0))                    // tan(0) → 0
 *   Tan(Var("x"))                  // tan(x)
 *   Tan(Neg(Var("x")))             // tan(-x) → -tan(x)
 * }}}
 */
final case class Tan(argument: Expr) extends Expr {
  override val precedence: Int = 4

  /**
   * Evaluate tangent numerically.
   *
   * @param variables Map of variable names to values
   * @return tan(argument) evaluated numerically
   */
  def eval(variables: Map[String, Double]): Double =
    math.tan(argument.eval(variables))

  /**
   * Apply symbol replacement to the argument.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Tangent with replaced argument
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Tan(argument.replaceSymbol(sym, repl))

  /**
   * Expand the tangent expression.
   *
   * Can optionally expand tan(x) as sin(x)/cos(x) when DistributeProduct is enabled.
   *
   * @param config Simplification configuration
   * @return Expanded expression
   */
  override def expand(implicit config: SimplificationConfig): Expr = {
    val expandedArg = argument.expand(config)

    // Optionally expand tan(x) → sin(x)/cos(x)
    if (config.isEnabled(DistributeProduct)) {
      Div(Vector(Sin(expandedArg), Cos(expandedArg))).simplify(config)
    } else {
      Tan(expandedArg).simplify(config)
    }
  }

  /**
   * Simplify the tangent expression.
   *
   * Applies trigonometric identities:
   * 1. tan(0) → 0
   * 2. tan(-x) → -tan(x) (odd function)
   * 3. Numeric evaluation for numeric arguments
   * 4. Simplify argument first
   *
   * @param config Simplification configuration
   * @return Simplified expression
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplifiedArg = argument.simplify(config)

    simplifiedArg match {
      // tan(0) = 0
      case Num(0, _) => Num(0)

      // tan(numeric) = evaluate
      case Num(x, _) if config.isEnabled(CombineNumericLiterals) =>
        Num(math.tan(x))

      // tan(-x) = -tan(x) (odd function)
      case Neg(inner) =>
        Neg(Tan(inner).simplify(config)).simplify(config)

      // tan(Sub(...)) with single negative term
      case Sub(Vector(Num(0, _), inner)) =>
        Neg(Tan(inner).simplify(config)).simplify(config)

      // Default: keep as Tan with simplified argument
      case _ =>
        Tan(simplifiedArg)
    }
  }

  override def toString: String = s"tan($argument)"
}
