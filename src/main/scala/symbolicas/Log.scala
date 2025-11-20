package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/**
 * Natural logarithm function (ln(x)).
 *
 * Represents log(argument) = ln(argument) - natural logarithm (base e).
 *
 * @param argument The expression inside the logarithm (must be positive)
 *
 * @example {{{
 *   Log(Num(1))                    // log(1) → 0
 *   Log(Var("x"))                  // log(x)
 *   Log(Exp(Var("x")))             // log(exp(x)) → x
 *   Log(Mul(Vector(Var("x"), Var("y"))))  // log(x*y) → log(x) + log(y)
 * }}}
 */
final case class Log(argument: Expr) extends Expr {
  override val precedence: Int = 4

  /**
   * Evaluate logarithm numerically.
   *
   * @param variables Map of variable names to values
   * @return ln(argument) evaluated numerically
   * @throws ArithmeticException if argument ≤ 0
   */
  def eval(variables: Map[String, Double]): Double = {
    val value = argument.eval(variables)
    if (value <= 0) throw new ArithmeticException(s"Logarithm of non-positive number: $value")
    math.log(value)
  }

  /**
   * Apply symbol replacement to the argument.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Log with replaced argument
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Log(argument.replaceSymbol(sym, repl))

  /**
   * Expand the logarithm expression.
   *
   * Applies logarithm laws:
   * - log(a*b) → log(a) + log(b)
   * - log(a/b) → log(a) - log(b)
   * - log(a^b) → b*log(a)
   *
   * @param config Simplification configuration
   * @return Expanded expression
   */
  override def expand(implicit config: SimplificationConfig): Expr = {
    val expandedArg = argument.expand(config)

    expandedArg match {
      // log(a*b) → log(a) + log(b)
      case Mul(factors) if config.isEnabled(DistributeProduct) && factors.length > 1 =>
        val logTerms = factors.map(f => Log(f).simplify(config))
        Add(logTerms).simplify(config)

      // log(a/b) → log(a) - log(b)
      case Div(Vector(numerator, denominator)) if config.isEnabled(DistributeProduct) =>
        Sub(Vector(Log(numerator).simplify(config), Log(denominator).simplify(config))).simplify(config)

      // log(a^b) → b*log(a)
      case Pow(base, exponent) =>
        Mul(Vector(exponent, Log(base).simplify(config))).simplify(config)

      // Default: keep as Log with expanded argument
      case _ =>
        Log(expandedArg).simplify(config)
    }
  }

  /**
   * Simplify the logarithm expression.
   *
   * Applies identities:
   * 1. log(1) → 0
   * 2. log(e) → 1
   * 3. log(exp(x)) → x
   * 4. log(x^k) → k*log(x)
   * 5. Numeric evaluation for numeric arguments
   *
   * @param config Simplification configuration
   * @return Simplified expression
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplifiedArg = argument.simplify(config)

    simplifiedArg match {
      // log(1) = 0
      case Num(1) => Num(0)

      // log(e) = 1 (where e ≈ 2.71828)
      case Num(x) if math.abs(x - math.E) < 1e-10 => Num(1)

      // log(numeric) = evaluate (only for positive numbers)
      case Num(x) if x > 0 && config.isEnabled(CombineNumericLiterals) =>
        Num(math.log(x))

      // log(exp(x)) = x
      case Exp(inner) =>
        inner

      // log(x^k) = k*log(x)
      case Pow(base, exponent) =>
        Mul(Vector(exponent, Log(base).simplify(config))).simplify(config)

      // Default: keep as Log with simplified argument
      case _ =>
        Log(simplifiedArg)
    }
  }

  override def toString: String = s"log($argument)"
}
