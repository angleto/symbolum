package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/**
 * Exponential function (e^x).
 *
 * Represents exp(argument) = e^argument where e ≈ 2.71828...
 *
 * @param argument The expression in the exponent
 *
 * @example {{{
 *   Exp(Num(0))                    // exp(0) → 1
 *   Exp(Num(1))                    // exp(1) → e ≈ 2.71828
 *   Exp(Log(Var("x")))             // exp(log(x)) → x
 *   Exp(Add(Vector(Var("x"), Var("y"))))  // exp(x+y) → exp(x)*exp(y)
 * }}}
 */
final case class Exp(argument: Expr) extends Expr {
  override val precedence: Int = 4

  /**
   * Evaluate exponential numerically.
   *
   * @param variables Map of variable names to values
   * @return e^argument evaluated numerically
   */
  def eval(variables: Map[String, Double]): Double =
    math.exp(argument.eval(variables))

  /**
   * Apply symbol replacement to the argument.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Exp with replaced argument
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Exp(argument.replaceSymbol(sym, repl))

  /**
   * Expand the exponential expression.
   *
   * Applies: exp(a+b) → exp(a) * exp(b) when DistributeProduct is enabled
   *
   * @param config Simplification configuration
   * @return Expanded expression
   */
  override def expand(implicit config: SimplificationConfig): Expr = {
    val expandedArg = argument.expand(config)

    expandedArg match {
      // exp(a+b) → exp(a) * exp(b)
      case Add(terms) if config.isEnabled(DistributeProduct) && terms.length > 1 =>
        val exponentials = terms.map(t => Exp(t).simplify(config))
        Mul(exponentials).simplify(config)

      // exp(k*x) where k is numeric could be kept as is or expanded
      case _ =>
        Exp(expandedArg).simplify(config)
    }
  }

  /**
   * Simplify the exponential expression.
   *
   * Applies identities:
   * 1. exp(0) → 1
   * 2. exp(1) → e (kept symbolic or numeric based on config)
   * 3. exp(log(x)) → x
   * 4. exp(k*log(x)) → x^k
   * 5. Numeric evaluation for numeric arguments
   *
   * @param config Simplification configuration
   * @return Simplified expression
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplifiedArg = argument.simplify(config)

    simplifiedArg match {
      // exp(0) = 1
      case Num(0) => Num(1)

      // exp(numeric) = evaluate
      case Num(x) if config.isEnabled(CombineNumericLiterals) =>
        Num(math.exp(x))

      // exp(log(x)) = x
      case Log(inner) =>
        inner

      // exp(k * log(x)) = x^k
      case Mul(Vector(Num(k), Log(inner))) =>
        Pow(inner, Num(k)).simplify(config)

      case Mul(Vector(Log(inner), Num(k))) =>
        Pow(inner, Num(k)).simplify(config)

      // Default: keep as Exp with simplified argument
      case _ =>
        Exp(simplifiedArg)
    }
  }

  override def toString: String = s"exp($argument)"
}
