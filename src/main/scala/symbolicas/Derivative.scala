package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/**
 * Symbolic derivative with respect to a variable.
 *
 * Represents d/dx of an expression.
 * Implements automatic differentiation using calculus rules.
 *
 * @param expression The expression to differentiate
 * @param variable The variable to differentiate with respect to
 *
 * @example {{{
 *   Derivative(Var("x"), "x")                      // d/dx(x) → 1
 *   Derivative(Pow(Var("x"), Num(2)), "x")         // d/dx(x^2) → 2*x
 *   Derivative(Sin(Var("x")), "x")                 // d/dx(sin(x)) → cos(x)
 *   Derivative(Mul(Vector(Var("x"), Var("y"))), "x")  // d/dx(x*y) → y
 * }}}
 */
final case class Derivative(expression: Expr, variable: String) extends Expr {
  override val precedence: Int = 4

  /**
   * Evaluate by differentiating and then evaluating the result.
   *
   * @param variables Map of variable names to values
   * @return Derivative evaluated numerically
   */
  def eval(variables: Map[String, Double]): Double =
    this.simplify().eval(variables)

  /**
   * Apply symbol replacement to the expression.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Derivative with replaced expression
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Derivative(expression.replaceSymbol(sym, repl), variable)

  /**
   * Expand the derivative by expanding the expression first.
   *
   * @param config Simplification configuration
   * @return Derivative of expanded expression
   */
  override def expand(implicit config: SimplificationConfig): Expr =
    Derivative(expression.expand(config), variable).simplify(config)

  /**
   * Compute the derivative using differentiation rules.
   *
   * Implements standard calculus rules:
   * - Constant rule: d/dx(c) = 0
   * - Power rule: d/dx(x^n) = n*x^(n-1)
   * - Sum rule: d/dx(f+g) = f' + g'
   * - Product rule: d/dx(f*g) = f'*g + f*g'
   * - Quotient rule: d/dx(f/g) = (f'*g - f*g')/g^2
   * - Chain rule: d/dx(f(g(x))) = f'(g(x)) * g'(x)
   * - Trig rules: d/dx(sin(x)) = cos(x), d/dx(cos(x)) = -sin(x), etc.
   * - Exp/Log rules: d/dx(exp(x)) = exp(x), d/dx(log(x)) = 1/x
   *
   * @param config Simplification configuration
   * @return Derivative computed symbolically
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplifiedExpr = expression.simplify(config)

    simplifiedExpr match{
      // Constant rule: d/dx(c) = 0
      case Num(_, _) => Num(0)

      // Variable rules
      case Var(name) if name == variable => Num(1)  // d/dx(x) = 1
      case Var(_) => Num(0)  // d/dx(y) = 0 (different variable)

      // Sum rule: d/dx(f + g) = f' + g'
      case Add(terms) =>
        val derivatives = terms.map(t => Derivative(t, variable).simplify(config))
        Add(derivatives).simplify(config)

      // Difference rule: d/dx(f - g) = f' - g'
      case Sub(terms) =>
        val derivatives = terms.map(t => Derivative(t, variable).simplify(config))
        Sub(derivatives).simplify(config)

      // Product rule: d/dx(f * g) = f' * g + f * g'
      case Mul(factors) if factors.length == 2 =>
        val f = factors(0)
        val g = factors(1)
        val fPrime = Derivative(f, variable).simplify(config)
        val gPrime = Derivative(g, variable).simplify(config)
        Add(Vector(
          Mul(Vector(fPrime, g)),
          Mul(Vector(f, gPrime))
        )).simplify(config)

      // Product rule for multiple factors: use product rule recursively
      case Mul(factors) if factors.length > 2 =>
        val first = factors.head
        val rest = Mul(factors.tail)
        Derivative(Mul(Vector(first, rest)), variable).simplify(config)

      // Constant multiple rule: d/dx(c * f) = c * f' (if c doesn't depend on variable)
      case Mul(Vector(c: Num, f)) =>
        Mul(Vector(c, Derivative(f, variable).simplify(config))).simplify(config)

      // Quotient rule: d/dx(f / g) = (f' * g - f * g') / g^2
      case Div(Vector(numerator, denominator)) =>
        val fPrime = Derivative(numerator, variable).simplify(config)
        val gPrime = Derivative(denominator, variable).simplify(config)
        Div(Vector(
          Sub(Vector(
            Mul(Vector(fPrime, denominator)),
            Mul(Vector(numerator, gPrime))
          )).simplify(config),
          Pow(denominator, Num(2)).simplify(config)
        )).simplify(config)

      // Power rule: d/dx(f^n) = n * f^(n-1) * f' (chain rule)
      case Pow(base, exponent) =>
        // General case: d/dx(f^g) = f^g * (g' * log(f) + g * f'/f)
        // Special case when exponent is constant: d/dx(f^n) = n * f^(n-1) * f'
        exponent match {
          case Num(_, _) =>
            // Exponent is constant with respect to variable
            val basePrime = Derivative(base, variable).simplify(config)
            Mul(Vector(
              exponent,
              Pow(base, Sub(Vector(exponent, Num(1))).simplify(config)).simplify(config),
              basePrime
            )).simplify(config)

          case Var(v) if v != variable =>
            // Exponent is constant with respect to variable
            val basePrime = Derivative(base, variable).simplify(config)
            Mul(Vector(
              exponent,
              Pow(base, Sub(Vector(exponent, Num(1))).simplify(config)).simplify(config),
              basePrime
            )).simplify(config)

          case _ =>
            // General power rule: d/dx(f^g) = f^g * (g' * log(f) + g * f'/f)
            val f = base
            val g = exponent
            val fPrime = Derivative(f, variable).simplify(config)
            val gPrime = Derivative(g, variable).simplify(config)
            Mul(Vector(
              Pow(f, g),
              Add(Vector(
                Mul(Vector(gPrime, Log(f))),
                Mul(Vector(g, Div(Vector(fPrime, f))))
              ))
            )).simplify(config)
        }

      // Negation: d/dx(-f) = -f'
      case Neg(inner) =>
        Neg(Derivative(inner, variable).simplify(config)).simplify(config)

      // Trigonometric functions
      case Sin(arg) =>
        // d/dx(sin(f)) = cos(f) * f'
        val argPrime = Derivative(arg, variable).simplify(config)
        Mul(Vector(Cos(arg), argPrime)).simplify(config)

      case Cos(arg) =>
        // d/dx(cos(f)) = -sin(f) * f'
        val argPrime = Derivative(arg, variable).simplify(config)
        Mul(Vector(Num(-1), Sin(arg), argPrime)).simplify(config)

      case Tan(arg) =>
        // d/dx(tan(f)) = sec^2(f) * f' = f' / cos^2(f)
        val argPrime = Derivative(arg, variable).simplify(config)
        Div(Vector(
          argPrime,
          Pow(Cos(arg), Num(2)).simplify(config)
        )).simplify(config)

      // Exponential and logarithm
      case Exp(arg) =>
        // d/dx(exp(f)) = exp(f) * f'
        val argPrime = Derivative(arg, variable).simplify(config)
        Mul(Vector(Exp(arg), argPrime)).simplify(config)

      case Log(arg) =>
        // d/dx(log(f)) = f' / f
        val argPrime = Derivative(arg, variable).simplify(config)
        Div(Vector(argPrime, arg)).simplify(config)

      // If we encounter another Derivative, just keep it
      case Derivative(_, _) =>
        this

      // Unknown expression type: keep as symbolic derivative
      case _ =>
        Derivative(simplifiedExpr, variable)
    }
  }

  override def toString: String = s"d/d$variable($expression)"
}

/**
 * Companion object with utility functions for differentiation.
 */
object Derivative {
  /**
   * Differentiate an expression with respect to a variable.
   *
   * @param expr Expression to differentiate
   * @param variable Variable to differentiate with respect to
   * @param config Simplification configuration
   * @return Derivative computed and simplified
   */
  def apply(expr: Expr, variable: String)(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr = {
    new Derivative(expr, variable).simplify(config)
  }

  /**
   * Compute nth derivative.
   *
   * @param expr Expression to differentiate
   * @param variable Variable to differentiate with respect to
   * @param n Number of times to differentiate
   * @param config Simplification configuration
   * @return nth derivative
   */
  def nth(expr: Expr, variable: String, n: Int)(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr = {
    require(n >= 0, s"n must be non-negative, got $n")
    if (n == 0) expr
    else nth(Derivative(expr, variable).simplify(config), variable, n - 1)(config)
  }
}
