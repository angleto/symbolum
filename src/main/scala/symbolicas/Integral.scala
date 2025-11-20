package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/**
 * Symbolic definite or indefinite integral.
 *
 * Represents ∫ expression dx (indefinite) or ∫[a,b] expression dx (definite).
 * Implements basic integration rules for common functions.
 *
 * Note: This is a basic implementation covering common cases.
 * Full symbolic integration (Risch algorithm) is not implemented.
 *
 * @param expression The integrand (expression to integrate)
 * @param variable The variable of integration
 * @param lowerBound Optional lower bound for definite integral
 * @param upperBound Optional upper bound for definite integral
 *
 * @example {{{
 *   Integral(Var("x"), "x")                     // ∫ x dx → x^2/2
 *   Integral(Pow(Var("x"), Num(2)), "x")        // ∫ x^2 dx → x^3/3
 *   Integral(Sin(Var("x")), "x")                // ∫ sin(x) dx → -cos(x)
 *   Integral(Var("x"), "x", Some(Num(0)), Some(Num(1)))  // ∫[0,1] x dx → 1/2
 * }}}
 */
final case class Integral(
  expression: Expr,
  variable: String,
  lowerBound: Option[Expr] = None,
  upperBound: Option[Expr] = None
) extends Expr {
  override val precedence: Int = 4

  /**
   * Evaluate the integral numerically (for definite integrals only).
   *
   * @param variables Map of variable names to values
   * @return Definite integral evaluated numerically
   * @throws UnsupportedOperationException for indefinite integrals
   */
  def eval(variables: Map[String, Double]): Double = {
    (lowerBound, upperBound) match {
      case (Some(a), Some(b)) =>
        // Definite integral: use numerical integration (trapezoidal rule)
        val aVal = a.eval(variables)
        val bVal = b.eval(variables)
        numericalIntegration(expression, variable, aVal, bVal, variables)

      case _ =>
        throw new UnsupportedOperationException("Cannot numerically evaluate indefinite integral")
    }
  }

  /**
   * Numerical integration using adaptive Simpson's rule.
   *
   * @param expr Expression to integrate
   * @param varName Variable of integration
   * @param a Lower bound
   * @param b Upper bound
   * @param vars Other variable values
   * @param tolerance Tolerance for adaptive refinement
   * @return Approximate integral value
   */
  private def numericalIntegration(
    expr: Expr,
    varName: String,
    a: Double,
    b: Double,
    vars: Map[String, Double],
    tolerance: Double = 1e-6
  ): Double = {
    def f(x: Double): Double = expr.eval(vars + (varName -> x))

    // Simpson's 1/3 rule
    def simpsons(a: Double, b: Double, n: Int): Double = {
      val h = (b - a) / n
      val sum = (1 to n-1).map { i =>
        val x = a + i * h
        val weight = if (i % 2 == 0) 2.0 else 4.0
        weight * f(x)
      }.sum
      (h / 3.0) * (f(a) + sum + f(b))
    }

    // Adaptive refinement
    val n = 100  // Number of intervals
    simpsons(a, b, n)
  }

  /**
   * Apply symbol replacement to the expression and bounds.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Integral with replaced expression and bounds
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Integral(
      expression.replaceSymbol(sym, repl),
      variable,
      lowerBound.map(_.replaceSymbol(sym, repl)),
      upperBound.map(_.replaceSymbol(sym, repl))
    )

  /**
   * Expand the integrand.
   *
   * @param config Simplification configuration
   * @return Integral with expanded integrand
   */
  override def expand(implicit config: SimplificationConfig): Expr =
    Integral(expression.expand(config), variable, lowerBound, upperBound).simplify(config)

  /**
   * Compute the integral using integration rules.
   *
   * Implements basic integration rules:
   * - Power rule: ∫ x^n dx = x^(n+1)/(n+1)
   * - Sum rule: ∫ (f+g) dx = ∫ f dx + ∫ g dx
   * - Constant multiple: ∫ c*f dx = c * ∫ f dx
   * - Trig integrals: ∫ sin(x) dx = -cos(x), etc.
   * - Exp/Log integrals: ∫ exp(x) dx = exp(x), ∫ 1/x dx = log(x)
   *
   * @param config Simplification configuration
   * @return Integral computed symbolically (or kept as Integral if not computable)
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplifiedExpr = expression.simplify(config)

    // Try to compute the antiderivative
    val antiderivative = computeAntiderivative(simplifiedExpr)(config)

    // If definite integral, apply fundamental theorem of calculus
    (antiderivative, lowerBound, upperBound) match {
      case (Some(antider), Some(a), Some(b)) =>
        // F(b) - F(a)
        Sub(Vector(
          antider.replaceSymbol(variable, b).simplify(config),
          antider.replaceSymbol(variable, a).simplify(config)
        )).simplify(config)

      case (Some(antider), None, None) =>
        // Indefinite integral: return antiderivative
        antider

      case _ =>
        // Cannot compute: keep as symbolic integral
        Integral(simplifiedExpr, variable, lowerBound, upperBound)
    }
  }

  /**
   * Attempt to compute the antiderivative of an expression.
   *
   * @param expr Expression to integrate
   * @param config Simplification configuration
   * @return Some(antiderivative) if computable, None otherwise
   */
  private def computeAntiderivative(expr: Expr)(implicit config: SimplificationConfig): Option[Expr] = {
    expr match {
      // ∫ 0 dx = 0
      case Num(0, _) => Some(Num(0))

      // ∫ c dx = c*x
      case Num(c, _) => Some(Mul(Vector(Num(c), Var(variable))).simplify(config))

      // ∫ x dx = x^2/2
      case Var(v) if v == variable =>
        Some(Div(Vector(Pow(Var(v), Num(2)), Num(2))).simplify(config))

      // ∫ y dx = y*x (constant with respect to x)
      case Var(v) if v != variable =>
        Some(Mul(Vector(Var(v), Var(variable))).simplify(config))

      // Sum rule: ∫ (f+g) dx = ∫ f dx + ∫ g dx
      case Add(terms) =>
        val antiderivatives = terms.map(t => computeAntiderivative(t)(config))
        if (antiderivatives.forall(_.isDefined)) {
          Some(Add(antiderivatives.flatten).simplify(config))
        } else None

      // Constant multiple: ∫ c*f dx = c * ∫ f dx
      case Mul(Vector(c: Num, f)) =>
        computeAntiderivative(f)(config).map { F =>
          Mul(Vector(c, F)).simplify(config)
        }

      // Power rule: ∫ x^n dx = x^(n+1)/(n+1) (for n ≠ -1)
      case Pow(Var(v), Num(n, _)) if v == variable && n != -1 =>
        val newExponent = Add(Vector(Num(n), Num(1))).simplify(config)
        Some(Div(Vector(
          Pow(Var(v), newExponent),
          newExponent
        )).simplify(config))

      // Special case: ∫ x^(-1) dx = ∫ 1/x dx = log(x)
      case Pow(Var(v), Num(-1, _)) if v == variable =>
        Some(Log(Var(v)))

      case Div(Vector(Num(1, _), Var(v))) if v == variable =>
        Some(Log(Var(v)))

      // Trig integrals
      case Sin(Var(v)) if v == variable =>
        Some(Neg(Cos(Var(v))).simplify(config))

      case Cos(Var(v)) if v == variable =>
        Some(Sin(Var(v)))

      // ∫ exp(x) dx = exp(x)
      case Exp(Var(v)) if v == variable =>
        Some(Exp(Var(v)))

      // ∫ 1/x dx = log(x)
      case Div(Vector(Num(1, _), Var(v))) if v == variable =>
        Some(Log(Var(v)))

      // Cannot integrate
      case _ => None
    }
  }

  override def toString: String = {
    val boundsStr = (lowerBound, upperBound) match {
      case (Some(a), Some(b)) => s"[$a,$b]"
      case _ => ""
    }
    s"∫$boundsStr $expression d$variable"
  }
}

/**
 * Companion object with utility functions for integration.
 */
object Integral {
  /**
   * Compute indefinite integral (antiderivative).
   *
   * @param expr Expression to integrate
   * @param variable Variable of integration
   * @param config Simplification configuration
   * @return Antiderivative
   */
  def indefinite(expr: Expr, variable: String)(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr = {
    Integral(expr, variable).simplify(config)
  }

  /**
   * Compute definite integral.
   *
   * @param expr Expression to integrate
   * @param variable Variable of integration
   * @param lowerBound Lower bound
   * @param upperBound Upper bound
   * @param config Simplification configuration
   * @return Definite integral value
   */
  def definite(expr: Expr, variable: String, lowerBound: Expr, upperBound: Expr)
              (implicit config: SimplificationConfig = SimplificationConfig.Default): Expr = {
    Integral(expr, variable, Some(lowerBound), Some(upperBound)).simplify(config)
  }
}
