package garden.xeno.symbolum

/**
 * An integral that has not been taken yet, definite when both bounds are present.
 *
 * Simplifying the node attempts the antiderivative; where no rule applies the node survives.
 * Only the elementary rules are implemented: this is not a general integrator, and no
 * Risch-style algorithm is attempted.
 *
 * @param expression the integrand
 * @param variable   the variable of integration
 * @param lowerBound lower limit, for a definite integral
 * @param upperBound upper limit, for a definite integral
 *
 * @example {{{
 * Integral(Var("x"), "x").simplify                                 // x^2/2
 * Integral(Var("x"), "x", Some(Num(0)), Some(Num(1))).simplify     // 1/2
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
   * Evaluate a definite integral numerically, by Simpson's rule.
   *
   * @throws UnsupportedOperationException for an indefinite integral, which has no single value
   */
  def eval(variables: Map[String, Double]): Double =
    (lowerBound, upperBound) match {
      case (Some(low), Some(high)) =>
        Integral.simpson(expression, variable, low.eval(variables), high.eval(variables), variables)
      case _ =>
        throw new UnsupportedOperationException("Cannot numerically evaluate indefinite integral")
    }

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Integral(
      expression.replaceSymbol(sym, repl),
      variable,
      lowerBound.map(_.replaceSymbol(sym, repl)),
      upperBound.map(_.replaceSymbol(sym, repl))
    )

  override def toString: String = {
    val bounds = (lowerBound, upperBound) match {
      case (Some(low), Some(high)) => s"[$low,$high]"
      case _ => ""
    }
    s"∫$bounds $expression d$variable"
  }
}

object Integral {

  /** Panels used by [[simpson]]; even, and enough for the smooth integrands this handles. */
  private val SimpsonPanels: Int = 1000

  /**
   * Integrate `expression`, applying the fundamental theorem of calculus when bounds are given.
   *
   * An integrand no rule covers comes back as an unevaluated [[Integral]] rather than as a
   * failure.
   */
  def integrate(expression: Expr, variable: String,
                lowerBound: Option[Expr], upperBound: Option[Expr])
               (implicit config: SimplificationConfig): Expr = {
    val integrand = expression.simplify(config)

    (antiderivative(integrand, variable), lowerBound, upperBound) match {
      case (Some(primitive), Some(low), Some(high)) =>
        Canonical.sum(Vector(
          primitive.replaceSymbol(variable, high).simplify(config),
          Canonical.negate(primitive.replaceSymbol(variable, low).simplify(config))
        ))

      case (Some(primitive), None, None) =>
        primitive

      case _ =>
        Integral(integrand, variable, lowerBound, upperBound)
    }
  }

  /**
   * The antiderivative of `e` with respect to `variable`, or `None` where no rule applies.
   *
   * Covers constants, the power rule including its `x^-1` exception, sums, constant multiples and
   * the elementary transcendental functions.
   */
  private def antiderivative(e: Expr, variable: String)
                            (implicit config: SimplificationConfig): Option[Expr] = {
    val x = Var(variable)

    e match {
      case n: Num if n.numerator == 0.0 => Some(Num(0))
      case n: Num => Some(Canonical.product(Vector(n, x)))

      case Var(name) if name == variable =>
        Some(Canonical.quotient(Canonical.power(x, Num(2)), Num(2)))

      case Var(_) => Some(Canonical.product(Vector(e, x)))

      case Add(terms) =>
        val parts = terms.map(antiderivative(_, variable))
        if (parts.forall(_.isDefined)) Some(Canonical.sum(parts.map(_.get))) else None

      // A constant multiple, recognised through the canonical form rather than through a
      // hand-written `Mul(Vector(c, f))` pattern that only ever matched a two-factor product.
      case Mul(_) =>
        val (coefficient, base) = Canonical.splitCoefficient(e)
        if (coefficient == Num(1)) None
        else antiderivative(base, variable).map(p => Canonical.product(Vector(coefficient, p)))

      case Pow(Var(name), exponent: Num) if name == variable && exponent.value != -1.0 =>
        val raised = Canonical.sum(Vector(exponent, Num(1)))
        Some(Canonical.quotient(Canonical.power(x, raised), raised))

      // 1/x, which the canonical form spells as a quotient rather than as x^-1.
      case Div(Vector(numerator: Num, Var(name)))
        if name == variable && numerator.value == 1.0 => Some(Log(x))

      case Sin(Var(name)) if name == variable => Some(Canonical.negate(Cos(x)))
      case Cos(Var(name)) if name == variable => Some(Sin(x))
      case Exp(Var(name)) if name == variable => Some(Exp(x))

      case _ => None
    }
  }

  /**
   * Composite Simpson's rule over [[SimpsonPanels]] panels.
   *
   * Fixed rather than adaptive: the integrands reachable here are elementary and smooth, and an
   * adaptive scheme would add a tolerance parameter to the public surface for no accuracy that
   * matters at this panel count.
   */
  private def simpson(expression: Expr, variable: String, low: Double, high: Double,
                      variables: Map[String, Double]): Double = {
    def f(x: Double): Double = expression.eval(variables + (variable -> x))

    val width = (high - low) / SimpsonPanels
    val interior = (1 until SimpsonPanels).map { i =>
      val weight = if (i % 2 == 0) 2.0 else 4.0
      weight * f(low + i * width)
    }.sum
    width / 3.0 * (f(low) + interior + f(high))
  }

  /** The indefinite integral of `expr`. */
  def indefinite(expr: Expr, variable: String)
                (implicit config: SimplificationConfig = SimplificationConfig.Default): Expr =
    integrate(expr, variable, None, None)(config)

  /** The definite integral of `expr` between the given bounds. */
  def definite(expr: Expr, variable: String, lowerBound: Expr, upperBound: Expr)
              (implicit config: SimplificationConfig = SimplificationConfig.Default): Expr =
    integrate(expr, variable, Some(lowerBound), Some(upperBound))(config)
}
