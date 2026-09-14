package garden.xeno.symbolum

/**
 * A derivative that has not been taken yet.
 *
 * Simplifying the node differentiates it; where no rule applies the node survives, so an
 * expression can carry an unevaluated derivative without the simplifier failing.
 *
 * @param expression the integrand of the differentiation
 * @param variable   the variable to differentiate with respect to
 *
 * @example {{{
 * Derivative(Pow(Var("x"), Num(2)), "x").simplify  // 2 * x
 * Derivative(Sin(Var("x")), "x").simplify          // cos(x)
 * }}}
 */
final case class Derivative(expression: Expr, variable: String) extends Expr {

  override val precedence: Int = 4

  def eval(variables: Map[String, Double]): Double =
    Derivative.differentiate(expression, variable)(SimplificationConfig.Default).eval(variables)

  def replaceSymbol(sym: String, repl: Expr): Expr =
    new Derivative(expression.replaceSymbol(sym, repl), variable)

  override def toString: String = s"d/d$variable($expression)"
}

object Derivative {

  /**
   * Differentiate `expression` with respect to `variable`.
   *
   * Implements the constant, power, sum, product, quotient and chain rules together with the
   * derivatives of the trigonometric, exponential and logarithmic functions. An expression no rule
   * covers comes back as an unevaluated [[Derivative]] rather than as a failure.
   */
  def differentiate(expression: Expr, variable: String)
                   (implicit config: SimplificationConfig): Expr = {
    val simplified = expression.simplify(config)

    def d(e: Expr): Expr = differentiate(e, variable)(config)

    simplified match {
      case _: Num => Num(0)

      case Var(name) => if (name == variable) Num(1) else Num(0)

      case Add(terms) =>
        Canonical.sum(terms.map(d))

      // Product rule, applied to the head against the rest so that any arity is covered by one
      // case rather than by one case per arity.
      case Mul(factors) =>
        val head = factors.head
        val rest = if (factors.length == 2) factors(1) else Mul(factors.tail)
        Canonical.sum(Vector(
          Canonical.product(Vector(d(head), rest)),
          Canonical.product(Vector(head, d(rest)))
        ))

      case Div(Vector(numerator, denominator)) =>
        Canonical.quotient(
          Canonical.sum(Vector(
            Canonical.product(Vector(d(numerator), denominator)),
            Canonical.negate(Canonical.product(Vector(numerator, d(denominator))))
          )),
          Canonical.power(denominator, Num(2))
        )

      case Pow(base, exponent) if !Symbols.contains(exponent, variable) =>
        // d/dx f^n = n * f^(n-1) * f'
        Canonical.product(Vector(
          exponent,
          Canonical.power(base, Canonical.sum(Vector(exponent, Num(-1)))),
          d(base)
        ))

      case Pow(base, exponent) =>
        // d/dx f^g = f^g * (g' * log f + g * f'/f)
        Canonical.product(Vector(
          Pow(base, exponent),
          Canonical.sum(Vector(
            Canonical.product(Vector(d(exponent), Log(base))),
            Canonical.product(Vector(exponent, Canonical.quotient(d(base), base)))
          ))
        ))

      case Sin(argument) =>
        Canonical.product(Vector(Cos(argument), d(argument)))

      case Cos(argument) =>
        Canonical.negate(Canonical.product(Vector(Sin(argument), d(argument))))

      case Tan(argument) =>
        Canonical.quotient(d(argument), Canonical.power(Cos(argument), Num(2)))

      case Exp(argument) =>
        Canonical.product(Vector(Exp(argument), d(argument)))

      case Log(argument) =>
        Canonical.quotient(d(argument), argument)

      // `new` rather than the companion `apply`, which differentiates: building the node through
      // it here would call straight back into this function.
      case other => new Derivative(other, variable)
    }
  }

  /** Differentiate and simplify in one step. */
  def apply(expr: Expr, variable: String)
           (implicit config: SimplificationConfig = SimplificationConfig.Default): Expr =
    differentiate(expr, variable)(config)

  /**
   * The `n`th derivative with respect to `variable`.
   *
   * @throws IllegalArgumentException if `n` is negative
   */
  def nth(expr: Expr, variable: String, n: Int)
         (implicit config: SimplificationConfig = SimplificationConfig.Default): Expr = {
    require(n >= 0, s"n must be non-negative, got $n")
    if (n == 0) expr else nth(differentiate(expr, variable)(config), variable, n - 1)(config)
  }
}
