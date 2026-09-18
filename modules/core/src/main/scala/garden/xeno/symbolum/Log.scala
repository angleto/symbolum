package garden.xeno.symbolum

import garden.xeno.symbolum.NumericConstants._
import garden.xeno.symbolum.SimplificationRule._

/**
 * The natural logarithm.
 *
 * @param argument the argument, which must be positive at evaluation time
 */
final case class Log(argument: Expr) extends Expr {

  override val precedence: Int = 4

  /**
   * @throws java.lang.ArithmeticException if the argument evaluates to a non-positive value
   */
  def eval(variables: Map[String, Double]): Double = {
    val value = argument.eval(variables)
    if (value <= 0.0) throw new ArithmeticException(s"Logarithm of non-positive number: $value")
    math.log(value)
  }

  def replaceSymbol(sym: String, repl: Expr): Expr = Log(argument.replaceSymbol(sym, repl))

  override def toString: String = s"log($argument)"
}

object Log {

  /**
   * Simplify `log(argument)` for an already-simplified argument.
   *
   * Splitting a logarithm over a product, a quotient or a power is an expansion, gated on
   * [[SimplificationRule.ExpandLogarithms]]. It is off by default because `log(a*b) = log a + log
   * b` does not hold over the reals when a factor is negative, so applying it unasked would turn
   * a defined expression into an undefined one.
   */
  private[symbolum] def simplified(argument: Expr)(implicit config: SimplificationConfig): Expr =
    argument match {
      case n: Num if n.value == 1.0 => Num(0)
      case n: Num if math.abs(n.value - math.E) < TOLERANCE => Num(1)
      case n: Num if n.value > 0.0 && config.isEnabled(CombineNumericLiterals) => Num(math.log(n.value))

      case Exp(inner) => inner

      case Mul(factors) if config.isEnabled(ExpandLogarithms) =>
        Canonical.sum(factors.map(factor => simplified(factor)))

      case Div(Vector(numerator, denominator)) if config.isEnabled(ExpandLogarithms) =>
        Canonical.sum(Vector(simplified(numerator), Canonical.negate(simplified(denominator))))

      case Pow(base, exponent) if config.isEnabled(ExpandLogarithms) =>
        Canonical.product(Vector(exponent, simplified(base)))

      case other => Log(other)
    }
}
