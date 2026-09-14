package garden.xeno.symbolum

import garden.xeno.symbolum.SimplificationRule._

/**
 * The natural exponential, `e^argument`.
 *
 * @param argument the exponent
 */
final case class Exp(argument: Expr) extends Expr {

  override val precedence: Int = 4

  def eval(variables: Map[String, Double]): Double = math.exp(argument.eval(variables))

  def replaceSymbol(sym: String, repl: Expr): Expr = Exp(argument.replaceSymbol(sym, repl))

  override def toString: String = s"exp($argument)"
}

object Exp {

  /**
   * Simplify `exp(argument)` for an already-simplified argument.
   *
   * Splitting `exp(a + b)` into a product is an expansion, and it is gated on
   * [[SimplificationRule.ExpandExponentials]]. It used to run whenever
   * [[SimplificationRule.DistributeProduct]] was enabled, so `exp(x + 1).expand` came back as a
   * product even though nothing in the request concerned products over sums.
   */
  private[symbolum] def simplified(argument: Expr)(implicit config: SimplificationConfig): Expr =
    argument match {
      case n: Num if n.numerator == 0.0 => Num(1)
      case n: Num if config.isEnabled(CombineNumericLiterals) => Num(math.exp(n.value))

      case Log(inner) => inner

      case Mul(Vector(exponent: Num, Log(inner))) => Canonical.power(inner, exponent)

      case Add(terms) if config.isEnabled(ExpandExponentials) =>
        Canonical.product(terms.map(term => simplified(term)))

      case other => Exp(other)
    }
}
