package garden.xeno.symbolum

/**
 * When comparing two expressions by their value is meaningful, and when it is not.
 *
 * Shared by the specs that assert simplification preserves value. They compare two doubles
 * against a fixed relative tolerance, and that comparison stops meaning anything long before it
 * stops being computable.
 */
object EvaluationBounds {

  /**
   * The largest argument of a trigonometric function these comparisons can survive.
   *
   * The spacing between doubles at magnitude M is about M times 2.2e-16, and sine and cosine pass
   * an error in their argument straight through to their result. So at M near 1e9 two ways of
   * computing the same argument, differing only in the order of the multiplications, give results
   * that differ by around 5e-7, while the properties compare at 1e-8. `cos((-5 * y)^3^3)` is the
   * case that found this: both sides are as correct as a double can be and they disagree.
   *
   * The limit is where the argument's own representation error stays well under the tolerance:
   * 1e6 times 2.2e-16 is 2e-10, two orders below 1e-8. Widening the tolerance instead would make
   * the comparison vacuous, because cosine is bounded by one and a tolerance of 35 accepts
   * anything.
   */
  val TrigonometricLimit: Double = 1e6

  /** True when no trigonometric function in `e` is applied to something too large to compare. */
  def comparable(e: Expr, sample: Map[String, Double]): Boolean = {
    def valueOf(argument: Expr): Option[Double] =
      try {
        val v = argument.eval(sample)
        if (v.isNaN || v.isInfinite) None else Some(v)
      } catch {
        case _: ArithmeticException => None
        case _: ExpressionError => None
      }

    def inRange(argument: Expr): Boolean =
      valueOf(argument).forall(v => math.abs(v) <= TrigonometricLimit)

    def go(current: Expr): Boolean = current match {
      case Cos(argument) => inRange(argument) && go(argument)
      case Sin(argument) => inRange(argument) && go(argument)
      case Tan(argument) => inRange(argument) && go(argument)

      case Add(terms) => terms.forall(go)
      case Sub(terms) => terms.forall(go)
      case Mul(factors) => factors.forall(go)
      case Div(operands) => operands.forall(go)
      case Neg(argument) => go(argument)
      case Pow(base, exponent) => go(base) && go(exponent)
      case Exp(argument) => go(argument)
      case Log(argument) => go(argument)

      case _ => true
    }

    go(e)
  }
}
