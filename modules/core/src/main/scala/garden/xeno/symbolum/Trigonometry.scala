package garden.xeno.symbolum

/**
 * Shared support for the trigonometric identities.
 *
 * `sin` and `tan` are odd and `cos` is even, and all three need the same question answered first:
 * is this argument negated, and what is it without the sign? Answering it in one place keeps the
 * three functions from drifting apart, which is what happened when each carried its own
 * `case Neg(inner)` plus a `case Sub(Vector(Num(0, _), inner))` that only ever matched a shape the
 * simplifier no longer produces.
 *
 * The argument is always canonical here, so the sign lives in a numeric coefficient and there is
 * no `Neg` node left to look for.
 */
private[symbolum] object Trigonometry {

  /**
   * Split the sign off an argument: whether it was negated, and its magnitude.
   *
   * A sum is deliberately left alone even when every term is negative. Moving a sign out of a sum
   * would rewrite the argument on every pass without ever reaching a form the next pass leaves
   * alone.
   */
  def splitSign(argument: Expr)(implicit config: SimplificationConfig): (Boolean, Expr) =
    argument match {
      case _: Add => (false, argument)
      case other =>
        val (coefficient, _) = Canonical.splitCoefficient(other)
        if (coefficient.value >= 0.0) (false, other)
        else {
          val magnitude = Canonical.negate(other)
          // Only worth taking the sign out if it actually came out. With numeric folding
          // disabled, negating prepends another -1 instead of cancelling the one already there,
          // so the argument would grow by a factor on every pass and simplification would never
          // settle.
          if (Canonical.splitCoefficient(magnitude)._1.value >= 0.0) (true, magnitude)
          else (false, other)
        }
    }
}
