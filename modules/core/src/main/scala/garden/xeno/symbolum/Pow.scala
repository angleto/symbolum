package garden.xeno.symbolum

/**
 * Exponentiation.
 *
 * == `x^0` is 1, and that includes `0^0` ==
 *
 * `x^n` is the product of `n` copies of `x`, so `x^0` is the empty product, and the empty product
 * is the unit of the ring whatever the base was. It is not a convenience: it follows from the
 * definition, which is why every comparable system states it without a side condition. HOL Light
 * proves `&0 pow n = if n = 0 then &1 else &0`; Mathlib's `pow_zero (a) : a ^ 0 = 1` has no
 * hypothesis and puts the condition on the other case, `zero_pow (hn : n ≠ 0)`; SymPy, Python and
 * Java all return 1. The convention that leaves `0^0` undefined belongs to analysis, where the
 * question is the limit of `x^y` as both approach zero, and that limit does not exist. Nothing
 * here asks that question.
 *
 * This class used to reject `0^0` at construction. It was the only dissenting voice in the
 * repository: [[Canonical.power]] reduces `_^0` to one as its first case, with no condition on the
 * base, `Rational.power` returns one for a zero exponent, and `eval` returns `1.0` because
 * `math.pow` does. `eval` has type `Map[String, Double] => Double` and no way to decline, so the
 * choice had already been made everywhere it could be; the constructor only stopped anybody from
 * writing down what the class computes. Two property generators carried a special case to avoid
 * tripping it, and one carried a `try` around construction to survive it.
 *
 * @param base     the base
 * @param exponent the exponent
 *
 * @example {{{
 * Pow(Var("x"), Num(2))          // x^2
 * Pow(Num(2), Num(3)).simplify   // 8
 * Pow(Var("x"), Num(1, 2))       // sqrt(x), left symbolic
 * Pow(Num(0), Num(0)).simplify   // 1, the empty product
 * }}}
 */
final case class Pow(base: Expr, exponent: Expr) extends Expr {

  override val precedence: Int = 3

  def eval(variables: Map[String, Double]): Double =
    math.pow(base.eval(variables), exponent.eval(variables))

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Pow(base.replaceSymbol(sym, repl), exponent.replaceSymbol(sym, repl))

  override def toString: String =
    s"${showWithParens(base, this)}^${showWithParens(exponent, this)}"
}

object Pow {

  /**
   * Expand a sum raised to a whole power, or `None` if that would exceed the expansion ceiling.
   *
   * The expansion is the product of `n` copies of the sum, handed to the ordinary distribution
   * machinery. A dedicated multinomial routine was rejected: it would be a second implementation
   * of the same combinatorics, and the two would have to be kept agreeing about term collection
   * and about the expansion ceiling.
   */
  private[symbolum] def expandedSum(terms: Vector[Expr], exponent: Int)
                                     (implicit config: SimplificationConfig): Option[Expr] = {
    if (exponent < 1) None
    else {
      val estimatedTerms = math.pow(terms.length.toDouble, exponent.toDouble)
      if (estimatedTerms > config.maxExpansionTerms) None
      else Some(Canonical.product(Vector.fill(exponent)(Add(terms))))
    }
  }
}
