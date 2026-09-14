package garden.xeno.symbolum

import scala.annotation.tailrec
import garden.xeno.symbolum.SimplificationRule._

/**
 * The simplification driver.
 *
 * It owns one thing: the traversal. Every node is rewritten bottom-up, and the rewritten children
 * are handed to the smart constructor in [[Canonical]], or, for a function with identities of its
 * own, to that function's `simplified` in its own file. Nothing here reaches into another node's
 * rewriting, which is what the previous design did and what made `Mul` and `Div` call each other
 * until the stack ran out.
 *
 * Because a constructor given canonical children returns a canonical result, one bottom-up pass
 * reaches the canonical form. [[fullSimplify]] still iterates, but the loop is a guard rather than
 * the mechanism: it exists for the rewrites that expose structure their own pass could not see,
 * such as a binomial expansion whose terms then collect. The previous implementation ran
 * expand-simplify seven times per iteration and compared with a numeric tolerance because no
 * single pass was complete and no two passes agreed on an ordering.
 */
object Simplifier {

  /** Rewrite `e` into canonical form under `config`. */
  def simplify(e: Expr)(implicit config: SimplificationConfig): Expr = normalise(e)

  /**
   * Rewrite `e` with distribution of products over sums forced on.
   *
   * Expansion is not a separate algorithm: it is simplification under one more rule. Keeping it
   * that way is what guarantees that expanding and simplifying agree about the shape of the
   * result, rather than each undoing the other's work.
   */
  def expand(e: Expr)(implicit config: SimplificationConfig): Expr =
    normalise(e)(config.withRule(DistributeProduct))

  /**
   * Rewrite `e` repeatedly until the result stops changing.
   *
   * Convergence is decided by structural equality. That is exact here because commutative
   * operands are sorted and numeric literals are normalised, so two runs on equal input produce
   * equal output; the earlier tolerance-based fallback existed to paper over an ordering that was
   * not canonical.
   *
   * @param maxIterations ceiling on the number of passes, so a rule set whose rules invert each
   *                      other terminates with a result instead of hanging
   */
  def fullSimplify(e: Expr, maxIterations: Int)(implicit config: SimplificationConfig): Expr = {
    @tailrec
    def loop(current: Expr, remaining: Int): Expr = {
      if (remaining <= 0) current
      else {
        val next = normalise(current)
        if (next == current) current else loop(next, remaining - 1)
      }
    }
    loop(normalise(e), maxIterations)
  }

  private def normalise(e: Expr)(implicit config: SimplificationConfig): Expr = e match {
    case n: Num => n
    case v: Var => v

    case Add(terms) =>
      Canonical.factorCommonTerms(Canonical.sum(terms.map(normalise)))

    case Sub(expressions) =>
      val normalised = expressions.map(normalise)
      Canonical.factorCommonTerms(
        Canonical.sum(normalised.head +: normalised.tail.map(Canonical.negate))
      )

    case Mul(factors) =>
      Canonical.product(factors.map(normalise))

    case Div(operands) =>
      operands.map(normalise).reduceLeft(Canonical.quotient)

    case Neg(argument) =>
      Canonical.negate(normalise(argument))

    case Pow(base, exponent) =>
      Canonical.power(normalise(base), normalise(exponent))

    case Sin(argument) => Sin.simplified(normalise(argument))
    case Cos(argument) => Cos.simplified(normalise(argument))
    case Tan(argument) => Tan.simplified(normalise(argument))
    case Exp(argument) => Exp.simplified(normalise(argument))
    case Log(argument) => Log.simplified(normalise(argument))

    case Derivative(expression, variable) =>
      Derivative.differentiate(expression, variable)

    case Integral(expression, variable, lowerBound, upperBound) =>
      Integral.integrate(expression, variable, lowerBound, upperBound)

    case other => other
  }
}
