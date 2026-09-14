package garden.xeno.symbolum

/**
 * Numeric constants used throughout the symbolic algebra system.
 *
 * These constants control numerical tolerances, iteration limits, and other
 * configurable parameters that affect simplification behavior.
 */
object NumericConstants {

  /**
   * Tolerance for floating-point comparisons.
   *
   * Simplification itself compares exactly: literals are normalised and commutative operands are
   * ordered, so equal results are equal expressions. This is for the comparisons that cannot be
   * exact: [[Expr.approxEqual]], and recognising `e` in `log(e)`.
   */
  val TOLERANCE: Double = 1e-10

  /**
   * Maximum number of iterations for fixpoint simplification.
   * Prevents infinite loops in fullSimplify() when expressions don't converge.
   */
  val MAX_ITERATIONS: Int = 100

  /**
   * Default maximum number of terms allowed after expansion.
   * Prevents combinatorial explosion when distributing products over sums.
   * For example, (a+b+c)*(d+e+f) creates 9 terms.
   */
  val DEFAULT_MAX_EXPANSION_TERMS: Int = 1000

}
