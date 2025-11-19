package symbolicas

/**
 * Numeric constants used throughout the symbolic algebra system.
 *
 * These constants control numerical tolerances, iteration limits, and other
 * configurable parameters that affect simplification behavior.
 */
object NumericConstants {

  /**
   * Tolerance for floating-point comparisons.
   * Used when checking if denominators match or if a value is "close enough" to zero.
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

  /**
   * Maximum recursion depth for expression tree traversal.
   * Prevents stack overflow on deeply nested expressions.
   */
  val MAX_RECURSION_DEPTH: Int = 500
}
