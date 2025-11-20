package symbolicas

import scala.annotation.tailrec
import scala.language.implicitConversions
import symbolicas.SimplificationConfig
import symbolicas.NumericConstants._

/**
 * Base trait for all symbolic algebraic expressions.
 *
 * This trait defines the core operations supported by the symbolic algebra system:
 * - Numeric evaluation
 * - Symbol substitution
 * - Algebraic expansion
 * - Algebraic simplification
 *
 * == Expression Types ==
 *
 * The expression hierarchy includes:
 *  - '''Atomic expressions''': [[Num]] (numeric literals), [[Var]] (variables)
 *  - '''Unary operations''': [[Neg]] (negation), [[Cos]] (cosine)
 *  - '''N-ary operations''': [[Add]] (addition), [[Sub]] (subtraction), [[Mul]] (multiplication), [[Div]] (division)
 *
 * == Simplification Architecture ==
 *
 * The simplification system uses a configurable rule-based approach:
 *
 *  1. '''Single-pass simplification''' ([[simplify]]): Applies enabled rules once
 *  2. '''Expansion''' ([[expand]]): Distributes products over sums (a*(b+c) → a*b + a*c)
 *  3. '''Full simplification''' ([[fullSimplify]]): Multi-pass expansion and simplification until fixpoint
 *
 * Each expression type implements these methods according to its semantics.
 *
 * == Design Patterns ==
 *
 * '''Expand Pattern''': Most implementations follow this pattern:
 * {{{
 *   override def expand(implicit config: SimplificationConfig): Expr = {
 *     val expandedChildren = children.map(_.expand(config))
 *     // ... apply expansion transformation ...
 *     result.simplify(config)  // Always simplify after expansion
 *   }
 * }}}
 *
 * '''Simplify Pattern''': Implementations check enabled rules and apply transformations:
 * {{{
 *   def simplify(implicit config: SimplificationConfig): Expr = {
 *     if (config.isEnabled(SomeRule)) {
 *       // ... apply transformation ...
 *     } else {
 *       // ... keep original form ...
 *     }
 *   }
 * }}}
 *
 * @see [[SimplificationConfig]] for controlling which simplification rules are applied
 */
trait Expr {
  /**
   * Precedence level for pretty printing.
   *
   * Lower values bind less tightly and require more parentheses.
   * Used only for display purposes, not for evaluation.
   *
   * Precedence levels:
   *  - 1: Addition, Subtraction
   *  - 2: Multiplication, Division
   *  - 3: Negation, Power
   *  - 4: Atomic expressions (Num, Var, Cos, Sin, Tan, Exp, Log)
   */
  def precedence: Int = 10

  /**
   * Structural hash code for fast comparisons.
   *
   * This hash is computed lazily and cached for performance.
   * Currently used for hash consing and fast set/map operations.
   *
   * @note Not used for fixpoint detection in fullSimplify due to potential hash collisions
   *       that could cause incorrect simplifications. Structural equality is used instead.
   *
   * @return Hash code based on expression structure
   */
  lazy val structuralHash: Int = this.hashCode

  /**
   * Check if this expression is structurally equivalent to another expression
   * using tolerance-based comparison for numeric values.
   *
   * This is more robust than `==` for fixpoint detection because it handles
   * floating-point precision issues that can occur during simplification.
   *
   * @param other the expression to compare with
   * @return true if expressions are structurally equivalent within tolerance
   */
  def approxEqual(other: Expr): Boolean = (this, other) match {
    case (Num(an, ad), Num(bn, bd)) =>
      // Compare fractions with tolerance: a/b ≈ c/d iff |a*d - b*c| < ε*b*d
      math.abs(an * bd - bn * ad) < TOLERANCE * math.abs(ad * bd)

    case (Var(an), Var(bn)) => an == bn

    case (Add(aterms), Add(bterms)) =>
      aterms.length == bterms.length &&
      aterms.zip(bterms).forall { case (x, y) => x.approxEqual(y) }

    case (Sub(aexprs), Sub(bexprs)) =>
      aexprs.length == bexprs.length &&
      aexprs.zip(bexprs).forall { case (x, y) => x.approxEqual(y) }

    case (Mul(afactors), Mul(bfactors)) =>
      afactors.length == bfactors.length &&
      afactors.zip(bfactors).forall { case (x, y) => x.approxEqual(y) }

    case (Div(aoperands), Div(boperands)) =>
      aoperands.length == boperands.length &&
      aoperands.zip(boperands).forall { case (x, y) => x.approxEqual(y) }

    case (Pow(abase, aexp), Pow(bbase, bexp)) =>
      abase.approxEqual(bbase) && aexp.approxEqual(bexp)

    case (Cos(aarg), Cos(barg)) => aarg.approxEqual(barg)
    case (Sin(aarg), Sin(barg)) => aarg.approxEqual(barg)
    case (Tan(aarg), Tan(barg)) => aarg.approxEqual(barg)
    case (Exp(aarg), Exp(barg)) => aarg.approxEqual(barg)
    case (Log(aarg), Log(barg)) => aarg.approxEqual(barg)
    case (Neg(aarg), Neg(barg)) => aarg.approxEqual(barg)

    case (Derivative(aexpr, avar), Derivative(bexpr, bvar)) =>
      avar == bvar && aexpr.approxEqual(bexpr)

    case _ => this == other  // Fall back to structural equality for other types
  }

  /**
   * Evaluate the expression numerically given variable assignments.
   *
   * @param variables map from variable names to their numeric values
   * @return the numeric result of evaluation
   * @throws Exception if a required variable is not defined
   *
   * @example {{{
   * val expr = Add(Array(Var("x"), Num(1)))  // x + 1
   * expr.eval(Map("x" -> 5.0))  // returns 6.0
   * }}}
   */
  def eval(variables: Map[String, Double]): Double

  /**
   * Replace all occurrences of a variable with another expression.
   *
   * @param sym the variable name to replace
   * @param repl the replacement expression
   * @return new expression with substitution applied
   *
   * @example {{{
   * val expr = Add(Array(Var("x"), Var("y")))  // x + y
   * expr.replaceSymbol("x", Num(3))  // returns: 3 + y
   * }}}
   */
  def replaceSymbol(sym: String, repl: Expr): Expr

  /**
   * Expand the expression by distributing products over sums.
   *
   * This operation recursively applies algebraic expansion rules:
   *  - Product distribution: a*(b+c) → a*b + a*c
   *  - Trigonometric identities: cos(A)*cos(B) → (1/2)*(cos(A-B) + cos(A+B))
   *  - Flattening nested operations
   *
   * The expansion behavior is controlled by the configuration, particularly:
   *  - [[SimplificationRule.DistributeProduct]]
   *  - [[SimplificationRule.ProductOfCosToSumOfCos]]
   *
   * Default implementation returns the expression unchanged (suitable for atomic expressions).
   *
   * @param config simplification configuration controlling which expansion rules to apply
   * @return expanded expression
   *
   * @example {{{
   * val expr = Mul(Array(Var("a"), Add(Array(Var("b"), Var("c")))))  // a*(b+c)
   * expr.expand()  // returns: a*b + a*c
   * }}}
   */
  def expand(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr = this

  /**
   * Perform single-pass algebraic simplification with configurable rules.
   *
   * This method applies enabled simplification rules once to produce a simpler
   * equivalent expression. The specific transformations depend on the expression
   * type and enabled rules.
   *
   * Common simplifications include:
   *  - Removing identity elements (0 for addition, 1 for multiplication)
   *  - Combining numeric literals
   *  - Collecting like terms
   *  - Simplifying fractions
   *  - Flattening nested operations
   *  - Eliminating double negatives
   *
   * This is abstract and must be implemented by each expression type.
   *
   * @param config simplification configuration controlling which rules to apply
   * @return simplified expression
   *
   * @example {{{
   * val expr = Add(Array(Num(0), Var("x")))  // 0 + x
   * expr.simplify()  // returns: x
   * }}}
   */
  def simplify(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr

  /**
   * Perform full simplification with multi-pass expansion and simplification until fixpoint.
   *
   * This is the most aggressive simplification strategy, designed to handle deeply
   * nested expressions that require multiple rounds of expansion and simplification
   * to reach optimal form.
   *
   * == Algorithm ==
   *
   * The algorithm uses an ultra-aggressive multi-pass strategy:
   *
   *  1. Initial normalization: simplify → expand → simplify
   *  2. Iterative refinement loop (until fixpoint or max iterations):
   *     - expand → simplify → expand → simplify → expand → simplify → simplify
   *     - The triple expand-simplify pattern captures deeply nested structures
   *     - Double simplify at the end handles cascading effects
   *  3. Convergence detection via structural equality comparison
   *
   * This pattern is particularly effective for:
   *  - Deeply nested Mul(Cos(...), Add(...)) structures
   *  - Collatz sequence expressions
   *  - Complex fraction simplifications
   *
   * == Fixpoint Detection ==
   *
   * The algorithm uses structural equality (`==`) to detect fixpoints.
   * If two consecutive iterations produce structurally equal expressions, a fixpoint has been reached.
   *
   * @param config simplification configuration controlling which rules to apply
   * @param maxIter maximum iterations to prevent infinite loops (default 100)
   * @return fully simplified expression
   *
   * @example {{{
   * val expr = Mul(Vector(Var("a"), Add(Vector(Var("b"), Var("c")))))  // a*(b+c)
   * expr.fullSimplify()  // returns: a*b + a*c (fully expanded and simplified)
   * }}}
   *
   * @note This operation can be expensive for very large expressions.
   *       Consider using [[simplify]] or [[expand]] individually if performance is critical.
   */
  def fullSimplify(implicit config: SimplificationConfig = SimplificationConfig.Default,
                   maxIter: Int = MAX_ITERATIONS): Expr = {
    @tailrec
    def loop(expr: Expr, iterationsLeft: Int, previousExpr: Expr): Expr = {
      if (iterationsLeft <= 0) {
        // Safety limit reached - return what we have
        return expr
      }

      // Ultra-aggressive multi-pass for deeply nested expressions:
      // expand → simplify → expand → simplify → expand → simplify → simplify
      // The triple expand ensures distribution of products over sums at all nesting levels
      val step1 = expr.expand(config)
      val step2 = step1.simplify(config)
      val step3 = step2.expand(config)  // Second expand catches newly exposed structure
      val step4 = step3.simplify(config)
      val step5 = step4.expand(config)  // Third expand for deeply nested Mul(Cos(...), Add(...))
      val step6 = step5.simplify(config)
      val step7 = step6.simplify(config)  // Double simplify for cascading effects

      // Check if we've reached a fixpoint using structural equality
      // CRITICAL FIX: Use structural equality instead of hash comparison to avoid
      // hash collisions that cause premature termination and incorrect simplifications
      //
      // ROBUSTNESS: Use approxEqual as a fallback to handle floating-point precision
      // issues that can prevent fixpoint detection when expressions are mathematically
      // equivalent but have tiny numerical differences due to floating-point arithmetic
      if (step7 == previousExpr || step7.approxEqual(previousExpr)) {
        step7
      } else {
        loop(step7, iterationsLeft - 1, step7)
      }
    }

    // Initial multi-pass to normalize deeply nested input
    val step0 = this.simplify(config)
    val step1 = step0.expand(config)
    val initial = step1.simplify(config)
    loop(initial, maxIter, initial)
  }

  /* -------- helper for pretty printing ------------------------------------ */
  protected def showWithParens(child: Expr, parent: Expr): String =
    if (child.precedence < parent.precedence) s"(${child.toString})"
    else child.toString
}
