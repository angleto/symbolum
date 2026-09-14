package garden.xeno.symbolum

import garden.xeno.symbolum.NumericConstants._

/**
 * A symbolic algebraic expression.
 *
 * An expression is plain data: it knows how to evaluate itself, how to substitute a variable, and
 * how to print itself. It does not know how to simplify itself. Rewriting lives in [[Simplifier]]
 * and [[Canonical]], and the three methods below delegate there.
 *
 * That split is deliberate. When each node simplified itself, a node's rewriting called the
 * rewriting of the nodes it built, and two rules that were individually correct (factoring a
 * sign out of a quotient, folding a coefficient into one) called each other without end. A
 * traversal that owns the recursion, over constructors that terminate, cannot.
 *
 * == Expression types ==
 *
 *  - atoms: [[Num]], [[Var]]
 *  - arithmetic: [[Add]], [[Sub]], [[Mul]], [[Div]], [[Pow]], [[Neg]]
 *  - functions: [[Sin]], [[Cos]], [[Tan]], [[Exp]], [[Log]]
 *  - calculus: [[Derivative]], [[Integral]]
 *
 * == Why this is not sealed ==
 *
 * It should be: an unhandled node would then be a compile error instead of a value that falls
 * through a catch-all unchanged, which is what `Simplifier.normalise` does today. Scala 3 admits
 * a sealed hierarchy only when every direct subtype is declared in this file, and the node types
 * are one per file with the documentation that goes with them. Merging them would put roughly
 * nine hundred lines in one file to buy exhaustiveness over a type that is, in the proof
 * assistant, untrusted: a wrong answer here costs a failed tactic, never a false theorem. The
 * kernel's own term type carries no such constraint and is sealed.
 *
 * @see [[SimplificationConfig]] for the rules that govern simplification
 * @see [[Canonical]] for the canonical form the simplifier produces
 */
trait Expr {

  /**
   * Binding strength for printing, used only to decide parentheses.
   *
   * 1 for sums, 2 for products and quotients, 3 for powers and negation, 4 for atoms and
   * function applications.
   */
  def precedence: Int = 10

  /**
   * Evaluate numerically under the given variable assignment.
   *
   * @throws UndefinedVariableError if a variable in the expression has no value
   */
  def eval(variables: Map[String, Double]): Double

  /** Replace every occurrence of the variable `sym` with `repl`. */
  def replaceSymbol(sym: String, repl: Expr): Expr

  /**
   * Compare two expressions structurally, allowing numeric literals to differ within
   * [[NumericConstants.TOLERANCE]] of their own size.
   *
   * Simplification itself compares exactly: numeric literals are normalised and commutative
   * operands are ordered, so equal results are equal expressions. This is offered for callers
   * comparing expressions that came from separate floating-point computations, where the last
   * digits legitimately differ.
   *
   * **The tolerance is relative, and it was absolute until 2026-09-05.** Scaled only by the
   * denominators, `1e-10` is smaller than one ulp for any value above about a million, so the
   * comparison was stricter than bit equality exactly where floating point is loosest and this
   * method was least able to do its job. `CanonicalFormSpec` found it, at seed
   * `443254023675775541`, on two orderings of one product whose coefficients came out
   * `-1490754.846579868` and `-1490754.8465798679`: five ulps apart, and rejected. Scaling by the
   * larger of the two values as well as by the denominators keeps the old behaviour wherever the
   * numbers are of ordinary size, since the scale is at least the product of the denominators.
   */
  def approxEqual(other: Expr): Boolean = (this, other) match {
    case (Num(an, ad), Num(bn, bd)) =>
      val left = an * bd
      val right = bn * ad
      val scale = math.max(math.abs(ad * bd), math.max(math.abs(left), math.abs(right)))
      math.abs(left - right) <= TOLERANCE * scale

    case (Var(a), Var(b)) => a == b

    case (Add(a), Add(b)) => allApproxEqual(a, b)
    case (Sub(a), Sub(b)) => allApproxEqual(a, b)
    case (Mul(a), Mul(b)) => allApproxEqual(a, b)
    case (Div(a), Div(b)) => allApproxEqual(a, b)

    case (Pow(baseA, expA), Pow(baseB, expB)) =>
      baseA.approxEqual(baseB) && expA.approxEqual(expB)

    case (Cos(a), Cos(b)) => a.approxEqual(b)
    case (Sin(a), Sin(b)) => a.approxEqual(b)
    case (Tan(a), Tan(b)) => a.approxEqual(b)
    case (Exp(a), Exp(b)) => a.approxEqual(b)
    case (Log(a), Log(b)) => a.approxEqual(b)
    case (Neg(a), Neg(b)) => a.approxEqual(b)

    case (Derivative(exprA, varA), Derivative(exprB, varB)) =>
      varA == varB && exprA.approxEqual(exprB)

    case _ => this == other
  }

  private def allApproxEqual(a: Vector[Expr], b: Vector[Expr]): Boolean =
    a.length == b.length && a.lazyZip(b).forall(_ approxEqual _)

  /**
   * Simplify in one bottom-up pass.
   *
   * The result is in the canonical form described on [[Canonical]] and applying this again
   * changes nothing.
   */
  final def simplify(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr =
    Simplifier.simplify(this)(config)

  /**
   * Simplify with distribution of products over sums forced on.
   *
   * `a*(b + c)` becomes `a*b + a*c`, `(a + b)^2` is expanded, and a product of cosines becomes a
   * sum where [[SimplificationRule.ProductOfCosToSumOfCos]] is enabled.
   */
  final def expand(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr =
    Simplifier.expand(this)(config)

  /**
   * Simplify repeatedly until the result stops changing.
   *
   * @param maxIter ceiling on the number of passes
   */
  final def fullSimplify(implicit config: SimplificationConfig = SimplificationConfig.Default,
                         maxIter: Int = MAX_ITERATIONS): Expr =
    Simplifier.fullSimplify(this, maxIter)(config)

  /** Wrap `child` in parentheses if it binds less tightly than `parent`. */
  protected def showWithParens(child: Expr, parent: Expr): String =
    if (child.precedence < parent.precedence) s"($child)" else child.toString
}
