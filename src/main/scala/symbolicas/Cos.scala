package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/* ============================================================================
 * Unary composites - Trigonometric Functions
 * ========================================================================== */
final case class Cos(expr: Expr) extends Expr {
  override val precedence: Int = 4

  /**
   * Evaluate this cosine expression numerically.
   * @param vars mapping from variable names to their numeric values
   * @return the cosine of the evaluated inner expression
   */
  def eval(vars: Map[String, Double]): Double =
    math.cos(expr.eval(vars))

  /**
   * Replace all occurrences of a symbol with another expression.
   * @param sym the symbol name to replace
   * @param repl the expression to substitute
   * @return a new Cos expression with substitutions applied
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Cos(expr.replaceSymbol(sym, repl))

  /**
   * Expand this cosine expression by expanding its inner expression.
   * @param config simplification configuration
   * @return cos of expanded inner expression
   */
  override def expand(implicit config: SimplificationConfig): Expr = Cos(expr.expand(config))

  /**
   * Simplify this cosine expression by simplifying its inner expression.
   * @param config simplification configuration
   * @return cos of simplified inner expression
   */
  def simplify(implicit config: SimplificationConfig): Expr = Cos(expr.simplify(config))

  override def toString: String = s"cos($expr)"
}

/* ============================================================================
 * Unary composites - Negation
 * ========================================================================== */
final case class Neg(expr: Expr) extends Expr {
  override val precedence: Int = 3

  /**
   * Evaluate this negation expression numerically.
   * @param vars mapping from variable names to their numeric values
   * @return the negative of the evaluated inner expression
   */
  def eval(vars: Map[String, Double]): Double =
    -expr.eval(vars)

  /**
   * Replace all occurrences of a symbol with another expression.
   * @param sym the symbol name to replace
   * @param repl the expression to substitute
   * @return a new Neg expression with substitutions applied
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Neg(expr.replaceSymbol(sym, repl))

  /**
   * Expand this negation expression by expanding the inner expression first.
   * @param config simplification configuration
   * @return negation of expanded inner expression, then simplified
   */
  override def expand(implicit config: SimplificationConfig): Expr =
    Neg(expr.expand(config)).simplify(config)

  /**
   * Simplify this negation expression using algebraic rules.
   *
   * Simplification rules:
   *   - Negate numeric literals: -(5) → -5
   *   - Remove double negatives: -(-x) → x
   *   - Distribute into additions: -(a + b) → -a + -b
   *   - Distribute into multiplications: -(a * b) → -a * b
   *   - Distribute into divisions: -(a/b) → (-a)/b
   *
   * @param config simplification configuration
   * @return simplified expression
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val s = expr.simplify(config)
    s match {
      case Num(n, d) => Num(-n, d)

      case Neg(inner) if config.isEnabled(SimplifyDoubleNegative) =>
        inner  // double negative: --x = x

      case Neg(inner) =>
        Neg(inner)  // keep double negative if rule disabled

      /* Push negation into Add: -(a + b + c) → (-a) + (-b) + (-c) */
      case Add(exprs) =>
        val negatedTerms = exprs.map(e => Neg(e).simplify(config))
        Add(negatedTerms).simplify(config)

      /* Push negation into Mul: -(a * b * ...) → (-a) * b * ... */
      case Mul(exprs) =>
        val (nums, others) = exprs.partition(_.isInstanceOf[Num])
        if (nums.nonEmpty) {
          // Negate all numeric factors
          val negatedNums = nums.collect { case Num(n, d) => Num(-n, d) }
          Mul(negatedNums ++ others).simplify(config)
        } else {
          // No numeric factors, add -1
          Mul(Array[Expr](Num(-1)) ++ exprs).simplify(config)
        }

      /* Push negation into Div: -(a/b) → (-a)/b */
      case Div(Array(num, den)) =>
        Div(Array(Neg(num).simplify(config), den)).simplify(config)

      /* For anything else, convert to multiplication by -1 */
      case other =>
        Mul(Array(Num(-1), other)).simplify(config)
    }
  }

  override def toString: String =
    s"-${showWithParens(expr, this)}"
}
