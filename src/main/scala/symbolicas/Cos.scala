package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/**
 * Cosine function expression.
 *
 * Represents cos(expr) for any expression expr.
 *
 * @param argument The argument to the cosine function
 *
 * @example {{{
 *   Cos(Var("x"))                    // cos(x)
 *   Cos(Mul(Vector(Var("n"), Num(2))))  // cos(2*n)
 * }}}
 */
final case class Cos(argument: Expr) extends Expr {
  override val precedence: Int = 4

  /**
   * Evaluates the cosine of the argument.
   *
   * @param variables Map of variable names to values
   * @return cos(argument.eval(variables))
   */
  def eval(variables: Map[String, Double]): Double =
    math.cos(argument.eval(variables))

  /**
   * Applies symbol replacement to the argument.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Cos with replaced argument
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Cos(argument.replaceSymbol(sym, repl))

  /**
   * Expands the argument.
   *
   * @param config Simplification configuration
   * @return Cos with expanded argument
   */
  override def expand(implicit config: SimplificationConfig): Expr =
    Cos(argument.expand(config))

  /**
   * Simplifies the argument.
   *
   * @param config Simplification configuration
   * @return Cos with simplified argument
   *
   * @note Time Complexity: O(n) where n is the size of the argument expression
   */
  def simplify(implicit config: SimplificationConfig): Expr =
    Cos(argument.simplify(config))

  override def toString: String = s"cos($argument)"
}

/**
 * Negation expression.
 *
 * Represents -expr for any expression expr.
 * Negation is pushed into sub-expressions during simplification for cleaner output.
 *
 * @param argument The expression to negate
 *
 * @example {{{
 *   Neg(Num(5))              // -5 (simplified to Num(-5))
 *   Neg(Neg(Var("x")))       // --x (simplified to x)
 *   Neg(Add(Vector(a, b)))   // -(a + b) (simplified to -a + -b)
 * }}}
 */
final case class Neg(argument: Expr) extends Expr {
  override val precedence: Int = 3

  /**
   * Evaluates the negation.
   *
   * @param variables Map of variable names to values
   * @return -argument.eval(variables)
   */
  def eval(variables: Map[String, Double]): Double =
    -argument.eval(variables)

  /**
   * Applies symbol replacement to the argument.
   *
   * @param sym Symbol to replace
   * @param repl Replacement expression
   * @return Negation with replaced argument
   */
  def replaceSymbol(sym: String, repl: Expr): Expr =
    Neg(argument.replaceSymbol(sym, repl))

  /**
   * Expands the argument and simplifies the negation.
   *
   * @param config Simplification configuration
   * @return Expanded and simplified negation
   */
  override def expand(implicit config: SimplificationConfig): Expr =
    Neg(argument.expand(config)).simplify(config)

  /**
   * Simplifies negation by pushing it into sub-expressions.
   *
   * Transformations applied:
   * - Double negative elimination: --x → x
   * - Negation of numbers: -(5) → -5
   * - Distribution into sums: -(a + b) → -a + -b
   * - Distribution into products: -(a * b) → (-a) * b
   * - Distribution into divisions: -(a/b) → (-a)/b
   *
   * @param config Simplification configuration
   * @return Simplified expression with negation pushed inward
   *
   * @note Time Complexity: O(n) where n is the size of the expression
   */
  def simplify(implicit config: SimplificationConfig): Expr = {
    val simplified = argument.simplify(config)
    simplified match {
      case Num(numerator, denominator) =>
        Num(-numerator, denominator)

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
          Mul(Num(-1) +: exprs).simplify(config)
        }

      /* Push negation into Div: -(a/b) → (-a)/b */
      case Div(Vector(numerator, denominator)) =>
        Div(Vector(Neg(numerator).simplify(config), denominator)).simplify(config)

      /* For anything else, convert to multiplication by -1 */
      case other =>
        Mul(Vector(Num(-1), other)).simplify(config)
    }
  }

  override def toString: String =
    s"-${showWithParens(argument, this)}"
}
