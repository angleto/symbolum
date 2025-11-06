package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/* ============================================================================
 * unary composites
 * ========================================================================== */
final case class Cos(expr: Expr) extends Expr {
  override val precedence: Int = 4

  def eval(vars: Map[String, Double]): Double =
    math.cos(expr.eval(vars))

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Cos(expr.replaceSymbol(sym, repl))

  override def expand(implicit config: SimplificationConfig): Expr = Cos(expr.expand(config))

  def simplify(implicit config: SimplificationConfig): Expr = Cos(expr.simplify(config))

  override def toString: String = s"cos($expr)"
}

/* ------------------------------------------------------------------------- */
final case class Neg(expr: Expr) extends Expr {
  override val precedence: Int = 3

  def eval(vars: Map[String, Double]): Double =
    -expr.eval(vars)

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Neg(expr.replaceSymbol(sym, repl))

  override def expand(implicit config: SimplificationConfig): Expr =
    Neg(expr.expand(config)).simplify(config)

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
