package symbolicas

import scala.language.implicitConversions ;

/* ============================================================================
 * DSL – a tiny “surface language” for building expressions in a natural way
 * ========================================================================== */
object Dsl {
  implicit def intToNum(i: Int): Expr    = Num(i.toDouble)
  implicit def doubleToNum(d: Double): Expr = Num(d)

  implicit class ExprOps(val self: Expr) extends AnyVal {
    def +(others: Expr*): Expr = Add(self +: others.toVector)
    def -(others: Expr*): Expr = Sub(self +: others.toVector)
    def *(others: Expr*): Expr = Mul(self +: others.toVector)
    def /(others: Expr*): Expr = Div(self +: others.toVector)
    def ^(exponent: Expr): Expr = Pow(self, exponent)

    // unary minus
    def unary_- : Expr = Neg(self)
  }

  // Trigonometric functions
  def cos(e: Expr): Expr = Cos(e)
  def sin(e: Expr): Expr = Sin(e)
  def tan(e: Expr): Expr = Tan(e)

  // Exponential and logarithm
  def exp(e: Expr): Expr = Exp(e)
  def log(e: Expr): Expr = Log(e)

  // Power function (alternative to ^ operator)
  def pow(base: Expr, exponent: Expr): Expr = Pow(base, exponent)

  // Mathematical constants
  val pi: Expr = Var("pi")
  val e:  Expr = Num(math.E)  // Natural base as numeric constant
}