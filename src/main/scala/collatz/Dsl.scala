package collatz

import scala.language.implicitConversions ;

/* ============================================================================
 * DSL – a tiny “surface language” for building expressions in a natural way
 * ========================================================================== */
object Dsl {
  implicit def intToNum(i: Int): Expr    = Num(i.toDouble)
  implicit def doubleToNum(d: Double): Expr = Num(d)

  implicit class ExprOps(val self: Expr) extends AnyVal {
    def +(others: Expr*): Expr = Add(self +: others.toArray)
    def -(others: Expr*): Expr = Sub(self +: others.toArray)
    def *(others: Expr*): Expr = Mul(self +: others.toArray)
    def /(others: Expr*): Expr = Div(self +: others.toArray)

    // unary minus
    def unary_- : Expr = Neg(self)
  }

  def cos(e: Expr): Expr = Cos(e)

  val pi: Expr = Var("pi")
  val e:  Expr = Var("e")
}