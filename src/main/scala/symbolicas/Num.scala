package symbolicas ;

import scala.annotation.tailrec ;

final case class Num(numerator: Double, denominator: Double = 1.0)
  extends Expr {

  override val precedence: Int = 4

  def eval(vars: Map[String, Double]): Double = numerator / denominator

  def replaceSymbol(sym: String, repl: Expr): Expr = this

  /* gcd on doubles – good enough for the use-case “integers stored as double” */
  private def gcd(a: Double, b: Double): Double = {
    @tailrec def loop(x: Double, y: Double): Double =
      if (y == 0) x else loop(y, x % y)

    loop(a.abs, b.abs)
  }

  def simplify: Num =
    if (denominator == 1.0) this
    else {
      val g = gcd(numerator, denominator)
      Num(numerator / g, denominator / g)
    }

  override def toString: String = {
    def isWhole(d: Double): Boolean = (d % 1.0) == 0.0

    if (denominator == 1.0) {
      if (isWhole(numerator))
        s"${numerator.toInt}"
      else
        s"$numerator"
    } else {
      if (isWhole(numerator) && isWhole(denominator))
        s"${numerator.toInt}/${denominator.toInt}"
      else
        s"$numerator/$denominator"
    }
  }
}