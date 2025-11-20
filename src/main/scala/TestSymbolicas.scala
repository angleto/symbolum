import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

object TestSymbolicas {
  def main(args: Array[String]): Unit = {
    // Example usage

    val n: Expr = Var("n")

    val collatz1: Expr = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    val collatz2Even: Expr = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd: Expr = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2: Expr = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val collatz3Even: Expr = collatz2.replaceSymbol("n", n/2)
    val collatz3Odd: Expr = collatz2.replaceSymbol("n", (n*3+1)/2)
    val collatz3: Expr = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)

    val test = collatz3
    val variables = Map("n" -> 123.0, "pi" -> math.Pi)
    val result = test.eval(variables)
    println(s"Evaluated result: $result")
    println()
    println("=" * 70)
    println("COLLATZ EXPRESSIONS (Fully Simplified)")
    println("=" * 70)
    println()
    println(s"collatz1(n) = ${collatz1.fullSimplify}")
    println()
    println(s"collatz2(n) = ${collatz2.fullSimplify}")
    println()
    println(s"collatz3(n) = ${collatz3.fullSimplify}")
  }
}
