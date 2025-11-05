import collatz.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import collatz.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

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
println(s"def collatz1(n): return ${collatz1.simplify.expand.simplify.expand.simplify}")
println(s"def collatz2(n): return ${collatz2.simplify.expand.simplify.expand.simplify}")
println(s"def collatz3(n): return ${collatz3.simplify.expand.simplify.expand.simplify}")
