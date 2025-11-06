import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 80)
println("QUICK DISTRIBUTION TEST")
println("=" * 80)
println()

val n: Expr = Var("n")

println("Test 1: Simple distribution")
println("-" * 80)
val test1 = Mul(Array(Num(2), Add(Array(n, Num(1)))))
val result1 = test1.fullSimplify
println(s"2 * (n + 1) = $result1")
println(s"Expected: 2 * n + 2")
println()

println("Test 2: Distribution with division")
println("-" * 80)
val test2 = Mul(Array(Div(Array(Num(1), Num(2))), Add(Array(n, Num(1)))))
val result2 = test2.fullSimplify
println(s"1/2 * (n + 1) = $result2")
println(s"Expected: n/2 + 1/2  OR  (n + 1)/2")
println()

println("Test 3: Nested distribution")
println("-" * 80)
val innerSum = Add(Array(n, Num(1)))
val middleSum = Add(Array(innerSum, Num(2)))
val test3 = Mul(Array(Num(2), middleSum))
val result3 = test3.fullSimplify
println(s"2 * ((n + 1) + 2) = $result3")
println(s"Expected: 2 * n + 6")
println()

println("Test 4: Complex distribution like Collatz")
println("-" * 80)
val sum1 = Add(Array(n, Num(1)))
val sum2 = Add(Array(Mul(Array(Num(2), n)), Num(3)))
val bigSum = Add(Array(sum1, sum2))
val test4 = Mul(Array(Div(Array(Num(1), Num(2))), Cos(Mul(Array(n, pi))), bigSum))
val result4 = test4.fullSimplify
println(s"1/2 * cos(n*pi) * ((n+1) + (2*n+3)) = $result4")
println(s"Should be distributed into separate terms")
val output4 = result4.toString
if (output4.contains("1/2 * cos(n * pi) * (") || output4.contains("cos(n * pi) * (")) {
  println("✗ FAIL: Still has undistributed multiplication")
} else {
  println("✓ PASS: Multiplication distributed")
}
println()

println("=" * 80)
