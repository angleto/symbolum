import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 70)
println("COSINE ARGUMENT SIMPLIFICATION TESTS")
println("=" * 70)
println()

val n: Expr = Var("n")

// Test 1: n * pi - n/2 * pi should simplify to n*pi/2 or (n*pi)/2
println("Test 1: n * pi - n/2 * pi")
val expr1 = n * pi - (n/2) * pi
println(s"  Original: $expr1")
println(s"  Simplified: ${expr1.simplify}")
println(s"  FullSimplified: ${expr1.fullSimplify}")
println()

// Test 2: Inside a cosine
println("Test 2: cos(n * pi - n/2 * pi)")
val expr2 = cos(n * pi - (n/2) * pi)
println(s"  Original: $expr2")
println(s"  Simplified: ${expr2.simplify}")
println(s"  FullSimplified: ${expr2.fullSimplify}")
println()

// Test 3: 2*n*pi - n*pi
println("Test 3: 2*n*pi - n*pi")
val expr3 = Num(2) * n * pi - n * pi
println(s"  Original: $expr3")
println(s"  Simplified: ${expr3.simplify}")
println(s"  FullSimplified: ${expr3.fullSimplify}")
println()

// Test 4: More complex: 3*n*pi/4 - n*pi/4
println("Test 4: 3*n*pi/4 - n*pi/4")
val expr4 = (Num(3) * n * pi) / 4 - (n * pi) / 4
println(s"  Original: $expr4")
println(s"  Simplified: ${expr4.simplify}")
println(s"  FullSimplified: ${expr4.fullSimplify}")
println()

// Test 5: n*pi + n*pi (should give 2*n*pi)
println("Test 5: n*pi + n*pi")
val expr5 = n * pi + n * pi
println(s"  Original: $expr5")
println(s"  Simplified: ${expr5.simplify}")
println(s"  FullSimplified: ${expr5.fullSimplify}")
println()

println("=" * 70)
println("EXPECTED RESULTS:")
println("=" * 70)
println("Test 1 should show: n*pi/2 or (n*pi)/2")
println("Test 2 should show: cos(n*pi/2) or cos((n*pi)/2)")
println("Test 3 should show: n*pi")
println("Test 4 should show: n*pi/2 or (n*pi)/2")
println("Test 5 should show: 2*n*pi")
