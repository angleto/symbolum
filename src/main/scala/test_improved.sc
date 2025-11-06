import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

// Test basic simplifications
println("=" * 60)
println("BASIC SIMPLIFICATION TESTS")
println("=" * 60)

val x: Expr = Var("x")
val y: Expr = Var("y")

// Test 1: Double negative elimination
val test1 = Neg(Neg(x))
println(s"Test 1 - Double negative: --x")
println(s"  Simplified: ${test1.simplify}")
println()

// Test 2: Addition with negative (should show - instead of + -)
val test2 = Add(Array(x, Neg(y)))
println(s"Test 2 - Addition with negative: x + (-y)")
println(s"  Simplified: ${test2.simplify}")
println()

// Test 3: Nested additions should flatten
val test3 = Add(Array(x, Add(Array(y, Num(5)))))
println(s"Test 3 - Nested addition: x + (y + 5)")
println(s"  Simplified: ${test3.simplify}")
println()

// Test 4: Fractions should not be automatically merged
val test4 = Add(Array(Num(1, 2), Num(1, 3)))
println(s"Test 4 - Fraction addition: 1/2 + 1/3")
println(s"  Simplified: ${test4.simplify}")
println()

// Test 5: Same denominator fractions should be merged
val test5 = Add(Array(Num(1, 4), Num(1, 4)))
println(s"Test 5 - Same denominator: 1/4 + 1/4")
println(s"  Simplified: ${test5.simplify}")
println()

// Test 6: Negative fractions
val test6 = Add(Array(Num(3, 4), Num(-1, 4)))
println(s"Test 6 - Negative fraction: 3/4 + (-1/4)")
println(s"  Simplified: ${test6.simplify}")
println()

// Test 7: Complex expression with cos
val n: Expr = Var("n")
val test7 = Mul(Array(Num(-1), Div(Array(Mul(Array(Num(2), n, Num(1))), Num(4))), cos(Mul(Array(n, pi)))))
println(s"Test 7 - Complex: -(2*n + 1)/4 * cos(n*pi)")
println(s"  Before simplification: $test7")
println(s"  After simplify: ${test7.simplify}")
println(s"  After fullSimplify: ${test7.fullSimplify}")
println()

// Test 8: Full Collatz expression
println("=" * 60)
println("COLLATZ EXPRESSION TEST")
println("=" * 60)

val collatz1: Expr = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
println(s"collatz1 (raw): $collatz1")
println(s"collatz1 (simplified): ${collatz1.simplify}")
println(s"collatz1 (fullSimplify): ${collatz1.fullSimplify}")
println()

val collatz2Even: Expr = collatz1.replaceSymbol("n", n/2)
val collatz2Odd: Expr = collatz1.replaceSymbol("n", (n*3+1)/2)
val collatz2: Expr = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

println(s"collatz2 (fullSimplify):")
println(s"${collatz2.fullSimplify}")
println()

// Test 9: Product to sum for cosines
println("=" * 60)
println("COSINE PRODUCT-TO-SUM TEST")
println("=" * 60)

val test9 = Mul(Array(cos(x), cos(y)))
println(s"Test 9 - Cosine product: cos(x) * cos(y)")
println(s"  Expanded: ${test9.expand}")
println()

println("=" * 60)
println("TESTS COMPLETE")
println("=" * 60)
