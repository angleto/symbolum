import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 70)
println("COMPREHENSIVE SIMPLIFICATION TESTS")
println("=" * 70)
println()

val n: Expr = Var("n")

// Test 1: No duplicate signs (+ -, - -, etc.)
println("Test 1: Sign normalization")
println("-" * 70)
val test1a = Add(Array(n, Neg(Mul(Array(Num(2), n)))))
val test1a_simplified = test1a.fullSimplify
println(s"n + Neg(2*n) = $test1a_simplified")
println(s"Expected: n - 2 * n OR -n")
println(s"Should NOT contain: + - OR - -")
println()

val test1b = Add(Array(n, Mul(Array(Num(-2), n))))
val test1b_simplified = test1b.fullSimplify
println(s"n + (-2)*n = $test1b_simplified")
println(s"Expected: n - 2 * n OR -n")
println(s"Should NOT contain: + -")
println()

// Test 2: Nested fractions simplification
println("Test 2: Nested fractions")
println("-" * 70)
val test2a = Div(Array(
  Add(Array(
    Mul(Array(Num(3), Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2))))),
    Num(1)
  )),
  Num(2)
))
val test2a_simplified = test2a.fullSimplify
println(s"(3 * (3*n + 1)/2 + 1)/2 = $test2a_simplified")
println(s"Expected: (9*n + 5)/4")
println()

val test2b = Div(Array(
  Add(Array(Num(1), Mul(Array(Num(3), n)), Div(Array(Num(1), Num(2))))),
  Num(2)
))
val test2b_simplified = test2b.fullSimplify
println(s"(1 + 3*n/2)/2 = $test2b_simplified")
println(s"Expected: (2 + 3*n)/4 OR (3*n + 2)/4")
println()

// Test 3: Cosine argument simplification
println("Test 3: Cosine argument simplification")
println("-" * 70)
val test3a = Cos(Div(Array(
  Add(Array(Num(1), Mul(Array(Num(3), n)), Div(Array(Num(1), Num(2))))),
  Num(2)
)))
val test3a_simplified = test3a.fullSimplify
println(s"cos((1 + 3*n/2)/2) = $test3a_simplified")
println(s"Expected: cos((3*n + 2)/4) OR similar")
println()

val test3b = Cos(Mul(Array(
  Div(Array(
    Add(Array(Mul(Array(Num(3), n)), Num(1))),
    Num(4)
  )),
  pi
)))
val test3b_simplified = test3b.fullSimplify
println(s"cos((3*n + 1)/4 * pi) = $test3b_simplified")
println(s"Expected: cos((3*n + 1)/4 * pi) OR cos(pi * (3*n + 1)/4)")
println()

// Test 4: Fraction addition with different denominators
println("Test 4: Fraction addition")
println("-" * 70)
val test4a = Add(Array(
  Div(Array(Mul(Array(Num(3), n)), Num(2))),
  Div(Array(Num(1), Num(2)))
))
val test4a_simplified = test4a.fullSimplify
println(s"(3*n)/2 + 1/2 = $test4a_simplified")
println(s"Expected: (3*n + 1)/2")
println()

val test4b = Add(Array(
  Div(Array(Mul(Array(Num(3), n)), Num(4))),
  Div(Array(Num(1), Num(4))),
  Div(Array(Num(2), Num(4)))
))
val test4b_simplified = test4b.fullSimplify
println(s"(3*n)/4 + 1/4 + 2/4 = $test4b_simplified")
println(s"Expected: (3*n + 3)/4")
println()

// Test 5: Distribution of division over addition
println("Test 5: Division distribution")
println("-" * 70)
val test5a = Div(Array(
  Add(Array(
    Div(Array(Mul(Array(Num(9), n)), Num(2))),
    Num(1)
  )),
  Num(2)
))
val test5a_simplified = test5a.fullSimplify
println(s"((9*n)/2 + 1)/2 = $test5a_simplified")
println(s"Expected: (9*n + 2)/4")
println()

// Test 6: Multiple levels of nesting
println("Test 6: Deep nesting")
println("-" * 70)
val innerExpr = Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2)))
val middleExpr = Div(Array(Add(Array(Mul(Array(Num(3), innerExpr)), Num(1))), Num(2)))
val outerExpr = Div(Array(Add(Array(middleExpr, Num(1))), Num(2))
val test6_simplified = outerExpr.fullSimplify
println(s"Complex nested: $test6_simplified")
println(s"Should be fully simplified without nested fractions")
println()

// Test 7: Collatz1 (should be simple)
println("Test 7: Collatz1 simplification")
println("-" * 70)
val collatz1: Expr = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
val collatz1_simplified = collatz1.fullSimplify
println(s"collatz1(n) = $collatz1_simplified")
println(s"Expected: n + 1/4 - (2*n + 1)/4 * cos(n * pi)")
println(s"Should NOT contain: + -, - -, or nested fractions")
println()

// Test 8: Check output format
println("Test 8: Output format validation")
println("-" * 70)
val output = collatz1_simplified.toString
val hasDuplicateSigns = output.contains("+ -") || output.contains("- -") || output.contains("- +")
println(s"Contains duplicate signs (+ -, - -, - +): $hasDuplicateSigns")
if (hasDuplicateSigns) {
  println("FAIL: Output contains duplicate signs")
  println(s"Output: $output")
} else {
  println("PASS: No duplicate signs")
}
println()

// Test 9: Numeric coefficients
println("Test 9: Numeric coefficients")
println("-" * 70)
val test9 = Mul(Array(Num(3), Div(Array(Mul(Array(Num(2), n)), Num(4)))))
val test9_simplified = test9.fullSimplify
println(s"3 * (2*n/4) = $test9_simplified")
println(s"Expected: (3*n)/2 OR (6*n)/4")
println()

println("=" * 70)
println("TEST SUITE COMPLETE")
println("=" * 70)
println()
println("NOTE: If any tests show duplicate signs, nested fractions,")
println("or unsimplified expressions, the simplification system needs fixes.")
