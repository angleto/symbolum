import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg, SimplificationConfig}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 80)
println("NESTED DIVISION SIMPLIFICATION TEST")
println("=" * 80)
println()

val n: Expr = Var("n")

// Test 1: Simple nested division
println("Test 1: expr/16/2 should become expr/32")
println("-" * 80)
val test1 = Div(Array(Div(Array(n, Num(16))), Num(2)))
val result1 = test1.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test1")
println(s"Simplified: $result1")
println(s"Expected: n/32")
println()

// Test 2: Complex numerator with nested division
println("Test 2: (9*n + 7)/16/2 should become (9*n + 7)/32")
println("-" * 80)
val test2 = Div(Array(
  Div(Array(Add(Array(Mul(Array(Num(9), n)), Num(7))), Num(16))),
  Num(2)
))
val result2 = test2.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test2")
println(s"Simplified: $result2")
println(s"Expected: (9 * n + 7)/32")
println()

// Test 3: Negative numerator with nested division
println("Test 3: (-9*n - 7)/16/2 should become (-9*n - 7)/32")
println("-" * 80)
val test3 = Div(Array(
  Div(Array(Add(Array(Mul(Array(Num(-9), n)), Num(-7))), Num(16))),
  Num(2)
))
val result3 = test3.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test3")
println(s"Simplified: $result3")
println(s"Expected: (-9 * n - 7)/32")
println()

// Test 4: Multiplication of fractions
println("Test 4: 1/2 * 2/2 should become 1/2")
println("-" * 80)
val test4 = Mul(Array(
  Num(1, 2),
  Div(Array(Num(2), Num(2)))
))
val result4 = test4.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test4")
println(s"Simplified: $result4")
println(s"Expected: 1/2")
println()

// Test 5: Num * Div should merge denominators
println("Test 5: 1/2 * n/16 should become n/32")
println("-" * 80)
val test5 = Mul(Array(
  Num(1, 2),
  Div(Array(n, Num(16)))
))
val result5 = test5.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test5")
println(s"Simplified: $result5")
println(s"Expected: n/32")
println()

// Test 6: Add expression in numerator with nested division
println("Test 6: (-n/16 - 1/8)/2 should become (-n/32 - 1/16)")
println("-" * 80)
val test6 = Div(Array(
  Add(Array(
    Div(Array(Neg(n), Num(16))),
    Num(-1, 8)
  )),
  Num(2)
))
val result6 = test6.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test6")
println(s"Simplified: $result6")
println(s"Expected: (-n/32 - 1/16) or similar")
println()

// Test 7: Multiple nested divisions
println("Test 7: n/2/4/8 should become n/64")
println("-" * 80)
val test7 = Div(Array(n, Num(2), Num(4), Num(8)))
val result7 = test7.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test7")
println(s"Simplified: $result7")
println(s"Expected: n/64")
println()

// Test 8: Div * Div multiplication
println("Test 8: (n + 1)/16 * 1/2 should become (n + 1)/32")
println("-" * 80)
val test8 = Mul(Array(
  Div(Array(Add(Array(n, Num(1))), Num(16))),
  Num(1, 2)
))
val result8 = test8.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test8")
println(s"Simplified: $result8")
println(s"Expected: (n + 1)/32")
println()

println("=" * 80)
println("NESTED DIVISION TEST COMPLETE")
println("=" * 80)
