import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg, SimplificationConfig}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 80)
println("FRACTION FACTORING TEST")
println("=" * 80)
println()

val n: Expr = Var("n")

// Test 1: Simple common denominator in Add
println("Test 1: -7/32 - 9/32 * n")
println("-" * 80)
val test1 = Add(Array(
  Num(-7, 32),
  Mul(Array(Num(-9, 32), n))
))
val result1 = test1.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test1")
println(s"Simplified: $result1")
println(s"Expected: (-7 - 9 * n)/32")
println()

// Test 2: Fractions that need Mul merging first
println("Test 2: -7/32 - 9/2 * n * 1/16")
println("-" * 80)
val test2 = Add(Array(
  Num(-7, 32),
  Mul(Array(Num(-9, 2), n, Num(1, 16)))
))
val result2 = test2.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test2")
println(s"Simplified: $result2")
println(s"Expected: (-7 - 9 * n)/32")
println()

// Test 3: Fractions in cosine argument
println("Test 3: cos(pi * (5/4 + 9 * n/4))")
println("-" * 80)
val test3 = Cos(Mul(Array(
  pi,
  Add(Array(
    Num(5, 4),
    Mul(Array(Num(9), n, Num(1, 4)))
  ))
)))
val result3 = test3.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test3")
println(s"Simplified: $result3")
println(s"Expected: cos(pi * (5 + 9 * n)/4)")
println()

// Test 4: More complex case with multiple terms
println("Test 4: 1/4 + 3/4 * n - 5/4")
println("-" * 80)
val test4 = Add(Array(
  Num(1, 4),
  Mul(Array(Num(3, 4), n)),
  Num(-5, 4)
))
val result4 = test4.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test4")
println(s"Simplified: $result4")
println(s"Expected: (-4 + 3 * n)/4 or (3 * n - 4)/4")
println()

// Test 5: Mixed Div and fractional Num
println("Test 5: 1/4 + (3*n)/4")
println("-" * 80)
val test5 = Add(Array(
  Num(1, 4),
  Div(Array(Mul(Array(Num(3), n)), Num(4)))
))
val result5 = test5.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test5")
println(s"Simplified: $result5")
println(s"Expected: (1 + 3 * n)/4")
println()

// Test 6: Expression from collatz3 - cosine argument simplification
println("Test 6: cos(pi * (5/4 + 9/4 * n))")
println("-" * 80)
val test6 = Cos(Mul(Array(
  pi,
  Add(Array(
    Num(5, 4),
    Mul(Array(Num(9, 4), n))
  ))
)))
val result6 = test6.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test6")
println(s"Simplified: $result6")
println(s"Expected: cos(pi * (5 + 9 * n)/4)")
println()

// Test 7: Negative terms with common denominator
println("Test 7: -7/32 - 9/2 * n/16")
println("-" * 80)
val test7a = Div(Array(Mul(Array(Num(9), n)), Num(2)))
val test7b = Div(Array(test7a, Num(16)))
val test7 = Add(Array(
  Num(-7, 32),
  Neg(test7b)
))
val result7 = test7.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test7")
println(s"Simplified: $result7")
println(s"Expected: (-7 - 72 * n)/32")
println()

println("=" * 80)
println("FRACTION FACTORING TEST COMPLETE")
println("=" * 80)
