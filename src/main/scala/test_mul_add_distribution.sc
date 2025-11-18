import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg, SimplificationConfig}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 80)
println("MUL * ADD DISTRIBUTION TEST")
println("=" * 80)
println()

val n: Expr = Var("n")

// Test 1: Simple cos * (a + b)
println("Test 1: cos(n*pi) * (a + b) should become cos(n*pi)*a + cos(n*pi)*b")
println("-" * 80)
val a = Var("a")
val b = Var("b")
val test1 = Mul(Array(
  Cos(Mul(Array(n, pi))),
  Add(Array(a, b))
))
val result1 = test1.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test1")
println(s"Simplified: $result1")
println(s"Should contain separate terms")
println()

// Test 2: Numeric * (sum of terms)
println("Test 2: 2 * (x + y + z) should become 2*x + 2*y + 2*z")
println("-" * 80)
val x = Var("x")
val y = Var("y")
val z = Var("z")
val test2 = Mul(Array(
  Num(2),
  Add(Array(x, y, z))
))
val result2 = test2.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test2")
println(s"Simplified: $result2")
println(s"Expected: 2 * x + 2 * y + 2 * z")
println()

// Test 3: Fraction * (sum)
println("Test 3: 1/2 * (n + 1) should become n/2 + 1/2")
println("-" * 80)
val test3 = Mul(Array(
  Num(1, 2),
  Add(Array(n, Num(1)))
))
val result3 = test3.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test3")
println(s"Simplified: $result3")
println(s"Expected: n/2 + 1/2 or (n + 1)/2")
println()

// Test 4: Collatz-like: cos(n/2*pi) * (term1 + term2 + term3)
println("Test 4: cos(n/2*pi) * (-1/8*n + -1/16 + 1/8)")
println("-" * 80)
val test4 = Mul(Array(
  Cos(Mul(Array(Div(Array(n, Num(2))), pi))),
  Add(Array(
    Mul(Array(Num(-1, 8), n)),
    Num(-1, 16),
    Num(1, 8)
  ))
))
val result4 = test4.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test4")
println(s"Simplified: $result4")
println(s"Should have 3 separate terms with cos(n/2*pi)")
val termsCount = result4.toString.split("\\+|(?<![\\(])-").length
println(s"Terms count: $termsCount (expecting 3 or more)")
println()

// Test 5: Nested case: cos(a) * (b + cos(c) * (d + e))
println("Test 5: Nested Mul-Add: cos(a) * (b + cos(c) * (d + e))")
println("-" * 80)
val test5 = Mul(Array(
  Cos(a),
  Add(Array(
    b,
    Mul(Array(
      Cos(Cos(a)),
      Add(Array(Var("d"), Var("e")))
    ))
  ))
))
val result5 = test5.fullSimplify(SimplificationConfig.Default)
println(s"Expression: $test5")
println(s"Simplified: $result5")
println(s"Should be fully distributed")
println()

println("=" * 80)
println("DISTRIBUTION TEST COMPLETE")
println("=" * 80)
