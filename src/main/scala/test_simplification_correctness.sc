import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 70)
println("SIMPLIFICATION CORRECTNESS TEST")
println("=" * 70)
println()

val TOLERANCE = 1e-10

def checkCorrectness(name: String, original: Expr, variables: Map[String, Double]): Unit = {
  val simplified = original.fullSimplify
  val originalValue = original.eval(variables)
  val simplifiedValue = simplified.eval(variables)
  val diff = math.abs(originalValue - simplifiedValue)

  println(s"Test: $name")
  println(s"  Original expression length: ${original.toString.length} chars")
  println(s"  Simplified expression length: ${simplified.toString.length} chars")
  println(s"  Original value: $originalValue")
  println(s"  Simplified value: $simplifiedValue")
  println(s"  Difference: $diff")

  if (diff < TOLERANCE) {
    println(s"  ✓ PASS: Simplification preserves mathematical meaning")
  } else {
    println(s"  ✗ FAIL: Simplification changed the value!")
    println(s"  Original: $original")
    println(s"  Simplified: $simplified")
  }
  println()
}

// Test 1: Simple expression
val x = Var("x")
checkCorrectness("x + x", x + x, Map("x" -> 5.0))

// Test 2: Collatz 1
val n = Var("n")
val variables = Map("n" -> 123.0, "pi" -> math.Pi)

val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
checkCorrectness("collatz1", collatz1, variables)

// Test 3: Collatz 2
val collatz2Even = collatz1.replaceSymbol("n", n/2)
val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)
checkCorrectness("collatz2", collatz2, variables)

// Test 4: Collatz 3
val collatz3Even = collatz2.replaceSymbol("n", n/2)
val collatz3Odd = collatz2.replaceSymbol("n", (n*3+1)/2)
val collatz3 = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)
checkCorrectness("collatz3", collatz3, variables)

// Test 5: Trigonometric
checkCorrectness("2 * cos(n*pi)", Num(2) * cos(n * pi), variables)

// Test 6: Fractions
checkCorrectness("1/2 + 1/3", Num(1,2) + Num(1,3), Map.empty)

// Test 7: Distribution
val y = Var("y")
checkCorrectness("x * (y + 2)", x * (y + Num(2)), Map("x" -> 3.0, "y" -> 7.0))

println("=" * 70)
println("SIMPLIFIED EXPRESSIONS")
println("=" * 70)
println()

println(s"collatz1(n) simplified = ${collatz1.fullSimplify}")
println()
println(s"collatz2(n) simplified = ${collatz2.fullSimplify}")
println()
println(s"collatz3(n) simplified = ${collatz3.fullSimplify}")
println()

println("=" * 70)
println("TEST COMPLETE")
println("=" * 70)
