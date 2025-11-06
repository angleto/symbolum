import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 80)
println("CRITICAL SIMPLIFICATION TESTS - MUST ALL PASS")
println("=" * 80)
println()

val n: Expr = Var("n")
var failCount = 0
var passCount = 0

def assertEqual(name: String, expr: Expr, expected: String, forbiddenPatterns: List[String] = List()): Unit = {
  println(s"Test: $name")
  println("-" * 80)
  val simplified = expr.fullSimplify
  val output = simplified.toString

  println(s"Output:   $output")
  println(s"Expected: $expected")

  var testPassed = true

  // Check exact match or semantic match
  if (output != expected) {
    // Allow some flexibility in formatting
    val normalizedOutput = output.replaceAll("\\s+", "")
    val normalizedExpected = expected.replaceAll("\\s+", "")

    if (normalizedOutput != normalizedExpected) {
      println(s"  ✗ FAIL: Output doesn't match expected")
      testPassed = false
    }
  }

  // Check for forbidden patterns
  for (pattern <- forbiddenPatterns) {
    if (output.contains(pattern)) {
      println(s"  ✗ FAIL: Contains forbidden pattern '$pattern'")
      testPassed = false
    }
  }

  if (testPassed) {
    println(s"  ✓ PASS")
    passCount += 1
  } else {
    failCount += 1
  }
  println()
}

def testNoForbidden(name: String, expr: Expr, forbiddenPatterns: List[String]): Unit = {
  println(s"Test: $name")
  println("-" * 80)
  val simplified = expr.fullSimplify
  val output = simplified.toString

  println(s"Output: $output")

  var testPassed = true

  for (pattern <- forbiddenPatterns) {
    if (output.contains(pattern)) {
      println(s"  ✗ FAIL: Contains forbidden pattern '$pattern'")
      val idx = output.indexOf(pattern)
      val start = math.max(0, idx - 20)
      val end = math.min(output.length, idx + pattern.length + 20)
      println(s"     Context: ...${output.substring(start, end)}...")
      testPassed = false
    }
  }

  if (testPassed) {
    println(s"  ✓ PASS - No forbidden patterns found")
    passCount += 1
  } else {
    failCount += 1
  }
  println()
}

println("SECTION 1: BASIC ARITHMETIC")
println("=" * 80)
println()

assertEqual("1 + 1",
  Add(Array(Num(1), Num(1))),
  "2",
  List("/", "+ -", "- -")
)

assertEqual("(1 + 1) / 2",
  Div(Array(Add(Array(Num(1), Num(1))), Num(2))),
  "1",
  List("/", "+ -")
)

assertEqual("n + n",
  Add(Array(n, n)),
  "2 * n",
  List("n + n", "+ -")
)

println()
println("SECTION 2: FRACTION SIMPLIFICATION")
println("=" * 80)
println()

assertEqual("(3*n + 1) / 2",
  Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2))),
  "(3 * n + 1)/2",
  List("+ -", "/2)/")
)

// CRITICAL TEST: This must work!
assertEqual("(1 + 3*n/2) / 2  →  (3*n + 2) / 4",
  Div(Array(
    Add(Array(Num(1), Div(Array(Mul(Array(Num(3), n)), Num(2))))),
    Num(2)
  )),
  "(3 * n + 2)/4",
  List("/2)/2", "()/", "+ -")
)

// CRITICAL TEST: Deeply nested
assertEqual("(3 * (3*n + 1)/2 + 1) / 2  →  (9*n + 5) / 4",
  Div(Array(
    Add(Array(
      Mul(Array(Num(3), Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2))))),
      Num(1)
    )),
    Num(2)
  )),
  "(9 * n + 5)/4",
  List("/2)/2", "/2)", "+ -")
)

// CRITICAL TEST: Triple nesting!
assertEqual("((3*(3*n+1)/2 + 1)/2 + 1) / 2  →  fully simplified",
  Div(Array(
    Add(Array(
      Div(Array(
        Add(Array(
          Mul(Array(Num(3), Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2))))),
          Num(1)
        )),
        Num(2)
      )),
      Num(1)
    )),
    Num(2)
  )),
  "(9 * n + 9)/8",  // (9n+5)/4 + 1 = (9n+5+4)/4 = (9n+9)/4, then /2 = (9n+9)/8
  List("/2)/2)/2", "/)/", "+ -")
)

println()
println("SECTION 3: NEGATIVE NUMBER HANDLING")
println("=" * 80)
println()

// CRITICAL TEST: All negative terms should factor
testNoForbidden("(-1 + -3*n/2) should not have + -",
  Add(Array(Num(-1), Mul(Array(Num(-3), Div(Array(n, Num(2))))))),
  List("+ -", "- -")
)

testNoForbidden("(-1 + -2*n/4)",
  Add(Array(Num(-1), Mul(Array(Num(-2), Div(Array(n, Num(4))))))),
  List("+ -", "- -")
)

println()
println("SECTION 4: COMPLEX FRACTION OPERATIONS")
println("=" * 80)
println()

assertEqual("2 * (n/4)  →  n/2",
  Mul(Array(Num(2), Div(Array(n, Num(4))))),
  "n/2",
  List("2 *", "* n", "/4")
)

assertEqual("3 * ((3*n+1)/2)  →  (9*n+3)/2",
  Mul(Array(Num(3), Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2))))),
  "(9 * n + 3)/2",
  List("3 * (", "/2)", "+ -")
)

assertEqual("n/2 + n/4  →  (3*n)/4",
  Add(Array(Div(Array(n, Num(2))), Div(Array(n, Num(4))))),
  "3 * n/4",
  List("n/2 +", "+ n/4", "/2 +")
)

println()
println("SECTION 5: REAL WORLD - COLLATZ COMPONENTS")
println("=" * 80)
println()

// Build collatz1
val collatz1_manual = Add(Array(
  n,
  Num(1, 4),
  Mul(Array(Num(-1), Div(Array(Add(Array(Mul(Array(Num(2), n)), Num(1))), Num(4))), Cos(Mul(Array(n, pi)))))
))

testNoForbidden("Collatz1 term",
  collatz1_manual,
  List("+ -", "- -", "/4)")
)

println()
println("=" * 80)
println("FINAL SUMMARY")
println("=" * 80)
println()
println(s"Tests passed: $passCount")
println(s"Tests failed: $failCount")
println()

if (failCount == 0) {
  println("✓✓✓ ALL CRITICAL TESTS PASSED ✓✓✓")
  println()
  println("System can now be tested with full Collatz3.")
} else {
  println("✗✗✗ CRITICAL TESTS FAILED ✗✗✗")
  println()
  println("DO NOT test Collatz3 until these basic tests pass!")
  println("The system has fundamental issues that must be fixed first.")
}
println()

System.exit(if (failCount == 0) 0 else 1)
