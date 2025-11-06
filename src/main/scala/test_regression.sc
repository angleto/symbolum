import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 80)
println("NON-REGRESSION TEST SUITE")
println("=" * 80)
println()

val n: Expr = Var("n")
var failCount = 0
var passCount = 0

def test(name: String, expr: Expr, expectedPatterns: List[String], forbiddenPatterns: List[String]): Unit = {
  println(s"Test: $name")
  println("-" * 80)
  val simplified = expr.fullSimplify
  val output = simplified.toString

  println(s"Input:  ${expr.toString.take(100)}${if (expr.toString.length > 100) "..." else ""}")
  println(s"Output: ${output.take(100)}${if (output.length > 100) "..." else ""}")

  var testPassed = true

  // Check for expected patterns
  for (pattern <- expectedPatterns) {
    if (!output.contains(pattern)) {
      println(s"  ✗ FAIL: Missing expected pattern '$pattern'")
      testPassed = false
    }
  }

  // Check for forbidden patterns
  for (pattern <- forbiddenPatterns) {
    if (output.contains(pattern)) {
      println(s"  ✗ FAIL: Contains forbidden pattern '$pattern'")
      testPassed = false
      // Show where it appears
      val idx = output.indexOf(pattern)
      val start = math.max(0, idx - 15)
      val end = math.min(output.length, idx + pattern.length + 15)
      println(s"     Found at: ...${output.substring(start, end)}...")
    }
  }

  if (testPassed) {
    println(s"  ✓ PASS")
    passCount += 1
  } else {
    println(s"  Full output: $output")
    failCount += 1
  }
  println()
}

println("BASIC TESTS")
println("=" * 80)
println()

// Test 1: Simple negation
test("Simple negation: -(2*n)",
  Neg(Mul(Array(Num(2), n))),
  List("-2", "n"),  // Should contain -2 and n
  List("+ -", "- -", "Neg", "--")  // Should not contain these
)

// Test 2: Negation in addition
test("Negation in addition: n + -(2*n)",
  Add(Array(n, Neg(Mul(Array(Num(2), n))))),
  List("-"),  // Should have subtraction
  List("+ -", "- -", "- +")  // No duplicate signs
)

// Test 3: Double negation
test("Double negation: -(-n)",
  Neg(Neg(n)),
  List("n"),  // Should be just n
  List("-", "Neg")  // No negation at all
)

// Test 4: Negation of addition
test("Negation of addition: -(n + 2)",
  Neg(Add(Array(n, Num(2)))),
  List(),  // Will check forbidden patterns
  List("+ -", "- -", "-(")  // No Neg wrapper
)

// Test 5: Simple fraction simplification
test("Simple fraction: (1 + 1)/2",
  Div(Array(Add(Array(Num(1), Num(1))), Num(2))),
  List("1"),  // Should be 1
  List("/", "2")  // Should not have division (simplifies to 1)
)

// Test 6: Fraction with variable
test("Fraction with variable: (3*n + 1)/2",
  Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2))),
  List("(3", "n", "1)", "/", "2"),  // Should be (3*n + 1)/2 or similar
  List("+ -", "- -")  // No duplicate signs
)

// Test 7: Nested fraction
test("Nested fraction: ((3*n + 1)/2 + 1)/2",
  Div(Array(Add(Array(Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2))), Num(1))), Num(2))),
  List("(3", "n", ")/4"),  // Should be (3*n + ...)/4
  List(")/2)/2", "()/2)/2")  // No nested divisions
)

// Test 8: Very nested fraction
test("Very nested: (3 * (3*n + 1)/2 + 1)/2",
  Div(Array(
    Add(Array(
      Mul(Array(Num(3), Div(Array(Add(Array(Mul(Array(Num(3), n)), Num(1))), Num(2))))),
      Num(1)
    )),
    Num(2)
  )),
  List("(9", "n", ")/4"),  // Should be (9*n + 5)/4
  List("/2)/2", "()/2")  // No nested divisions
)

// Test 9: Addition with different denominators
test("Different denominators: n/2 + 1/4",
  Add(Array(Div(Array(n, Num(2))), Div(Array(Num(1), Num(4))))),
  List("/4"),  // Should have common denominator 4
  List()
)

// Test 10: Multiplication with fraction
test("Multiplication with fraction: 2 * (n/4)",
  Mul(Array(Num(2), Div(Array(n, Num(4))))),
  List("n", "/"),  // Should be n/2
  List("2 *")  // 2 should be merged into fraction
)

// Test 11: Cosine with simple argument
test("Cosine: cos(n * pi)",
  Cos(Mul(Array(n, pi))),
  List("cos", "n", "pi"),
  List("+ -", "- -")
)

// Test 12: Negated fraction coefficient
test("Negated fraction coefficient: -(1/4 * cos(n*pi))",
  Neg(Mul(Array(Div(Array(Num(1), Num(4))), Cos(Mul(Array(n, pi)))))),
  List("-", "1/4", "cos"),
  List("+ -", "- -", "-(")  // No Neg wrapper
)

println()
println("=" * 80)
println("INTERMEDIATE COMPLEXITY TESTS")
println("=" * 80)
println()

// Test 13: Expression from collatz1
val collatz1_term = Neg(Mul(Array(Div(Array(Add(Array(Mul(Array(Num(2), n)), Num(1))), Num(4))), Cos(Mul(Array(n, pi))))))
test("Collatz1 term: -((2*n + 1)/4 * cos(n*pi))",
  collatz1_term,
  List("-", "(2", "n", "1)", "/", "4", "cos"),
  List("+ -", "- -", "- +", "-(", ")/4)")  // No wrappers or bad nesting
)

// Test 14: Sum of fractions
test("Sum of fractions: 1/4 + 1/2 + 1/4",
  Add(Array(Div(Array(Num(1), Num(4))), Div(Array(Num(1), Num(2))), Div(Array(Num(1), Num(4))))),
  List("1"),  // Should be 1
  List("/")  // No fractions left
)

// Test 15: Fraction addition with variables
test("Fraction addition: n/4 + n/4 + n/2",
  Add(Array(
    Div(Array(n, Num(4))),
    Div(Array(n, Num(4))),
    Div(Array(n, Num(2)))
  )),
  List("n"),
  List("n/4 +", "+ n/4")  // Should be combined
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
  println("✓✓✓ ALL TESTS PASSED ✓✓✓")
  println()
  println("System is ready for Collatz3 testing.")
} else {
  println("✗✗✗ SOME TESTS FAILED ✗✗✗")
  println()
  println("Fix the failures above before testing Collatz3.")
  println("The simplification system has regressions that must be fixed.")
}
println()
