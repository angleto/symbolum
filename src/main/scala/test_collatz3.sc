import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 80)
println("COLLATZ3 SIMPLIFICATION TEST")
println("=" * 80)
println()

val n: Expr = Var("n")

// Build collatz expressions
val collatz1: Expr = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

val collatz2Even: Expr = collatz1.replaceSymbol("n", n/2)
val collatz2Odd: Expr = collatz1.replaceSymbol("n", (n*3+1)/2)
val collatz2: Expr = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

val collatz3Even: Expr = collatz2.replaceSymbol("n", n/2)
val collatz3Odd: Expr = collatz2.replaceSymbol("n", (n*3+1)/2)
val collatz3: Expr = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)

println("Testing collatz1 simplification:")
println("-" * 80)
val c1_simplified = collatz1.fullSimplify
println(s"collatz1(n) = $c1_simplified")
println()

val c1_output = c1_simplified.toString
val c1_hasDuplicateSigns = c1_output.contains("+ -") || c1_output.contains("- -") || c1_output.contains("- +")
println(s"✓ Duplicate signs check (should be false): $c1_hasDuplicateSigns")
println()

println("Testing collatz2 simplification:")
println("-" * 80)
val c2_simplified = collatz2.fullSimplify
val c2_output = c2_simplified.toString
println(s"Output length: ${c2_output.length} characters")
println()
if (c2_output.length < 500) {
  println(s"collatz2(n) = $c2_simplified")
} else {
  println("Output is long (>500 chars), showing first 300 characters:")
  println(c2_output.take(300) + "...")
}
println()

val c2_hasDuplicateSigns = c2_output.contains("+ -") || c2_output.contains("- -") || c2_output.contains("- +")
println(s"✓ Duplicate signs check (should be false): $c2_hasDuplicateSigns")
println()

println("Testing collatz3 simplification:")
println("-" * 80)
println("This may take a moment...")
val c3_simplified = collatz3.fullSimplify
val c3_output = c3_simplified.toString
println(s"Output length: ${c3_output.length} characters")
println()

if (c3_output.length < 800) {
  println(s"collatz3(n) = $c3_simplified")
} else {
  println("Output is long (>800 chars), showing first 400 characters:")
  println(c3_output.take(400) + "...")
  println()
  println("Last 400 characters:")
  println("..." + c3_output.takeRight(400))
}
println()

// Check for specific issues
println("Diagnostic checks:")
println("-" * 80)

val c3_hasDuplicateSigns = c3_output.contains("+ -") || c3_output.contains("- -") || c3_output.contains("- +")
println(s"1. Duplicate signs (+ -, - -, - +): $c3_hasDuplicateSigns")
if (c3_hasDuplicateSigns) {
  println("   FAIL: Output contains duplicate signs")
  // Find and show examples
  val duplicatePatterns = Seq("+ -", "- -", "- +")
  duplicatePatterns.foreach { pattern =>
    val idx = c3_output.indexOf(pattern)
    if (idx >= 0) {
      val start = math.max(0, idx - 20)
      val end = math.min(c3_output.length, idx + pattern.length + 20)
      println(s"   Found '$pattern' at position $idx:")
      println(s"   ...${c3_output.substring(start, end)}...")
    }
  }
} else {
  println("   PASS: No duplicate signs found")
}
println()

val hasUnsimplifiedCosArg = c3_output.contains("(1 + 3 * n") || c3_output.contains("(3 * (3 * n")
println(s"2. Unsimplified cosine arguments: $hasUnsimplifiedCosArg")
if (hasUnsimplifiedCosArg) {
  println("   FAIL: Cosine arguments not fully simplified")
  println("   Examples found:")
  if (c3_output.contains("(1 + 3 * n")) {
    println("   - Contains '(1 + 3 * n' pattern")
  }
  if (c3_output.contains("(3 * (3 * n")) {
    println("   - Contains '(3 * (3 * n' nested pattern")
  }
} else {
  println("   PASS: Cosine arguments appear simplified")
}
println()

val hasNestedFractions = c3_output.matches(".*/.*/.+") // Very rough check
println(s"3. Potentially nested fractions: $hasNestedFractions")
if (hasNestedFractions) {
  println("   WARNING: May contain nested fractions (manual check needed)")
} else {
  println("   PASS: No obvious nested fraction patterns")
}
println()

// Count the number of terms (very rough estimate)
val numPlusMinusSigns = c3_output.count(c => c == '+' || c == '-')
println(s"4. Number of +/- operations: $numPlusMinusSigns")
println("   (Expected: ~40-50 for fully simplified collatz3)")
println()

println("=" * 80)
println("TEST SUMMARY")
println("=" * 80)

val allTestsPass = !c1_hasDuplicateSigns && !c3_hasDuplicateSigns && !hasUnsimplifiedCosArg
if (allTestsPass) {
  println("✓ ALL TESTS PASSED")
} else {
  println("✗ SOME TESTS FAILED - See details above")
}
println()

println("Expected final form (from LaTeX):")
println("- Clean sum of terms with no duplicate signs")
println("- Each term: coefficient * cos(simple_arg)")
println("- Fractions like 3/4, (2n+1)/4, (3n+2)/8, etc.")
println("- Cosine args like: πn, π(3n+1)/2, π(n+1)/2, etc.")
println()
