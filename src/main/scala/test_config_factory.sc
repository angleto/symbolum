import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg, SimplificationConfig}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 80)
println("SIMPLIFICATION CONFIGURATION TEST")
println("=" * 80)
println()

val n: Expr = Var("n")

// Test 1: List available configurations
println("Available configurations:")
println("-" * 80)
SimplificationConfig.availableConfigurations.foreach(name => println(s"  - $name"))
println()

// Test 2: Use factory to get configurations
println("Test factory pattern:")
println("-" * 80)
val defaultConfig = SimplificationConfig("default")
val collatz0Config = SimplificationConfig("collatz0")
val minimalConfig = SimplificationConfig("minimal")

println(s"Default config has ${defaultConfig.enabledRules.length} rules")
println(s"Collatz0 config has ${collatz0Config.enabledRules.length} rules")
println(s"Minimal config has ${minimalConfig.enabledRules.length} rules")
println()

// Test 3: Show Collatz0 rules in order
println("Collatz0 rules (in order):")
println("-" * 80)
collatz0Config.enabledRules.zipWithIndex.foreach { case (rule, idx) =>
  println(s"  ${idx + 1}. $rule")
}
println()

// Test 4: Test expression with Collatz0 config
println("Test Collatz0 configuration:")
println("-" * 80)

// Build a collatz-like expression
val collatz1 = Add(Array(
  n,
  Num(1, 4),
  Mul(Array(
    Num(-1),
    Div(Array(Add(Array(Mul(Array(Num(2), n)), Num(1))), Num(4))),
    Cos(Mul(Array(n, pi)))
  ))
))

println("Expression: n + 1/4 - (2*n + 1)/4 * cos(n*pi)")
println()

val simplified = collatz1.fullSimplify(collatz0Config)
println(s"Simplified with Collatz0: $simplified")
println()

// Check for product-to-sum application
val hasDistributed = !simplified.toString.contains(" * (")
println(s"Distribution applied: ${if (hasDistributed) "✓ YES" else "✗ NO"}")

val hasNoNegativePatterns = !simplified.toString.contains("+ -") &&
                            !simplified.toString.contains("- -")
println(s"Clean negative handling: ${if (hasNoNegativePatterns) "✓ YES" else "✗ NO"}")
println()

// Test 5: Compare with Default config
println("Comparison with Default configuration:")
println("-" * 80)
val simplifiedDefault = collatz1.fullSimplify(SimplificationConfig.Default)
println(s"With Default: $simplifiedDefault")
println()

if (simplified.toString != simplifiedDefault.toString) {
  println("✓ Collatz0 produces different result (as expected)")
  println(s"  Collatz0 length: ${simplified.toString.length}")
  println(s"  Default length: ${simplifiedDefault.toString.length}")
} else {
  println("✗ Results are the same")
}
println()

// Test 6: Invalid configuration name
println("Test error handling:")
println("-" * 80)
try {
  val invalid = SimplificationConfig("invalid_name")
  println("✗ FAIL: Should have thrown exception")
} catch {
  case e: IllegalArgumentException =>
    println("✓ PASS: Correctly threw IllegalArgumentException")
    println(s"  Message: ${e.getMessage}")
}
println()

println("=" * 80)
println("CONFIGURATION TEST COMPLETE")
println("=" * 80)
