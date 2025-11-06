import symbolicas.{Expr, Num, Var, Add, Mul, Cos}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 80)
println("TESTING AGGRESSIVE EXPANSION")
println("=" * 80)
println()

val n: Expr = Var("n")
val A = n * pi / 2.0
val B = Num(1, 16)
val C = (n + 1) / 32.0

// Test 1: Simple product distribution
println("Test 1: cos(A) * (B + C)")
println("-" * 80)
val expr1: Expr = cos(A) * (B + C)
println(s"Original: $expr1")
val simplified1 = expr1.fullSimplify
println(s"Simplified: $simplified1")
println()

// Check that it's expanded (no large blocks)
val str1 = simplified1.toString
val hasLargeParens = str1.contains("(") && str1.indexOf(")") - str1.indexOf("(") > 20
println(s"Has large parenthesized blocks: $hasLargeParens (should be false)")
println()

// Test 2: Nested product distribution
println("Test 2: cos(A) * (B + cos(A) * C)")
println("-" * 80)
val expr2: Expr = cos(A) * (B + cos(A) * C)
println(s"Original: $expr2")
val simplified2 = expr2.fullSimplify
println(s"Simplified: $simplified2")
println()

// Count terms (should have multiple separate terms)
val str2 = simplified2.toString
val numTerms = str2.count(c => c == '+' || c == '-') + 1
println(s"Number of top-level terms: $numTerms (should be >= 2)")
println()

// Test 3: Larger expression with 5 terms
println("Test 3: cos(A) * (B + C + B + C + B) - 5 terms")
println("-" * 80)
val expr3: Expr = cos(A) * (B + C + B + C + B)
println(s"Original: $expr3")
val simplified3 = expr3.fullSimplify
println(s"Simplified: $simplified3")
println()

val str3 = simplified3.toString
val hasCosParen = str3.matches(".*cos\\([^)]+\\)\\s*\\*\\s*\\([^)]{20,}.*")
println(s"Has pattern 'cos(...) * (large_block)': $hasCosParen (should be false)")
println()

println("=" * 80)
println("SUMMARY")
println("=" * 80)
println("If all tests show 'false' for large blocks, the expansion is working correctly!")
println()
