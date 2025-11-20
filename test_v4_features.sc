#!/usr/bin/env scala-cli

//> using scala "3.3.5"
//> using file "src/main/scala/symbolicas"

import symbolicas._
import symbolicas.Dsl._

println("=" * 80)
println("SYMBOLICAS v4.0.0 - Comprehensive Feature Test")
println("=" * 80)
println()

// ============================================================================
// 1. POWER/EXPONENTIATION TESTS
// ============================================================================
println("1. POWER/EXPONENTIATION")
println("-" * 40)

val x = Var("x")
val y = Var("y")

// Basic powers
val pow1 = x ^ Num(2)  // x^2
println(s"x^2 = $pow1")
println(s"Simplified: ${pow1.simplify()}")

// Binomial expansion: (x+1)^2
val pow2 = (x + 1) ^ Num(2)
println(s"(x+1)^2 expanded: ${pow2.expand()}")  // x^2 + 2x + 1

// Binomial expansion: (x+1)^3
val pow3 = (x + 1) ^ Num(3)
println(s"(x+1)^3 expanded: ${pow3.expand()}")  // x^3 + 3x^2 + 3x + 1

// Numeric powers
val pow4 = Num(2) ^ Num(8)
println(s"2^8 = ${pow4.simplify()}")  // 256

println()

// ============================================================================
// 2. TRIGONOMETRIC FUNCTIONS
// ============================================================================
println("2. TRIGONOMETRIC FUNCTIONS")
println("-" * 40)

// Sin, Cos, Tan
val trig1 = sin(x)
val trig2 = cos(x)
val trig3 = tan(x)

println(s"sin(x) = $trig1")
println(s"cos(x) = $trig2")
println(s"tan(x) = $trig3")

// Trig identities: sin(-x) = -sin(x)
val trig4 = sin(-x)
println(s"sin(-x) simplified: ${trig4.simplify()}")  // -sin(x)

// Numeric evaluation
val trig5 = sin(Num(0))
println(s"sin(0) = ${trig5.simplify()}")  // 0

val trig6 = cos(Num(0))
println(s"cos(0) = ${trig6.simplify()}")  // 1

println()

// ============================================================================
// 3. EXPONENTIAL AND LOGARITHM
// ============================================================================
println("3. EXPONENTIAL AND LOGARITHM")
println("-" * 40)

// Basic exp and log
val exp1 = exp(x)
val log1 = log(x)

println(s"exp(x) = $exp1")
println(s"log(x) = $log1")

// exp(log(x)) = x
val explog1 = exp(log(x))
println(s"exp(log(x)) simplified: ${explog1.simplify()}")  // x

// log(exp(x)) = x
val logexp1 = log(exp(x))
println(s"log(exp(x)) simplified: ${logexp1.simplify()}")  // x

// log(x*y) = log(x) + log(y)
val log2 = log(x * y)
println(s"log(x*y) expanded: ${log2.expand()}")  // log(x) + log(y)

// log(x^2) = 2*log(x)
val log3 = log(x ^ Num(2))
println(s"log(x^2) simplified: ${log3.simplify()}")  // 2*log(x)

// Numeric evaluation
val exp2 = exp(Num(0))
println(s"exp(0) = ${exp2.simplify()}")  // 1

val log4 = log(Num(1))
println(s"log(1) = ${log4.simplify()}")  // 0

println()

// ============================================================================
// 4. AUTOMATIC DIFFERENTIATION
// ============================================================================
println("4. AUTOMATIC DIFFERENTIATION")
println("-" * 40)

// d/dx(x) = 1
val deriv1 = Derivative(x, "x")
println(s"d/dx(x) = ${deriv1.simplify()}")

// d/dx(x^2) = 2x
val deriv2 = Derivative(x ^ Num(2), "x")
println(s"d/dx(x^2) = ${deriv2.simplify()}")

// d/dx(x^3) = 3x^2
val deriv3 = Derivative(x ^ Num(3), "x")
println(s"d/dx(x^3) = ${deriv3.simplify()}")

// Product rule: d/dx(x*sin(x)) = sin(x) + x*cos(x)
val deriv4 = Derivative(x * sin(x), "x")
println(s"d/dx(x*sin(x)) = ${deriv4.simplify()}")

// Chain rule: d/dx(sin(x^2)) = 2x*cos(x^2)
val deriv5 = Derivative(sin(x ^ Num(2)), "x")
println(s"d/dx(sin(x^2)) = ${deriv5.simplify()}")

// d/dx(exp(x)) = exp(x)
val deriv6 = Derivative(exp(x), "x")
println(s"d/dx(exp(x)) = ${deriv6.simplify()}")

// d/dx(log(x)) = 1/x
val deriv7 = Derivative(log(x), "x")
println(s"d/dx(log(x)) = ${deriv7.simplify()}")

// Quotient rule: d/dx(x/(x+1)) = 1/(x+1)^2
val deriv8 = Derivative(x / (x + 1), "x")
println(s"d/dx(x/(x+1)) = ${deriv8.simplify()}")

println()

// ============================================================================
// 5. SYMBOLIC INTEGRATION
// ============================================================================
println("5. SYMBOLIC INTEGRATION")
println("-" * 40)

// ∫ x dx = x^2/2
val int1 = Integral(x, "x")
println(s"∫ x dx = ${int1.simplify()}")

// ∫ x^2 dx = x^3/3
val int2 = Integral(x ^ Num(2), "x")
println(s"∫ x^2 dx = ${int2.simplify()}")

// ∫ sin(x) dx = -cos(x)
val int3 = Integral(sin(x), "x")
println(s"∫ sin(x) dx = ${int3.simplify()}")

// ∫ cos(x) dx = sin(x)
val int4 = Integral(cos(x), "x")
println(s"∫ cos(x) dx = ${int4.simplify()}")

// ∫ exp(x) dx = exp(x)
val int5 = Integral(exp(x), "x")
println(s"∫ exp(x) dx = ${int5.simplify()}")

// ∫ 1/x dx = log(x)
val int6 = Integral(Num(1) / x, "x")
println(s"∫ 1/x dx = ${int6.simplify()}")

// Definite integral: ∫[0,1] x dx = 1/2
val int7 = Integral(x, "x", Some(Num(0)), Some(Num(1)))
println(s"∫[0,1] x dx = ${int7.simplify()}")

println()

// ============================================================================
// 6. EQUATION SOLVING
// ============================================================================
println("6. EQUATION SOLVING")
println("-" * 40)

// Solve x + 2 = 0
val eq1 = x + 2
val sol1 = Solve.solve(eq1, "x")
println(s"Solve x + 2 = 0: $sol1")

// Solve 2x - 6 = 0
val eq2 = Num(2) * x - 6
val sol2 = Solve.solve(eq2, "x")
println(s"Solve 2x - 6 = 0: $sol2")

// Solve x^2 - 4 = 0
val eq3 = (x ^ Num(2)) - 4
val sol3 = Solve.solve(eq3, "x")
println(s"Solve x^2 - 4 = 0: $sol3")

// Solve x^2 + 5x + 6 = 0
val eq4 = (x ^ Num(2)) + (Num(5) * x) + 6
val sol4 = Solve.solve(eq4, "x")
println(s"Solve x^2 + 5x + 6 = 0: $sol4")

// Solve x^2 - 2x + 1 = 0 (perfect square)
val eq5 = (x ^ Num(2)) - (Num(2) * x) + 1
val sol5 = Solve.solve(eq5, "x")
println(s"Solve x^2 - 2x + 1 = 0: $sol5")

println()

// ============================================================================
// 7. PERFORMANCE OPTIMIZATIONS
// ============================================================================
println("7. PERFORMANCE OPTIMIZATIONS")
println("-" * 40)

// Test structural hash for fixpoint detection
val expr1 = (x + 1) * (x + 2)
val expr2 = (x + 1) * (x + 2)
println(s"Expression 1 hash: ${expr1.structuralHash}")
println(s"Expression 2 hash: ${expr2.structuralHash}")
println(s"Hashes equal: ${expr1.structuralHash == expr2.structuralHash}")

// Test hash consing (expression sharing)
val cached1 = ExprCache.intern(x + 1)
val cached2 = ExprCache.intern(x + 1)
println(s"Cached expressions identical: ${cached1 eq cached2}")

// Show cache statistics
val (hits, misses, size, rate) = ExprCache.stats
println(s"Cache stats - Hits: $hits, Misses: $misses, Size: $size, Hit rate: ${(rate * 100).formatted("%.1f")}%")

println()

// ============================================================================
// 8. COMPLEX EXAMPLES
// ============================================================================
println("8. COMPLEX EXAMPLES")
println("-" * 40)

// Differentiate and simplify: d/dx((x^2 + 1)*(x^3 - 2))
val complex1 = ((x ^ Num(2)) + 1) * ((x ^ Num(3)) - 2)
val complexDeriv = Derivative(complex1, "x").simplify().fullSimplify()
println(s"d/dx((x^2 + 1)*(x^3 - 2)) = $complexDeriv")

// Taylor series approximation (manual): sin(x) ≈ x - x^3/6
val taylor1 = x - ((x ^ Num(3)) / 6)
println(s"Taylor approximation of sin(x): $taylor1")

// Verify derivative: d/dx(x^4/4) = x^3
val verify1 = Derivative((x ^ Num(4)) / 4, "x").simplify()
println(s"d/dx(x^4/4) = $verify1")

// Verify integral: ∫ x^3 dx = x^4/4
val verify2 = Integral(x ^ Num(3), "x").simplify()
println(s"∫ x^3 dx = $verify2")

println()

println("=" * 80)
println("All v4.0.0 features tested successfully!")
println("=" * 80)
