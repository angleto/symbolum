# Testing Guide for Symbolicas

**Version:** 4.0.0-SNAPSHOT
**Last Updated:** 2025-11-20

## Overview

This guide covers testing for Symbolicas v4.0, including basic algebra, calculus, equation solving, and advanced features.

## Prerequisites

You need Scala 3.3.5 and SBT installed. Install using one of these methods:

### Option 1: Using Coursier (Recommended)
```bash
curl -fL https://github.com/coursier/coursier/releases/latest/download/cs-x86_64-pc-linux.gz | gzip -d > cs
chmod +x cs
./cs setup
```

### Option 2: Using SDKMAN
```bash
curl -s "https://get.sdkman.io" | bash
source "$HOME/.sdkman/bin/sdkman-init.sh"
sdk install java
sdk install scala 3.3.5
sdk install sbt
```

### Option 3: Manual Download
Download Scala 3.3.5 from: https://github.com/scala/scala3/releases/tag/3.3.5

## Running Tests

From the project root directory:

### Test 1: Compile the Project
```bash
sbt compile
```

**Expected output:** Successful compilation with no errors

### Test 2: Run Basic Simplification Tests
```bash
cd src/main/scala
scala-cli test_improved.sc
```

**Expected output:**
- Double negative elimination: `--x` → `x`
- Addition with negative: `x + (-y)` displayed as `x - y`
- Nested additions flattened
- Fractions kept symbolic (unless same denominator)
- Clean display without `.0` decimals

### Test 3: Run Configuration Tests
```bash
cd src/main/scala
scala-cli test_config.sc
```

**Expected output:** Verification of all 12 simplification rules working correctly

### Test 4: Run Trigonometric Tests
```bash
cd src/main/scala
scala-cli test_cosine_simplification.sc
```

**Expected output:** Product-to-sum transformations and cosine argument simplification

### Test 5: Run Collatz Tests
```bash
cd src/main/scala
scala-cli test_collatz3.sc
```

**Expected output:** Complex Collatz expressions with:
- Clean subtraction symbols (`-` not `+ -`)
- Proper parenthesization
- Symbolic fractions preserved
- Coefficients grouped logically

## v4.0 Feature Tests

### Power and Exponentiation
```scala
import symbolicas._
import symbolicas.Dsl._

val x = Var("x")

// Power operator
val test1 = (x ^ Num(2)).toString
println(s"x^2 = $test1")  // Should show: x^2

// Binomial expansion
val test2 = ((x + 1) ^ Num(3)).expand()
println(s"(x+1)^3 = $test2")  // Should show: x^3 + 3*x^2 + 3*x + 1

// Power laws
val test3 = (x ^ Num(0)).simplify()
println(s"x^0 = $test3")  // Should show: 1
```

### Trigonometric Functions
```scala
import symbolicas._
import symbolicas.Dsl._

val x = Var("x")

// Sin and tan
val test1 = sin(x).toString
val test2 = tan(x).toString
println(s"sin(x) = $test1")
println(s"tan(x) = $test2")

// Odd function property
val test3 = sin(-x).simplify()
println(s"sin(-x) = $test3")  // Should show: -sin(x)
```

### Exponential and Logarithm
```scala
import symbolicas._
import symbolicas.Dsl._

val x = Var("x")
val y = Var("y")

// Inverse properties
val test1 = exp(log(x)).simplify()
val test2 = log(exp(x)).simplify()
println(s"exp(log(x)) = $test1")  // Should show: x
println(s"log(exp(x)) = $test2")  // Should show: x

// Logarithm laws
val test3 = log(x * y).expand()
println(s"log(x*y) = $test3")  // Should show: log(x) + log(y)
```

### Symbolic Calculus
```scala
import symbolicas._
import symbolicas.Dsl._

val x = Var("x")

// Differentiation
val test1 = Derivative(x ^ Num(2), "x").simplify()
println(s"d/dx(x^2) = $test1")  // Should show: 2*x

// Chain rule
val test2 = Derivative(Sin(x ^ Num(2)), "x").simplify()
println(s"d/dx(sin(x^2)) = $test2")  // Should show: 2*x*cos(x^2)

// Integration
val test3 = Integral(x, "x").simplify()
println(s"∫x dx = $test3")  // Should show: x^2/2
```

### Equation Solving
```scala
import symbolicas._
import symbolicas.Dsl._

val x = Var("x")

// Linear equation
val solutions1 = Solve.solve(x + 2, "x")
println(s"x + 2 = 0: $solutions1")  // Should show: List(Num(-2))

// Quadratic equation
val eq = (x ^ Num(2)) - (Num(5) * x) + 6
val solutions2 = Solve.solve(eq, "x")
println(s"x^2 - 5x + 6 = 0: $solutions2")  // Should show: List(Num(2), Num(3))
```

## Verification Checklist

### ✓ Basic Simplification
- [ ] No `+ -` sequences in output
- [ ] All negative terms use `-` symbol
- [ ] Example: `x - y` not `x + -y`

### ✓ Fraction Handling
- [ ] Fractions with different denominators stay separate by default
- [ ] Example: `1/2 + 1/3` stays as `1/2 + 1/3` (with Default config)
- [ ] Fractions with same denominator are combined
- [ ] Example: `1/4 + 1/4` becomes `1/2`

### ✓ Number Display
- [ ] Integers show without decimals
- [ ] Example: `3` not `3.0`
- [ ] Fractions show as `3/4` not `3.0/4.0`

### ✓ Power Operations (v4.0)
- [ ] Power operator works: `x ^ Num(2)` displays as `x^2`
- [ ] Binomial expansion works for small powers
- [ ] Power laws apply: `x^0 = 1`, `x^1 = x`

### ✓ Trigonometry (v4.0)
- [ ] Sin, cos, tan functions work
- [ ] Odd/even function properties: `sin(-x) = -sin(x)`, `cos(-x) = cos(x)`
- [ ] Product-to-sum transformations apply

### ✓ Exponential & Logarithm (v4.0)
- [ ] Inverse properties: `exp(log(x)) = x`, `log(exp(x)) = x`
- [ ] Logarithm laws: `log(x*y) = log(x) + log(y)`
- [ ] Exponential laws: `exp(x+y) = exp(x) * exp(y)`

### ✓ Calculus (v4.0)
- [ ] Power rule: `d/dx(x^n) = n*x^(n-1)`
- [ ] Chain rule works for composite functions
- [ ] Basic integration works for polynomials
- [ ] Definite integrals compute correctly

### ✓ Equation Solving (v4.0)
- [ ] Linear equations solve correctly
- [ ] Quadratic equations find all solutions
- [ ] Works with symbolic coefficients

### ✓ Recursive Simplification
- [ ] Arguments inside functions are simplified
- [ ] Example: `cos(2*n)` not `cos(n*2)`
- [ ] Nested expressions fully reduced

### ✓ Fixpoint Convergence
- [ ] `fullSimplify()` reaches stable state
- [ ] No infinite loops (max 100 iterations)
- [ ] Output doesn't change on subsequent calls

### ✓ Performance (v4.0)
- [ ] Hash consing available via ExprCache
- [ ] Structural hash for fixpoint detection (O(1) comparison)
- [ ] Expansion limits prevent OOM

## Example Expected Outputs

### Polynomial
```
Input:  3*x + 2*x - x + 5 - 3
Output: 4*x + 2
```

### Power Expansion
```
Input:  (x + 1)^3
Output: x^3 + 3*x^2 + 3*x + 1
```

### Differentiation
```
Input:  d/dx(x^3 + 2*x)
Output: 3*x^2 + 2
```

### Equation Solving
```
Input:  x^2 - 5*x + 6 = 0
Output: [2, 3]
```

## Troubleshooting

### Compilation Errors
If you see compilation errors:
1. Verify Scala version: `scala -version` should show 3.3.5
2. Clean build: `sbt clean compile`
3. Check Java version: `java -version` (needs Java 11+)

### Runtime Errors
If tests fail at runtime:
1. Check that all files are in the correct location
2. Verify imports in .sc files
3. Look for stack traces indicating which rule failed
4. Check for Vector vs Array issues (v3.0 migration)

### Unexpected Output
If output doesn't match expectations:
1. Check that you're using `fullSimplify()` not just `simplify()`
2. Verify the expression is correctly constructed
3. Try intermediate steps: `expr.simplify`, `expr.expand`, etc.
4. Check SimplificationConfig settings

### v4.0 Feature Issues
If v4.0 features don't work:
1. Verify all v4.0 files exist: Pow.scala, Sin.scala, Tan.scala, Exp.scala, Log.scala, Derivative.scala, Integral.scala, Solve.scala
2. Check imports include new functions: `import symbolicas.Dsl._`
3. Verify version is 4.0.0-SNAPSHOT in build.sbt

## Performance Benchmarks

To verify performance:

```scala
val startTime = System.nanoTime()
val result = complexExpr.fullSimplify
val endTime = System.nanoTime()
println(s"Time: ${(endTime - startTime) / 1e6} ms")
```

**Expected:** Most expressions should simplify in < 100ms

## Reporting Issues

If you find issues, please report:
1. The expression that failed
2. Expected vs actual output
3. Any error messages
4. Scala version and platform
5. Which version (v2, v3, v4) you're using

## Additional Test Cases

Create your own tests to verify edge cases:

```scala
import symbolicas._
import symbolicas.Dsl._

val x = Var("x")

// Test 1: Triple negative
val expr1 = Neg(Neg(Neg(x)))
println(s"Triple neg: ${expr1.fullSimplify}")  // Should be: -x

// Test 2: Complex fraction
val expr2 = (x + 1) / (x - 1)
println(s"Complex div: ${expr2.fullSimplify}")  // Should be clean

// Test 3: Higher derivatives
val expr3 = Derivative.nth(x ^ Num(4), "x", 2)
println(s"d²/dx²(x^4) = ${expr3.simplify}")  // Should be: 12*x^2

// Test 4: Nested functions
val expr4 = exp(log(x + 1))
println(s"exp(log(x+1)) = ${expr4.simplify}")  // Should be: x + 1
```

## Next Steps

Once tests pass:
1. Review [CHANGELOG.md](CHANGELOG.md) for v4.0 features
2. Read [SIMPLIFICATION_CONFIG_GUIDE.md](SIMPLIFICATION_CONFIG_GUIDE.md) for configuration options
3. Check [README.md](README.md) for comprehensive examples
4. Explore advanced features like ExprCache for performance optimization

## Documentation

For more information:
- **Configuration**: [SIMPLIFICATION_CONFIG_GUIDE.md](SIMPLIFICATION_CONFIG_GUIDE.md)
- **API Documentation**: Run `sbt doc` to generate Scaladoc
- **Examples**: See README.md and test scripts
- **Version History**: [CHANGELOG.md](CHANGELOG.md)

---

**Happy testing! 🧪**
