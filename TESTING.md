# Testing Guide for Symbolum

**EXCERPT — for anyone scanning the index:**
How to run the suite, how to measure coverage, and where the tests live, followed by worked
snippets a reader may want to try by hand, every one of them compiled by `OtherDocumentsSpec` so
that a snippet which stopped being a program fails the build. It does not enumerate the suites: they
are discovered from the source tree, so a list here would go stale silently. It says nothing about what the
proof-assistant modules prove, only how to run what they carry.

*If you modify this file and this excerpt no longer accurately describes its content, you must
update it.*

## Overview

This guide covers testing for Symbolum, including basic algebra, calculus, equation solving,
and advanced features.

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

From the project root:

```bash
# Compile every module
sbt compile

# Run the whole suite
sbt test

# Run the suite of one module
sbt core/test

# Run one suite
sbt "core/testOnly garden.xeno.symbolum.BasicSimplificationSpec"

# Run the tests whose name matches a substring
sbt "core/testOnly * -- -z fraction"
```

**Expected output:** every suite green, and a final line giving the totals. A failure prints the
expression that produced it, so the first thing to do with one is paste that expression into the
console below.

Each module carries its own suites, one per area, named after what they cover. They are not listed
here on purpose: a list in a document is maintained by hand and goes stale without anything
failing, and the source tree already answers the question.

```bash
ls modules/*/src/test/scala/garden/xeno/symbolum/*/
```

| Module | What its tests establish |
|---|---|
| `core` | the algebra: canonical form, value preservation, the rules, the solver |
| `kernel` | each inference rule where it applies and where it must refuse, plus the properties the rest of the system assumes and never re-checks |
| `logic` | the connective definitions, the derived rules, matching and rewriting, the parser, and the compile-time assertions that hold the trust boundary |
| `theories` | the axioms are exactly the sixteen listed, and every arithmetic lemma is proved rather than assumed |
| `tactics` | the bridge certifies what is true and refuses what is not, and every example printed in the documentation is executed |

Two of these are worth knowing about specifically. `TrustBoundarySpec` asserts at compile time that
the kernel's constructors are unreachable from outside it, paired each time with the sanctioned
route so the assertion cannot pass for an unrelated reason. `DocumentationSpec` runs every example
in `README.md` and `docs/proving.md`; if it fails, the document is wrong, not the test.

### Coverage

```bash
sbt coverage test coverageReport
```

Each module has a statement floor in `build.sbt`, set to the value measured when it was last
raised, and the build fails below it. The floor only rises: when a change raises the measurement,
raise the number with it rather than leaving slack for later. `modules/examples` has no floor and
the reason is written where the setting would be.

The floors sit about a point below the measurement because the property tests generate different
inputs on each run, so which statements execute varies slightly. A floor exactly at the
measurement would fail on a different sample rather than on a regression.

### Trying things by hand

```bash
sbt core/console
```

```scala
import garden.xeno.symbolum._, garden.xeno.symbolum.Dsl._
val x = Var("x")
(x + Num(2) * x).simplify()
```

The runnable demonstrations are a separate module, so they are not part of the published library:

```bash
sbt "examples/runMain garden.xeno.symbolum.examples.TestSymbolum"
sbt "examples/runMain garden.xeno.symbolum.examples.TestCollatzSeries"
```

## Feature Tests

### Power and Exponentiation
```scala
import garden.xeno.symbolum._
import garden.xeno.symbolum.Dsl._

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
import garden.xeno.symbolum._
import garden.xeno.symbolum.Dsl._

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
import garden.xeno.symbolum._
import garden.xeno.symbolum.Dsl._

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
import garden.xeno.symbolum._
import garden.xeno.symbolum.Dsl._

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
import garden.xeno.symbolum._
import garden.xeno.symbolum.Dsl._

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

### ✓ Power Operations
- [ ] Power operator works: `x ^ Num(2)` displays as `x^2`
- [ ] Binomial expansion works for small powers
- [ ] Power laws apply: `x^0 = 1`, `x^1 = x`

### ✓ Trigonometry
- [ ] Sin, cos, tan functions work
- [ ] Odd/even function properties: `sin(-x) = -sin(x)`, `cos(-x) = cos(x)`
- [ ] Product-to-sum transformations apply

### ✓ Exponential & Logarithm
- [ ] Inverse properties: `exp(log(x)) = x`, `log(exp(x)) = x`
- [ ] Logarithm laws: `log(x*y) = log(x) + log(y)`
- [ ] Exponential laws: `exp(x+y) = exp(x) * exp(y)`

### ✓ Calculus
- [ ] Power rule: `d/dx(x^n) = n*x^(n-1)`
- [ ] Chain rule works for composite functions
- [ ] Basic integration works for polynomials
- [ ] Definite integrals compute correctly

### ✓ Equation Solving
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

### ✓ Performance
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
1. Read the stack trace for the rule that failed
2. Re-run the single suite that covers it, so the output is short enough to read
3. Reduce the expression until the failure disappears: the last step that still fails is the case

### Unexpected Output
If output doesn't match expectations:
1. Check that you're using `fullSimplify()` not just `simplify()`
2. Verify the expression is correctly constructed
3. Try intermediate steps: `expr.simplify`, `expr.expand`, etc.
4. Check SimplificationConfig settings

### A function is not recognised
1. Check that the import brings in the DSL: `import garden.xeno.symbolum.Dsl._`
2. The operators come from `ExprOps`, the functions (`sin`, `cos`, `exp`, `log`) from `Dsl` itself

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
import garden.xeno.symbolum._
import garden.xeno.symbolum.Dsl._

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
2. Read [SIMPLIFICATION_CONFIG_GUIDE.md](SIMPLIFICATION_CONFIG_GUIDE.md) for configuration options
3. Check [README.md](README.md) for comprehensive examples
4. Explore the canonical form and the rule configuration in `SIMPLIFICATION_CONFIG_GUIDE.md`

## Documentation

For more information:
- **Configuration**: [SIMPLIFICATION_CONFIG_GUIDE.md](SIMPLIFICATION_CONFIG_GUIDE.md)
- **API Documentation**: Run `sbt doc` to generate Scaladoc
- **Examples**: See README.md and test scripts

---

**Happy testing! 🧪**
