# Testing Guide for Symbolicas Improvements

## Prerequisites

You need Scala 3.3.5 installed to test the improvements. Install it using one of these methods:

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

Once Scala is installed, run the following commands:

### Test 1: Compile the Project
```bash
cd /home/user/symbolicas
sbt compile
```

Expected output: Successful compilation with no errors

### Test 2: Run Basic Tests
```bash
cd /home/user/symbolicas/src/main/scala
scala-cli test_improved.sc
```

Expected output: A series of test results showing:
- Double negative elimination: `--x` → `x`
- Addition with negative: `x + (-y)` displayed as `x - y`
- Nested additions flattened
- Fractions kept symbolic (unless same denominator)
- Clean display without `.0` decimals

### Test 3: Run Collatz Tests
```bash
cd /home/user/symbolicas/src/main/scala
scala-cli test.sc
```

Expected output: The collatz expressions fully simplified with:
- Clean subtraction symbols (`-` not `+ -`)
- Proper parenthesization
- Symbolic fractions preserved
- Coefficients grouped logically

### Test 4: Run Original Test
```bash
cd /home/user/symbolicas/src/main/scala
scala-cli test2.sc
```

Expected output: Numeric result from CollatzSeries

## Verification Checklist

Compare the output against these criteria:

### ✓ Negative Terms Display
- [ ] No `+ -` sequences in output
- [ ] All negative terms use `-` symbol
- [ ] Example: `x - y` not `x + -y`

### ✓ Fraction Handling
- [ ] Fractions with different denominators stay separate
- [ ] Example: `1/2 + 1/3` stays as `1/2 + 1/3` (not merged to `5/6`)
- [ ] Fractions with same denominator are combined
- [ ] Example: `1/4 + 1/4` becomes `1/2`

### ✓ Number Display
- [ ] Integers show without decimals
- [ ] Example: `3` not `3.0`
- [ ] Fractions show as `3/4` not `3.0/4.0`

### ✓ Recursive Simplification
- [ ] Arguments inside cos() are simplified
- [ ] Example: `cos(2*n)` not `cos(n*2)`
- [ ] Nested expressions fully reduced

### ✓ Fixpoint Convergence
- [ ] `fullSimplify()` reaches stable state
- [ ] No infinite loops (max 100 iterations)
- [ ] Output doesn't change on subsequent calls

### ✓ Parenthesization
- [ ] Operations clearly disambiguated
- [ ] Division denominators properly parenthesized
- [ ] Example: `x/(y + z)` not `x/y + z`

### ✓ Coefficient Grouping
- [ ] Numeric coefficients appear first in products
- [ ] Example: `2 * x * y` not `x * 2 * y`

## Example Expected Outputs

### Collatz1
```
n + 1/4 - (2*n + 1)/4 * cos(n*pi)
```

### Collatz3 (Partial)
Should look similar to:
```
n + 3/4
- (2*n + 1)/4 * cos(pi*n)
- (3*n + 2)/8 * cos(pi*(3*n + 1)/2)
+ (3*n + 2)/16 * cos(pi*(n + 1)/2)
...
```

Key characteristics:
- Clean `-` symbols, no `+ -`
- Fractions preserved as `a/b`
- Proper grouping with coefficients first
- Parentheses used correctly

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
3. Look for stack traces indicating which simplification rule failed

### Unexpected Output
If output doesn't match expectations:
1. Check that you're using `fullSimplify()` not just `simplify()`
2. Verify the expression is correctly constructed
3. Try intermediate steps: `expr.simplify`, `expr.expand`, etc.

## Performance Benchmarks

To verify performance hasn't degraded:

```scala
val startTime = System.nanoTime()
val result = complexExpr.fullSimplify
val endTime = System.nanoTime()
println(s"Time: ${(endTime - startTime) / 1e6} ms")
```

Expected: Most expressions should simplify in < 100ms

## Reporting Issues

If you find issues, please report:
1. The expression that failed
2. Expected vs actual output
3. Any error messages
4. Scala version and platform

## Next Steps After Testing

Once tests pass:
1. Review IMPROVEMENTS.md for detailed change descriptions
2. Compare output with your desired Collatz formula format
3. If further improvements needed, identify specific issues
4. Test with your own expressions beyond Collatz

## Additional Test Cases

Create your own tests to verify edge cases:

```scala
// Test 1: Triple negative
val expr1 = Neg(Neg(Neg(x)))
println(s"Triple neg: ${expr1.fullSimplify}")  // Should be: -x

// Test 2: Complex fraction
val expr2 = Div(Array(Add(Array(x, Num(1))), Add(Array(x, Num(-1)))))
println(s"Complex div: ${expr2.fullSimplify}")  // Should be clean

// Test 3: Multiple cosines
val expr3 = Mul(Array(cos(x), cos(y), cos(Var("z"))))
println(s"Multiple cos: ${expr3.expand}")  // Should apply product-to-sum
```
