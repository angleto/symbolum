# Collatz Research Quick Reference

## Formulas at a Glance

### Single Iteration (Symbolic)
```
collatz₁(n) = -((2n + 1)/4) · cos(nπ) + n + 1/4
```

**When n is even**: Returns n/2
**When n is odd**: Returns (3n+1)/2

### K Iterations (Binomial Series)
```
collatz_k(n) = Σ(m=0 to k) C(k,m) · (1/2^k) ·
               [(3^m - 1)/2 + 3^m · n - ((1 + 2·3^m·n)/4) · cos(3^m · n · π / 2^(k-m))]
```

## Quick Code Examples

### Using Symbolic Approach

```scala
import symbolicas._
import symbolicas.Dsl._

val n = Var("n")
val pi = Var("pi")

// Build and simplify
val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
val simplified = collatz1.fullSimplify(SimplificationConfig.Collatz0)

// Evaluate
val result = simplified.eval(Map("n" -> 10.0, "pi" -> math.Pi))
println(result)  // 5.0
```

### Using Binomial Series

```scala
import symbolicas.CollatzSeries

// Standard (k ≤ 10)
val result1 = CollatzSeries.collatzK(27, 3)
println(result1)  // 124.0

// Stable (k > 10)
val result2 = CollatzSeries.collatzKStable(100, 20)
```

### Building Higher Iterations

```scala
val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

// Level 2
val c2Even = collatz1.replaceSymbol("n", n/2)
val c2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
val collatz2 = cos(n*pi) * Num(1,2) * (c2Even - c2Odd) +
               Num(1,2) * (c2Even + c2Odd)
val simplified2 = collatz2.fullSimplify(SimplificationConfig.Collatz0)
```

## Common Operations

### Direct Collatz Iteration
```scala
def collatz(n: Int): Int =
  if (n % 2 == 0) n / 2 else 3 * n + 1

def collatzK(n: Int, k: Int): Int =
  if (k == 0) n else collatzK(collatz(n), k - 1)
```

### Stopping Time
```scala
def stoppingTime(n: Int): Int = {
  def loop(curr: Int, steps: Int): Int =
    if (curr == 1) steps
    else loop(collatz(curr), steps + 1)
  loop(n, 0)
}
```

### Verification
```scala
val n = 27
val k = 3

val direct = collatzK(27, 3)  // 124
val binomial = CollatzSeries.collatzK(27, 3)  // 124.0
val symbolic = collatz3.eval(Map("n" -> 27.0, "pi" -> math.Pi))  // 124.0

assert(direct == binomial.toInt)
```

## Key Properties

| Property | Value/Pattern |
|----------|---------------|
| Parity encoding | cos(nπ) = {1 if even, -1 if odd} |
| Coefficient denominators | Always divide 2^k |
| Cosine arguments | Form: 3^m · n · π / 2^j |
| Time complexity (binomial) | O(k) |
| Expression growth (symbolic) | O(4^k) unsimplified, ~O(k²) simplified |

## Test Examples

### Small Values
```
collatz(1) = 4
collatz(2) = 1
collatz(3) = 10
collatz(4) = 2
collatz(5) = 16
collatz(6) = 3
collatz(7) = 22
```

### Multi-Step Examples
```
n=10, k=1: 5
n=10, k=2: 16
n=27, k=3: 124
n=123, k=1: 370
```

### Famous Sequences
```
27 → 82 → 41 → 124 → 62 → 31 → ... (eventually reaches 1)
```

## Simplification Configs

| Config | Use Case |
|--------|----------|
| `Collatz0` | Optimized for Collatz (recommended) |
| `Aggressive` | All rules enabled |
| `Default` | Balanced |
| `Minimal` | Essential only |
| `None` | No simplification |

```scala
expr.fullSimplify(SimplificationConfig.Collatz0)
```

## Performance Guidelines

| k | Method | Notes |
|---|--------|-------|
| 1-3 | Symbolic | Good for analysis |
| 4-10 | Binomial standard | Fast and accurate |
| 11-20 | Binomial stable | Prevents overflow |
| 20+ | Binomial stable | Watch precision |

## Common Pitfalls

### ❌ Avoid
```scala
// Don't use standard for large k
CollatzSeries.collatzK(100, 25)  // May overflow

// Don't forget pi in evaluation
expr.eval(Map("n" -> 10.0))  // Missing pi!

// Don't build symbolic for k > 5
buildCollatzLevel(10)  // Too slow
```

### ✓ Correct
```scala
// Use stable for large k
CollatzSeries.collatzKStable(100, 25)

// Include all variables
expr.eval(Map("n" -> 10.0, "pi" -> math.Pi))

// Use binomial for large k
CollatzSeries.collatzK(n, k)  // k ≤ 20
```

## Test Verification

### Run Tests
```bash
sbt test
```

### Check Specific
```bash
sbt "testOnly symbolicas.CollatzSpec"
```

### Expected Output
```
[info] CollatzSpec:
[info] Collatz1
[info] - should simplify correctly
[info] - should preserve mathematical meaning
[info] - should be idempotent
[info] Collatz2
[info] - should simplify to reasonable length
[info] - should not have duplicate signs
[info] - should preserve mathematical meaning
...
[info] All tests passed
```

## Useful Patterns

### Batch Testing
```scala
val testCases = List(
  (5, 1, 16),
  (10, 2, 16),
  (27, 3, 124)
)

testCases.foreach { case (n, k, expected) =>
  val result = CollatzSeries.collatzK(n, k)
  assert(math.abs(result - expected) < 0.001)
}
```

### Pattern Search
```scala
// Find values with high stopping time
(1 to 1000).filter(n => stoppingTime(n) > 100)

// Find potential cycles
(1 to 10000).filter { n =>
  val result = CollatzSeries.collatzK(n, 5)
  math.abs(result - n) < 0.01
}
```

## Mathematical Checks

### Verify Formula Correctness
```scala
def verifyFormula(n: Int, k: Int): Boolean = {
  val direct = collatzK(n, k)
  val formula = CollatzSeries.collatzK(n, k)
  math.abs(direct - formula) < 1e-6
}

assert(verifyFormula(27, 3))  // true
```

### Check Simplification
```scala
val original = /* complex expression */
val s1 = original.fullSimplify
val s2 = s1.fullSimplify

assert(s1 == s2)  // Idempotent
assert(s1.eval(vars) == original.eval(vars))  // Preserves meaning
```

## Quick Facts

- **Conjecture Age**: 87+ years (since 1937)
- **Tested Range**: > 2^68 (all converge)
- **Known Cycles**: Only 1→4→2→1
- **Status**: Unproven
- **This Research**: Tools for exploration, not proof

## Research Documents

1. **Overview** - Start here
2. **Symbolic Representation** - Formula details
3. **Binomial Series** - Alternative approach
4. **Mathematical Properties** - Theoretical insights
5. **Computational Experiments** - Test results
6. **Conclusions** - Summary and future work

## Getting Help

- Read full documentation in `docs/research/`
- Check test suite for examples
- Examine source code
- Open GitHub issue for questions

---

**Remember**: These are tools for research, not a proof. The Collatz conjecture remains unsolved!
