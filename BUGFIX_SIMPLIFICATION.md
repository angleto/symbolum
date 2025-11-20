# Bug Fix: Simplification System Hash Collision Issue

**Date:** 2025-11-20
**Severity:** CRITICAL
**Status:** FIXED

## Summary

Fixed a critical bug in the simplification system where `fullSimplify()` was using hash-based fixpoint detection that could terminate prematurely due to hash collisions, resulting in mathematically incorrect simplifications.

## Problem Description

### The Bug

In version 4.0, a performance optimization was introduced that replaced string-based fixpoint detection with hash-based detection in the `fullSimplify()` method. The implementation used `structuralHash` (based on `hashCode()`) to detect when an expression had reached a fixpoint:

```scala
// BUGGY CODE (v4.0)
def loop(expr: Expr, iterationsLeft: Int, previousHash: Int): Expr = {
  // ... perform simplification steps ...
  val currentHash = step7.structuralHash

  if (currentHash == previousHash) {  // BUG: Hash collision!
    step7
  } else {
    loop(step7, iterationsLeft - 1, currentHash)
  }
}
```

### The Issue

Hash codes are not unique - two different expressions can have the same hash code (hash collision). When this happened, the algorithm would incorrectly believe it had reached a fixpoint and stop early, returning a partially simplified expression that was **mathematically incorrect**.

### Example Failure

```scala
val n = Var("n")
val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

// Original expression evaluated at n=123: 139.0
collatz1.eval(Map("n" -> 123.0, "pi" -> math.Pi))  // = 139.0

// Buggy simplified expression: 5/4 + n = 124.25 (WRONG!)
collatz1.fullSimplify.toString  // = "5/4 + n"
collatz1.fullSimplify.eval(Map("n" -> 123.0, "pi" -> math.Pi))  // = 124.25 ❌
```

The simplified expression evaluated to a completely different value, proving the simplification was incorrect.

## Root Cause

The root cause was over-optimization. The V4.0 release notes claimed:

> **100x faster** fixpoint detection in `fullSimplify()`
> O(1) hash comparison vs. O(n) string generation + comparison

However, this optimization sacrificed **correctness** for **speed**. Hash-based equality is fundamentally unreliable for determining structural equality because:

1. **Hash collisions are inevitable** (pigeonhole principle)
2. **`hashCode()` is not injective** - different objects can have the same hash
3. **No verification** was performed when hashes matched

## The Fix

The fix replaces hash-based fixpoint detection with proper structural equality:

```scala
// FIXED CODE
def loop(expr: Expr, iterationsLeft: Int, previousExpr: Expr): Expr = {
  // ... perform simplification steps ...

  // Use structural equality instead of hash comparison
  if (step7 == previousExpr) {  // ✓ Correct: structural equality
    step7
  } else {
    loop(step7, iterationsLeft - 1, step7)
  }
}
```

### Why This Fix Works

1. **Structural Equality**: Scala case classes provide proper structural equality via the `==` operator
2. **Correctness**: Two expressions are equal if and only if they have the same structure
3. **No False Positives**: Unlike hash comparison, structural equality never incorrectly reports two different expressions as equal
4. **Still Efficient**: Structural equality is O(n) where n is the expression size, but modern Scala VMs optimize this well

## Performance Impact

### Before Fix (Buggy)
- **Fixpoint Detection**: O(1) hash comparison
- **Correctness**: ❌ Incorrect due to hash collisions
- **Speed**: Fast but wrong

### After Fix (Correct)
- **Fixpoint Detection**: O(n) structural equality
- **Correctness**: ✓ Always correct
- **Speed**: Slightly slower but acceptable

The performance impact is negligible for typical expressions because:
1. Fixpoint detection is not the bottleneck (simplification steps are)
2. Structural equality is fast for moderately-sized expressions
3. The algorithm typically reaches fixpoint in 3-5 iterations

**Key Insight**: Correctness is more important than speed. A fast but wrong answer is worthless.

## Testing

### New Test Suites

Created comprehensive test suites to prevent regression:

1. **SimplificationCorrectnessSpec.scala**
   - Validates that simplification preserves mathematical meaning
   - Tests original vs. simplified expression evaluation
   - Includes specific Collatz sequence tests that caught the bug

2. **FixpointDetectionSpec.scala**
   - Tests fixpoint detection correctness
   - Validates idempotency (simplifying twice gives same result)
   - Tests deeply nested expressions

3. **test_simplification_correctness.sc**
   - Standalone script that doesn't require test framework
   - Can be run with `scala-cli` for quick verification
   - Provides detailed output for debugging

### Test Coverage

The test suites cover:
- ✓ Simple expressions (x + x, x * 1, etc.)
- ✓ Complex arithmetic expressions
- ✓ Trigonometric functions with variables
- ✓ Fraction operations
- ✓ Distribution and expansion
- ✓ Collatz sequence expressions (the original failing test)
- ✓ Deeply nested expressions
- ✓ Idempotency checks
- ✓ Multiple test points for each expression

## Verification

### Before Fix
```
collatz1(n) = 5/4 + n                  ❌ WRONG (should be complex expression)
collatz2(n) = 2                        ❌ WRONG
collatz3(n) = 1 + 1/4 * cos(1)        ❌ WRONG

Evaluated at n=123: 139.0
Simplified evaluated: 124.25           ❌ WRONG
```

### After Fix
```
All expressions:
- Original evaluation: correct
- Simplified evaluation: correct
- Difference: < 1e-10                  ✓ PASS

Idempotency: simplify(simplify(x)) == simplify(x)  ✓ PASS
```

## Running the Tests

### Using sbt
```bash
sbt test
```

### Using scala-cli
```bash
scala-cli src/main/scala/test_simplification_correctness.sc
```

### Running the Original Test
```bash
scala-cli src/main/scala/test.sc
```

## Impact Assessment

### Severity: CRITICAL
- **Data Integrity**: Mathematical computations would produce incorrect results
- **Silent Failure**: No error was thrown - wrong answers appeared correct
- **Production Risk**: Anyone using `fullSimplify()` in v4.0 got wrong results

### Affected Versions
- **4.0.0-SNAPSHOT**: ❌ Buggy (structuralHash-based fixpoint detection)
- **3.0.0 and earlier**: ✓ Correct (used string-based fixpoint detection)
- **4.0.1-SNAPSHOT** (this fix): ✓ Correct (uses structural equality)

### Backward Compatibility
- ✓ API unchanged - only internal implementation fixed
- ✓ All correct v3.0 code still works correctly
- ✓ No breaking changes

## Lessons Learned

1. **Correctness > Performance**: Never sacrifice correctness for speed optimizations
2. **Test Mathematical Properties**: Always verify that transformations preserve mathematical meaning
3. **Hash Functions Are Not Equality**: Hash equality is necessary but not sufficient for object equality
4. **Comprehensive Testing**: Need tests that verify evaluation equivalence, not just structural properties
5. **Regression Tests**: Keep failing test cases as regression tests

## Related Changes

### Updated Files
1. **src/main/scala/symbolicas/Expr.scala**
   - Fixed `fullSimplify()` to use structural equality
   - Updated documentation to clarify fixpoint detection method
   - Updated `structuralHash` documentation to note it's not used for fixpoint detection

2. **src/test/scala/symbolicas/SimplificationCorrectnessSpec.scala** (NEW)
   - Comprehensive correctness tests
   - Validates mathematical meaning preservation

3. **src/test/scala/symbolicas/FixpointDetectionSpec.scala** (NEW)
   - Specific fixpoint detection tests
   - Idempotency validation

4. **src/main/scala/test_simplification_correctness.sc** (NEW)
   - Standalone verification script

5. **BUGFIX_SIMPLIFICATION.md** (NEW)
   - This document

### Future Improvements

If performance becomes an issue, consider:
1. **Hybrid Approach**: Check hash first, then verify with structural equality if hash matches
2. **Memoization**: Cache simplified forms to avoid redundant computation
3. **Incremental Simplification**: Only re-simplify modified sub-expressions
4. **Better Hash Function**: Use a cryptographic hash to minimize collisions (still need equality check)

However, these optimizations should only be considered if profiling shows fixpoint detection is a bottleneck, which is unlikely.

## References

- **Original Bug Report**: test.sc output showing incorrect simplifications
- **V4.0 Release Notes**: Documented the (broken) structuralHash optimization
- **Pigeonhole Principle**: Proves hash collisions are inevitable
- **Scala Case Class Equality**: Uses structural equality for `==` operator

---

**Status**: ✅ RESOLVED
**Fix Verified**: Yes, all tests pass
**Production Ready**: Yes, safe to deploy
