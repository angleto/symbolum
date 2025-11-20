# Bug Fix: Mul.simplify Losing Symbolic Factors

**Date:** 2025-11-20
**Severity:** CRITICAL
**Status:** FIXED

## Summary

Fixed a critical bug in `Mul.simplify()` where symbolic factors (variables, cosines, etc.) were being completely lost during simplification when there were no numeric factors to combine. This caused expressions like `n * pi` to simplify to `1` instead of remaining unchanged.

## Problem Description

### The Bug

In `Mul.scala` line 336, there was a devastating logic error in how the final result was constructed:

```scala
// BUGGY CODE (line 336):
val combinedFactors: Vector[Expr] =
  if (numericPart == one) numericFactors else Vector(numericPart) ++ symbolicFactors
```

### The Issue

When an expression had **only symbolic factors** (no numeric values), the code would:
1. Partition factors into `numericFactors` (empty) and `symbolicFactors` (non-empty)
2. Set `numericPart = one` (since no numerics to combine)
3. Return `numericFactors` (empty!) when `numericPart == one`
4. **Completely lose all symbolic factors**

### Example Failure

```scala
Mul(Vector(Var("n"), Var("pi")))  // Represents: n * pi

// During simplification:
numericFactors = Vector()           // No Num instances
symbolicFactors = Vector(Var("n"), Var("pi"))
numericPart = one                   // No numerics to combine

// BUG: Returns numericFactors (EMPTY!)
combinedFactors = Vector()
Result = Num(1.0)                   // WRONG! Should be n * pi
```

### Observable Symptoms

This manifested in user-visible bugs:

1. **collatz1 expression:**
   ```
   Before: -((2 * n + 1)/4) * cos(n * pi) + n + 1/4
   Buggy:  5/4 + n                           // cos term vanished!
   ```

2. **collatz2 expression:**
   ```
   Before: [complex expression with cos terms]
   Buggy:  2                                 // Everything vanished!
   ```

3. **collatz3 expression:**
   ```
   Before: [complex nested expression]
   Buggy:  1 + 1/4 * cos(1)                 // n*pi became 1!
   ```

The `cos(1)` was particularly telling - it revealed that `Mul(Vector(Var("n"), Var("pi")))` inside a `Cos(...)` was being simplified to `Num(1)`, giving us `Cos(Num(1))` which prints as `cos(1)`.

## Root Cause Analysis

### Why This Happened

The original logic assumed that if `numericPart == one`, it meant "we haven't combined any numerics yet, so keep the original numeric factors". But this is **wrong** when there are **zero** numeric factors!

```scala
// The flawed assumption:
if (numericPart == one) {
  // "No combination happened, return original numerics"
  numericFactors  // BUG: What if numericFactors is empty?
}
```

### Why It Went Unnoticed

This bug slipped through because:
1. Most multiplication expressions have at least one numeric coefficient
2. The bug only triggered on pure symbolic products like `x * y` or `n * pi`
3. Tests focused on numeric-heavy expressions
4. The Collatz expressions were the first to stress-test pure symbolic multiplication

## The Fix

### Code Change

```scala
// FIXED CODE:
val combinedFactors: Vector[Expr] =
  if (numericPart == one) {
    // No numeric factors to combine, keep both numeric and symbolic factors
    numericFactors ++ symbolicFactors
  } else {
    // Combined numeric factors into numericPart, add symbolic factors
    Vector(numericPart) ++ symbolicFactors
  }
```

### Why This Works

Now the logic correctly handles all cases:

| Case | numericFactors | symbolicFactors | numericPart | combinedFactors | Result |
|------|----------------|-----------------|-------------|-----------------|--------|
| **Pure symbolic** | `[]` | `[n, pi]` | `one` | `[] ++ [n, pi]` | `n * pi` ✓ |
| **Pure numeric** | `[2, 3]` | `[]` | `6` | `[6] ++ []` | `6` ✓ |
| **Mixed** | `[2]` | `[n]` | `2` | `[2] ++ [n]` | `2 * n` ✓ |
| **Single numeric** | `[5]` | `[]` | `one` | `[5] ++ []` | `5` ✓ |

## Verification

### Before Fix

```scala
collatz1(n) = 5/4 + n                        // ❌ cos term lost
collatz2(n) = 2                              // ❌ entire expression lost
collatz3(n) = 1 + 1/4 * cos(1)              // ❌ n*pi became 1
```

### After Fix

```scala
collatz1(n) = 1/4 - 1/2 * n * cos(n * pi) + n - 1/4 * cos(n * pi)  // ✓ All terms present
collatz2(n) = [complex expression with cos terms preserved]         // ✓ All terms present
collatz3(n) = [complex expression with cos terms preserved]         // ✓ All terms present
```

The simplified expressions are now **mathematically correct** - they preserve all terms and evaluate to the same values as the original expressions.

## Impact Assessment

### Severity: CRITICAL

- **Data Integrity:** Mathematical computations produced completely incorrect results
- **Silent Failure:** No error was thrown - wrong answers appeared as valid expressions
- **Scope:** Affected ANY multiplication of purely symbolic terms
- **Production Risk:** Anyone using symbolic algebra with variable multiplication got wrong results

### Affected Versions

- **All versions with the buggy logic:** ❌ Symbolic factors lost
- **After this fix:** ✓ All factors preserved correctly

### Affected Operations

Any expression involving multiplication of symbols without numeric coefficients:
- ✗ `x * y` → `1` (WRONG)
- ✗ `n * pi` → `1` (WRONG)
- ✗ `cos(n * pi)` → `cos(1)` (WRONG)
- ✗ Product chains like `a * b * c` → `1` (WRONG)

After fix, all work correctly.

## Testing

### Verification Steps

1. **Run existing tests:**
   ```bash
   sbt test
   ```

2. **Run Collatz test:**
   ```bash
   sbt "runMain TestSymbolicas"
   ```

3. **Verify symbolic multiplication:**
   ```scala
   val expr = Mul(Vector(Var("n"), Var("pi")))
   val simplified = expr.simplify()
   // Should return: Mul(Vector(Var("n"), Var("pi")))
   // NOT: Num(1.0)
   ```

### New Test Cases Needed

Should add specific tests for:
- Pure symbolic multiplication: `x * y`
- Symbol * constant expressions: `n * pi`
- Nested symbolic products: `(a * b) * (c * d)`
- Single symbol: `x` (edge case)

## Related Files

### Modified Files

1. **src/main/scala/symbolicas/Mul.scala**
   - Fixed `combinedFactors` logic (line 335-342)
   - Now correctly preserves symbolic factors

2. **BUGFIX_MUL_SIMPLIFY.md** (NEW)
   - This document

### Debugging Files (Temporary)

- **run_test.sh** - Test runner script (can be kept for convenience)
- Debug logging in `Expr.scala` - Removed in final commit

## Lessons Learned

1. **Test Edge Cases:** Always test expressions with zero numeric factors
2. **Verify Assumptions:** The assumption "numericPart == one means keep numericFactors" was wrong
3. **Partition Carefully:** When partitioning data, ensure all parts are included in final result
4. **Symbolic Testing:** Need more tests focusing on pure symbolic manipulation
5. **Debug Early:** Debug logging immediately revealed the issue location

## Backward Compatibility

- ✓ API unchanged - only internal logic fixed
- ✓ All previously correct code still works correctly
- ✓ Previously broken code now works correctly
- ✓ No breaking changes

## References

- **Original Bug Report:** User reported `cos(1)` appearing in simplified output
- **Debug Session:** Added logging to trace cos term disappearance
- **Root Cause:** Found in Mul.scala line 336 via debug output analysis

---

**Status**: ✅ RESOLVED
**Fix Verified**: Yes, all tests pass and Collatz expressions simplify correctly
**Production Ready**: Yes, safe to deploy
