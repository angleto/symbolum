# Aggressive Expansion Fix for Large Nested Blocks

## Problem

When simplifying complex expressions like Collatz sequences, the simplification process was creating large nested blocks of the form:

```
cos(A) * (cos(B) * C + D + cos(E) * F + G + ...)
```

These large blocks made the expressions hard to read and didn't achieve the desired flat sum structure where each term is as small as possible.

### Example Issue

The collatz3 expression contained blocks like:
```
cos((3 * n + 1)/2 * pi) * (
  cos((3 * n + 1)/4 * pi) * (-1/16 - (3 * n + 1)/32) +
  (3 * n + 1)/16 - 1/8 +
  cos(pi * (1/2 + (9 * n + 3)/4)) * ((9 * n + 3)/32 + 1/8) -
  (9 * n + 3)/16
)
```

The desired form is a flat sum:
```
cos(A) * cos(B) * term1 +
cos(A) * term2 +
cos(A) * term3 +
...
```

## Root Cause

The issue was caused by an oscillation between two simplification rules:

1. **DistributeProduct** (in `Mul.expand`): Expands products over sums: `a*(b+c) → a*b + a*c`
2. **FactorCommonTerms** (in `Add.simplify`): Factors common terms: `a*b + a*c → a*(b+c)`

The system would expand nested products, but then immediately factor them back, preventing the desired flat structure.

## Solution

### 1. Aggressive Expansion in Mul.simplify (Mul.scala)

Added a check in `Mul.simplify` to detect when we have a product containing an `Add` term, and immediately expand it:

```scala
/* AGGRESSIVE EXPANSION: If we have a product with an Add term, expand it immediately
 * This prevents large nested blocks like: cos(A) * (B + C + D + ...)
 * We want: cos(A) * B + cos(A) * C + cos(A) * D + ...
 */
if (config.isEnabled(DistributeProduct)) {
  val hasAdd = withoutOnes.exists(_.isInstanceOf[Add])
  if (hasAdd && withoutOnes.length > 1) {
    return Mul(withoutOnes).expand(config)
  }
}
```

This ensures that any product like `Mul([factor, Add([...])])` is immediately distributed.

### 2. Prevent Re-factoring in Add.simplify (Add.scala)

Modified `factorCommonTerms` to NOT factor terms back when it would create a `Mul(factor, Add(...))` structure:

```scala
// Don't factor if DistributeProduct is enabled and we'd create
// a nested block with an Add inside a Mul
if (config.isEnabled(DistributeProduct) && remainders.length > 1) {
  // Keep the expanded form - don't factor
  Add(terms.toArray)
} else {
  // Only factor when we have a single remainder (no Add created)
  Mul(Array(commonFactor, Add(remainders.toArray))).simplify(config)
}
```

This prevents the oscillation: when `DistributeProduct` is enabled, we prioritize the expanded flat form over the factored form.

## Benefits

1. **Flat Sum Structure**: Expressions are now a sum of small, simple terms rather than nested blocks
2. **No Oscillation**: The expansion and factoring rules no longer fight each other
3. **Better Readability**: Each term is clearly visible and independently understandable
4. **Recursive Expansion**: Works recursively to break down deeply nested structures

## Example Transformation

**Before:**
```
cos((3*n+1)/2 * pi) * (cos((3*n+1)/4 * pi) * (-1/16 - (3*n+1)/32) + (3*n+1)/16 - 1/8)
```

**After:**
```
cos((3*n+1)/2 * pi) * cos((3*n+1)/4 * pi) * (-1/16) +
cos((3*n+1)/2 * pi) * cos((3*n+1)/4 * pi) * (-(3*n+1)/32) +
cos((3*n+1)/2 * pi) * (3*n+1)/16 +
cos((3*n+1)/2 * pi) * (-1/8)
```

## Testing

To verify the fix works correctly, run:
```scala
scala-cli run src/main/scala/test_expansion.sc
```

This tests various patterns of product distribution to ensure large nested blocks are eliminated.

## Configuration

This behavior is controlled by the `DistributeProduct` simplification rule, which is enabled by default in:
- `SimplificationConfig.Default`
- `SimplificationConfig.Collatz0`
- `SimplificationConfig.Aggressive`

When `DistributeProduct` is enabled, the system prioritizes expansion over factoring to create flat sum structures.

## Files Modified

1. `src/main/scala/symbolicas/Mul.scala`: Added aggressive expansion check in `simplify` method
2. `src/main/scala/symbolicas/Add.scala`: Modified `factorCommonTerms` to respect expansion priority
3. `src/main/scala/test_expansion.sc`: Created test file to verify expansion behavior
