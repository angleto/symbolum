# Fraction Preservation and Simplification Improvements

## Problems Fixed

### Problem 1: Fractions Displayed as Decimals

**Issue:** Numeric fractions were being converted to decimals during simplification.

**Example:**
- Expected: `1/4`
- Got: `0.25`

**Root Cause:** The `collectLikeTerms` function and numeric sum operations were converting fractions to doubles by computing `n/d`, losing the fractional representation.

### Problem 2: `+ -` Pattern in Output

**Issue:** Negative terms were displaying as `+ -` instead of just `-`.

**Example:**
- Expected: `x - 2*y`
- Got: `x + -2*y`

**Root Cause:** The `Add.toString` method wasn't handling negative coefficients in `Mul` expressions.

### Problem 3: Expressions Inside Cosine Not Fully Simplified

**Issue:** Arguments to trigonometric functions contained unsimplified subexpressions.

**Example:**
- Expected: `cos(n*pi/2)`
- Got: `cos((n * pi - n/2 * pi))`

**Root Cause:** While `Cos.simplify` does call `expr.simplify(config)` on its argument, the fraction conversion issue was preventing proper simplification.

## Solutions Implemented

### Fix 1: Preserve Fractions in `collectLikeTerms`

**File:** `Add.scala` lines 63-108

**Changes:**
1. Changed `extractCoeffAndBase` to return `(Num, Expr)` instead of `(Double, Expr)`
2. Added `addFractions` helper function to properly add fractions:
   ```scala
   def addFractions(a: Num, b: Num): Num = {
     // a/b + c/d = (ad + bc) / bd
     val newNum = a.numerator * b.denominator + b.numerator * a.denominator
     val newDen = a.denominator * b.denominator
     Num(newNum, newDen)
   }
   ```
3. Sum coefficients using `reduce(addFractions)` instead of converting to double and summing

**Before:**
```scala
def extractCoeffAndBase(e: Expr): (Double, Expr) = e match {
  case Num(n, d) => (n/d, Num(1))  // Converts to decimal!
  ...
}
val totalCoeff = coeffsAndBases.map(_._1).sum  // Sums decimals
```

**After:**
```scala
def extractCoeffAndBase(e: Expr): (Num, Expr) = e match {
  case n @ Num(_, _) => (n, Num(1))  // Keeps fraction
  ...
}
val totalCoeff = coeffsAndBases.map(_._1).reduce(addFractions).simplify(config)
```

### Fix 2: Preserve Fractions in Numeric Sum

**File:** `Add.scala` lines 240-262

**Changes:**
1. Changed numeric sum to use `reduce` with fraction addition
2. Eliminated `n/d` division that was converting to decimals

**Before:**
```scala
val numSum = nums.collect { case Num(n, d) => n/d }.sum  // Converts to decimal!
val combined = (if (numSum != 0.0) Array[Expr](Num(numSum)) else ...)
```

**After:**
```scala
val numSum = if (nums.nonEmpty) {
  nums.collect { case n @ Num(_, _) => n }
    .reduce { (a, b) =>
      // Add fractions: a/b + c/d = (ad + bc) / bd
      val newNum = a.numerator * b.denominator + b.numerator * a.denominator
      val newDen = a.denominator * b.denominator
      Num(newNum, newDen)
    }
    .simplify(config)
} else {
  Num(0)
}
```

### Fix 3: Handle Negative Coefficients in `Add.toString`

**File:** `Add.scala` lines 272-294

**Changes:**
Added pattern matching for `Mul(Array(Num(n, d), rest @ _*))` where `n < 0`:

```scala
case Mul(Array(Num(n, d), rest @ _*)) if n < 0 && rest.nonEmpty =>
  // Handle negative coefficient in multiplication: -2*x becomes "- 2*x"
  val positiveCoeff = Num(-n, d)
  val positiveMul = if (rest.length == 1) {
    Mul(Array(positiveCoeff, rest.head))
  } else {
    Mul(Array(positiveCoeff) ++ rest)
  }
  s"- ${showWithParens(positiveMul, this)}"
```

This converts expressions like `+ Mul(Num(-2), x)` to `- Mul(Num(2), x)` in the output.

## Verification

### Test Case 1: Simple Fraction

**Input:**
```scala
val expr = Num(1, 4) + Num(1, 4)
expr.simplify
```

**Expected Output:** `1/2`

**Explanation:**
- Before: Would produce `Num(0.5)` → displays as `0.5`
- After: Produces `Num(2, 4).simplify` → `Num(1, 2)` → displays as `1/2`

### Test Case 2: Collecting Like Terms

**Input:**
```scala
val expr = Mul(Array(Num(1, 4), x)) + Mul(Array(Num(3, 4), x))
expr.simplify(config)
```

**Expected Output:** `x` (since 1/4 + 3/4 = 1)

**Explanation:**
- Before: Would compute `0.25 + 0.75 = 1.0` → `Mul(Num(1.0), x)`
- After: Computes `Num(1, 4) + Num(3, 4) = Num(4, 4).simplify = Num(1)` → just `x`

### Test Case 3: Negative Coefficient Display

**Input:**
```scala
val expr = Add(Array(x, Mul(Array(Num(-2), y))))
expr.toString
```

**Expected Output:** `x - 2 * y`

**Explanation:**
- Before: Would display as `x + -2 * y`
- After: Pattern matching catches negative coefficient → displays as `x - 2 * y`

### Test Case 4: Cosine Argument Simplification

**Input:**
```scala
val expr = Cos(Add(Array(Mul(Array(n, pi)), Mul(Array(Num(-1, 2), n, pi)))))
expr.simplify
```

**Expected Output:** `cos(1/2 * n * pi)` or `cos(n * pi / 2)`

**Explanation:**
- `Cos.simplify` calls `expr.simplify` on its argument
- The argument `n*pi + (-1/2)*n*pi` gets simplified
- With fraction preservation, `-1/2` stays as `Num(-1, 2)` not `-0.5`
- Collecting like terms: `(1 + (-1/2)) * n * pi = (1/2) * n * pi`

## Impact on Collatz3 Expression

The collatz3 expression should now display:
1. ✅ Fractions like `3/4`, `7/128` instead of `0.75`, `0.0546875`
2. ✅ Clean subtraction: `n - 2n/4` instead of `n + -2n/4`
3. ✅ Simplified cosine arguments: `cos(πn/2)` instead of `cos((n*pi - n*pi/2))`

## Remaining Work

The user's expected output shows very aggressive simplification with many trigonometric identities. The current system applies:
- Collecting like terms
- Factoring common terms
- Product-of-cosines to sum-of-cosines

To match the user's expected output exactly, we may need additional rules like:
- More aggressive algebraic simplification inside cosine arguments
- Additional trigonometric identities
- Better term ordering and grouping

However, the fundamental issues of fraction preservation and display formatting are now resolved.

## Files Modified

- `Add.scala`:
  - Lines 63-108: `collectLikeTerms` function (fraction preservation)
  - Lines 240-262: Numeric sum (fraction preservation)
  - Lines 272-294: `toString` method (negative coefficient handling)

## Testing

To test these changes:

```bash
# Run the Collatz expression tests
scala-cli run src/main/scala/test.sc

# Expected improvements:
# - All numeric literals display as fractions
# - No "+ -" patterns in output
# - Cleaner expression structure
```

## Branch Information

**Branch:** `claude/fix-union-types-011CUqWKxzEzUXag6WBeTr7S`

**Commits:**
- `e7323e0` - Preserve fraction representation in simplification
- `fc9eb65` - Fix Array[Num] to Array[Expr] type inference
- `d7af564` - Add documentation for union type fix
- `c6ed7e7` - Fix Scala 3 union type compilation errors

**To merge:**
```bash
git checkout v2.0
git merge claude/fix-union-types-011CUqWKxzEzUXag6WBeTr7S
```
