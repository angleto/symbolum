# Negative Fraction Simplification Feature

## Overview

This document describes the implementation of negative numerator simplification for division expressions in the Symbolicas computer algebra system.

## Problem Statement

Previously, expressions like `(-1 - n)/8` would remain in their original form after simplification. The desired behavior is to factor out the negative sign and simplify to `-(1 + n)/8`.

## Solution

### Implementation Details

The solution adds logic to the `Div.simplify` method to detect when a fraction's numerator (when it's an `Add` expression) has all terms with negative coefficients, and factors out the `-1`.

### Files Modified

1. **src/main/scala/symbolicas/Div.scala**
   - Added `hasNegativeCoefficient` helper method to check if an expression has a negative leading coefficient
   - Added `negateCoefficient` helper method to flip the sign of an expression's coefficient
   - Added case 9 in the `simplify` method to handle negative numerator factoring
   - Updated documentation to reflect the new transformation

2. **src/test/scala/symbolicas/FractionOperationsSpec.scala**
   - Added comprehensive test suite for negative numerator simplification
   - Tests cover various cases: simple expressions, multiple terms, polynomials, and edge cases

### Algorithm

The simplification works as follows:

1. **Detection**: When simplifying a `Div(Vector(numerator, denominator))` where the numerator is an `Add`:
   - Check if all terms in the Add have negative coefficients

2. **Transformation**: If all terms are negative:
   - Negate each term's coefficient
   - Create a new Add expression with the positive terms
   - Wrap the result in `Mul(Vector(Num(-1), Div(Vector(positiveNumerator, denominator))))`

3. **Examples**:
   ```scala
   // Before: (-1 - n)/8
   Div(Vector(Add(Vector(Num(-1), Mul(Vector(Num(-1), n)))), Num(8)))

   // After: -(1 + n)/8
   Mul(Vector(Num(-1), Div(Vector(Add(Vector(Num(1), n)), Num(8)))))
   ```

### Configuration

The simplification is controlled by the `CombineNumericLiterals` rule in `SimplificationConfig`. It only applies when this rule is enabled (which is the default).

### Test Cases

The test suite includes:

1. **Simple expression**: `(-1 - n)/8` → `-(1 + n)/8`
2. **Multiple terms**: `(-2 - 3*n)/4` → `-(2 + 3*n)/4`
3. **Polynomial**: `(-1 - 2*n - 3*n²)/6` → `-(1 + 2*n + 3*n²)/6`
4. **Mixed signs**: `(-1 + 2*n)/8` → remains unchanged (not all negative)
5. **Single negative number**: `(-3)/4` → `Num(-3, 4)` (already simplified)

## Benefits

1. **Improved readability**: Expressions with negative fractions are more intuitive when written with a leading negative sign
2. **Canonical form**: Provides a consistent representation for negative fractions
3. **Mathematical convention**: Matches standard mathematical notation where negative signs are typically factored out

## Performance

The implementation adds minimal overhead:
- Time complexity: O(n) where n is the number of terms in the numerator
- Only activates when the numerator is an Add expression
- Leverages existing simplification infrastructure

## Future Enhancements

Potential improvements could include:
1. Factoring out common negative factors when not all terms are negative (e.g., `(-2a - 4b + c)` → `-(2a + 4b) + c`)
2. Extending to handle more complex nested structures
3. Configuration option to control this specific transformation independently
