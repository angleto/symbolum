# Symbolic Representation of Collatz Sequences

## The Challenge

The traditional Collatz function has a branching structure:

```
C(n) = {
  n/2      if n is even
  3n+1     if n is odd
}
```

This conditional makes it difficult to analyze algebraically. We need a single, continuous expression that captures both cases.

## The Unified Formula

We represent the Collatz function using a cosine-based parity detector:

```
collatz₁(n) = -((2n + 1)/4) · cos(nπ) + n + 1/4
```

### Why This Works

The key insight is that `cos(nπ)` acts as a parity indicator:

- **When n is even**: cos(nπ) = cos(2kπ) = 1
- **When n is odd**: cos(nπ) = cos((2k+1)π) = -1

Let's verify both cases:

#### Case 1: n is even (cos(nπ) = 1)
```
collatz₁(n) = -((2n + 1)/4) · 1 + n + 1/4
            = -(2n + 1)/4 + n + 1/4
            = -2n/4 - 1/4 + n + 1/4
            = -n/2 + n
            = n/2 ✓
```

#### Case 2: n is odd (cos(nπ) = -1)
```
collatz₁(n) = -((2n + 1)/4) · (-1) + n + 1/4
            = (2n + 1)/4 + n + 1/4
            = 2n/4 + 1/4 + n + 1/4
            = n/2 + 1/4 + n + 1/4
            = 3n/2 + 1/2
            = (3n + 1)/2 ✓
```

Note: The traditional odd case gives `3n + 1`, but since we know the result is even, we can immediately apply the division by 2, giving `(3n + 1)/2`.

## Higher Iterations

### Collatz₂: Two Iterations

For the second iteration, we need to handle four cases (EE, EO, OE, OO):

```scala
val collatz2Even = collatz1.replaceSymbol("n", n/2)
val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
val collatz2 = cos(n*pi) * (1/2) * (collatz2Even - collatz2Odd) +
               (1/2) * (collatz2Even + collatz2Odd)
```

This formula:
1. Substitutes the two possible results of the first iteration
2. Uses `cos(nπ)` to select between them
3. Combines them algebraically

After simplification using the Symbolicas CAS, this expands into a more complex expression with multiple cosine terms.

### Collatz₃: Three Iterations

Similarly, we can build the third iteration:

```scala
val collatz3Even = collatz2.replaceSymbol("n", n/2)
val collatz3Odd = collatz2.replaceSymbol("n", (n*3+1)/2)
val collatz3 = cos(n*pi) * (1/2) * (collatz3Even - collatz3Odd) +
               (1/2) * (collatz3Even + collatz3Odd)
```

The pattern is recursive: each level substitutes the previous level's formula into even/odd branches.

## Mathematical Properties

### Expression Complexity

The expression size grows with each iteration:

- **Collatz₁**: ~50 characters when simplified
- **Collatz₂**: ~300 characters when simplified
- **Collatz₃**: ~800 characters when simplified

The growth is roughly exponential, but aggressive simplification keeps it manageable.

### Cosine Arguments

After simplification, cosine arguments have the form:

```
cos(3^m · n · π / 2^k)
```

Where:
- m represents the number of "odd" steps taken
- k is the total number of iterations
- These arguments relate to the binary representation of paths through the Collatz tree

### Coefficient Structure

The coefficients involve:
- Powers of 3 (from odd steps: 3n+1)
- Powers of 2 (from even steps: n/2)
- Binomial coefficients (from path counting)

## Implementation in Symbolicas

The implementation leverages several CAS features:

### 1. Exact Rational Arithmetic
```scala
Num(1, 4)  // Represents 1/4 exactly, not 0.25
```

### 2. Symbolic Variables
```scala
val n = Var("n")
val pi = Var("pi")
```

### 3. Expression Building
```scala
val expr = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
```

### 4. Simplification
```scala
val simplified = expr.fullSimplify(SimplificationConfig.Collatz0)
```

### 5. Substitution
```scala
val next = expr.replaceSymbol("n", newValue)
```

## Verification

Each symbolic expression is verified by:

1. **Numerical Evaluation**: Testing with concrete values
2. **Direct Comparison**: Comparing against iterative Collatz computation
3. **Invariant Checking**: Ensuring mathematical properties hold
4. **Idempotency**: Verifying `simplify(simplify(x)) = simplify(x)`

Example from test suite:

```scala
val vars = Map("n" -> 123.0, "pi" -> math.Pi)
val originalValue = collatz1.eval(vars)
val simplifiedValue = collatz1.fullSimplify.eval(vars)
math.abs(originalValue - simplifiedValue) should be < TOLERANCE
```

## Advantages of Symbolic Representation

1. **Unified Expression**: Single formula instead of conditional logic
2. **Algebraic Analysis**: Can apply mathematical transformations
3. **Pattern Recognition**: Easier to spot structural regularities
4. **Theoretical Proofs**: Enables algebraic proof techniques
5. **Computational Efficiency**: Can compute k iterations without k evaluations

## Limitations

1. **Expression Growth**: Expressions become very large for high k
2. **Simplification Complexity**: Aggressive simplification is computationally expensive
3. **Numerical Precision**: Floating-point evaluation may lose accuracy for large n
4. **Cosine Evaluation**: Requires accurate evaluation at multiples of π

## Next Steps

The symbolic representation enables:
- Analysis of convergence properties
- Study of periodic points
- Investigation of growth rates
- Exploration of algebraic invariants

See the next document on the binomial series formula for an alternative approach that scales better to higher iterations.
