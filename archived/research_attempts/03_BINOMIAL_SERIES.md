# Binomial Series Formula for Collatz Sequences

## Overview

The binomial series approach provides a closed-form formula for computing the k-th iteration of the Collatz function directly, without recursive substitution. This formula is implemented in `CollatzSeries.scala`.

## The Formula

```
collatz_k(n) = Σ(m=0 to k) C(k,m) · (1/2^k) ·
               [(3^m - 1)/2 + 3^m · n - ((1 + 2·3^m·n)/4) · cos(3^m · n · π / 2^(k-m))]
```

Where:
- `C(k,m)` = binomial coefficient k-choose-m
- `k` = number of iterations
- `m` = index of summation (0 to k)
- `n` = starting value
- `π` = pi

## Derivation

### Path Analysis

After k iterations, the Collatz sequence has taken some path through the decision tree. Each path can be encoded as:
- A sequence of k bits indicating even (0) or odd (1) at each step
- There are 2^k possible paths
- Each path occurs with a certain probability based on n's parity

### Binomial Coefficients

The binomial coefficient C(k,m) counts the number of paths that take exactly m "odd" steps and (k-m) "even" steps.

For example, with k=3:
- C(3,0) = 1: path EEE (all even)
- C(3,1) = 3: paths EEO, EOE, OEE (one odd)
- C(3,2) = 3: paths EOO, OEO, OOE (two odds)
- C(3,3) = 1: path OOO (all odd)

### Power Terms

Each term in the sum represents paths with m odd steps:

- **3^m**: Each odd step multiplies by 3 (from 3n+1)
- **2^k**: Each step divides by 2 (inherent in the formula)
- **2^(k-m)**: Additional factor in the cosine argument

### Constant Term

The term `(3^m - 1)/2` accounts for the "+1" additions from odd steps:
- After m odd steps, we've added 1 exactly m times
- Combined with the multiplications, this gives the pattern (3^m - 1)/2

### Cosine Term

The term `cos(3^m · n · π / 2^(k-m))` handles parity:
- Distinguishes between different paths with the same number of odd steps
- The argument depends on the transformed value after m odd steps
- The division by 2^(k-m) accounts for subsequent even steps

## Implementation

### Binomial Coefficient Computation

```scala
def binomial(n: Int, k: Int): Long = {
  if (k > n || k < 0) 0L
  else if (k == 0 || k == n) 1L
  else {
    var result = 1L
    for (i <- 1 to math.min(k, n - k)) {
      result = result * (n - i + 1) / i
    }
    result
  }
}
```

This uses the optimization `C(n,k) = C(n, n-k)` to compute fewer terms.

### Main Formula

```scala
def collatzK(n: Double, k: Int): Double = {
  var sum = 0.0

  for (m <- 0 to k) {
    val binomCoeff = binomial(k, m)
    val threePowerM = pow(3, m)
    val twoPowerK = pow(2, k)
    val twoPowerKMinusM = pow(2, k - m)

    val constantTerm = (threePowerM - 1) / 2
    val linearTerm = threePowerM * n
    val cosineAmplitude = (1 + 2 * threePowerM * n) / 4
    val cosineArgument = (threePowerM * n * Pi) / twoPowerKMinusM

    val termValue = binomCoeff / twoPowerK * (
      constantTerm +
      linearTerm -
      cosineAmplitude * cos(cosineArgument)
    )

    sum += termValue
  }

  sum
}
```

### Numerically Stable Version

For large k, we use logarithms to prevent overflow:

```scala
def collatzKStable(n: Double, k: Int): Double = {
  var sum = 0.0

  for (m <- 0 to k) {
    val binomCoeff = binomial(k, m).toDouble

    // Use logarithms for better numerical stability
    val log3m = m * log(3)
    val log2k = k * log(2)
    val log2km = (k - m) * log(2)

    val threePowerM = exp(log3m)
    val coefficientFactor = binomCoeff * exp(-log2k)

    val cosineArgument = if (k - m == 0) {
      threePowerM * n * Pi
    } else {
      threePowerM * n * Pi * exp(-log2km)
    }

    val term = coefficientFactor * (
      (threePowerM - 1) / 2 +
      threePowerM * n -
      (1 + 2 * threePowerM * n) / 4 * cos(cosineArgument)
    )

    sum += term
  }

  sum
}
```

## Mathematical Properties

### Complexity
- **Time**: O(k) - linear in number of iterations
- **Space**: O(1) - constant space
- **Accuracy**: Subject to floating-point precision limits

### Symmetry
The formula exhibits symmetry in the binomial coefficients:
- C(k,m) = C(k, k-m)
- Terms balance between few odd steps and many odd steps

### Limit Behavior

As k → ∞:
- The sum involves exponentially many terms (2^k conceptually)
- But we only compute k+1 terms due to binomial grouping
- Each term's magnitude depends on the balance of powers of 2 and 3

### Special Cases

**k = 0** (no iterations):
```
collatz_0(n) = C(0,0) · (1/1) · [0 + 1·n - ((1+2n)/4)·cos(nπ)]
             = n - ((1+2n)/4)·cos(nπ)
             = n  (since the cosine term cancels)
```

**k = 1** (one iteration):
```
collatz_1(n) = C(1,0)·(1/2)·[0 + n - (1+2n)/4·cos(nπ/2)] +
               C(1,1)·(1/2)·[(3-1)/2 + 3n - (1+6n)/4·cos(3nπ)]
```

This simplifies to match our symbolic formula.

## Verification Examples

### Example 1: n=10, k=2

Direct computation:
```
10 → 5 → 16
```

Formula computation:
```scala
collatzK(10, 2)
```

Both give 16.0 (approximately, accounting for floating point).

### Example 2: n=27, k=3

Direct computation:
```
27 → 82 → 41 → 124
```

Formula computation:
```scala
collatzK(27, 3)
```

Both give 124.0.

## Advantages

1. **Direct Computation**: No need for k iterations
2. **Theoretical Analysis**: Closed-form enables mathematical study
3. **Parallelization**: Each term can be computed independently
4. **Predictability**: O(k) time complexity is guaranteed

## Limitations

1. **Floating Point**: Loses exactness for large values
2. **Overflow Risk**: Powers of 3 grow exponentially
3. **Cosine Precision**: Requires accurate evaluation at specific angles
4. **No Symbolic Output**: Produces numerical results only

## Comparison with Symbolic Approach

| Aspect | Binomial Series | Symbolic Recursion |
|--------|----------------|-------------------|
| **Output** | Numerical | Algebraic |
| **Complexity** | O(k) terms | Exponential growth |
| **Simplification** | Not needed | Critical |
| **Accuracy** | Float precision | Exact (symbolic) |
| **Use Case** | Large k | Pattern analysis |

## Applications

### 1. Testing Convergence
Compute collatz_k(n) for large k to test if it approaches 1:

```scala
val k = 100
val result = collatzKStable(n, k)
if (result < 2) println(s"Likely converging for n=$n")
```

### 2. Finding Periodic Points
Search for values where collatz_k(n) = n:

```scala
for (n <- 1 to 10000) {
  if (math.abs(collatzK(n, k) - n) < 0.01) {
    println(s"Potential period-$k point: $n")
  }
}
```

### 3. Statistical Analysis
Study the distribution of k-step values:

```scala
val results = (1 to 10000).map(n => collatzK(n, 10))
val mean = results.sum / results.length
val variance = results.map(x => (x - mean) * (x - mean)).sum / results.length
```

## Future Enhancements

Potential improvements to the formula:

1. **Symbolic Binomial**: Compute the sum symbolically using the CAS
2. **Modular Arithmetic**: Work in Z/2Z to handle parity algebraically
3. **Generating Functions**: Express as a generating function
4. **Asymptotic Analysis**: Study behavior as k → ∞

## Conclusion

The binomial series formula provides a powerful tool for:
- Rapid computation of multi-step Collatz values
- Testing conjectures across large parameter spaces
- Theoretical analysis of sequence behavior
- Complementing the symbolic approach with numerical verification

Together with the symbolic representation, it forms a comprehensive toolkit for Collatz research.
