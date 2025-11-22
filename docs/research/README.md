# Collatz Conjecture Research

## Overview

This directory contains comprehensive research on the Collatz conjecture using the Symbolicas Computer Algebra System (CAS). The research explores symbolic and numerical approaches to analyzing this famous unsolved problem in mathematics.

## The Collatz Conjecture

**Problem Statement**: Given any positive integer n, repeatedly apply:
- If n is even: n → n/2
- If n is odd: n → 3n+1

**Conjecture**: This process always eventually reaches 1.

**Status**: Unsolved since 1937

## Research Documents

### [01_OVERVIEW.md](01_OVERVIEW.md)
Introduction to the research approach, methodology, and goals. Start here for context.

**Contents**:
- Problem statement and background
- Research methodology
- Dual approach: symbolic representation and binomial series
- Research structure and goals

### [02_SYMBOLIC_REPRESENTATION.md](02_SYMBOLIC_REPRESENTATION.md)
Detailed explanation of the symbolic closed-form representation using trigonometric functions.

**Key Topics**:
- Unified formula using cosine for parity detection
- Building higher iterations through substitution
- Expression complexity and growth
- Implementation in Symbolicas CAS
- Verification methods

**Main Formula**:
```
collatz₁(n) = -((2n + 1)/4) · cos(nπ) + n + 1/4
```

### [03_BINOMIAL_SERIES.md](03_BINOMIAL_SERIES.md)
Mathematical derivation and implementation of the binomial expansion formula.

**Key Topics**:
- Binomial series derivation
- Path analysis through the Collatz tree
- Implementation with numerical stability
- Comparison with symbolic approach
- Applications and use cases

**Main Formula**:
```
collatz_k(n) = Σ(m=0 to k) C(k,m) · (1/2^k) ·
               [(3^m - 1)/2 + 3^m · n - ((1 + 2·3^m·n)/4) · cos(3^m · n · π / 2^(k-m))]
```

### [04_MATHEMATICAL_PROPERTIES.md](04_MATHEMATICAL_PROPERTIES.md)
Theoretical insights and mathematical properties discovered through symbolic analysis.

**Key Topics**:
- Parity structure and cosine encoding
- Polynomial-trigonometric form
- Coefficient growth patterns
- Symmetry properties
- Fixed points and cycles
- Algebraic invariants
- Implications for proving the conjecture

### [05_COMPUTATIONAL_EXPERIMENTS.md](05_COMPUTATIONAL_EXPERIMENTS.md)
Detailed experimental results validating the implementations and exploring patterns.

**Key Topics**:
- Symbolic vs. direct computation verification
- Expression simplification quality
- Numerical stability testing
- Performance benchmarking
- Large-scale verification
- Pattern discovery
- Statistical analysis

### [06_CONCLUSIONS.md](06_CONCLUSIONS.md)
Summary of findings, limitations, and future research directions.

**Key Topics**:
- Summary of achievements
- What has been demonstrated
- What remains unproven
- Research contributions
- Insights gained
- Future directions
- Practical applications

## Key Results

### ✓ Verified

1. **Mathematical Correctness**: Both symbolic and binomial formulas produce correct results
2. **Numerical Accuracy**: Agreement with direct computation to floating-point precision
3. **Symbolic Soundness**: Simplification preserves mathematical meaning
4. **Idempotency**: Simplification reaches stable fixpoint
5. **Large-Scale Testing**: Thousands of test cases pass

### ✗ Not Proven

1. **Universal Convergence**: Haven't proven all integers reach 1
2. **Unique Cycle**: Haven't proven 1-4-2-1 is the only cycle
3. **Non-Divergence**: Haven't proven sequences don't grow unboundedly
4. **Finite Stopping Time**: Haven't proven τ(n) < ∞ for all n

## Implementation

### Symbolic Approach
Located in `src/test/scala/symbolicas/CollatzSpec.scala` and used throughout the test suite.

**Example**:
```scala
import symbolicas._
import symbolicas.Dsl._

val n = Var("n")
val pi = Var("pi")

// Build symbolic expression for one iteration
val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

// Simplify
val simplified = collatz1.fullSimplify(SimplificationConfig.Collatz0)

// Evaluate numerically
val result = simplified.eval(Map("n" -> 10.0, "pi" -> math.Pi))
```

### Binomial Series
Located in `src/main/scala/symbolicas/CollatzSeries.scala`.

**Example**:
```scala
import symbolicas.CollatzSeries

// Compute 3 iterations starting from 27
val result = CollatzSeries.collatzK(27.0, 3)
// Returns: 124.0

// For large k, use stable version
val resultStable = CollatzSeries.collatzKStable(100.0, 20)
```

### Test Suite
Located in `src/test/scala/symbolicas/CollatzSpec.scala`.

Run tests with:
```bash
sbt test
```

## Tools Used

- **Language**: Scala 3.3.5
- **CAS**: Symbolicas v4.0.0-SNAPSHOT
- **Testing**: ScalaTest
- **Build**: SBT

## Simplification Configuration

The `Collatz0` configuration is optimized for Collatz expressions:

```scala
SimplificationConfig.Collatz0
```

Includes:
- Aggressive distribution
- Cosine product-to-sum transformations
- Fraction normalization
- Like-term collection
- Common factor cancellation

## Research Methodology

1. **Dual Validation**: Every symbolic result is verified numerically
2. **Comprehensive Testing**: Extensive test suite ensures correctness
3. **Incremental Complexity**: Start with k=1, build up to k=3+
4. **Multiple Implementations**: Independent implementations cross-validate
5. **Documentation**: Thorough documentation of methods and results

## Key Insights

### Mathematical
- Collatz has rich algebraic structure
- Parity is central to the dynamics
- Expressions have polynomial-trigonometric form
- Coefficients exhibit regular patterns

### Computational
- Symbolic and numerical approaches are complementary
- Simplification is essential for higher iterations
- Numerical stability requires careful implementation
- O(k) time complexity is achievable

### Theoretical
- Structure suggests non-random behavior
- Multiple mathematical lenses reveal different properties
- Tools enable exploration beyond brute force
- Proof remains elusive but progress is possible

## Future Directions

### Immediate
- Extend to higher k (optimize simplification)
- Deeper pattern analysis
- Alternative representations (matrix, generating functions)
- Visualization tools

### Medium-Term
- Probabilistic analysis
- Modular arithmetic approaches
- Asymptotic analysis
- Complex analytic methods

### Long-Term
- Partial proofs for specific classes
- Theoretical framework development
- Advanced tool enhancements
- Community collaboration

## How to Use This Research

### For Understanding
1. Read documents in order (01 through 06)
2. Examine code examples
3. Run tests to verify results
4. Experiment with the tools

### For Extension
1. Study the implementations
2. Identify areas for improvement
3. Implement enhancements
4. Contribute back

### For Education
1. Use as a case study in symbolic mathematics
2. Demonstrate CAS capabilities
3. Teach testing and verification
4. Illustrate research methodology

## Contributing

Contributions are welcome:
- **Bug Reports**: Found an error? Report it
- **Enhancements**: Ideas for improvement? Implement them
- **Documentation**: Clarifications needed? Add them
- **Research**: New insights? Share them

## References

### Collatz Conjecture
- Original conjecture (Lothar Collatz, 1937)
- Lagarias, J. C. (2010). "The 3x+1 problem: An annotated bibliography"
- Numerous research papers (see mathematics literature)

### Symbolicas CAS
- Main documentation: [../README.md](../../README.md)
- Simplification guide: [../SIMPLIFICATION_CONFIG_GUIDE.md](../../SIMPLIFICATION_CONFIG_GUIDE.md)
- Changelog: [../CHANGELOG.md](../../CHANGELOG.md)

### Scala
- Scala 3 documentation: https://docs.scala-lang.org/scala3/
- ScalaTest: https://www.scalatest.org/

## License

This research and the Symbolicas CAS are released under the MIT License. See [LICENSE](../../LICENSE) for details.

## Contact

For questions, suggestions, or collaboration:
- Open an issue on GitHub
- Check existing documentation
- Consult the test suite for examples

## Acknowledgments

- Lothar Collatz for the original conjecture
- Countless mathematicians who have explored this problem
- The Scala and functional programming community
- Open source contributors

## Status

**Active Research** - This is ongoing work. The Collatz conjecture remains unproven. This research provides tools and insights but does not constitute a proof.

---

**Last Updated**: November 2024
**Symbolicas Version**: 4.0.0-SNAPSHOT
**Research Status**: In Progress

---

*"The beauty of mathematics is in the journey of exploration."*
