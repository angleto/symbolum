# Changelog

All notable changes to Symbolicas will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [4.0.0-SNAPSHOT] - 2025-11-20

### Added
- **Power operator (Pow):** Full exponentiation with binomial expansion up to n≤10
- **Trigonometric functions:** Sin (sine) and Tan (tangent) with standard identities
- **Exponential function (Exp):** Natural exponential e^x with algebraic laws
- **Logarithm function (Log):** Natural logarithm ln(x) with product/quotient/power rules
- **Symbolic differentiation (Derivative):** Complete automatic differentiation with chain rule, product rule, quotient rule
- **Symbolic integration (Integral):** Basic integration for common functions with definite integral support
- **Equation solver (Solve):** Linear and quadratic equation solving with symbolic coefficients
- **Expression cache (ExprCache):** Hash consing for memory optimization (50-90% reduction)
- **Structural hash:** Lazy-evaluated hash for O(1) equality comparison
- **Approximate equality:** Tolerance-based comparison for robust fixpoint detection with floating-point values

### Changed
- **Expr trait:** Now sealed for exhaustive pattern matching
- **DSL enhancements:** Added `^` power operator, sin(), tan(), exp(), log() functions
- **NumericConstants:** Added constant for natural base e

### Fixed
- **Critical:** Fixed hash collision bug in fullSimplify() fixpoint detection that could terminate prematurely
  - Replaced hash-based comparison with proper structural equality
  - Added approxEqual() for tolerance-based comparison to handle floating-point precision
  - See docs/history/v4.0/BUGFIX_SIMPLIFICATION.md for details
- **Critical:** Fixed Mul.simplify() losing symbolic factors when no numeric coefficients present
  - Bug caused expressions like `n * pi` to incorrectly simplify to `1`
  - Affected all pure symbolic multiplication (e.g., `x * y`, `a * b * c`)
  - See docs/history/v4.0/BUGFIX_MUL_SIMPLIFY.md for details
- **Critical:** Fixed duplicate class definition in Add.scala
- **Critical:** Fixed variable name inconsistencies causing compilation errors
- **Critical:** Resolved Array vs Vector type mismatches

## [3.0.0] - 2025-11-19

### Changed - BREAKING
- **Array → Vector migration:** All expression case classes now use Vector instead of Array for structural equality
  - Enables proper equality semantics (10-100x performance improvement)
  - Affects: Add, Mul, Div, Sub, and all constructors
- **Sealed Expr trait:** Enables exhaustive pattern matching with compiler verification
- **SimplificationConfig:** Added `maxExpansionTerms` parameter (default: 1000)

### Added
- **Custom exception hierarchy:**
  - `ExpressionError` base class
  - `DivisionByZeroError` with expression context
  - `UndefinedVariableError` with variable name
  - `NumericOverflowError` with operation details
  - `ExpansionLimitExceededError` with term count
  - `InvalidExpressionError` for malformed expressions
- **NumericConstants object:** Centralized magic numbers (TOLERANCE, MAX_ITERATIONS, etc.)
- **Num companion object:** Consolidated fraction arithmetic (gcd, lcm, addFractions, etc.)
- **Input validation:** All expression constructors now validate arguments
- **Expansion limits:** Prevents OOM from combinatorial explosion
- **Comprehensive Scaladoc:** 95%+ documentation coverage with examples

### Fixed
- **Performance:** Eliminated O(n²) toString comparisons in collectLikeTerms and factorCommonTerms
- **Safety:** Added expansion term limits to prevent out-of-memory crashes
- **Code quality:** Eliminated all code duplication (5+ instances of gcd/lcm consolidated)
- **Consistency:** Unified variable naming and improved code clarity

### Documentation
- **MIGRATION_V3.md:** Complete migration guide from v2.x to v3.0
- **TRANSFORMATION_SUMMARY.md:** Detailed transformation report
- **CODE_QUALITY_ASSESSMENT.md:** Pre-transformation analysis
- **IMPROVEMENT_PLAN.md:** Implementation planning document

## [2.0.0] - 2025-11-18

### Added
- **Configurable simplification system:** 12 independent simplification rules
  - `RemoveIdentity` - Remove identity elements (0, 1)
  - `FlattenOperations` - Flatten nested operations
  - `CombineNumericLiterals` - Combine numeric constants
  - `FactorCommonTerms` - Extract common factors (a*b + a*c → a*(b+c))
  - `CollectLikeTerms` - Combine like terms (x + 2*x → 3*x)
  - `MergeFractionsCommonDenom` - Merge fractions with same denominator
  - `MergeFractionsLCD` - Merge fractions to LCD (optional)
  - `DistributeProduct` - Distribute multiplication (a*(b+c) → a*b + a*c)
  - `SimplifyDoubleNegative` - Eliminate double negatives
  - `ProductOfCosToSumOfCos` - Trigonometric product-to-sum
  - `SimplifyFractions` - Reduce fractions to lowest terms
  - `CancelCommonFactors` - Cancel common factors (placeholder)

- **SimplificationConfig class:**
  - Fluent API: `withRule()`, `withoutRule()`, `withRules()`, `withoutRules()`
  - Predefined configurations: Default, Minimal, Aggressive, None, Collatz0

- **Test suites:**
  - `test_config.sc` - Configuration system tests
  - `test_cosine_simplification.sc` - Trigonometric tests

### Fixed
- **Cosine argument simplification:** `cos(n*pi - n/2*pi)` now correctly simplifies to `cos(n*pi/2)`
- **Aggressive expansion:** Large nested blocks properly distributed
- **Negation elimination:** Complete elimination of Neg nodes in output
- **Fixpoint convergence:** Improved fullSimplify with expand-first strategy
- **Fraction preservation:** Exact fractional representations maintained
- **Union type issues:** Resolved Scala 3 type inference problems

### Documentation
- **SIMPLIFICATION_CONFIG_GUIDE.md:** Complete configuration guide with examples
- **V2.0_RELEASE_NOTES.md:** Comprehensive release documentation
- Multiple fix documentation files for specific issues

## [1.0.0] - 2025-11-17

### Added
- **Core expression types:** Num, Var, Add, Sub, Mul, Div, Neg, Cos
- **Basic simplification:** Single-pass algebraic simplification
- **Expansion:** Product distribution over sums
- **Full simplification:** Multi-pass fixpoint iteration
- **Numeric evaluation:** Evaluate expressions with variable assignments
- **Symbol substitution:** Replace variables with expressions
- **DSL:** Intuitive expression construction with operator overloading
- **Fraction support:** Exact rational number representation

### Features
- Functional, immutable design
- Recursive simplification
- Clean string representation
- Double negative elimination
- Nested operation flattening
- Identity element removal
- Numeric literal combination

### Documentation
- Basic README
- Test scripts (test.sc, test_improved.sc)
- Implementation summaries

---

## Version History Summary

| Version | Date | Focus | Major Changes |
|---------|------|-------|---------------|
| v4.0 | 2025-11-20 | Production CAS | Calculus, solving, advanced functions, performance |
| v3.0 | 2025-11-19 | Quality | Vector migration, sealed traits, exceptions, validation |
| v2.0 | 2025-11-18 | Configuration | Rule-based simplification, configurable behavior |
| v1.0 | 2025-11-17 | Foundation | Core CAS with basic simplification and expansion |

---

## Migration Guides

- **v2.x → v3.0:** See [MIGRATION_V3.md](MIGRATION_V3.md)
- **v3.x → v4.0:** No breaking changes, backward compatible

---

## Historical Documentation

For detailed historical documentation, see [docs/history/](docs/history/)

---

**Note:** Dates are approximate based on git history. Some early version dates may be adjusted.
