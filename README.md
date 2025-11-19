# Symbolicas

A **Scala Computer Algebra System (CAS)** for symbolic algebraic expression manipulation with configurable simplification rules.

[![Scala Version](https://img.shields.io/badge/scala-3.3.5-red.svg)](https://www.scala-lang.org/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

## Overview

Symbolicas provides a powerful and flexible framework for building, manipulating, and simplifying symbolic mathematical expressions. The system uses a configurable rule-based approach that gives you fine-grained control over which algebraic transformations are applied.

### Key Features

- **Symbolic Expression Building**: Construct complex algebraic expressions using an intuitive DSL
- **Configurable Simplification**: 12 independent simplification rules that can be selectively enabled/disabled
- **Algebraic Expansion**: Distribute products over sums with proper handling of nested structures
- **Fraction Handling**: Preserve exact fractional representations throughout computations
- **Trigonometric Transformations**: Product-to-sum identities for cosine functions
- **Multi-pass Optimization**: Aggressive full simplification with fixpoint detection
- **Type-safe**: Built with Scala 3.3.5 for compile-time safety

## Quick Start

### Installation

Add Symbolicas to your `build.sbt`:

```scala
scalaVersion := "3.3.5"

libraryDependencies += "com.github.symbolicas" %% "symbolicas" % "2.0.0"
```

### Basic Usage

```scala
import symbolicas._
import symbolicas.Dsl._

// Define a variable
val n = Var("n")

// Build an expression: 2*n + 3*n - 1
val expr = 2 * n + 3 * n - 1

// Simplify the expression
val simplified = expr.simplify()
println(simplified)  // Output: 5 * n - 1

// Evaluate numerically
val result = simplified.eval(Map("n" -> 10.0))
println(result)  // Output: 49.0

// Expand a product: a * (b + c)
val a = Var("a")
val b = Var("b")
val c = Var("c")
val product = a * (b + c)
val expanded = product.expand()
println(expanded)  // Output: a * b + a * c
```

### Working with Fractions

```scala
import symbolicas._
import symbolicas.Dsl._

val x = Var("x")

// Fractions are preserved exactly
val expr = Num(1, 2) + Num(1, 3) + x  // 1/2 + 1/3 + x

// Simplify combines fractions via LCD
val simplified = expr.simplify()
println(simplified)  // Output: 5/6 + x

// Full simplification for complex expressions
val complex = (x / 2) + (x / 3)
val result = complex.fullSimplify()
println(result)  // Output: (5 * x)/6
```

### Trigonometric Simplification

```scala
import symbolicas._
import symbolicas.Dsl._

val a = Var("a")
val b = Var("b")

// Product-to-sum transformations
val expr = cos(a) * cos(b)
val simplified = expr.expand()
// Output: 1/2 * (cos(a - b) + cos(a + b))
```

## Architecture

### Expression Hierarchy

```
Expr (trait)
├── Num         - Numeric literals with fraction support
├── Var         - Symbolic variables
├── Add         - N-ary addition
├── Sub         - N-ary subtraction
├── Mul         - N-ary multiplication
├── Div         - Division
├── Neg         - Unary negation
└── Cos         - Cosine function
```

### Simplification System

The simplification system is built around three core operations:

1. **`simplify()`** - Single-pass simplification applying enabled rules once
2. **`expand()`** - Distributes products over sums (a*(b+c) → a*b + a*c)
3. **`fullSimplify()`** - Multi-pass expansion and simplification until fixpoint

#### Configuration

Control simplification behavior using `SimplificationConfig`:

```scala
import symbolicas._
import SimplificationRule._

// Use a predefined configuration
val expr = /* ... */
expr.simplify(SimplificationConfig.Minimal)
expr.simplify(SimplificationConfig.Aggressive)
expr.simplify(SimplificationConfig.Collatz0)

// Build a custom configuration
val custom = SimplificationConfig.Default
  .withRule(ProductOfCosToSumOfCos)
  .withoutRule(FactorCommonTerms)

expr.simplify(custom)
```

### Available Simplification Rules

| Rule | Description | Example |
|------|-------------|---------|
| `RemoveIdentity` | Remove 0s and 1s | `0 + x → x`, `1 * x → x` |
| `FlattenOperations` | Flatten nested ops | `Add(a, Add(b, c)) → Add(a, b, c)` |
| `CombineNumericLiterals` | Combine constants | `2 + 3 → 5` |
| `SimplifyFractions` | Reduce fractions | `4/6 → 2/3` |
| `CollectLikeTerms` | Combine like terms | `x + 2*x → 3*x` |
| `MergeFractionsLCD` | Merge to LCD | `1/2 + 1/3 → 5/6` |
| `MergeFractionsCommonDenom` | Merge same denom | `a/d + b/d → (a+b)/d` |
| `DistributeProduct` | Distribute | `a*(b+c) → a*b + a*c` |
| `FactorCommonTerms` | Factor common | `a*b + a*c → a*(b+c)` |
| `SimplifyDoubleNegative` | Remove double neg | `--x → x` |
| `ProductOfCosToSumOfCos` | Cosine product-to-sum | `cos(A)*cos(B) → ...` |
| `CancelCommonFactors` | Cancel factors | `(a*b)/(a*c) → b/c` |

### Predefined Configurations

```scala
// Default - balanced for most use cases
SimplificationConfig.Default

// Minimal - only essential simplifications
SimplificationConfig.Minimal

// Aggressive - all rules enabled
SimplificationConfig.Aggressive

// Collatz0 - optimized for Collatz sequences
SimplificationConfig.Collatz0

// None - no simplifications
SimplificationConfig.None
```

## Advanced Usage

### Building Custom Configurations

```scala
import symbolicas._
import SimplificationRule._

// Start from scratch
val custom = SimplificationConfig(
  enabledRules = List(
    RemoveIdentity,
    CombineNumericLiterals,
    CollectLikeTerms
  )
)

// Modify existing configurations
val modified = SimplificationConfig.Default
  .withoutRules(FactorCommonTerms, MergeFractionsLCD)
  .withRule(ProductOfCosToSumOfCos)
```

### Full Simplification

For deeply nested expressions, use `fullSimplify()` which applies multiple passes until reaching a fixpoint:

```scala
val expr = /* complex nested expression */
val fullySimplified = expr.fullSimplify()

// With custom config and iteration limit
val result = expr.fullSimplify(customConfig, maxIter = 50)
```

### Symbol Substitution

Replace variables with expressions:

```scala
val expr = x + y * 2
val substituted = expr.replaceSymbol("y", z - 1)
// Result: x + (z - 1) * 2

val simplified = substituted.fullSimplify()
// Result: x + 2*z - 2
```

### Numeric Evaluation

```scala
val expr = x * x + 2 * x + 1  // x^2 + 2x + 1

// Evaluate at x = 3
val result = expr.eval(Map("x" -> 3.0))
// Result: 16.0

// Multiple variables
val expr2 = x + y + z
val result2 = expr2.eval(Map("x" -> 1.0, "y" -> 2.0, "z" -> 3.0))
// Result: 6.0
```

## Use Cases

Symbolicas is particularly effective for:

- **Collatz Sequence Analysis**: Symbolic computation of Collatz formulas
- **Algebraic Manipulation**: General symbolic algebra with customizable behavior
- **Educational Tools**: Teaching computer algebra system concepts
- **Mathematical Research**: Exploring algebraic structures and transformations
- **Code Generation**: Generating optimized mathematical code from symbolic expressions

## Implementation Details

### Design Patterns

**Expand Pattern**: Most expression types follow this pattern:
```scala
override def expand(implicit config: SimplificationConfig): Expr = {
  val expandedChildren = children.map(_.expand(config))
  // Apply expansion transformation
  result.simplify(config)  // Always simplify after expansion
}
```

**Simplify Pattern**: Check enabled rules and apply transformations:
```scala
def simplify(implicit config: SimplificationConfig): Expr = {
  if (config.isEnabled(SomeRule)) {
    // Apply transformation
  } else {
    // Keep original form
  }
}
```

### Fraction Representation

Numeric values use `Num(numerator, denominator)` to preserve exact fractions:
```scala
val half = Num(1, 2)       // 1/2 (not 0.5)
val third = Num(1, 3)      // 1/3 (not 0.333...)
val sum = half + third     // 5/6 (exact)
```

### Performance Considerations

- **Single-pass simplification** (`simplify()`) is fast and suitable for most cases
- **Full simplification** (`fullSimplify()`) is more expensive but handles complex nested structures
- **Fixpoint detection** prevents infinite loops in `fullSimplify()`
- **Maximum iteration limit** (default 100) provides safety for pathological cases

## Testing

Run the comprehensive test suite:

```bash
# Compile the project
sbt compile

# Run test scripts (various test scenarios)
cd src/main/scala
scala-cli test_improved.sc
scala-cli test_config.sc
scala-cli test_cosine_simplification.sc
scala-cli test_collatz3.sc
```

Test coverage includes:
- Basic arithmetic operations
- Fraction handling and simplification
- Trigonometric transformations
- Configuration system
- Collatz sequence formulas
- Edge cases and regression scenarios

## Documentation

- **API Documentation**: See Scaladoc comments in source files
- **User Guide**: [SIMPLIFICATION_CONFIG_GUIDE.md](SIMPLIFICATION_CONFIG_GUIDE.md)
- **Release Notes**: [V2.0_RELEASE_NOTES.md](V2.0_RELEASE_NOTES.md)
- **Testing Guide**: [TESTING.md](TESTING.md)
- **Technical Details**: See `*.md` files in the repository

## Examples

### Example 1: Simplifying Polynomials

```scala
import symbolicas._
import symbolicas.Dsl._

val x = Var("x")

// Build: 3*x + 2*x - x + 5 - 3
val expr = 3*x + 2*x - x + 5 - 3

// Simplify
val result = expr.simplify()
println(result)  // Output: 4*x + 2
```

### Example 2: Expanding Products

```scala
import symbolicas._
import symbolicas.Dsl._

val x = Var("x")
val y = Var("y")

// Build: (x + 1) * (y + 2)
val expr = (x + 1) * (y + 2)

// Expand
val result = expr.expand()
println(result)  // Output: x*y + 2*x + y + 2
```

### Example 3: Fraction Simplification

```scala
import symbolicas._
import symbolicas.Dsl._

val x = Var("x")

// Build: x/2 + x/3 + x/6
val expr = x/2 + x/3 + x/6

// Simplify
val result = expr.fullSimplify()
println(result)  // Output: x
```

### Example 4: Custom Configuration

```scala
import symbolicas._
import symbolicas.Dsl._
import SimplificationRule._

val x = Var("x")

// Build: (x + 1) * (x + 2)
val expr = (x + 1) * (x + 2)

// Expand but don't collect like terms
val config = SimplificationConfig.Default
  .withoutRule(CollectLikeTerms)

val result = expr.expand(config)
// Output: x*x + x + 2*x + 2 (without combining x terms)

// Now collect like terms
val final_result = result.simplify()
// Output: x*x + 3*x + 2
```

## Contributing

Contributions are welcome! Please see [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

### Development Setup

```bash
# Clone the repository
git clone https://github.com/yourusername/symbolicas.git
cd symbolicas

# Compile
sbt compile

# Run tests
sbt test

# Generate documentation
sbt doc
```

## Version History

- **v2.0** - Configurable simplification system with 12 independent rules
- **v1.0** - Initial release with basic simplification and expansion

See [V2.0_RELEASE_NOTES.md](V2.0_RELEASE_NOTES.md) for detailed changes.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Acknowledgments

- Built with Scala 3.3.5
- Inspired by traditional computer algebra systems (Mathematica, Maple, SymPy)
- Designed for the Collatz sequence research community

## Support

For issues, questions, or suggestions:
- Open an issue on GitHub
- Check existing documentation in the `docs/` directory
- Review test cases for usage examples

## Project Status

**Status**: Active Development

The project is actively maintained and accepts contributions. The core functionality is stable and production-ready.

---

**Happy symbolic computing! 🧮**
