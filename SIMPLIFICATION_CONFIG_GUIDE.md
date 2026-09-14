# Symbolum Simplification Configuration Guide

## Overview

Symbolum lets you choose which algebraic transformations the simplifier applies.

A rule switches an *algebraic* rewrite on or off. It does not switch off *normalisation*:
numeric literals are always reduced to lowest terms, `Sub` and `Neg` are always rewritten as
sums and `-1` coefficients, nested sums and products are always flattened, and the operands of a
commutative node are always ordered. Every rule below is stated over that form, so those steps
cannot be switched off without leaving the rules with nothing well-defined to act on.

## Quick Start

### Basic Usage

```scala
import garden.xeno.symbolum.{Expr, SimplificationConfig}
import garden.xeno.symbolum.SimplificationRule._

// Use default configuration
val result = expr.fullSimplify

// Use aggressive configuration (all rules)
val result = expr.simplify(SimplificationConfig.Aggressive)

// Use minimal configuration (essential rules only)
val result = expr.simplify(SimplificationConfig.Minimal)
```

### Custom Configuration

```scala
// Start with default and add rules
val config = SimplificationConfig.Default
  .withRule(FactorCommonTerms)
  .withRule(CollectLikeTerms)

val result = expr.fullSimplify(config)

// Or remove specific rules
val config = SimplificationConfig.Default
  .withoutRule(MergeFractionsCommonDenom)

// Or create from scratch
val config = SimplificationConfig(List(
  RemoveIdentity,
  CombineNumericLiterals
))
```

## Available Simplification Rules

### 1. RemoveIdentity
Removes identity elements (0 for addition, 1 for multiplication).

```scala
// x + 0 → x
// x * 1 → x
// x / 1 → x
```

### 2. CombineNumericLiterals
Combines numeric constants.

```scala
// 2 + 3 → 5
// 2 * 3 → 6
```

### 3. FactorCommonTerms
Extracts common factors from sums.

```scala
// a*b + a*c → a*(b + c)
// n*pi + n*2*pi → n*pi*(1 + 2) = 3*n*pi

// SOLVES: n*pi - n/2*pi → n*pi*(1 - 1/2) = n*pi/2
```

This is the exact inverse of `DistributeProduct`, so the two cannot both run: they would undo
each other forever. Where both are enabled, distribution wins and this rule is inert. To use it,
build a configuration without `DistributeProduct`.

### 4. CollectLikeTerms
Combines terms that differ only by a numeric coefficient.

```scala
// x + 2*x + 3*y → 3*x + 3*y
// a*b + 2*a*b → 3*a*b
```

### 5. MergeFractionsCommonDenom
Puts the terms of a sum over one denominator, their least common one.

```scala
// n/2 + 1/4 → (2*n + 1)/4
```

With the rule off, each term keeps its own denominator: `n/2 + 1/4`. Either way a fractional
coefficient is spelled as a quotient (`n/2`, never `1/2 * n`) because one value with two
spellings is what stops like terms from being recognised.

### 6. DistributeProduct
Distributes multiplication over addition.

```scala
// a*(b + c) → a*b + a*c
// 2*(x + y) → 2*x + 2*y
```

**Note**: `expand()` is simplification with this rule forced on.

### 7. ProductOfCosToSumOfCos
Applies product-to-sum identity for cosines.

```scala
// cos(A) * cos(B) → (cos(A-B) + cos(A+B))/2
```

### 8. SimplifyFractions
Reduces the numeric content a quotient shares with its denominator.

```scala
// (2*n)/4 → n/2
// (9*x - 27)/6 → (3*x - 9)/2
```

A numeric literal is reduced to lowest terms whatever the configuration: `Num(4, 6)` is `2/3` the
moment it is built.

### 9. CancelCommonFactors
Cancels a factor shared by both sides of a quotient.

```scala
// (a*b)/(a*c) → b/c
```

### 10. ExpandLogarithms
Splits a logarithm over its argument.

```scala
// log(a*b) → log(a) + log(b)
// log(a/b) → log(a) - log(b)
// log(a^k) → k*log(a)
```

Off by default: `log(a*b) = log(a) + log(b)` does not hold over the reals when a factor is
negative, so applying it unasked would turn a defined expression into an undefined one.

### 11. ExpandExponentials
Splits an exponential over its argument.

```scala
// exp(a + b) → exp(a) * exp(b)
```

## Predefined Configurations

### Default Configuration
```scala
SimplificationConfig.Default
```

Includes:
- RemoveIdentity
- DistributeProduct
- CombineNumericLiterals
- SimplifyFractions
- CollectLikeTerms
- MergeFractionsCommonDenom
- FactorCommonTerms (inert while DistributeProduct is enabled)

**Best for**: General symbolic computation, keeping expressions clean and readable.

### Minimal Configuration
```scala
SimplificationConfig.Minimal
```

Includes only:
- RemoveIdentity
- CombineNumericLiterals
- SimplifyFractions

**Best for**: When you want minimal interference with expression structure.

### Aggressive Configuration
```scala
SimplificationConfig.Aggressive
```

Includes: **All rules**

**Best for**: Maximum simplification, numeric computation.

### None Configuration
```scala
SimplificationConfig.None
```

Includes: **No rules** (identity transformation)

**Best for**: Debugging, testing, preserving exact structure.

## Solving the Cosine Simplification Problem

### Problem
Expressions like `cos(n*pi - n/2*pi)` weren't being simplified, leaving the argument as `n*pi - n/2*pi` instead of `n*pi/2`.

### Solution
Use `FactorCommonTerms` to extract common factors:

```scala
import garden.xeno.symbolum.Dsl._
import garden.xeno.symbolum.SimplificationRule._

val n = Var("n")

// Problem expression
val expr = cos(n*pi - (n/2)*pi)

// Solution 1: Use aggressive config
val result1 = expr.fullSimplify(SimplificationConfig.Aggressive)
// Result: cos(n*pi/2)  ✓

// Solution 2: Custom config with factoring
val config = SimplificationConfig.Default.withRule(FactorCommonTerms)
val result2 = expr.fullSimplify(config)
// Result: cos(n*pi/2)  ✓

// Solution 3: Just the argument
val arg = n*pi - (n/2)*pi
val simplifiedArg = arg.fullSimplify(config)
// Result: n*pi/2  ✓
```

## Advanced Examples

### Example 1: Selective Fraction Handling

```scala
import garden.xeno.symbolum.Dsl._

// Keep fractions symbolic (default)
val expr1 = Num(1,2) + Num(1,3)
println(expr1.simplify)
// Output: 1/2 + 1/3

// Merge to LCD
val configMerged = SimplificationConfig.Default.withRule(MergeFractionsCommonDenom)
println(expr1.simplify(configLCD))
// Output: 5/6
```

### Example 2: Collatz Expression Simplification

```scala
val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

// Default simplification
val simple1 = collatz1.fullSimplify

// With all advanced rules
val config = SimplificationConfig.Default
  .withRule(FactorCommonTerms)
  .withRule(CollectLikeTerms)

val simple2 = collatz1.fullSimplify(config)
```

### Example 3: Control Distribution

```scala
// Expand fully
val expr = 2 * (x + y)
println(expr.expand)
// Output: 2*x + 2*y

// Keep factored
val configNoDistribute = SimplificationConfig.Default
  .withoutRule(DistributeProduct)
println(expr.expand(configNoDistribute))
// Output: 2*(x + y)
```

### Example 4: Like Terms Collection

```scala
val expr = x + 2*x + 3*x + y + 4*y
val config = SimplificationConfig.Default.withRule(CollectLikeTerms)

println(expr.fullSimplify(config))
// Output: 6*x + 5*y
```

## Testing Your Configuration

Run the suite that covers the rule set:

```bash
sbt "core/testOnly garden.xeno.symbolum.ConfigurationSpec"
```

Cosine simplification has its own suite:

```bash
sbt "core/testOnly garden.xeno.symbolum.CosineSimplificationSpec"
```

## API Reference

### SimplificationConfig Class

```scala
case class SimplificationConfig(
  enabledRules: List[SimplificationRule] = SimplificationConfig.DefaultRules,
  maxExpansionTerms: Int = DEFAULT_MAX_EXPANSION_TERMS
)
```

**Methods:**
- `isEnabled(rule: SimplificationRule): Boolean` - Check if a rule is enabled
- `withRule(rule: SimplificationRule): SimplificationConfig` - Add a rule
- `withoutRule(rule: SimplificationRule): SimplificationConfig` - Remove a rule
- `withRules(rules: SimplificationRule*): SimplificationConfig` - Add multiple rules
- `withoutRules(rules: SimplificationRule*): SimplificationConfig` - Remove multiple rules

### Expr Methods

```scala
trait Expr {
  // Use default config
  def simplify: Expr

  // Use custom config
  def simplify(implicit config: SimplificationConfig): Expr

  // Full simplification with config
  def fullSimplify(implicit config: SimplificationConfig = SimplificationConfig.Default,
                   maxIter: Int = 100): Expr

  // Expand with config
  def expand(implicit config: SimplificationConfig): Expr
}
```

## Best Practices

### 1. Start with Default
The default configuration is designed for most use cases. Only customize when needed.

### 2. Test Your Configuration
Always test your configuration with representative expressions to ensure it behaves as expected.

### 3. Use Aggressive Sparingly
Aggressive configuration applies all rules, which might over-simplify for symbolic work.

### 4. Factor for Cosine Arguments
When working with trigonometric functions, enable `FactorCommonTerms` to simplify arguments.

### 5. Document Your Configs
When using custom configurations in production code, document why specific rules were chosen.

## Migration from v1.0

The new system is **backward compatible**. Existing code using `simplify()` and `fullSimplify()` will continue to work with the default configuration.

To take advantage of new features:

```scala
// Old way (still works)
val result = expr.fullSimplify

// New way (more control)
val config = SimplificationConfig.Default.withRule(FactorCommonTerms)
val result = expr.fullSimplify(config)
```

## Troubleshooting

### Expression Not Simplifying as Expected

1. Check which rules are enabled:
   ```scala
   val config = SimplificationConfig.Default
   println(config.isEnabled(FactorCommonTerms))
   ```

2. Try aggressive config to see maximum simplification:
   ```scala
   expr.fullSimplify(SimplificationConfig.Aggressive)
   ```

3. Add rules incrementally:
   ```scala
   var config = SimplificationConfig.Default
   config = config.withRule(FactorCommonTerms)
   config = config.withRule(CollectLikeTerms)
   ```

### Fractions Being Merged When You Don't Want Them

Disable LCD merging (it's off by default):
```scala
val config = SimplificationConfig.Default.withoutRule(MergeFractionsCommonDenom)
```

### Over-Simplification

Use minimal config or remove specific rules:
```scala
val config = SimplificationConfig.Minimal
// or
val config = SimplificationConfig.Default
  .withoutRule(FactorCommonTerms)
  .withoutRule(CollectLikeTerms)
```

## Future Extensions

The rule-based system is designed for easy extension. New rules can be added by:

1. Adding to `SimplificationRule` enumeration
2. Implementing the rule in the appropriate expression class
3. Checking `config.isEnabled(NewRule)` before applying

## Conclusion

The configurable simplification system provides precise control over algebraic transformations while maintaining backward compatibility and ease of use. It solves the cosine simplification problem and provides a foundation for future enhancements.

For questions or issues, see the test files for working examples.
