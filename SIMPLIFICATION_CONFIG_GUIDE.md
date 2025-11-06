# Symbolicas Simplification Configuration Guide

## Overview

Symbolicas v2.0 introduces a powerful configurable simplification system that gives you fine-grained control over which algebraic transformations are applied to your expressions.

## Quick Start

### Basic Usage

```scala
import symbolicas.{Expr, SimplificationConfig}
import symbolicas.SimplificationRule._

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
  .withoutRule(MergeFractionsLCD)

// Or create from scratch
val config = SimplificationConfig(Set(
  RemoveIdentity,
  FlattenOperations,
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

### 2. FlattenOperations
Flattens nested operations of the same type.

```scala
// Add(a, Add(b, c)) → Add(a, b, c)
// Mul(a, Mul(b, c)) → Mul(a, b, c)
```

### 3. CombineNumericLiterals
Combines numeric constants.

```scala
// 2 + 3 → 5
// 2 * 3 → 6
```

### 4. FactorCommonTerms ⭐ NEW
Extracts common factors from sums.

```scala
// a*b + a*c → a*(b + c)
// n*pi + n*2*pi → n*pi*(1 + 2) = 3*n*pi

// SOLVES: n*pi - n/2*pi → n*pi*(1 - 1/2) = n*pi/2
```

**This is the key rule for simplifying cosine arguments!**

### 5. CollectLikeTerms ⭐ NEW
Combines terms that differ only by a numeric coefficient.

```scala
// x + 2*x + 3*y → 3*x + 3*y
// a*b + 2*a*b → 3*a*b
```

### 6. MergeFractionsCommonDenom
Merges only fractions with the same denominator.

```scala
// 1/4 + 3/4 → 4/4 = 1
// 1/2 + 1/3 → 1/2 + 1/3  (unchanged, different denominators)
```

### 7. MergeFractionsLCD
Merges all fractions using least common denominator.

```scala
// 1/2 + 1/3 → 3/6 + 2/6 → 5/6
```

**Note**: By default, this is **disabled** to keep expressions symbolic.

### 8. DistributeProduct
Distributes multiplication over addition.

```scala
// a*(b + c) → a*b + a*c
// 2*(x + y) → 2*x + 2*y
```

**Note**: Used during `expand()`, not `simplify()`.

### 9. SimplifyDoubleNegative
Eliminates double negatives.

```scala
// --x → x
// -(-5) → 5
```

### 10. ProductOfCosToSumOfCos
Applies product-to-sum identity for cosines.

```scala
// cos(A) * cos(B) → (cos(A-B) + cos(A+B))/2
```

### 11. SimplifyFractions
Reduces fractions to lowest terms.

```scala
// 4/6 → 2/3
// 10/15 → 2/3
```

### 12. CancelCommonFactors
Cancels common factors in divisions (placeholder for future implementation).

```scala
// (a*b)/(a*c) → b/c
```

## Predefined Configurations

### Default Configuration
```scala
SimplificationConfig.Default
```

Includes:
- RemoveIdentity
- FlattenOperations
- CombineNumericLiterals
- FactorCommonTerms
- MergeFractionsCommonDenom
- SimplifyDoubleNegative
- SimplifyFractions
- CollectLikeTerms

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
import symbolicas.Dsl._
import symbolicas.SimplificationRule._

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
import symbolicas.Dsl._

// Keep fractions symbolic (default)
val expr1 = Num(1,2) + Num(1,3)
println(expr1.simplify)
// Output: 1/2 + 1/3

// Merge to LCD
val configLCD = SimplificationConfig.Default.withRule(MergeFractionsLCD)
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

Run the comprehensive test suite:

```bash
cd src/main/scala
scala-cli test_config.sc
```

Test cosine simplification:

```bash
scala-cli test_cosine_simplification.sc
```

## API Reference

### SimplificationConfig Class

```scala
case class SimplificationConfig(enabledRules: Set[SimplificationRule])
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
val config = SimplificationConfig.Default.withoutRule(MergeFractionsLCD)
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
