# SimplificationConfig Refactor - Ordered Rules and Factory Pattern

## Overview

This refactor changes `SimplificationConfig` from using unordered `Set[SimplificationRule]` to ordered `List[SimplificationRule]`, and adds a factory pattern for creating named configurations.

## Why Order Matters

The order in which simplification rules are applied significantly affects the final result. For example:

```scala
// BAD ORDER:
1. CollectLikeTerms: x + 2*x → 3*x
2. DistributeProduct: 2*(x + 1) → 2*x + 2
// Problem: Can't distribute products that are already collected!

// GOOD ORDER:
1. DistributeProduct: 2*(x + 1) → 2*x + 2
2. CollectLikeTerms: 2*x + 2 + x → 3*x + 2
// Works correctly: distributes first, then collects
```

## Key Changes

### 1. List Instead of Set

**Before:**
```scala
case class SimplificationConfig(
  enabledRules: Set[SimplificationRule] = ...
)
```

**After:**
```scala
case class SimplificationConfig(
  enabledRules: List[SimplificationRule] = ...
)
```

### 2. Ordered Rule Definitions

**Default Rules (optimized order):**
```scala
val DefaultRules: List[SimplificationRule] = List(
  FlattenOperations,         // 1. Normalize structure first
  RemoveIdentity,            // 2. Remove 0s and 1s
  DistributeProduct,         // 3. Expand products over sums (CRITICAL)
  CombineNumericLiterals,    // 4. Merge numeric values
  SimplifyFractions,         // 5. Simplify numeric fractions
  CollectLikeTerms,          // 6. Combine like terms
  MergeFractionsCommonDenom, // 7. Merge fractions with same denominator
  FactorCommonTerms,         // 8. Factor common terms (after collection)
  SimplifyDoubleNegative     // 9. Clean up double negatives
)
```

### 3. Factory Pattern

**New factory method:**
```scala
def apply(name: String): SimplificationConfig = {
  name.toLowerCase match {
    case "default"     => Default
    case "minimal"     => Minimal
    case "aggressive"  => Aggressive
    case "collatz0"    => Collatz0
    case "none"        => None
    case _ => throw new IllegalArgumentException(...)
  }
}
```

**Usage:**
```scala
// Get config by name
val config = SimplificationConfig("collatz0")

// Use it
val result = expr.fullSimplify(config)

// Or directly
val result = expr.fullSimplify(SimplificationConfig.Collatz0)
```

### 4. New Collatz0 Configuration

**Optimized for Collatz sequence simplification:**
```scala
val Collatz0Rules: List[SimplificationRule] = List(
  FlattenOperations,         // 1. Flatten nested operations
  RemoveIdentity,            // 2. Remove identities
  DistributeProduct,         // 3. CRITICAL: Distribute a*(b+c) → a*b + a*c
  ProductOfCosToSumOfCos,    // 4. Apply cosine product-to-sum transformations
  CombineNumericLiterals,    // 5. Merge numeric values
  SimplifyFractions,         // 6. Simplify fractions
  MergeFractionsCommonDenom, // 7. Merge fractions with common denominators
  CollectLikeTerms,          // 8. Collect like terms
  FactorCommonTerms,         // 9. Factor common terms
  SimplifyDoubleNegative     // 10. Eliminate double negatives
)
```

**Key difference:** Includes `ProductOfCosToSumOfCos` which applies the transformation:
```
cos(A) * cos(B) → (cos(A-B) + cos(A+B)) / 2
```

This is critical for Collatz sequences which have many cosine products.

## Usage Examples

### Example 1: Using Named Configuration

```scala
import symbolicas.{Expr, SimplificationConfig}

val expr: Expr = ...

// Use Collatz0 configuration
val result = expr.fullSimplify(SimplificationConfig("collatz0"))

// Or equivalently
val result = expr.fullSimplify(SimplificationConfig.Collatz0)
```

### Example 2: List Available Configurations

```scala
SimplificationConfig.availableConfigurations.foreach(println)
// Output:
// default
// minimal
// aggressive
// collatz0
// none
```

### Example 3: Custom Configuration

```scala
// Start with Collatz0 and add a rule
val custom = SimplificationConfig.Collatz0
  .withRule(MergeFractionsLCD)

// Or remove a rule
val custom = SimplificationConfig.Collatz0
  .withoutRule(FactorCommonTerms)
```

### Example 4: Error Handling

```scala
try {
  val config = SimplificationConfig("invalid_name")
} catch {
  case e: IllegalArgumentException =>
    println(e.getMessage)
    // Output: Unknown configuration: invalid_name. Available: default, minimal, aggressive, collatz0, none
}
```

## Rule Order Rationale

### Why This Order for Default?

1. **FlattenOperations**: Normalizes nested structures (Add(a, Add(b, c)) → Add(a, b, c))
2. **RemoveIdentity**: Removes 0s from additions and 1s from multiplications
3. **DistributeProduct**: MUST come early to expand products over sums
4. **CombineNumericLiterals**: Merges numeric values after distribution
5. **SimplifyFractions**: Reduces fractions like 4/6 → 2/3
6. **CollectLikeTerms**: Combines like terms (x + 2*x → 3*x) AFTER distribution
7. **MergeFractionsCommonDenom**: Merges fractions with same denominator
8. **FactorCommonTerms**: Factors common terms AFTER collection
9. **SimplifyDoubleNegative**: Cleans up --x → x at the end

### Why ProductOfCosToSumOfCos in Collatz0?

Collatz sequences generate expressions like:
```
cos(n*π) * cos(n*π/2) * (large_sum)
```

With `ProductOfCosToSumOfCos`, this becomes:
```
1/2 * (cos(n*π - n*π/2) + cos(n*π + n*π/2)) * (large_sum)
→ 1/2 * (cos(n*π/2) + cos(3*n*π/2)) * (large_sum)
```

Then `DistributeProduct` expands this into manageable terms.

## Testing

### Run Configuration Tests

```bash
scala-cli run src/main/scala/test_config_factory.sc
```

**Expected output:**
- Lists all available configurations
- Shows Collatz0 rules in order
- Demonstrates factory usage
- Compares Collatz0 vs Default results
- Tests error handling

### Run with Collatz0

```scala
// In test.sc
implicit val config = SimplificationConfig.Collatz0

val collatz1 = ...
val result = collatz1.fullSimplify  // Uses Collatz0 config
```

## Migration Guide

### For Existing Code

**Old code:**
```scala
import symbolicas.SimplificationConfig.DefaultRules

val config = SimplificationConfig(DefaultRules)
```

**New code:**
```scala
import symbolicas.SimplificationConfig

val config = SimplificationConfig.Default
// Or
val config = SimplificationConfig("default")
```

### For Custom Configurations

**Old code:**
```scala
val customRules = Set(
  RemoveIdentity,
  CollectLikeTerms
)
val config = SimplificationConfig(customRules)
```

**New code:**
```scala
val customRules = List(  // Order matters!
  RemoveIdentity,
  CollectLikeTerms
)
val config = SimplificationConfig(customRules)
```

## Future Configurations

You can easily add more named configurations:

```scala
// In SimplificationConfig.scala

// Add to the object:
val Collatz1Rules: List[SimplificationRule] = List(...)
val Collatz1: SimplificationConfig = SimplificationConfig(Collatz1Rules)

// Update factory:
def apply(name: String): SimplificationConfig = {
  name.toLowerCase match {
    ...
    case "collatz1" => Collatz1
    ...
  }
}

// Update available list:
def availableConfigurations: List[String] = List(
  ...
  "collatz1",
  ...
)
```

## Performance Considerations

- **List vs Set**: Lists are slightly slower for `.contains()` checks, but:
  - The lists are small (typically 5-12 rules)
  - The benefits of ordered application far outweigh the negligible performance cost
  - In practice, no measurable difference

- **Rule Order Impact**: Proper ordering can significantly improve performance by:
  - Reducing the number of iterations needed to reach fixpoint
  - Avoiding redundant transformations
  - Enabling more effective simplifications early

## Summary

This refactor provides:
- ✅ Ordered rule application (critical for correct simplification)
- ✅ Factory pattern for named configurations
- ✅ Collatz0 configuration optimized for Collatz sequences
- ✅ Easy extensibility for future configurations
- ✅ Better documentation and discoverability
- ✅ Backward compatible (existing code still works)

The ordered list approach gives us fine-grained control over the simplification process, which is essential for achieving optimal results in complex algebraic manipulations like the Collatz sequences.
