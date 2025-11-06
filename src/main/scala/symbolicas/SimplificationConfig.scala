package symbolicas

/**
 * Simplification rules that can be selectively enabled/disabled.
 *
 * This allows fine-grained control over which algebraic transformations
 * are applied during simplification.
 */
object SimplificationRule extends Enumeration {
  type SimplificationRule = Value

  /** Remove identity elements (0 for addition, 1 for multiplication) */
  val RemoveIdentity = Value("removeIdentity")

  /** Flatten nested operations: Add(a, Add(b, c)) → Add(a, b, c) */
  val FlattenOperations = Value("flattenOperations")

  /** Combine numeric literals: 2 + 3 → 5 */
  val CombineNumericLiterals = Value("combineNumericLiterals")

  /** Factor common terms: a*b + a*c → a*(b + c) */
  val FactorCommonTerms = Value("factorCommonTerms")

  /** Merge fractions with common denominators: a/b + c/b → (a+c)/b */
  val MergeFractionsCommonDenom = Value("mergeFractionsCommonDenom")

  /** Merge all fractions to LCD: 1/2 + 1/3 → 5/6 */
  val MergeFractionsLCD = Value("mergeFractionsLCD")

  /** Distribute products over sums: a*(b + c) → a*b + a*c */
  val DistributeProduct = Value("distributeProduct")

  /** Simplify double negatives: --x → x */
  val SimplifyDoubleNegative = Value("simplifyDoubleNegative")

  /** Apply product-to-sum for cosines: cos(A)*cos(B) → (cos(A-B)+cos(A+B))/2 */
  val ProductOfCosToSumOfCos = Value("productOfCosToSumOfCos")

  /** Cancel common factors: (a*b)/(a*c) → b/c */
  val CancelCommonFactors = Value("cancelCommonFactors")

  /** Collect like terms in sums: x + 2*x → 3*x */
  val CollectLikeTerms = Value("collectLikeTerms")

  /** Simplify fractions: 4/6 → 2/3 */
  val SimplifyFractions = Value("simplifyFractions")
}

import SimplificationRule._

/**
 * Configuration for simplification operations.
 *
 * Controls which algebraic rules are applied during simplification.
 * Rules are applied in the order specified in the list.
 *
 * @param enabledRules Ordered list of enabled simplification rules
 */
case class SimplificationConfig(
  enabledRules: List[SimplificationRule] = SimplificationConfig.DefaultRules
) {

  /** Check if a rule is enabled */
  def isEnabled(rule: SimplificationRule): Boolean = enabledRules.contains(rule)

  /** Create a new config with an additional rule enabled (appended to end) */
  def withRule(rule: SimplificationRule): SimplificationConfig =
    copy(enabledRules = enabledRules :+ rule)

  /** Create a new config with a rule disabled */
  def withoutRule(rule: SimplificationRule): SimplificationConfig =
    copy(enabledRules = enabledRules.filterNot(_ == rule))

  /** Create a new config with multiple rules enabled (appended to end) */
  def withRules(rules: SimplificationRule*): SimplificationConfig =
    copy(enabledRules = enabledRules ++ rules)

  /** Create a new config with multiple rules disabled */
  def withoutRules(rules: SimplificationRule*): SimplificationConfig =
    copy(enabledRules = enabledRules.filterNot(rules.contains))
}

object SimplificationConfig {

  /**
   * Default simplification rules (safe, commonly-desired simplifications).
   * Rules are applied in this order - ORDER MATTERS!
   */
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

  /** All available rules */
  val AllRules: List[SimplificationRule] = SimplificationRule.values.toList

  /** Minimal rules (only essential simplifications) */
  val MinimalRules: List[SimplificationRule] = List(
    RemoveIdentity,
    CombineNumericLiterals,
    SimplifyFractions
  )

  /**
   * Collatz0 configuration - optimized for Collatz sequence simplification.
   * Uses aggressive distribution and trigonometric simplifications.
   */
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

  /** Aggressive rules (all simplifications) */
  val AggressiveRules: List[SimplificationRule] = AllRules

  /** Default configuration */
  val Default: SimplificationConfig = SimplificationConfig(DefaultRules)

  /** Minimal configuration */
  val Minimal: SimplificationConfig = SimplificationConfig(MinimalRules)

  /** Aggressive configuration */
  val Aggressive: SimplificationConfig = SimplificationConfig(AggressiveRules)

  /** Collatz0 configuration - optimized for Collatz sequences */
  val Collatz0: SimplificationConfig = SimplificationConfig(Collatz0Rules)

  /** No simplifications (identity) */
  val None: SimplificationConfig = SimplificationConfig(List.empty)

  /**
   * Factory method to get a configuration by name.
   *
   * @param name Configuration name (case-insensitive)
   * @return SimplificationConfig for the named configuration
   * @throws IllegalArgumentException if configuration name is unknown
   */
  def apply(name: String): SimplificationConfig = {
    name.toLowerCase match {
      case "default"     => Default
      case "minimal"     => Minimal
      case "aggressive"  => Aggressive
      case "collatz0"    => Collatz0
      case "none"        => None
      case _ => throw new IllegalArgumentException(
        s"Unknown configuration: $name. " +
        s"Available: default, minimal, aggressive, collatz0, none"
      )
    }
  }

  /**
   * Get a list of all available configuration names.
   */
  def availableConfigurations: List[String] = List(
    "default",
    "minimal",
    "aggressive",
    "collatz0",
    "none"
  )
}
