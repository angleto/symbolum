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
 *
 * @param enabledRules Set of enabled simplification rules
 */
case class SimplificationConfig(
  enabledRules: Set[SimplificationRule] = SimplificationConfig.DefaultRules
) {

  /** Check if a rule is enabled */
  def isEnabled(rule: SimplificationRule): Boolean = enabledRules.contains(rule)

  /** Create a new config with an additional rule enabled */
  def withRule(rule: SimplificationRule): SimplificationConfig =
    copy(enabledRules = enabledRules + rule)

  /** Create a new config with a rule disabled */
  def withoutRule(rule: SimplificationRule): SimplificationConfig =
    copy(enabledRules = enabledRules - rule)

  /** Create a new config with multiple rules enabled */
  def withRules(rules: SimplificationRule*): SimplificationConfig =
    copy(enabledRules = enabledRules ++ rules)

  /** Create a new config with multiple rules disabled */
  def withoutRules(rules: SimplificationRule*): SimplificationConfig =
    copy(enabledRules = enabledRules -- rules)
}

object SimplificationConfig {

  /** Default simplification rules (safe, commonly-desired simplifications) */
  val DefaultRules: Set[SimplificationRule] = Set(
    RemoveIdentity,
    FlattenOperations,
    CombineNumericLiterals,
    FactorCommonTerms,
    MergeFractionsCommonDenom,
    SimplifyDoubleNegative,
    SimplifyFractions,
    CollectLikeTerms,
    DistributeProduct  // CRITICAL: Must distribute a*(b+c) → a*b + a*c
  )

  /** All available rules */
  val AllRules: Set[SimplificationRule] = SimplificationRule.values.toSet

  /** Minimal rules (only essential simplifications) */
  val MinimalRules: Set[SimplificationRule] = Set(
    RemoveIdentity,
    CombineNumericLiterals,
    SimplifyFractions
  )

  /** Aggressive rules (all simplifications including automatic fraction merging) */
  val AggressiveRules: Set[SimplificationRule] = AllRules

  /** Default configuration */
  val Default: SimplificationConfig = SimplificationConfig(DefaultRules)

  /** Minimal configuration */
  val Minimal: SimplificationConfig = SimplificationConfig(MinimalRules)

  /** Aggressive configuration */
  val Aggressive: SimplificationConfig = SimplificationConfig(AggressiveRules)

  /** No simplifications (identity) */
  val None: SimplificationConfig = SimplificationConfig(Set.empty)
}
