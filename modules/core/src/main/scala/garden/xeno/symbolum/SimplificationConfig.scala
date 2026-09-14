package garden.xeno.symbolum

import garden.xeno.symbolum.NumericConstants._

/**
 * The algebraic transformations the simplifier may apply.
 *
 * A rule switches an ''algebraic'' rewrite on or off. It does not switch off ''normalisation'':
 * reducing a numeric literal to lowest terms, flattening nested sums and products, rewriting
 * `Sub` as a sum and `Neg` as a `-1` coefficient, and ordering the operands of a commutative node
 * always happen, because they are what makes two spellings of the same expression one object.
 * Simplification that cannot rely on that is simplification that misses matches, which is the
 * defect this design removes.
 *
 * Flattening and negation had been switches here. Neither had a coherent off position. Every
 * other rule is stated over the flattened form, so with flattening off the simplifier went on
 * reassociating through fractions while leaving nested products alone, and each pass exposed a
 * little more than the last. With negation off a `Neg` node survived as something opaque, and
 * `-2 * 2` stopped folding at all because one of its factors was no longer a number. A switch
 * whose off position has no meaning is worse than no switch, so both are now normalisation:
 * `-(-x)` collapses because `(-1) * (-1)` is `1`, under the rule that folds numeric literals.
 */
enum SimplificationRule {

  /** Remove identity elements: `x + 0` becomes `x`, `x * 1` becomes `x`. */
  case RemoveIdentity

  /** Fold numeric literals together: `2 + 3` becomes `5`. */
  case CombineNumericLiterals

  /**
   * Factor a common factor out of a sum: `a*b + a*c` becomes `a*(b + c)`.
   *
   * This is the exact inverse of [[DistributeProduct]], so the two cannot both run: they would
   * undo each other forever. Where both are enabled, distribution wins and this rule is inert.
   */
  case FactorCommonTerms

  /** Put a sum of fractions over their least common denominator: `n/2 + 1/4` becomes `(2n + 1)/4`. */
  case MergeFractionsCommonDenom

  /** Distribute a product over a sum: `a*(b + c)` becomes `a*b + a*c`. */
  case DistributeProduct

  /** Product-to-sum for cosines: `cos(A)*cos(B)` becomes `(cos(A-B) + cos(A+B))/2`. */
  case ProductOfCosToSumOfCos

  /** Cancel a factor shared by both sides of a quotient: `(a*b)/(a*c)` becomes `b/c`. */
  case CancelCommonFactors

  /** Collect like terms in a sum: `x + 2*x` becomes `3*x`. */
  case CollectLikeTerms

  /** Reduce the numeric content of a quotient: `(2*n)/4` becomes `n/2`. */
  case SimplifyFractions

  /** Split a logarithm over its argument: `log(a*b)` becomes `log(a) + log(b)`. */
  case ExpandLogarithms

  /** Split an exponential over its argument: `exp(a + b)` becomes `exp(a) * exp(b)`. */
  case ExpandExponentials
}

import SimplificationRule._

/**
 * Which simplification rules are in force, and how far expansion may go.
 *
 * @param enabledRules      the rules to apply; membership is what matters, not position
 * @param maxExpansionTerms ceiling on the number of terms a single distribution may produce,
 *                          which bounds the combinatorial blow-up of `(a+b+c)*(d+e+f)`
 */
case class SimplificationConfig(
  enabledRules: List[SimplificationRule] = SimplificationConfig.DefaultRules,
  maxExpansionTerms: Int = DEFAULT_MAX_EXPANSION_TERMS
) {

  require(maxExpansionTerms > 0, s"maxExpansionTerms must be positive, got $maxExpansionTerms")

  /**
   * Rules as a set.
   *
   * `isEnabled` is called once per node per rule on every traversal, so the linear scan of a
   * `List` showed up directly in simplification time on Collatz-sized trees.
   */
  private lazy val ruleSet: Set[SimplificationRule] = enabledRules.toSet

  /** True if `rule` is in force. */
  def isEnabled(rule: SimplificationRule): Boolean = ruleSet.contains(rule)

  /** This configuration with `rule` additionally enabled. */
  def withRule(rule: SimplificationRule): SimplificationConfig =
    if (isEnabled(rule)) this else copy(enabledRules = enabledRules :+ rule)

  /** This configuration with `rule` disabled. */
  def withoutRule(rule: SimplificationRule): SimplificationConfig =
    copy(enabledRules = enabledRules.filterNot(_ == rule))

  /** This configuration with all of `rules` additionally enabled. */
  def withRules(rules: SimplificationRule*): SimplificationConfig =
    rules.foldLeft(this)(_ withRule _)

  /** This configuration with all of `rules` disabled. */
  def withoutRules(rules: SimplificationRule*): SimplificationConfig =
    copy(enabledRules = enabledRules.filterNot(rules.contains))
}

object SimplificationConfig {

  /**
   * The safe, commonly wanted simplifications.
   *
   * [[SimplificationRule.FactorCommonTerms]] appears here for callers who build on this list with
   * `withoutRule(DistributeProduct)`; while distribution is enabled it is inert, for the reason
   * given on the rule itself.
   */
  val DefaultRules: List[SimplificationRule] = List(
    RemoveIdentity,
    DistributeProduct,
    CombineNumericLiterals,
    SimplifyFractions,
    CollectLikeTerms,
    MergeFractionsCommonDenom,
    FactorCommonTerms
  )

  /** Every rule the simplifier knows. */
  val AllRules: List[SimplificationRule] = SimplificationRule.values.toList

  /** Only the simplifications no caller would want suppressed. */
  val MinimalRules: List[SimplificationRule] = List(
    RemoveIdentity,
    CombineNumericLiterals,
    SimplifyFractions
  )

  /** Tuned for Collatz sequences: distribution plus the cosine product-to-sum identity. */
  val Collatz0Rules: List[SimplificationRule] = List(
    RemoveIdentity,
    DistributeProduct,
    ProductOfCosToSumOfCos,
    CombineNumericLiterals,
    SimplifyFractions,
    MergeFractionsCommonDenom,
    CollectLikeTerms,
    FactorCommonTerms
  )

  /** Every rule enabled. */
  val AggressiveRules: List[SimplificationRule] = AllRules

  val Default: SimplificationConfig = SimplificationConfig(DefaultRules)
  val Minimal: SimplificationConfig = SimplificationConfig(MinimalRules)
  val Aggressive: SimplificationConfig = SimplificationConfig(AggressiveRules)
  val Collatz0: SimplificationConfig = SimplificationConfig(Collatz0Rules)

  /** No algebraic rewriting at all; normalisation still applies. */
  val None: SimplificationConfig = SimplificationConfig(List.empty)

  private val byName: Map[String, SimplificationConfig] = Map(
    "default" -> Default,
    "minimal" -> Minimal,
    "aggressive" -> Aggressive,
    "collatz0" -> Collatz0,
    "none" -> None
  )

  /**
   * Look a configuration up by name, case-insensitively.
   *
   * @throws IllegalArgumentException if no configuration carries that name
   */
  def apply(name: String): SimplificationConfig =
    byName.getOrElse(
      name.toLowerCase,
      throw new IllegalArgumentException(
        s"Unknown configuration: $name. Available: ${availableConfigurations.mkString(", ")}"
      )
    )

  /** Every name [[apply(String)*]] accepts. */
  def availableConfigurations: List[String] = byName.keys.toList.sorted
}
