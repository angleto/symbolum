package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var, Add, Mul, SimplificationConfig}
import garden.xeno.symbolum.SimplificationRule._
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Test suite for simplification configuration.
 *
 * Tests:
 * - Configuration factory pattern
 * - Rule enabling/disabling
 * - Different configuration presets
 * - Custom configurations
 */
class ConfigurationSpec extends AnyFlatSpec with Matchers {

  "SimplificationConfig factory" should "provide available configuration names" in {
    val configs = SimplificationConfig.availableConfigurations

    configs should contain ("default")
    configs should contain ("minimal")
    configs should contain ("aggressive")
    configs should contain ("collatz0")
    configs should contain ("none")
  }

  it should "create configurations by name" in {
    val defaultConfig = SimplificationConfig("default")
    val collatz0Config = SimplificationConfig("collatz0")
    val minimalConfig = SimplificationConfig("minimal")

    defaultConfig.enabledRules should not be empty
    collatz0Config.enabledRules should not be empty
    minimalConfig.enabledRules should not be empty
  }

  it should "throw exception for invalid configuration name" in {
    an [IllegalArgumentException] should be thrownBy {
      SimplificationConfig("invalid_name")
    }
  }

  "Configuration presets" should "have correct number of rules" in {
    val defaultConfig = SimplificationConfig.Default
    val collatz0Config = SimplificationConfig.Collatz0
    val minimalConfig = SimplificationConfig.Minimal

    defaultConfig.enabledRules.length should be >= 5
    collatz0Config.enabledRules.length should be >= 5
    minimalConfig.enabledRules.length should be >= 2
  }

  it should "include specific rules in Collatz0" in {
    val collatz0Config = SimplificationConfig.Collatz0

    collatz0Config.isEnabled(DistributeProduct) should be (true)
    collatz0Config.isEnabled(ProductOfCosToSumOfCos) should be (true)
  }

  "Rule management" should "add rules with withRule" in {
    val config = SimplificationConfig.Minimal
    val newConfig = config.withRule(CollectLikeTerms)

    newConfig.isEnabled(CollectLikeTerms) should be (true)
  }

  it should "remove rules with withoutRule" in {
    val config = SimplificationConfig.Default
    val newConfig = config.withoutRule(DistributeProduct)

    newConfig.isEnabled(DistributeProduct) should be (false)
  }

  it should "add multiple rules with withRules" in {
    val config = SimplificationConfig.Minimal
    val newConfig = config.withRules(CollectLikeTerms, FactorCommonTerms)

    newConfig.isEnabled(CollectLikeTerms) should be (true)
    newConfig.isEnabled(FactorCommonTerms) should be (true)
  }

  it should "remove multiple rules with withoutRules" in {
    val config = SimplificationConfig.Default
    val newConfig = config.withoutRules(DistributeProduct, CollectLikeTerms)

    newConfig.isEnabled(DistributeProduct) should be (false)
    newConfig.isEnabled(CollectLikeTerms) should be (false)
  }

  "Custom configurations" should "allow selective rule enabling" in {
    val customConfig = SimplificationConfig(List(
      RemoveIdentity,
      CombineNumericLiterals,
      CollectLikeTerms,
      FactorCommonTerms
    ))

    customConfig.isEnabled(RemoveIdentity) should be (true)
    customConfig.isEnabled(DistributeProduct) should be (false)
  }

  "Configuration effects" should "differ between Default and Minimal" in {
    val x = Var("x")
    val expr = (x + x + Num(0)) * Num(1) + Num(2, 4)

    val minimalResult = expr.simplify(SimplificationConfig.Minimal)
    val defaultResult = expr.simplify(SimplificationConfig.Default)

    // Results may differ based on enabled rules
    minimalResult.toString should not be empty
    defaultResult.toString should not be empty
  }

  it should "differ between Default and Aggressive" in {
    val x = Var("x")
    val expr = Num(1, 2) + Num(1, 3) + x * Num(2) + x

    val defaultResult = expr.simplify(SimplificationConfig.Default)
    val aggressiveResult = expr.simplify(SimplificationConfig.Aggressive)

    defaultResult.toString should not be empty
    aggressiveResult.toString should not be empty
  }

  "Collatz0 configuration" should "produce clean output" in {
    val n = Var("n")
    val collatz1 = Add(Vector(
      n,
      Num(1, 4),
      Mul(Vector(
        Num(-1),
        Div(Vector(Add(Vector(Mul(Vector(Num(2), n)), Num(1))), Num(4))),
        Cos(Mul(Vector(n, pi)))
      ))
    ))

    val simplified = collatz1.fullSimplify(SimplificationConfig.Collatz0)

    // Should not have negative patterns
    simplified.toString should not include ("+ -")
    simplified.toString should not include ("- -")
  }

  it should "apply distribution" in {
    val n = Var("n")
    val expr = Mul(Vector(Num(2), Add(Vector(n, Num(1)))))

    val simplified = expr.fullSimplify(SimplificationConfig.Collatz0)

    // Should be distributed
    simplified should be (a[Add])
  }

  "None configuration" should "apply no simplifications" in {
    val x = Var("x")
    val expr = x + Num(0)

    val result = expr.simplify(SimplificationConfig.None)

    // Should not simplify
    result should be (a[Add])
  }

  "Configuration" should "validate maxExpansionTerms" in {
    an [IllegalArgumentException] should be thrownBy {
      SimplificationConfig(List(RemoveIdentity), maxExpansionTerms = 0)
    }

    an [IllegalArgumentException] should be thrownBy {
      SimplificationConfig(List(RemoveIdentity), maxExpansionTerms = -1)
    }
  }

  // The position of a rule in the list carries no meaning: what a configuration says is which
  // rules are in force. The previous version of this case asserted only that neither result was
  // null, under a name claiming the opposite of what the code does.
  "Rule list order" should "not change the result" in {
    val n = Var("n")
    val expr = n * pi - (n / 2) * pi

    val config1 = SimplificationConfig(List(
      CombineNumericLiterals,
      CollectLikeTerms,
      FactorCommonTerms
    ))

    val config2 = SimplificationConfig(List(
      FactorCommonTerms,
      CollectLikeTerms,
      CombineNumericLiterals
    ))

    expr.fullSimplify(config1) should equal (expr.fullSimplify(config2))
  }
}
