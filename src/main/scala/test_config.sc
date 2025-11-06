import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.{SimplificationConfig, SimplificationRule}
import symbolicas.SimplificationRule._
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

println("=" * 70)
println("SIMPLIFICATION CONFIGURATION TESTS")
println("=" * 70)
println()

val n: Expr = Var("n")
val x: Expr = Var("x")

// Test 1: Collect like terms
println("Test 1: Collect like terms (x + 2*x)")
val expr1 = x + Num(2) * x
println(s"  Expression: $expr1")
println(s"  Default: ${expr1.fullSimplify}")
val config1 = SimplificationConfig.Default.withRule(CollectLikeTerms)
println(s"  With CollectLikeTerms: ${expr1.fullSimplify(config1)}")
println()

// Test 2: n*pi - n/2*pi should simplify
println("Test 2: n*pi - (n/2)*pi (should factor to n*pi*(1 - 1/2) = n*pi/2)")
val expr2 = n * pi - (n / 2) * pi
println(s"  Expression: $expr2")
println(s"  Default: ${expr2.fullSimplify}")
val config2 = SimplificationConfig.Default.withRule(FactorCommonTerms)
println(s"  With FactorCommonTerms: ${expr2.fullSimplify(config2)}")
println()

// Test 3: Fraction merging control
println("Test 3: 1/2 + 1/3 (fraction merging control)")
val expr3 = Num(1, 2) + Num(1, 3)
println(s"  Expression: $expr3")
println(s"  Default (no LCD merge): ${expr3.simplify}")
val configLCD = SimplificationConfig.Default.withRule(MergeFractionsLCD)
println(s"  With MergeFractionsLCD: ${expr3.simplify(configLCD)}")
println()

// Test 4: Product-to-sum for cosines
println("Test 4: cos(x) * cos(y) (product-to-sum)")
val y: Expr = Var("y")
val expr4 = cos(x) * cos(y)
println(s"  Expression: $expr4")
val configNoCos = SimplificationConfig.Default.withoutRule(ProductOfCosToSumOfCos)
println(s"  Without ProductOfCosToSumOfCos: ${expr4.expand(configNoCos)}")
val configCos = SimplificationConfig.Default.withRule(ProductOfCosToSumOfCos)
println(s"  With ProductOfCosToSumOfCos: ${expr4.expand(configCos)}")
println()

// Test 5: Inside cosine simplification
println("Test 5: cos(n*pi - n/2*pi) should simplify argument")
val expr5 = cos(n * pi - (n / 2) * pi)
println(s"  Expression: $expr5")
println(s"  Default: ${expr5.fullSimplify}")
val config5 = config2  // With factoring
println(s"  With FactorCommonTerms: ${expr5.fullSimplify(config5)}")
println()

// Test 6: Distribute product control
println("Test 6: 2*(x + y) distribution control")
val expr6 = Num(2) * (x + y)
println(s"  Expression: $expr6")
val configNoDist = SimplificationConfig.Default.withoutRule(DistributeProduct)
println(s"  Without DistributeProduct: ${expr6.expand(configNoDist)}")
val configDist = SimplificationConfig.Default.withRule(DistributeProduct)
println(s"  With DistributeProduct: ${expr6.expand(configDist)}")
println()

// Test 7: Minimal config (bare essentials only)
println("Test 7: Minimal configuration")
val expr7 = (x + x + Num(0)) * Num(1) + Num(2, 4)
println(s"  Expression: $expr7")
println(s"  Minimal config: ${expr7.simplify(SimplificationConfig.Minimal)}")
println(s"  Default config: ${expr7.simplify(SimplificationConfig.Default)}")
println()

// Test 8: Aggressive config (all rules)
println("Test 8: Aggressive configuration")
val expr8 = Num(1, 2) + Num(1, 3) + x * Num(2) + x
println(s"  Expression: $expr8")
println(s"  Default: ${expr8.simplify(SimplificationConfig.Default)}")
println(s"  Aggressive: ${expr8.simplify(SimplificationConfig.Aggressive)}")
println()

println("=" * 70)
println("CUSTOM CONFIG EXAMPLE")
println("=" * 70)

// Create a custom configuration
val customConfig = SimplificationConfig(Set(
  RemoveIdentity,
  FlattenOperations,
  CombineNumericLiterals,
  CollectLikeTerms,
  FactorCommonTerms
))

val expr9 = n * pi - (n / 2) * pi + Num(1) + Num(2)
println(s"Expression: $expr9")
println(s"Custom config result: ${expr9.fullSimplify(customConfig)}")
println()

println("=" * 70)
println("TESTS COMPLETE")
println("=" * 70)
