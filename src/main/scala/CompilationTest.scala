// Simple compilation test for symbolicas v2.0
package symbolicas

object CompilationTest {
  def main(args: Array[String]): Unit = {
    import symbolicas.{Expr, Num, Var, Add, SimplificationConfig}
    import symbolicas.SimplificationRule._
    import symbolicas.Dsl._

    println("Testing compilation...")

    // Test 1: Basic expression
    val x: Expr = Var("x")
    val n: Expr = Var("n")

    // Test 2: Create expression with DSL
    val expr1 = x + Num(2) * x
    println(s"Expression: $expr1")

    // Test 3: Default simplification
    val simple1 = expr1.simplify
    println(s"Default simplify: $simple1")

    // Test 4: Custom configuration
    val config = SimplificationConfig.Default.withRule(CollectLikeTerms)
    val simple2 = expr1.simplify(config)
    println(s"With CollectLikeTerms: $simple2")

    // Test 5: Cosine simplification
    val expr2 = cos(n*pi - (n/Num(2))*pi)
    val config2 = SimplificationConfig.Default.withRule(FactorCommonTerms)
    val simple3 = expr2.fullSimplify(config2)
    println(s"Cosine simplified: $simple3")

    println("Compilation test passed!")
  }
}
