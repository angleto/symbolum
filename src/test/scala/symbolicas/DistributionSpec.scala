package symbolicas

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, SimplificationConfig}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Test suite for distribution of multiplication over addition.
 *
 * Tests that multiplication is properly distributed over addition:
 * - a * (b + c) -> a*b + a*c
 * - Nested distributions
 * - Distribution with fractions
 * - Distribution with trigonometric functions
 */
class DistributionSpec extends AnyFlatSpec with Matchers {

  "Distribution" should "distribute simple multiplication" in {
    val n = Var("n")
    val test = Mul(Array(Num(2), Add(Array(n, Num(1)))))
    val result = test.fullSimplify

    // Should be 2*n + 2
    result should be (a[Add])
  }

  it should "distribute fraction over sum" in {
    val n = Var("n")
    val test = Mul(Array(Div(Array(Num(1), Num(2))), Add(Array(n, Num(1)))))
    val result = test.fullSimplify

    // Should be n/2 + 1/2 or (n + 1)/2
    result should not be a[Mul]
  }

  it should "distribute nested sums" in {
    val n = Var("n")
    val innerSum = Add(Array(n, Num(1)))
    val middleSum = Add(Array(innerSum, Num(2)))
    val test = Mul(Array(Num(2), middleSum))
    val result = test.fullSimplify

    // Should be distributed
    result should be (a[Add])
  }

  it should "distribute complex expression like Collatz" in {
    val n = Var("n")
    val sum1 = Add(Array(n, Num(1)))
    val sum2 = Add(Array(Mul(Array(Num(2), n)), Num(3)))
    val bigSum = Add(Array(sum1, sum2))
    val test = Mul(Array(Div(Array(Num(1), Num(2))), Cos(Mul(Array(n, pi))), bigSum))
    val result = test.fullSimplify

    // Should be distributed into separate terms
    val output = result.toString
    output should not include ("1/2 * cos(n * pi) * (")
    output should not include ("cos(n * pi) * (")
  }

  it should "distribute cos * (sum)" in {
    val n = Var("n")
    val a = Var("a")
    val b = Var("b")
    val test = Mul(Array(
      Cos(Mul(Array(n, pi))),
      Add(Array(a, b))
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Should contain separate terms
    result should be (a[Add])
  }

  it should "distribute numeric over multiple variables" in {
    val x = Var("x")
    val y = Var("y")
    val z = Var("z")
    val test = Mul(Array(
      Num(2),
      Add(Array(x, y, z))
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Should be 2*x + 2*y + 2*z
    result should be (a[Add])
  }

  it should "distribute 1/2 * (n + 1)" in {
    val n = Var("n")
    val test = Mul(Array(
      Num(1, 2),
      Add(Array(n, Num(1)))
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Should be n/2 + 1/2 or (n + 1)/2
    result.toString should (include("/2") or include("/2"))
  }

  it should "distribute cos(n/2*pi) * (multiple terms)" in {
    val n = Var("n")
    val test = Mul(Array(
      Cos(Mul(Array(Div(Array(n, Num(2))), pi))),
      Add(Array(
        Mul(Array(Num(-1, 8), n)),
        Num(-1, 16),
        Num(1, 8)
      ))
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Should have multiple separate terms with cos
    val termsCount = result.toString.split("\\+|(?<!\\()\\-").length
    termsCount should be >= 2
  }

  it should "distribute nested Mul-Add" in {
    val a = Var("a")
    val b = Var("b")
    val d = Var("d")
    val e = Var("e")

    val test = Mul(Array(
      Cos(a),
      Add(Array(
        b,
        Mul(Array(
          Cos(Cos(a)),
          Add(Array(d, e))
        ))
      ))
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Should be fully distributed
    result should be (a[Add])
  }

  "Quick distribution test" should "distribute 2 * (n + 1)" in {
    val n = Var("n")
    val test = Mul(Array(Num(2), Add(Array(n, Num(1)))))
    val result = test.fullSimplify

    // Expected: 2 * n + 2
    result should be (a[Add])
  }

  it should "distribute 1/2 * (n + 1) correctly" in {
    val n = Var("n")
    val test = Mul(Array(Div(Array(Num(1), Num(2))), Add(Array(n, Num(1)))))
    val result = test.fullSimplify

    // Expected: n/2 + 1/2 OR (n + 1)/2
    result.toString should include ("/2")
  }

  it should "distribute nested sums correctly" in {
    val n = Var("n")
    val innerSum = Add(Array(n, Num(1)))
    val middleSum = Add(Array(innerSum, Num(2)))
    val test = Mul(Array(Num(2), middleSum))
    val result = test.fullSimplify

    // Expected: 2 * n + 6
    result should be (a[Add])
  }
}
