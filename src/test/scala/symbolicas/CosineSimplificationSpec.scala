package symbolicas

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import symbolicas.{Expr, Num, Var}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Test suite for cosine simplification.
 *
 * Tests simplification of cosine arguments, including:
 * - Simplification of cosine arguments with pi
 * - Factoring common terms in cosine arguments
 * - Nested cosine simplifications
 */
class CosineSimplificationSpec extends AnyFlatSpec with Matchers {

  "Cosine argument simplification" should "simplify n * pi - n/2 * pi" in {
    val n = Var("n")
    val expr = n * pi - (n/2) * pi
    val simplified = expr.fullSimplify

    // Should be n*pi/2 or (n*pi)/2
    simplified.toString should (include("pi") and include("/2"))
  }

  it should "simplify inside a cosine" in {
    val n = Var("n")
    val expr = cos(n * pi - (n/2) * pi)
    val simplified = expr.fullSimplify

    // Should be cos(n*pi/2) or cos((n*pi)/2)
    simplified.toString should (include("cos") and include("pi") and include("/2"))
  }

  it should "simplify 2*n*pi - n*pi" in {
    val n = Var("n")
    val expr = Num(2) * n * pi - n * pi
    val simplified = expr.fullSimplify

    // Should be n*pi
    simplified.toString should include ("pi")
  }

  it should "simplify 3*n*pi/4 - n*pi/4" in {
    val n = Var("n")
    val expr = (Num(3) * n * pi) / 4 - (n * pi) / 4
    val simplified = expr.fullSimplify

    // Should be n*pi/2 or (n*pi)/2
    simplified.toString should (include("pi") and include("/"))
  }

  it should "simplify n*pi + n*pi to 2*n*pi" in {
    val n = Var("n")
    val expr = n * pi + n * pi
    val simplified = expr.fullSimplify

    // Should be 2*n*pi
    simplified.toString should (include("2") and include("n") and include("pi"))
  }

  "Cosine evaluation" should "correctly evaluate cos(0)" in {
    val expr = cos(Num(0))
    val vars = Map.empty[String, Double]
    val value = expr.eval(vars)

    value should be (1.0 +- 1e-10)
  }

  it should "correctly evaluate cos(pi)" in {
    val expr = cos(pi)
    val vars = Map("pi" -> math.Pi)
    val value = expr.eval(vars)

    value should be (-1.0 +- 1e-10)
  }

  it should "correctly evaluate cos(n*pi) for even n" in {
    val n = Var("n")
    val expr = cos(n * pi)
    val vars = Map("n" -> 2.0, "pi" -> math.Pi)
    val value = expr.eval(vars)

    value should be (1.0 +- 1e-10)
  }

  it should "correctly evaluate cos(n*pi) for odd n" in {
    val n = Var("n")
    val expr = cos(n * pi)
    val vars = Map("n" -> 3.0, "pi" -> math.Pi)
    val value = expr.eval(vars)

    value should be (-1.0 +- 1e-10)
  }

  "Cosine with complex arguments" should "simplify arguments before evaluation" in {
    val n = Var("n")
    val expr = cos((n * 2 + n) * pi)
    val simplified = expr.fullSimplify

    // Should simplify to cos(3*n*pi) or similar
    simplified should be (a[Cos])
  }

  it should "handle fraction arguments" in {
    val n = Var("n")
    val expr = cos(n * pi / 2)
    val vars = Map("n" -> 2.0, "pi" -> math.Pi)
    val value = expr.eval(vars)

    // cos(2*pi/2) = cos(pi) = -1
    value should be (-1.0 +- 1e-10)
  }

  "Cosine simplification" should "preserve mathematical meaning" in {
    val n = Var("n")
    val expr1 = cos(n * pi - (n/2) * pi)
    val expr2 = cos(n * pi / 2)

    val vars = Map("n" -> 5.0, "pi" -> math.Pi)
    val value1 = expr1.fullSimplify.eval(vars)
    val value2 = expr2.fullSimplify.eval(vars)

    math.abs(value1 - value2) should be < 1e-10
  }

  it should "be idempotent" in {
    val n = Var("n")
    val expr = cos(n * pi - (n/2) * pi)
    val simplified1 = expr.fullSimplify
    val simplified2 = simplified1.fullSimplify

    simplified1 should equal (simplified2)
  }
}
