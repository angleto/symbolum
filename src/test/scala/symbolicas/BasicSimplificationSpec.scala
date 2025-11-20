package symbolicas

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Test suite for basic simplification operations.
 *
 * Tests basic simplification rules including:
 * - Double negation elimination
 * - Addition with negatives
 * - Nested operation flattening
 * - Basic fraction operations
 */
class BasicSimplificationSpec extends AnyFlatSpec with Matchers {

  "Simplification" should "eliminate double negation" in {
    val x = Var("x")
    val test = Neg(Neg(x))
    val simplified = test.simplify

    simplified should equal (x)
  }

  it should "handle addition with negative correctly" in {
    val x = Var("x")
    val y = Var("y")
    val test = Add(Array(x, Neg(y)))
    val simplified = test.simplify

    // Should be x - y, not x + (-y)
    simplified.toString should not include ("+ -")
  }

  it should "flatten nested additions" in {
    val x = Var("x")
    val y = Var("y")
    val test = Add(Array(x, Add(Array(y, Num(5)))))
    val simplified = test.simplify

    // Should be flattened
    simplified should be (a[Add])
  }

  it should "merge fractions with same denominator" in {
    val test = Add(Array(Num(1, 4), Num(1, 4)))
    val simplified = test.simplify

    simplified should equal (Num(1, 2))
  }

  it should "handle negative fractions" in {
    val test = Add(Array(Num(3, 4), Num(-1, 4)))
    val simplified = test.simplify

    simplified should equal (Num(1, 2))
  }

  it should "simplify complex multiplication with fractions" in {
    val n = Var("n")
    val test = Mul(Array(Num(-1), Div(Array(Mul(Array(Num(2), n, Num(1))), Num(4))), cos(Mul(Array(n, pi)))))
    val simplified = test.fullSimplify

    // Should not have duplicate signs
    simplified.toString should not include ("+ -")
    simplified.toString should not include ("- -")
  }

  "Collatz expression" should "simplify without duplicate signs" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
    val simplified = collatz1.fullSimplify

    simplified.toString should not include ("+ -")
    simplified.toString should not include ("- -")
  }

  it should "handle collatz2 simplification" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val simplified = collatz2.fullSimplify

    // Basic sanity check - should complete without error
    simplified should not be null
  }

  "Product to sum" should "handle cosine products" in {
    val x = Var("x")
    val y = Var("y")
    val test = Mul(Array(cos(x), cos(y)))
    val expanded = test.expand

    // Should complete without error
    expanded should not be null
  }

  "Numeric literals" should "combine correctly" in {
    val test = Add(Array(Num(1), Num(2)))
    val simplified = test.simplify

    simplified should equal (Num(3))
  }

  it should "multiply correctly" in {
    val test = Mul(Array(Num(2), Num(3)))
    val simplified = test.simplify

    simplified should equal (Num(6))
  }

  "Zero and identity" should "be removed in addition" in {
    val x = Var("x")
    val test = x + Num(0)
    val simplified = test.simplify

    simplified should equal (x)
  }

  it should "be removed in multiplication" in {
    val x = Var("x")
    val test = x * Num(1)
    val simplified = test.simplify

    simplified should equal (x)
  }

  it should "make entire expression zero when multiplying by zero" in {
    val x = Var("x")
    val test = x * Num(0)
    val simplified = test.simplify

    simplified should equal (Num(0))
  }
}
