package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg}
import garden.xeno.symbolum.Dsl
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
    val test = Add(Vector(x, Neg(y)))
    val simplified = test.simplify

    // Should be x - y, not x + (-y)
    simplified.toString should not include ("+ -")
  }

  it should "flatten nested additions" in {
    val x = Var("x")
    val y = Var("y")
    val test = Add(Vector(x, Add(Vector(y, Num(5)))))
    val simplified = test.simplify

    // Should be flattened
    simplified should be (a[Add])
  }

  it should "merge fractions with same denominator" in {
    val test = Add(Vector(Num(1, 4), Num(1, 4)))
    val simplified = test.simplify

    simplified should equal (Num(1, 2))
  }

  it should "handle negative fractions" in {
    val test = Add(Vector(Num(3, 4), Num(-1, 4)))
    val simplified = test.simplify

    simplified should equal (Num(1, 2))
  }

  it should "simplify complex multiplication with fractions" in {
    val n = Var("n")
    val test = Mul(Vector(Num(-1), Div(Vector(Mul(Vector(Num(2), n, Num(1))), Num(4))), cos(Mul(Vector(n, pi)))))
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
    val test = Mul(Vector(cos(x), cos(y)))
    val expanded = test.expand

    // Should complete without error
    expanded should not be null
  }

  "Numeric literals" should "combine correctly" in {
    val test = Add(Vector(Num(1), Num(2)))
    val simplified = test.simplify

    simplified should equal (Num(3))
  }

  it should "multiply correctly" in {
    val test = Mul(Vector(Num(2), Num(3)))
    val simplified = test.simplify

    simplified should equal (Num(6))
  }

  "The empty product" should "be one for every base, including zero" in {
    // `x^n` is n copies of x multiplied together, so `x^0` is the product of none of them, and that
    // is the ring's unit whatever x was. Construction, evaluation and simplification all say so;
    // until this was written the constructor alone refused, while `eval` returned 1.0 for the same
    // expression and the canonical form reduced it to 1.
    val x = Var("x")

    Pow(Num(0), Num(0)).simplify should equal(Num(1))
    Pow(Num(0), Num(0)).eval(Map.empty) should equal(1.0)
    Pow(x, Num(0)).simplify should equal(Num(1))
    Pow(x, Num(0)).eval(Map("x" -> 0.0)) should equal(1.0)

    // The condition belongs to the other case, and it is still there: `0^n` is zero for a positive
    // n. Mathlib puts its hypothesis on exactly this one and not on the one above.
    Pow(Num(0), Num(3)).simplify should equal(Num(0))
    Pow(Num(0), Num(1)).simplify should equal(Num(0))
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
