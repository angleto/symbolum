package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var, Add, Sub, Mul, Div, Pow, Log, Cos, Neg}
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Test suite for simplification correctness.
 *
 * This test suite validates that simplification preserves the mathematical
 * meaning of expressions by checking that:
 * 1. Original and simplified expressions evaluate to the same value
 * 2. Simplification is idempotent (simplifying twice gives the same result)
 * 3. Known mathematical identities are correctly simplified
 *
 * These are the cases that catch a rule which is wrong rather than merely unhelpful: a
 * simplified expression that no longer evaluates to the same number.
 */
class SimplificationCorrectnessSpec extends AnyFlatSpec with Matchers {

  val TOLERANCE = 1e-10

  /**
   * Helper to check that an expression and its simplified form evaluate to the same value.
   */
  def assertEvaluationEquivalent(original: Expr, simplified: Expr, vars: Map[String, Double]): Unit = {
    val originalValue = original.eval(vars)
    val simplifiedValue = simplified.eval(vars)
    val diff = math.abs(originalValue - simplifiedValue)

    withClue(s"Original: $original\nSimplified: $simplified\nOriginal eval: $originalValue\nSimplified eval: $simplifiedValue\n") {
      diff should be < TOLERANCE
    }
  }

  /**
   * Helper to check that simplification is correct across multiple test points.
   */
  def assertSimplificationCorrect(original: Expr, testPoints: List[Map[String, Double]]): Unit = {
    val simplified = original.fullSimplify

    for (vars <- testPoints) {
      assertEvaluationEquivalent(original, simplified, vars)
    }
  }

  "Simplification" should "preserve mathematical meaning for simple expressions" in {
    val x = Var("x")
    val vars = Map("x" -> 5.0)

    // Test basic arithmetic
    assertEvaluationEquivalent(x + 0, (x + 0).simplify, vars)
    assertEvaluationEquivalent(x * 1, (x * 1).simplify, vars)
    assertEvaluationEquivalent(x * 0, (x * 0).simplify, vars)
    assertEvaluationEquivalent(x + x, (x + x).simplify, vars)
  }

  it should "preserve mathematical meaning for complex expressions" in {
    val x = Var("x")
    val y = Var("y")
    val vars = Map("x" -> 3.0, "y" -> 7.0)

    // Test distribution
    val expr1 = x * (y + Num(2))
    assertEvaluationEquivalent(expr1, expr1.fullSimplify, vars)

    // Test nested operations
    val expr2 = (x + y) * (x - y)
    assertEvaluationEquivalent(expr2, expr2.fullSimplify, vars)
  }

  it should "preserve mathematical meaning for Collatz expressions" in {
    val n = Var("n")
    val testPoints = List(
      Map("n" -> 1.0, "pi" -> math.Pi),
      Map("n" -> 5.0, "pi" -> math.Pi),
      Map("n" -> 10.0, "pi" -> math.Pi),
      Map("n" -> 123.0, "pi" -> math.Pi)
    )

    // Test collatz1: -((n*2 + 1) / 4.0) * cos(n * pi) + n + 1/4
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
    assertSimplificationCorrect(collatz1, testPoints)

    // Test collatz2
    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)
    assertSimplificationCorrect(collatz2, testPoints)

    // Test collatz3
    val collatz3Even = collatz2.replaceSymbol("n", n/2)
    val collatz3Odd = collatz2.replaceSymbol("n", (n*3+1)/2)
    val collatz3 = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)
    assertSimplificationCorrect(collatz3, testPoints)
  }

  it should "preserve mathematical meaning for trigonometric expressions" in {
    val x = Var("x")
    val testPoints = List(
      Map("x" -> 0.0, "pi" -> math.Pi),
      Map("x" -> math.Pi/4, "pi" -> math.Pi),
      Map("x" -> math.Pi/2, "pi" -> math.Pi),
      Map("x" -> math.Pi, "pi" -> math.Pi)
    )

    // Test cos with various arguments
    val expr1 = cos(x)
    assertSimplificationCorrect(expr1, testPoints)

    val expr2 = cos(x * Var("pi"))
    assertSimplificationCorrect(expr2, testPoints)

    val expr3 = Num(2) * cos(x)
    assertSimplificationCorrect(expr3, testPoints)
  }

  it should "preserve mathematical meaning for fraction operations" in {
    val x = Var("x")
    val vars = Map("x" -> 6.0)

    // Test fraction addition
    val expr1 = Num(1, 2) + Num(1, 3)
    assertEvaluationEquivalent(expr1, expr1.simplify, Map.empty)

    // Test fraction multiplication
    val expr2 = Num(2, 3) * Num(3, 4)
    assertEvaluationEquivalent(expr2, expr2.simplify, Map.empty)

    // Test mixed operations
    val expr3 = x / Num(2) + x / Num(3)
    assertEvaluationEquivalent(expr3, expr3.fullSimplify, vars)
  }

  it should "be idempotent" in {
    val x = Var("x")
    val n = Var("n")

    // Test that simplifying twice gives the same result
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
    val simplified1 = collatz1.fullSimplify
    val simplified2 = simplified1.fullSimplify

    simplified1 should equal (simplified2)
  }

  it should "handle nested multiplications with cosines correctly" in {
    val x = Var("x")
    val testPoints = List(
      Map("x" -> 1.0, "pi" -> math.Pi),
      Map("x" -> 2.0, "pi" -> math.Pi),
      Map("x" -> 3.0, "pi" -> math.Pi)
    )

    // Test deeply nested expression
    val expr = cos(x * Var("pi")) * (x + Num(1))
    assertSimplificationCorrect(expr, testPoints)
  }

  it should "handle division simplification correctly" in {
    val x = Var("x")
    val vars = Map("x" -> 10.0)

    // Test division simplification
    val expr1 = (x * Num(2)) / Num(4)
    assertEvaluationEquivalent(expr1, expr1.simplify, vars)

    // Test nested division
    val expr2 = x / Num(2) / Num(3)
    assertEvaluationEquivalent(expr2, expr2.fullSimplify, vars)
  }

  it should "handle negation correctly" in {
    val x = Var("x")
    val vars = Map("x" -> 5.0)

    // Test double negation
    val expr1 = -(-x)
    assertEvaluationEquivalent(expr1, expr1.simplify, vars)

    // Test negation distribution
    val expr2 = -(x + Num(2))
    assertEvaluationEquivalent(expr2, expr2.simplify, vars)
  }

  it should "handle subtraction correctly" in {
    val x = Var("x")
    val y = Var("y")
    val vars = Map("x" -> 8.0, "y" -> 3.0)

    // Test basic subtraction
    val expr1 = x - y
    assertEvaluationEquivalent(expr1, expr1.simplify, vars)

    // Test multiple subtractions
    val expr2 = x - y - Num(1)
    assertEvaluationEquivalent(expr2, expr2.simplify, vars)
  }

  // A fractional literal is one value, not a numerator and a denominator to be matched
  // separately. Rules written as `case Num(1, _)` fired on 1/2 and 1/3 as though they were 1,
  // which is what these cases pin down.
  "Rules on numeric literals" should "not treat a fractional exponent as the exponent 1" in {
    val x = Var("x")
    val root = Pow(x, Num(1, 2))

    root.simplify should equal (root)
    root.eval(Map("x" -> 9.0)) should equal (3.0 +- 1e-9)
  }

  it should "not treat a fractional base of 1/3 as the base 1" in {
    val x = Var("x")
    val expr = Pow(Num(1, 3), x)

    expr.simplify should not equal (Num(1))
    expr.simplify.eval(Map("x" -> 2.0)) should equal (1.0 / 9.0 +- 1e-9)
  }

  it should "not treat log(1/3) as log(1)" in {
    val expr = Log(Num(1, 3))

    expr.simplify.eval(Map.empty) should equal (math.log(1.0 / 3.0) +- 1e-9)
  }

  it should "reduce a literal to lowest terms whatever the configuration" in {
    Num(6, 8) should equal (Num(3, 4))
    Num(3, -4) should equal (Num(-3, 4))
    Num(4, 2) should equal (Num(2))
    an [IllegalArgumentException] should be thrownBy Num(1, 0)
  }

  "A quotient with an all-negative numerator" should "not send the simplifier into a loop" in {
    val n = Var("n")
    val expr = Div(Vector(Add(Vector(Num(-1), Mul(Vector(Num(-1), n)))), Num(8)))

    // Division used to factor the -1 out and multiplication used to fold it back in, without end.
    val simplified = expr.fullSimplify
    simplified.toString should not include ("+ -")
    assertEvaluationEquivalent(expr, simplified, Map("n" -> 5.0))
  }

  it should "correctly evaluate the exact test.sc scenario" in {
    val n = Var("n")
    val variables = Map("n" -> 123.0, "pi" -> math.Pi)

    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val collatz3Even = collatz2.replaceSymbol("n", n/2)
    val collatz3Odd = collatz2.replaceSymbol("n", (n*3+1)/2)
    val collatz3 = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)

    // The critical test: simplified and original should evaluate to the same value
    val originalValue = collatz3.eval(variables)
    val simplifiedValue = collatz3.fullSimplify.eval(variables)

    withClue(s"Original value: $originalValue, Simplified value: $simplifiedValue\n") {
      math.abs(originalValue - simplifiedValue) should be < TOLERANCE
    }

    // Also verify all intermediate steps
    assertEvaluationEquivalent(collatz1, collatz1.fullSimplify, variables)
    assertEvaluationEquivalent(collatz2, collatz2.fullSimplify, variables)
    assertEvaluationEquivalent(collatz3, collatz3.fullSimplify, variables)
  }
}
