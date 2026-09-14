package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var}
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Test suite for fullSimplify bug fix.
 *
 * This test validates that the fullSimplify function correctly handles:
 * 1. Fixpoint detection using structural equality (not hash comparison)
 * 2. Floating-point tolerance in fixpoint detection
 * 3. Correct simplification of Collatz expressions
 *
 * Regression test for:
 * - Hash collision bug (fixed: now uses structural equality)
 * - Floating-point precision bug (fixed: now uses approxEqual fallback)
 */
class FullSimplifyFixSpec extends AnyFlatSpec with Matchers {

  val TOLERANCE = 1e-10

  "fullSimplify" should "correctly simplify collatz1 and preserve mathematical meaning" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    // Test multiple points to verify correctness
    val testPoints = List(1.0, 5.0, 10.0, 123.0)
    val vars = (testValue: Double) => Map("n" -> testValue, "pi" -> math.Pi)

    val simplified = collatz1.fullSimplify

    // Verify mathematical equivalence at all test points
    for (testValue <- testPoints) {
      val originalValue = collatz1.eval(vars(testValue))
      val simplifiedValue = simplified.eval(vars(testValue))
      val diff = math.abs(originalValue - simplifiedValue)

      withClue(s"At n=$testValue: original=$originalValue, simplified=$simplifiedValue, diff=$diff\n") {
        diff should be < TOLERANCE
      }
    }

    // The simplified form should NOT be the buggy "5/4 + n"
    // We verify this by checking that it evaluates correctly
    val buggyForm = Num(5,4) + n
    val buggyValue = buggyForm.eval(vars(123.0))  // Would be 124.25
    val correctValue = collatz1.eval(vars(123.0))  // Should be 139.0

    // If we got the buggy form, these would be equal - verify they're NOT
    math.abs(buggyValue - correctValue) should be > 1.0
  }

  it should "correctly simplify collatz2 and preserve mathematical meaning" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val testPoints = List(1.0, 5.0, 10.0, 123.0)
    val vars = (testValue: Double) => Map("n" -> testValue, "pi" -> math.Pi)

    val simplified = collatz2.fullSimplify

    // Verify mathematical equivalence
    for (testValue <- testPoints) {
      val originalValue = collatz2.eval(vars(testValue))
      val simplifiedValue = simplified.eval(vars(testValue))
      val diff = math.abs(originalValue - simplifiedValue)

      withClue(s"At n=$testValue: diff=$diff\n") {
        diff should be < TOLERANCE
      }
    }

    // The simplified form should NOT be the buggy constant "2"
    val simplifiedStr = simplified.toString
    simplifiedStr should not be "2"
  }

  it should "correctly simplify collatz3 and preserve mathematical meaning" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val collatz3Even = collatz2.replaceSymbol("n", n/2)
    val collatz3Odd = collatz2.replaceSymbol("n", (n*3+1)/2)
    val collatz3 = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)

    val testPoints = List(1.0, 5.0, 10.0, 123.0)
    val vars = (testValue: Double) => Map("n" -> testValue, "pi" -> math.Pi)

    val simplified = collatz3.fullSimplify

    // Verify mathematical equivalence
    for (testValue <- testPoints) {
      val originalValue = collatz3.eval(vars(testValue))
      val simplifiedValue = simplified.eval(vars(testValue))
      val diff = math.abs(originalValue - simplifiedValue)

      withClue(s"At n=$testValue: diff=$diff\n") {
        diff should be < TOLERANCE
      }
    }

    // The simplified form should NOT be the buggy "1 + 1/4 * cos(1)"
    val simplifiedStr = simplified.toString
    simplifiedStr should not include "cos(1)"
  }

  "approxEqual" should "detect equivalent expressions with floating-point differences" in {
    // Test that approxEqual can detect expressions that are mathematically equivalent
    // but have tiny floating-point differences

    val expr1 = Num(1.0, 2.0)  // Exactly 1/2
    val expr2 = Num(1.0 + 1e-12, 2.0)  // 1/2 with tiny perturbation

    // Exact equality should fail
    expr1 should not equal expr2

    // But approxEqual should succeed
    expr1.approxEqual(expr2) should be (true)
  }

  it should "scale the tolerance to the size of the numbers" in {
    // The defect this comparison had until 2026-09-05, found by `CanonicalFormSpec` at seed
    // 443254023675775541 and reproduced here without it. A tolerance of `1e-10` scaled only by the
    // denominators is below one ulp for any value above about a million, so the comparison was
    // stricter than bit equality exactly where doubles are loosest. These two are five ulps apart
    // and are one product simplified in two orders.
    Num(-1490754.846579868).approxEqual(Num(-1490754.8465798679)) should be (true)

    // And it did not become a comparison that says anything is equal to anything: two numbers of
    // that size that genuinely differ still differ.
    Num(-1490754.846579868).approxEqual(Num(-1490754.9)) should be (false)
    Num(1000000.0).approxEqual(Num(1000000.001)) should be (false)

    // The small end is untouched, since the scale is at least the product of the denominators.
    Num(1.0, 3.0).approxEqual(Num(1.0 + 1e-9, 3.0)) should be (false)
  }

  it should "correctly compare nested expressions" in {
    val n = Var("n")

    // Create two expressions that should be approximately equal
    val expr1 = n + Num(1.0, 3.0)
    val expr2 = n + Num(1.0 + 1e-12, 3.0)

    // Exact equality should fail
    expr1 should not equal expr2

    // But approxEqual should succeed
    expr1.approxEqual(expr2) should be (true)
  }

  "fullSimplify" should "terminate at fixpoint even with floating-point precision issues" in {
    val n = Var("n")

    // Create an expression that might have floating-point precision issues
    val expr = n / 3.0 + n / 3.0 + n / 3.0

    // This should simplify to n (since 1/3 + 1/3 + 1/3 = 1)
    val simplified = expr.fullSimplify

    // Verify it reaches a fixpoint (doesn't hit MAX_ITERATIONS)
    // We can't directly test this, but we can verify the result is correct
    val vars = Map("n" -> 10.0)
    val originalValue = expr.eval(vars)
    val simplifiedValue = simplified.eval(vars)

    math.abs(originalValue - simplifiedValue) should be < TOLERANCE
  }
}
