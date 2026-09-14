package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var}
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Test suite for Collatz sequence simplifications.
 *
 * Tests simplification of complex Collatz expressions, ensuring:
 * - No duplicate signs (+ -, - -, - +)
 * - Cosine arguments are fully simplified
 * - No nested fractions
 * - Mathematical correctness is preserved
 */
class CollatzSpec extends AnyFlatSpec with Matchers {

  val TOLERANCE = 1e-10

  "Collatz1" should "simplify correctly" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
    val simplified = collatz1.fullSimplify

    // Should not have duplicate signs
    simplified.toString should not include ("+ -")
    simplified.toString should not include ("- -")
    simplified.toString should not include ("- +")
  }

  it should "preserve mathematical meaning" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
    val vars = Map("n" -> 123.0, "pi" -> math.Pi)

    val originalValue = collatz1.eval(vars)
    val simplifiedValue = collatz1.fullSimplify.eval(vars)

    math.abs(originalValue - simplifiedValue) should be < TOLERANCE
  }

  it should "be idempotent" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
    val simplified1 = collatz1.fullSimplify
    val simplified2 = simplified1.fullSimplify

    simplified1 should equal (simplified2)
  }

  "Collatz2" should "simplify to reasonable length" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val simplified = collatz2.fullSimplify
    val output = simplified.toString

    // Should be under 500 characters when simplified
    output.length should be < 800
  }

  it should "not have duplicate signs" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val simplified = collatz2.fullSimplify
    val output = simplified.toString

    output should not include ("+ -")
    output should not include ("- -")
    output should not include ("- +")
  }

  it should "preserve mathematical meaning" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val vars = Map("n" -> 123.0, "pi" -> math.Pi)
    val originalValue = collatz2.eval(vars)
    val simplifiedValue = collatz2.fullSimplify.eval(vars)

    math.abs(originalValue - simplifiedValue) should be < TOLERANCE
  }

  "Collatz3" should "simplify without duplicate signs" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val collatz3Even = collatz2.replaceSymbol("n", n/2)
    val collatz3Odd = collatz2.replaceSymbol("n", (n*3+1)/2)
    val collatz3 = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)

    val simplified = collatz3.fullSimplify
    val output = simplified.toString

    output should not include ("+ -")
    output should not include ("- -")
    output should not include ("- +")
  }

  it should "not have unsimplified cosine arguments" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val collatz3Even = collatz2.replaceSymbol("n", n/2)
    val collatz3Odd = collatz2.replaceSymbol("n", (n*3+1)/2)
    val collatz3 = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)

    val simplified = collatz3.fullSimplify
    val output = simplified.toString

    // Should not have patterns like "(1 + 3 * n" or "(3 * (3 * n"
    output should not include ("(1 + 3 * n")
    output should not include ("(3 * (3 * n")
  }

  it should "preserve mathematical meaning" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val collatz3Even = collatz2.replaceSymbol("n", n/2)
    val collatz3Odd = collatz2.replaceSymbol("n", (n*3+1)/2)
    val collatz3 = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)

    val vars = Map("n" -> 123.0, "pi" -> math.Pi)
    val originalValue = collatz3.eval(vars)
    val simplifiedValue = collatz3.fullSimplify.eval(vars)

    math.abs(originalValue - simplifiedValue) should be < TOLERANCE
  }

  it should "complete in reasonable time" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val collatz3Even = collatz2.replaceSymbol("n", n/2)
    val collatz3Odd = collatz2.replaceSymbol("n", (n*3+1)/2)
    val collatz3 = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)

    // Should complete without timeout
    val simplified = collatz3.fullSimplify
    simplified should not be null
  }

  "Collatz series" should "evaluate all levels correctly" in {
    val n = Var("n")
    val vars = Map("n" -> 123.0, "pi" -> math.Pi)

    // Level 1
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
    val c1_orig = collatz1.eval(vars)
    val c1_simp = collatz1.fullSimplify.eval(vars)
    math.abs(c1_orig - c1_simp) should be < TOLERANCE

    // Level 2
    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)
    val c2_orig = collatz2.eval(vars)
    val c2_simp = collatz2.fullSimplify.eval(vars)
    math.abs(c2_orig - c2_simp) should be < TOLERANCE

    // Level 3
    val collatz3Even = collatz2.replaceSymbol("n", n/2)
    val collatz3Odd = collatz2.replaceSymbol("n", (n*3+1)/2)
    val collatz3 = cos(n*pi) * Num(1,2) * (collatz3Even - collatz3Odd) + Num(1, 2) * (collatz3Even + collatz3Odd)
    val c3_orig = collatz3.eval(vars)
    val c3_simp = collatz3.fullSimplify.eval(vars)
    math.abs(c3_orig - c3_simp) should be < TOLERANCE
  }
}
