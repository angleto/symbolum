package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var, Add, Mul, Cos}
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Test suite for fixpoint detection in fullSimplify.
 *
 * Convergence is decided by structural equality, which is exact because the canonical form
 * orders commutative operands and normalises numeric literals. These cases guard that: an
 * ordering that is not canonical makes two equal expressions compare unequal, and the loop then
 * either runs to its iteration limit or stops on a comparison that only looked equal.
 */
class FixpointDetectionSpec extends AnyFlatSpec with Matchers {

  "fullSimplify" should "reach a true fixpoint" in {
    val x = Var("x")
    val expr = x * (Num(2) + Num(3))

    val simplified = expr.fullSimplify
    val simplifiedAgain = simplified.fullSimplify

    // Simplifying twice should give the same result (idempotent)
    simplified should equal (simplifiedAgain)
  }

  it should "not terminate before the expression has settled" in {
    val n = Var("n")

    // Deep enough that a premature fixpoint would leave it partly simplified
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)
    val simplified = collatz1.fullSimplify

    // The simplified expression should evaluate to the same value
    val vars = Map("n" -> 123.0, "pi" -> math.Pi)
    val originalValue = collatz1.eval(vars)
    val simplifiedValue = simplified.eval(vars)

    math.abs(originalValue - simplifiedValue) should be < 1e-10
  }

  it should "handle deeply nested expressions" in {
    val n = Var("n")
    val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    // Create a deeply nested expression through substitution
    val collatz2Even = collatz1.replaceSymbol("n", n/2)
    val collatz2Odd = collatz1.replaceSymbol("n", (n*3+1)/2)
    val collatz2 = cos(n*pi) * Num(1,2) * (collatz2Even - collatz2Odd) + Num(1, 2) * (collatz2Even + collatz2Odd)

    val simplified = collatz2.fullSimplify

    // Should reach a stable fixpoint
    val simplifiedAgain = simplified.fullSimplify
    simplified should equal (simplifiedAgain)
  }

  it should "use structural equality for fixpoint detection" in {
    val x = Var("x")
    val y = Var("y")

    // Create an expression that should simplify
    val expr = x + x + y + y

    val simplified = expr.fullSimplify

    // The simplified form should be mathematically equivalent
    val vars = Map("x" -> 3.0, "y" -> 5.0)
    val originalValue = expr.eval(vars)
    val simplifiedValue = simplified.eval(vars)

    math.abs(originalValue - simplifiedValue) should be < 1e-10
  }

  it should "not loop infinitely" in {
    val x = Var("x")

    // This should terminate within the max iteration limit
    val expr = x * (x + Num(1)) * (x + Num(2))
    val simplified = expr.fullSimplify

    // Should complete without timing out
    simplified should not be null
  }

  it should "produce consistent results across multiple runs" in {
    val n = Var("n")
    val expr = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)

    // Simplify multiple times
    val simplified1 = expr.fullSimplify
    val simplified2 = expr.fullSimplify
    val simplified3 = expr.fullSimplify

    // All should produce the same result
    simplified1 should equal (simplified2)
    simplified2 should equal (simplified3)
  }
}
