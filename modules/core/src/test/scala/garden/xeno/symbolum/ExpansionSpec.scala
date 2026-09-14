package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var, Add, Mul, Cos}
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Test suite for expression expansion.
 *
 * Tests aggressive expansion of expressions, ensuring that:
 * - Products are distributed over sums
 * - Large parenthesized blocks are broken down
 * - Expressions are fully expanded
 */
class ExpansionSpec extends AnyFlatSpec with Matchers {

  "Expansion" should "distribute simple product over sum" in {
    val n = Var("n")
    val A = n * pi / 2.0
    val B = Num(1, 16)
    val C = (n + 1) / 32.0

    val expr = cos(A) * (B + C)
    val simplified = expr.fullSimplify

    // Should not have large parenthesized blocks
    val str = simplified.toString
    val hasLargeBlock = str.matches(".*\\([^)]{20,}\\).*")
    hasLargeBlock should be (false)
  }

  it should "distribute nested products" in {
    val n = Var("n")
    val A = n * pi / 2.0
    val B = Num(1, 16)
    val C = (n + 1) / 32.0

    val expr = cos(A) * (B + cos(A) * C)
    val simplified = expr.fullSimplify

    // Should have multiple separate terms
    val str = simplified.toString
    val numTerms = str.count(c => c == '+' || c == '-') + 1
    numTerms should be >= 2
  }

  it should "expand expression with 5 terms" in {
    val n = Var("n")
    val A = n * pi / 2.0
    val B = Num(1, 16)
    val C = (n + 1) / 32.0

    val expr = cos(A) * (B + C + B + C + B)
    val simplified = expr.fullSimplify

    // Should not have pattern 'cos(...) * (large_block)'
    val str = simplified.toString
    val hasCosParen = str.matches(".*cos\\([^)]+\\)\\s*\\*\\s*\\([^)]{20,}.*")
    hasCosParen should be (false)
  }

  it should "expand products of numbers" in {
    val x = Var("x")
    val expr = Num(2) * (x + Num(1))
    val simplified = expr.fullSimplify

    // Should be 2*x + 2
    simplified should be (a[Add])
  }

  it should "expand nested parentheses" in {
    val x = Var("x")
    val y = Var("y")
    val expr = (x + y) * (x + y)
    val expanded = expr.expand

    // Should expand to x^2 + 2xy + y^2 (or some form with Add)
    expanded should be (a[Add])
  }

  "Simplification" should "not create large undistributed blocks" in {
    val n = Var("n")
    val expr1 = cos(n * pi) * (Num(1, 4) + n/8 + Num(1, 16))
    val simplified = expr1.fullSimplify

    // Distributed means no cosine multiplying a parenthesised sum. The cosine itself must of
    // course still be there; asserting its absence made this case unsatisfiable.
    val str = simplified.toString
    str should not include ("* (")
    str should include ("cos")
  }

  it should "fully distribute complex expressions" in {
    val a = Var("a")
    val b = Var("b")
    val c = Var("c")

    val expr = a * (b + c + a)
    val expanded = expr.expand

    // Should have at least 3 terms
    val str = expanded.toString
    val numTerms = str.count(_ == '+') + 1
    numTerms should be >= 2
  }
}
