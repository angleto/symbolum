package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Regression tests for a quotient whose numerator is entirely negative.
 *
 * This shape used to make simplification diverge: division factored a `-1` out of the numerator,
 * multiplication folded it straight back in, and the two called each other until the stack ran
 * out. The canonical form keeps the signs in the numerator and produces the leading minus when
 * printing, so there is nothing left for the two rules to pass back and forth.
 */
class NegativeFractionTestSimple extends AnyFlatSpec with Matchers {

  "A quotient with an all-negative numerator" should "keep its signs in the numerator" in {
    val n = Var("n")
    val test = Div(Vector(
      Add(Vector(Num(-1), Mul(Vector(Num(-1), n)))),
      Num(8)
    ))

    val result = test.fullSimplify(SimplificationConfig.Default)

    result should be (a[Div])
    result.toString should include ("/8")
    result.toString should not include ("+ -")
    result.toString should not include ("- -")

    val vars = Map("n" -> 5.0)
    math.abs(result.eval(vars) - test.eval(vars)) should be < 1e-10
  }

  it should "stay canonical inside a larger product" in {
    val n = Var("n")
    val x = Var("x")
    val y = Var("y")
    val test = Mul(Vector(
      Div(Vector(Add(Vector(Num(-1), Mul(Vector(Num(-1), n)))), Num(8))),
      x,
      y
    ))

    val result = test.fullSimplify(SimplificationConfig.Default)

    result should be (a[Div])
    result.toString should not include ("+ -")
    result.toString should not include ("- -")

    val vars = Map("n" -> 5.0, "x" -> 3.0, "y" -> 2.0)
    math.abs(result.eval(vars) - test.eval(vars)) should be < 1e-10
  }

  it should "reach the same result whether simplified once or repeatedly" in {
    val n = Var("n")
    val test = Div(Vector(
      Add(Vector(Num(-1), Mul(Vector(Num(-1), n)))),
      Num(8)
    ))

    val once = test.simplify(SimplificationConfig.Default)
    once.fullSimplify(SimplificationConfig.Default) should equal (once)
  }
}
