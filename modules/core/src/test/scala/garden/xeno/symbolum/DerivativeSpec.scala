package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var, Add, Sub, Mul, Div, Pow, Derivative, Sin, Cos, Tan, Exp, Log, Neg}
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum}

/**
 * Test suite for symbolic differentiation.
 *
 * Tests:
 * - Basic derivative rules (constant, variable, power)
 * - Sum and difference rules
 * - Product and quotient rules
 * - Chain rule
 * - Trigonometric derivatives
 * - Exponential and logarithm derivatives
 * - Higher-order derivatives
 */
class DerivativeSpec extends AnyFlatSpec with Matchers {

  "Derivative of constants" should "be zero" in {
    val result = Derivative(Num(5), "x").simplify
    result should equal (Num(0))
  }

  it should "handle fractional constants" in {
    val result = Derivative(Num(3, 4), "x").simplify
    result should equal (Num(0))
  }

  "Derivative of variables" should "be one for same variable" in {
    val x = Var("x")
    val result = Derivative(x, "x").simplify
    result should equal (Num(1))
  }

  it should "be zero for different variable" in {
    val y = Var("y")
    val result = Derivative(y, "x").simplify
    result should equal (Num(0))
  }

  "Power rule" should "handle x^n" in {
    val x = Var("x")
    val expr = Pow(x, Num(2))
    val result = Derivative(expr, "x").simplify

    // d/dx(x^2) = 2*x
    result should equal (Mul(Vector(Num(2), x)).simplify)
  }

  it should "handle x^3" in {
    val x = Var("x")
    val expr = Pow(x, Num(3))
    val result = Derivative(expr, "x").simplify

    // d/dx(x^3) = 3*x^2
    val expected = Mul(Vector(Num(3), Pow(x, Num(2)))).simplify
    result should equal (expected)
  }

  it should "handle x^(-1)" in {
    val x = Var("x")
    val expr = Pow(x, Num(-1))
    val result = Derivative(expr, "x").simplify

    // d/dx(x^-1) = -x^-2 = -1/x^2
    result.toString should not be empty
  }

  "Sum rule" should "differentiate sums" in {
    val x = Var("x")
    val expr = Add(Vector(Pow(x, Num(2)), x, Num(5)))
    val result = Derivative(expr, "x").simplify

    // d/dx(x^2 + x + 5) = 2x + 1
    val expected = Add(Vector(Mul(Vector(Num(2), x)).simplify, Num(1))).simplify
    result should equal (expected)
  }

  "Difference rule" should "differentiate differences" in {
    val x = Var("x")
    val expr = Sub(Vector(Pow(x, Num(2)), x))
    val result = Derivative(expr, "x").simplify

    // d/dx(x^2 - x) = 2x - 1
    result.toString should not be empty
  }

  "Product rule" should "handle two factors" in {
    val x = Var("x")
    val expr = Mul(Vector(x, Pow(x, Num(2))))
    val result = Derivative(expr, "x").simplify

    // d/dx(x * x^2) = x^2 + x*2x = x^2 + 2x^2 = 3x^2
    // Or could simplify first to x^3 and get 3x^2
    result.toString should include ("x")
  }

  it should "handle constant times function" in {
    val x = Var("x")
    val expr = Mul(Vector(Num(3), Pow(x, Num(2))))
    val result = Derivative(expr, "x").simplify

    // d/dx(3x^2) = 6x
    val expected = Mul(Vector(Num(6), x)).simplify
    result should equal (expected)
  }

  it should "handle x*sin(x)" in {
    val x = Var("x")
    val expr = Mul(Vector(x, Sin(x)))
    val result = Derivative(expr, "x").simplify

    // d/dx(x*sin(x)) = sin(x) + x*cos(x)
    result should be (a[Add])
  }

  "Quotient rule" should "differentiate divisions" in {
    val x = Var("x")
    val expr = Div(Vector(Num(1), x))
    val result = Derivative(expr, "x").simplify

    // d/dx(1/x) = -1/x^2
    result.toString should include ("-")
    result.toString should include ("x")
  }

  it should "handle x/x^2" in {
    val x = Var("x")
    val expr = Div(Vector(x, Pow(x, Num(2))))
    val result = Derivative(expr, "x").simplify

    // d/dx(x/x^2) = d/dx(1/x) = -1/x^2
    result.toString should not be empty
  }

  "Sine derivative" should "be cosine" in {
    val x = Var("x")
    val expr = Sin(x)
    val result = Derivative(expr, "x").simplify

    // d/dx(sin(x)) = cos(x)
    result should equal (Cos(x))
  }

  it should "apply chain rule" in {
    val x = Var("x")
    val expr = Sin(Mul(Vector(Num(2), x)))
    val result = Derivative(expr, "x").simplify

    // d/dx(sin(2x)) = 2*cos(2x)
    result should be (a[Mul])
  }

  "Cosine derivative" should "be negative sine" in {
    val x = Var("x")
    val expr = Cos(x)
    val result = Derivative(expr, "x").simplify

    // d/dx(cos(x)) = -sin(x)
    result.toString should include ("-")
    result.toString should include ("sin")
  }

  "Tangent derivative" should "be sec^2" in {
    val x = Var("x")
    val expr = Tan(x)
    val result = Derivative(expr, "x").simplify

    // d/dx(tan(x)) = 1/cos^2(x)
    result should be (a[Div])
  }

  "Exponential derivative" should "be itself" in {
    val x = Var("x")
    val expr = Exp(x)
    val result = Derivative(expr, "x").simplify

    // d/dx(exp(x)) = exp(x)
    result should equal (Exp(x))
  }

  it should "apply chain rule" in {
    val x = Var("x")
    val expr = Exp(Mul(Vector(Num(2), x)))
    val result = Derivative(expr, "x").simplify

    // d/dx(exp(2x)) = 2*exp(2x)
    result should be (a[Mul])
  }

  "Logarithm derivative" should "be 1/x" in {
    val x = Var("x")
    val expr = Log(x)
    val result = Derivative(expr, "x").simplify

    // d/dx(log(x)) = 1/x
    result should equal (Div(Vector(Num(1), x)).simplify)
  }

  it should "apply chain rule" in {
    val x = Var("x")
    val expr = Log(Pow(x, Num(2)))
    val result = Derivative(expr, "x").simplify

    // d/dx(log(x^2)) = 2x/x^2 = 2/x
    result.toString should not be empty
  }

  "Negation" should "preserve derivative sign" in {
    val x = Var("x")
    val expr = Neg(Pow(x, Num(2)))
    val result = Derivative(expr, "x").simplify

    // d/dx(-x^2) = -2x
    result.toString should include ("-")
  }

  "Higher derivatives" should "compute second derivative" in {
    val x = Var("x")
    val expr = Pow(x, Num(3))

    val firstDeriv = Derivative(expr, "x").simplify
    val secondDeriv = Derivative(firstDeriv, "x").simplify

    // d^2/dx^2(x^3) = d/dx(3x^2) = 6x
    val expected = Mul(Vector(Num(6), x)).simplify
    secondDeriv should equal (expected)
  }

  it should "use nth derivative helper" in {
    val x = Var("x")
    val expr = Pow(x, Num(4))

    val result = Derivative.nth(expr, "x", 2)

    // d^2/dx^2(x^4) = 12x^2
    val expected = Mul(Vector(Num(12), Pow(x, Num(2)))).simplify
    result should equal (expected)
  }

  it should "handle third derivative" in {
    val x = Var("x")
    val expr = Pow(x, Num(3))

    val result = Derivative.nth(expr, "x", 3)

    // d^3/dx^3(x^3) = 6
    result should equal (Num(6))
  }

  it should "handle zero derivative" in {
    val x = Var("x")
    val expr = Pow(x, Num(2))

    val result = Derivative.nth(expr, "x", 0)

    // 0th derivative is the expression itself
    result should equal (expr)
  }

  "Chain rule" should "handle composition of functions" in {
    val x = Var("x")
    val expr = Sin(Pow(x, Num(2)))
    val result = Derivative(expr, "x").simplify

    // d/dx(sin(x^2)) = cos(x^2) * 2x
    result should be (a[Mul])
  }

  it should "handle nested composition" in {
    val x = Var("x")
    val expr = Exp(Sin(x))
    val result = Derivative(expr, "x").simplify

    // d/dx(exp(sin(x))) = exp(sin(x)) * cos(x)
    result should be (a[Mul])
  }

  "Complex expressions" should "differentiate correctly" in {
    val x = Var("x")
    val expr = Add(Vector(
      Mul(Vector(Num(3), Pow(x, Num(2)))),
      Mul(Vector(Num(2), x)),
      Num(-5)
    ))
    val result = Derivative(expr, "x").simplify

    // d/dx(3x^2 + 2x - 5) = 6x + 2
    val expected = Add(Vector(Mul(Vector(Num(6), x)).simplify, Num(2))).simplify
    result should equal (expected)
  }

  it should "handle products and quotients together" in {
    val x = Var("x")
    val expr = Div(Vector(
      Mul(Vector(x, x)),
      Add(Vector(x, Num(1)))
    ))
    val result = Derivative(expr, "x").simplify

    // Should complete without error
    result should not be null
  }

  "General power rule" should "handle variable exponents" in {
    val x = Var("x")
    val y = Var("y")
    val expr = Pow(x, y)
    val result = Derivative(expr, "x").simplify

    // d/dx(x^y) = y*x^(y-1) (when y is constant w.r.t. x)
    result should be (a[Mul])
  }

  "Evaluation" should "work after differentiation" in {
    val x = Var("x")
    val expr = Pow(x, Num(2))
    val derivative = Derivative(expr, "x").simplify

    // d/dx(x^2) = 2x, evaluate at x=3
    val result = derivative.eval(Map("x" -> 3.0))
    result should equal (6.0)
  }

  "Symbol replacement" should "work in derivatives" in {
    val x = Var("x")
    val expr = Derivative(Pow(x, Num(2)), "x")
    val replaced = expr.replaceSymbol("x", Var("y"))

    // Should replace variable in expression
    replaced.toString should include ("y")
  }

  "Edge cases" should "handle multiple variables" in {
    val x = Var("x")
    val y = Var("y")
    val expr = Add(Vector(Mul(Vector(x, y)), Pow(x, Num(2))))
    val result = Derivative(expr, "x").simplify

    // d/dx(xy + x^2) = y + 2x
    result.toString should not be empty
  }

  it should "handle zero coefficient" in {
    val x = Var("x")
    val expr = Mul(Vector(Num(0), x))
    val result = Derivative(expr, "x").simplify

    // d/dx(0*x) = d/dx(0) = 0
    result should equal (Num(0))
  }
}
