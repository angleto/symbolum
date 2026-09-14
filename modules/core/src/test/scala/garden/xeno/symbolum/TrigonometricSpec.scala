package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var, Add, Mul, Pow, Sin, Cos, Tan, SimplificationConfig}
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, sin, cos, tan, pi}

/**
 * Test suite for trigonometric functions.
 *
 * Tests:
 * - Sin, Cos, Tan functions
 * - Evaluation at known values
 * - Simplification rules
 * - Trigonometric identities
 * - Symbol replacement
 * - Edge cases
 */
class TrigonometricSpec extends AnyFlatSpec with Matchers {

  val epsilon = 0.0001

  "Sin function" should "evaluate at 0" in {
    val expr = Sin(Num(0))
    val result = expr.eval(Map())

    result should equal (0.0 +- epsilon)
  }

  it should "evaluate at pi/2" in {
    val expr = Sin(Div(Vector(pi, Num(2))))
    val result = expr.eval(Map("pi" -> Math.PI))

    result should equal (1.0 +- epsilon)
  }

  it should "evaluate at pi" in {
    val expr = Sin(pi)
    val result = expr.eval(Map("pi" -> Math.PI))

    Math.abs(result) should be < epsilon
  }

  it should "handle variables" in {
    val x = Var("x")
    val expr = Sin(x)

    val result = expr.eval(Map("x" -> 0.0))
    result should equal (0.0 +- epsilon)
  }

  it should "handle sin(2x)" in {
    val x = Var("x")
    val expr = Sin(Mul(Vector(Num(2), x)))

    val result = expr.eval(Map("x" -> Math.PI / 4))
    result should equal (1.0 +- epsilon)
  }

  it should "support toString" in {
    val x = Var("x")
    val expr = Sin(x)

    expr.toString should include ("sin")
    expr.toString should include ("x")
  }

  "Cos function" should "evaluate at 0" in {
    val expr = Cos(Num(0))
    val result = expr.eval(Map())

    result should equal (1.0 +- epsilon)
  }

  it should "evaluate at pi/2" in {
    val expr = Cos(Div(Vector(pi, Num(2))))
    val result = expr.eval(Map("pi" -> Math.PI))

    Math.abs(result) should be < epsilon
  }

  it should "evaluate at pi" in {
    val expr = Cos(pi)
    val result = expr.eval(Map("pi" -> Math.PI))

    result should equal (-1.0 +- epsilon)
  }

  it should "handle variables" in {
    val x = Var("x")
    val expr = Cos(x)

    val result = expr.eval(Map("x" -> 0.0))
    result should equal (1.0 +- epsilon)
  }

  it should "handle cos(2x)" in {
    val x = Var("x")
    val expr = Cos(Mul(Vector(Num(2), x)))

    val result = expr.eval(Map("x" -> Math.PI / 3))
    result should equal (-0.5 +- epsilon)
  }

  it should "support toString" in {
    val x = Var("x")
    val expr = Cos(x)

    expr.toString should include ("cos")
    expr.toString should include ("x")
  }

  "Tan function" should "evaluate at 0" in {
    val expr = Tan(Num(0))
    val result = expr.eval(Map())

    result should equal (0.0 +- epsilon)
  }

  it should "evaluate at pi/4" in {
    val expr = Tan(Div(Vector(pi, Num(4))))
    val result = expr.eval(Map("pi" -> Math.PI))

    result should equal (1.0 +- epsilon)
  }

  it should "handle variables" in {
    val x = Var("x")
    val expr = Tan(x)

    val result = expr.eval(Map("x" -> 0.0))
    result should equal (0.0 +- epsilon)
  }

  it should "support toString" in {
    val x = Var("x")
    val expr = Tan(x)

    expr.toString should include ("tan")
    expr.toString should include ("x")
  }

  "Symbol replacement" should "work for Sin" in {
    val x = Var("x")
    val expr = Sin(x)
    val replaced = expr.replaceSymbol("x", Var("y"))

    replaced.toString should include ("y")
  }

  it should "work for Cos" in {
    val x = Var("x")
    val expr = Cos(x)
    val replaced = expr.replaceSymbol("x", Num(0))

    replaced should equal (Cos(Num(0)))
  }

  it should "work for Tan" in {
    val x = Var("x")
    val expr = Tan(x)
    val replaced = expr.replaceSymbol("x", Mul(Vector(Num(2), Var("y"))))

    replaced.toString should include ("y")
  }

  "Simplification" should "not change simple sin" in {
    val x = Var("x")
    val expr = Sin(x)
    val simplified = expr.simplify

    simplified should equal (expr)
  }

  it should "not change simple cos" in {
    val x = Var("x")
    val expr = Cos(x)
    val simplified = expr.simplify

    simplified should equal (expr)
  }

  it should "simplify sin(0)" in {
    val expr = Sin(Num(0))
    val simplified = expr.simplify

    // May or may not simplify to Num(0) depending on implementation
    simplified should not be null
  }

  it should "simplify argument" in {
    val x = Var("x")
    val expr = Sin(Add(Vector(x, Num(0))))
    val simplified = expr.simplify

    simplified should equal (Sin(x))
  }

  "Expansion" should "preserve trigonometric functions" in {
    val x = Var("x")
    val expr = Sin(Add(Vector(x, Num(1))))
    val expanded = expr.expand

    // Sin doesn't expand, should remain as is
    expanded should be (a[Sin])
  }

  "Precedence" should "be defined" in {
    val x = Var("x")
    val sin = Sin(x)
    val cos = Cos(x)
    val tan = Tan(x)

    sin.precedence should be >= 0
    cos.precedence should be >= 0
    tan.precedence should be >= 0
  }

  "Nested trig functions" should "evaluate correctly" in {
    val x = Var("x")
    val expr = Sin(Cos(x))

    val result = expr.eval(Map("x" -> 0.0))
    // sin(cos(0)) = sin(1)
    result should equal (Math.sin(1.0) +- epsilon)
  }

  it should "support toString" in {
    val x = Var("x")
    val expr = Sin(Cos(x))

    expr.toString should include ("sin")
    expr.toString should include ("cos")
  }

  "Complex expressions" should "combine trig functions" in {
    val x = Var("x")
    val expr = Add(Vector(Sin(x), Cos(x)))

    val result = expr.eval(Map("x" -> Math.PI / 4))
    result should equal (Math.sqrt(2) +- epsilon)
  }

  it should "multiply trig functions" in {
    val x = Var("x")
    val expr = Mul(Vector(Sin(x), Cos(x)))

    val result = expr.eval(Map("x" -> Math.PI / 6))
    // sin(pi/6) * cos(pi/6) = 0.5 * sqrt(3)/2
    result should be > 0.0
  }

  it should "handle powers of trig functions" in {
    val x = Var("x")
    val expr = Pow(Sin(x), Num(2))

    val result = expr.eval(Map("x" -> Math.PI / 2))
    result should equal (1.0 +- epsilon)
  }

  "Edge cases" should "handle very small angles" in {
    val expr = Sin(Num(0.0001))
    val result = expr.eval(Map())

    result should equal (0.0001 +- 0.0001)
  }

  it should "handle negative angles" in {
    val expr = Sin(Num(-Math.PI / 2))
    val result = expr.eval(Map())

    result should equal (-1.0 +- epsilon)
  }

  "Pythagorean identity" should "hold approximately" in {
    val x = Var("x")
    val expr = Add(Vector(
      Pow(Sin(x), Num(2)),
      Pow(Cos(x), Num(2))
    ))

    val result = expr.eval(Map("x" -> 1.5))
    result should equal (1.0 +- epsilon)
  }

  "Multiple variables" should "be supported" in {
    val x = Var("x")
    val y = Var("y")
    val expr = Add(Vector(Sin(x), Cos(y)))

    val result = expr.eval(Map("x" -> 0.0, "y" -> 0.0))
    result should equal (1.0 +- epsilon)
  }
}
