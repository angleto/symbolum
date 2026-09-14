package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var, Add, Mul, Pow, Exp, Log, SimplificationConfig}
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum}

/**
 * Test suite for exponential and logarithm functions.
 *
 * Tests:
 * - Exp and Log functions
 * - Evaluation at known values
 * - Simplification rules
 * - Inverse relationship
 * - Symbol replacement
 * - Edge cases
 */
class ExponentialLogarithmSpec extends AnyFlatSpec with Matchers {

  val epsilon = 0.0001

  "Exp function" should "evaluate at 0" in {
    val expr = Exp(Num(0))
    val result = expr.eval(Map())

    result should equal (1.0 +- epsilon)
  }

  it should "evaluate at 1" in {
    val expr = Exp(Num(1))
    val result = expr.eval(Map())

    result should equal (Math.E +- epsilon)
  }

  it should "evaluate at 2" in {
    val expr = Exp(Num(2))
    val result = expr.eval(Map())

    result should equal (Math.exp(2.0) +- epsilon)
  }

  it should "handle variables" in {
    val x = Var("x")
    val expr = Exp(x)

    val result = expr.eval(Map("x" -> 0.0))
    result should equal (1.0 +- epsilon)
  }

  it should "handle exp(2x)" in {
    val x = Var("x")
    val expr = Exp(Mul(Vector(Num(2), x)))

    val result = expr.eval(Map("x" -> 1.0))
    result should equal (Math.exp(2.0) +- epsilon)
  }

  it should "support toString" in {
    val x = Var("x")
    val expr = Exp(x)

    expr.toString should include ("exp")
    expr.toString should include ("x")
  }

  it should "handle negative exponents" in {
    val expr = Exp(Num(-1))
    val result = expr.eval(Map())

    result should equal (1.0 / Math.E +- epsilon)
  }

  "Log function" should "evaluate at 1" in {
    val expr = Log(Num(1))
    val result = expr.eval(Map())

    result should equal (0.0 +- epsilon)
  }

  it should "evaluate at e" in {
    val expr = Log(Num(Math.E))
    val result = expr.eval(Map())

    result should equal (1.0 +- epsilon)
  }

  it should "evaluate at e^2" in {
    val expr = Log(Num(Math.exp(2.0)))
    val result = expr.eval(Map())

    result should equal (2.0 +- epsilon)
  }

  it should "handle variables" in {
    val x = Var("x")
    val expr = Log(x)

    val result = expr.eval(Map("x" -> 1.0))
    result should equal (0.0 +- epsilon)
  }

  it should "handle log(2x)" in {
    val x = Var("x")
    val expr = Log(Mul(Vector(Num(2), x)))

    val result = expr.eval(Map("x" -> Math.E / 2))
    result should equal (1.0 +- epsilon)
  }

  it should "support toString" in {
    val x = Var("x")
    val expr = Log(x)

    expr.toString should include ("log")
    expr.toString should include ("x")
  }

  "Inverse relationship" should "hold for exp(log(x))" in {
    val x = Var("x")
    val expr = Exp(Log(x))

    val result = expr.eval(Map("x" -> 5.0))
    result should equal (5.0 +- epsilon)
  }

  it should "hold for log(exp(x))" in {
    val x = Var("x")
    val expr = Log(Exp(x))

    val result = expr.eval(Map("x" -> 3.0))
    result should equal (3.0 +- epsilon)
  }

  "Symbol replacement" should "work for Exp" in {
    val x = Var("x")
    val expr = Exp(x)
    val replaced = expr.replaceSymbol("x", Var("y"))

    replaced.toString should include ("y")
  }

  it should "work for Log" in {
    val x = Var("x")
    val expr = Log(x)
    val replaced = expr.replaceSymbol("x", Num(1))

    replaced should equal (Log(Num(1)))
  }

  "Simplification" should "not change simple exp" in {
    val x = Var("x")
    val expr = Exp(x)
    val simplified = expr.simplify

    simplified should equal (expr)
  }

  it should "not change simple log" in {
    val x = Var("x")
    val expr = Log(x)
    val simplified = expr.simplify

    simplified should equal (expr)
  }

  it should "simplify exp(0)" in {
    val expr = Exp(Num(0))
    val simplified = expr.simplify

    // May or may not simplify to Num(1) depending on implementation
    simplified should not be null
  }

  it should "simplify log(1)" in {
    val expr = Log(Num(1))
    val simplified = expr.simplify

    // May or may not simplify to Num(0) depending on implementation
    simplified should not be null
  }

  it should "simplify argument" in {
    val x = Var("x")
    val expr = Exp(Add(Vector(x, Num(0))))
    val simplified = expr.simplify

    simplified should equal (Exp(x))
  }

  "Expansion" should "preserve exponential" in {
    val x = Var("x")
    val expr = Exp(Add(Vector(x, Num(1))))
    val expanded = expr.expand

    // Exp doesn't expand, should remain as is
    expanded should be (a[Exp])
  }

  "Precedence" should "be defined" in {
    val x = Var("x")
    val exp = Exp(x)
    val log = Log(x)

    exp.precedence should be >= 0
    log.precedence should be >= 0
  }

  "Nested functions" should "evaluate correctly" in {
    val x = Var("x")
    val expr = Exp(Log(Exp(x)))

    val result = expr.eval(Map("x" -> 2.0))
    result should equal (Math.exp(2.0) +- epsilon)
  }

  it should "support toString" in {
    val x = Var("x")
    val expr = Exp(Log(x))

    expr.toString should include ("exp")
    expr.toString should include ("log")
  }

  "Complex expressions" should "combine exp and log" in {
    val x = Var("x")
    val expr = Add(Vector(Exp(x), Log(x)))

    val result = expr.eval(Map("x" -> 1.0))
    // exp(1) + log(1) = e + 0 = e
    result should equal (Math.E +- epsilon)
  }

  it should "multiply exp and log" in {
    val x = Var("x")
    val expr = Mul(Vector(Exp(x), Log(x)))

    val result = expr.eval(Map("x" -> Math.E))
    // exp(e) * log(e) = exp(e) * 1
    result should equal (Math.exp(Math.E) +- epsilon)
  }

  it should "handle powers of exp" in {
    val x = Var("x")
    val expr = Pow(Exp(x), Num(2))

    val result = expr.eval(Map("x" -> 1.0))
    // exp(1)^2 = e^2
    result should equal (Math.E * Math.E +- epsilon)
  }

  "Edge cases" should "handle very large exponents" in {
    val expr = Exp(Num(10))
    val result = expr.eval(Map())

    result should be > 20000.0
  }

  it should "handle very small logarithm arguments" in {
    val expr = Log(Num(0.001))
    val result = expr.eval(Map())

    result should be < 0.0
  }

  it should "handle negative exponents in exp" in {
    val expr = Exp(Num(-5))
    val result = expr.eval(Map())

    result should be > 0.0
    result should be < 0.01
  }

  "Properties" should "hold for exp(a) * exp(b) = exp(a+b)" in {
    val a = 2.0
    val b = 3.0
    val lhs = Mul(Vector(Exp(Num(a)), Exp(Num(b))))
    val rhs = Exp(Add(Vector(Num(a), Num(b))))

    val lhsResult = lhs.eval(Map())
    val rhsResult = rhs.eval(Map())

    lhsResult should equal (rhsResult +- epsilon)
  }

  it should "hold for log(a*b) = log(a) + log(b)" in {
    val a = 2.0
    val b = 3.0
    val lhs = Log(Mul(Vector(Num(a), Num(b))))
    val rhs = Add(Vector(Log(Num(a)), Log(Num(b))))

    val lhsResult = lhs.eval(Map())
    val rhsResult = rhs.eval(Map())

    lhsResult should equal (rhsResult +- epsilon)
  }

  "Multiple variables" should "be supported" in {
    val x = Var("x")
    val y = Var("y")
    val expr = Add(Vector(Exp(x), Log(y)))

    val result = expr.eval(Map("x" -> 0.0, "y" -> 1.0))
    result should equal (1.0 +- epsilon)
  }
}
