package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var, Add, Mul, SimplificationConfig}
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum}

/**
 * Test suite for core expression types.
 *
 * Tests:
 * - Num (numeric literals)
 * - Var (variables)
 * - Basic operations and properties
 * - Evaluation
 * - Symbol replacement
 * - Edge cases
 */
class CoreTypesSpec extends AnyFlatSpec with Matchers {

  val epsilon = 0.0001

  "Num" should "create integer literals" in {
    val num = Num(5)

    num.numerator should equal (5)
    num.denominator should equal (1)
  }

  it should "create fractional literals" in {
    val num = Num(3, 4)

    num.numerator should equal (3)
    num.denominator should equal (4)
  }

  it should "simplify fractions" in {
    val num = Num(6, 8)

    // Should reduce to 3/4
    num.numerator should equal (3)
    num.denominator should equal (4)
  }

  it should "handle negative numerators" in {
    val num = Num(-3, 4)

    num.numerator should equal (-3)
    num.denominator should equal (4)
  }

  it should "handle negative denominators" in {
    val num = Num(3, -4)

    // Negative should move to numerator
    num.numerator should equal (-3)
    num.denominator should equal (4)
  }

  it should "handle negative both" in {
    val num = Num(-3, -4)

    // Both negatives cancel out
    num.numerator should equal (3)
    num.denominator should equal (4)
  }

  it should "handle zero" in {
    val num = Num(0)

    num.numerator should equal (0)
    num.denominator should equal (1)
  }

  it should "throw on zero denominator" in {
    an [IllegalArgumentException] should be thrownBy {
      Num(1, 0)
    }
  }

  it should "evaluate to double" in {
    val num = Num(3, 4)
    val result = num.eval(Map())

    result should equal (0.75 +- epsilon)
  }

  it should "evaluate integers correctly" in {
    val num = Num(42)
    val result = num.eval(Map())

    result should equal (42.0 +- epsilon)
  }

  it should "support decimal constructor" in {
    val num = Num(0.5)

    num.eval(Map()) should equal (0.5 +- epsilon)
  }

  it should "convert to string for integers" in {
    val num = Num(5)

    num.toString should equal ("5")
  }

  it should "convert to string for fractions" in {
    val num = Num(3, 4)

    num.toString should include ("/")
    num.toString should include ("3")
    num.toString should include ("4")
  }

  it should "simplify to itself" in {
    val num = Num(5)
    val simplified = num.simplify

    simplified should equal (num)
  }

  it should "not be affected by symbol replacement" in {
    val num = Num(5)
    val replaced = num.replaceSymbol("x", Var("y"))

    replaced should equal (num)
  }

  it should "compare equal by value" in {
    val num1 = Num(6, 8)
    val num2 = Num(3, 4)

    num1 should equal (num2)
  }

  it should "have precedence defined" in {
    val num = Num(5)

    num.precedence should be >= 0
  }

  "Var" should "create variables" in {
    val v = Var("x")

    v.name should equal ("x")
  }

  it should "evaluate with provided value" in {
    val v = Var("x")
    val result = v.eval(Map("x" -> 5.0))

    result should equal (5.0 +- epsilon)
  }

  it should "throw when variable not provided" in {
    val v = Var("x")

    an [UndefinedVariableError] should be thrownBy {
      v.eval(Map())
    }
  }

  it should "convert to string" in {
    val v = Var("x")

    v.toString should equal ("x")
  }

  it should "simplify to itself" in {
    val v = Var("x")
    val simplified = v.simplify

    simplified should equal (v)
  }

  it should "support symbol replacement for same variable" in {
    val v = Var("x")
    val replaced = v.replaceSymbol("x", Num(5))

    replaced should equal (Num(5))
  }

  it should "not replace different variables" in {
    val v = Var("x")
    val replaced = v.replaceSymbol("y", Num(5))

    replaced should equal (v)
  }

  it should "support replacement with expressions" in {
    val v = Var("x")
    val expr = Add(Vector(Var("y"), Num(1)))
    val replaced = v.replaceSymbol("x", expr)

    replaced should equal (expr)
  }

  it should "compare equal by name" in {
    val v1 = Var("x")
    val v2 = Var("x")

    v1 should equal (v2)
  }

  it should "compare unequal for different names" in {
    val v1 = Var("x")
    val v2 = Var("y")

    v1 should not equal (v2)
  }

  it should "have precedence defined" in {
    val v = Var("x")

    v.precedence should be >= 0
  }

  "Multiple variables" should "evaluate independently" in {
    val x = Var("x")
    val y = Var("y")
    val expr = Add(Vector(x, y))

    val result = expr.eval(Map("x" -> 3.0, "y" -> 4.0))
    result should equal (7.0 +- epsilon)
  }

  it should "replace independently" in {
    val x = Var("x")
    val y = Var("y")
    val expr = Add(Vector(x, y))

    val replaced = expr.replaceSymbol("x", Num(3))
    replaced.toString should include ("y")
    replaced.toString should include ("3")
  }

  "Num arithmetic" should "add correctly" in {
    val num1 = Num(1, 2)
    val num2 = Num(1, 3)
    val result = Add(Vector(num1, num2)).simplify

    // 1/2 + 1/3 = 5/6
    result should equal (Num(5, 6))
  }

  it should "multiply correctly" in {
    val num1 = Num(2, 3)
    val num2 = Num(3, 4)
    val result = Mul(Vector(num1, num2)).simplify

    // 2/3 * 3/4 = 1/2
    result should equal (Num(1, 2))
  }

  "Implicit conversions" should "work for integers" in {
    import Dsl._

    val expr: Expr = 5
    expr should be (a[Num])
  }

  it should "work for doubles" in {
    import Dsl._

    val expr: Expr = 3.5
    expr should be (a[Num])
  }

  it should "work for operators" in {
    import Dsl._

    val x = Var("x")
    val expr = x + 5

    expr should be (a[Add])
  }

  "Edge cases" should "handle very large numbers" in {
    val num = Num(1000000)
    val result = num.eval(Map())

    result should equal (1000000.0 +- epsilon)
  }

  it should "handle very small fractions" in {
    val num = Num(1, 1000000)
    val result = num.eval(Map())

    result should equal (0.000001 +- epsilon)
  }

  it should "handle variable names with underscores" in {
    val v = Var("my_var")
    v.name should equal ("my_var")
  }

  it should "handle variable names with numbers" in {
    val v = Var("x1")
    v.name should equal ("x1")
  }

  "Num expansion" should "return itself" in {
    val num = Num(5)
    val expanded = num.expand

    expanded should equal (num)
  }

  "Var expansion" should "return itself" in {
    val v = Var("x")
    val expanded = v.expand

    expanded should equal (v)
  }

  "GCD reduction" should "work for common factors" in {
    val num = Num(12, 18)

    // Should reduce to 2/3
    num.numerator should equal (2)
    num.denominator should equal (3)
  }

  it should "work for coprime numbers" in {
    val num = Num(7, 11)

    // Should not reduce
    num.numerator should equal (7)
    num.denominator should equal (11)
  }

  "Num comparison" should "work for fractions and integers" in {
    val num1 = Num(4, 2)
    val num2 = Num(2)

    num1 should equal (num2)
  }
}
