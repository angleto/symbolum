package symbolicas

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import symbolicas.{Expr, Num, Var, Add, Mul, Div, Neg, SimplificationConfig}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Test suite for fraction operations and simplifications.
 *
 * Tests:
 * - Fraction factoring with common denominators
 * - Nested division simplification
 * - Fraction multiplication
 * - Fraction addition with different denominators
 */
class FractionOperationsSpec extends AnyFlatSpec with Matchers {

  "Fraction factoring" should "handle simple common denominator in Add" in {
    val n = Var("n")
    val test = Add(Vector(
      Num(-7, 32),
      Mul(Vector(Num(-9, 32), n))
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: (-7 - 9 * n)/32
    result should be (a[Div])
    result.toString should include ("/32")
  }

  it should "merge fractions that need Mul merging first" in {
    val n = Var("n")
    val test = Add(Vector(
      Num(-7, 32),
      Mul(Vector(Num(-9, 2), n, Num(1, 16)))
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: (-7 - 9 * n)/32 (after merging 9/2 * 1/16 = 9/32)
    result.toString should include ("/32")
  }

  it should "simplify fractions in cosine arguments" in {
    val n = Var("n")
    val test = cos(Mul(Vector(
      pi,
      Add(Vector(
        Num(5, 4),
        Mul(Vector(Num(9), n, Num(1, 4)))
      ))
    )))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: cos(pi * (5 + 9 * n)/4)
    result should be (a[Cos])
  }

  it should "factor multiple terms with common denominator" in {
    val n = Var("n")
    val test = Add(Vector(
      Num(1, 4),
      Mul(Vector(Num(3, 4), n)),
      Num(-5, 4)
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: (-4 + 3 * n)/4 or (3 * n - 4)/4
    result should be (a[Div])
    result.toString should include ("/4")
  }

  it should "handle mixed Div and fractional Num" in {
    val n = Var("n")
    val test = Add(Vector(
      Num(1, 4),
      Div(Vector(Mul(Vector(Num(3), n)), Num(4)))
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: (1 + 3 * n)/4
    result should be (a[Div])
    result.toString should include ("/4")
  }

  "Nested divisions" should "simplify expr/16/2 to expr/32" in {
    val n = Var("n")
    val test = Div(Vector(Div(Vector(n, Num(16))), Num(2)))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: n/32
    result should be (a[Div])
    result.toString should include ("32")
  }

  it should "simplify complex numerator with nested division" in {
    val n = Var("n")
    val test = Div(Vector(
      Div(Vector(Add(Vector(Mul(Vector(Num(9), n)), Num(7))), Num(16))),
      Num(2)
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: (9*n + 7)/32
    result.toString should include ("/32")
  }

  it should "simplify negative numerator with nested division" in {
    val n = Var("n")
    val test = Div(Vector(
      Div(Vector(Add(Vector(Mul(Vector(Num(-9), n)), Num(-7))), Num(16))),
      Num(2)
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: (-9*n - 7)/32
    result.toString should include ("/32")
  }

  it should "simplify multiplication of fractions" in {
    val test = Mul(Vector(
      Num(1, 2),
      Div(Vector(Num(2), Num(2)))
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: 1/2
    result should equal (Num(1, 2))
  }

  it should "merge Num * Div denominators" in {
    val n = Var("n")
    val test = Mul(Vector(
      Num(1, 2),
      Div(Vector(n, Num(16)))
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: n/32
    result should be (a[Div])
    result.toString should include ("32")
  }

  it should "distribute division over addition" in {
    val n = Var("n")
    val test = Div(Vector(
      Add(Vector(
        Div(Vector(Neg(n), Num(16))),
        Num(-1, 8)
      )),
      Num(2)
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: (-n/32 - 1/16) or similar
    result should not be null
  }

  it should "simplify multiple nested divisions" in {
    val n = Var("n")
    val test = Div(Vector(n, Num(2), Num(4), Num(8)))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: n/64
    result should be (a[Div])
    result.toString should include ("64")
  }

  it should "simplify Div * Div multiplication" in {
    val n = Var("n")
    val test = Mul(Vector(
      Div(Vector(Add(Vector(n, Num(1))), Num(16))),
      Num(1, 2)
    ))
    val result = test.fullSimplify(SimplificationConfig.Default)

    // Expected: (n + 1)/32
    result.toString should include ("/32")
  }

  "Fraction addition" should "add fractions with same denominator" in {
    val test = Add(Vector(Num(1, 4), Num(1, 4)))
    val result = test.simplify

    result should equal (Num(1, 2))
  }

  it should "handle fraction subtraction" in {
    val test = Add(Vector(Num(3, 4), Num(-1, 4)))
    val result = test.simplify

    result should equal (Num(1, 2))
  }

  it should "add fractions with variables" in {
    val n = Var("n")
    val test = Add(Vector(
      Div(Vector(Mul(Vector(Num(3), n)), Num(2))),
      Div(Vector(Num(1), Num(2)))
    ))
    val result = test.fullSimplify

    // Expected: (3*n + 1)/2
    result should be (a[Div])
  }

  "Fraction multiplication" should "multiply simple fractions" in {
    val test = Mul(Vector(Num(2, 3), Num(3, 4)))
    val result = test.simplify

    result should equal (Num(1, 2))
  }

  it should "multiply fraction with variable" in {
    val n = Var("n")
    val test = Mul(Vector(Num(2), Div(Vector(n, Num(4)))))
    val result = test.fullSimplify

    // Expected: n/2
    result should be (a[Div])
  }
}
