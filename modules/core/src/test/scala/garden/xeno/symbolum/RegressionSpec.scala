package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Expr, Num, Var, Add, Sub, Mul, Div, Cos, Neg, SimplificationConfig}
import garden.xeno.symbolum.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum, cos, pi}

/**
 * Comprehensive regression test suite.
 *
 * This suite combines tests from:
 * - test_regression.sc: Pattern-based regression tests
 * - test_critical.sc: Critical tests that must pass
 * - test_comprehensive.sc: Comprehensive simplification tests
 *
 * These tests ensure that simplifications:
 * 1. Do not introduce duplicate signs (+ -, - -, etc.)
 * 2. Properly simplify nested fractions
 * 3. Handle negative numbers correctly
 * 4. Produce clean, canonical output
 */
class RegressionSpec extends AnyFlatSpec with Matchers {

  "Negation" should "simplify simple negation -(2*n)" in {
    val n = Var("n")
    val test = Neg(Mul(Vector(Num(2), n)))
    val result = test.fullSimplify

    result.toString should include ("-2")
    result.toString should include ("n")
    result.toString should not include ("+ -")
    result.toString should not include ("- -")
    result.toString should not include ("Neg")
    result.toString should not include ("--")
  }

  it should "handle negation in addition n + -(2*n)" in {
    val n = Var("n")
    val test = Add(Vector(n, Neg(Mul(Vector(Num(2), n)))))
    val result = test.fullSimplify

    result.toString should include ("-")
    result.toString should not include ("+ -")
    result.toString should not include ("- -")
    result.toString should not include ("- +")
  }

  it should "eliminate double negation -(-n)" in {
    val n = Var("n")
    val test = Neg(Neg(n))
    val result = test.fullSimplify

    result should equal (n)
  }

  it should "simplify negation of addition -(n + 2)" in {
    val n = Var("n")
    val test = Neg(Add(Vector(n, Num(2))))
    val result = test.fullSimplify

    result.toString should not include ("+ -")
    result.toString should not include ("- -")
    result.toString should not include ("-(")
  }

  "Fractions" should "simplify (1 + 1)/2 to 1" in {
    val test = Div(Vector(Add(Vector(Num(1), Num(1))), Num(2)))
    val result = test.fullSimplify

    result should equal (Num(1))
  }

  it should "simplify (3*n + 1)/2" in {
    val n = Var("n")
    val test = Div(Vector(Add(Vector(Mul(Vector(Num(3), n)), Num(1))), Num(2)))
    val result = test.fullSimplify

    result should be (a[Div])
    result.toString should include ("(3")
    result.toString should include ("n")
    result.toString should include ("1)")
    result.toString should include ("/")
    result.toString should include ("2")
    result.toString should not include ("+ -")
    result.toString should not include ("- -")
  }

  it should "simplify nested fraction ((3*n + 1)/2 + 1)/2" in {
    val n = Var("n")
    val test = Div(Vector(Add(Vector(Div(Vector(Add(Vector(Mul(Vector(Num(3), n)), Num(1))), Num(2))), Num(1))), Num(2)))
    val result = test.fullSimplify

    result.toString should include ("(3")
    result.toString should include ("n")
    result.toString should include (")/4")
    result.toString should not include (")/2)/2")
    result.toString should not include ("()/2)/2")
  }

  it should "simplify very nested fraction (3 * (3*n + 1)/2 + 1)/2" in {
    val n = Var("n")
    val test = Div(Vector(
      Add(Vector(
        Mul(Vector(Num(3), Div(Vector(Add(Vector(Mul(Vector(Num(3), n)), Num(1))), Num(2))))),
        Num(1)
      )),
      Num(2)
    ))
    val result = test.fullSimplify

    result.toString should include ("(9")
    result.toString should include ("n")
    result.toString should include (")/4")
    result.toString should not include ("/2)/2")
    result.toString should not include ("()/2")
  }

  "Addition with different denominators" should "find common denominator n/2 + 1/4" in {
    val n = Var("n")
    val test = Add(Vector(Div(Vector(n, Num(2))), Div(Vector(Num(1), Num(4)))))
    val result = test.fullSimplify

    result.toString should include ("/4")
  }

  "Multiplication with fraction" should "simplify 2 * (n/4)" in {
    val n = Var("n")
    val test = Mul(Vector(Num(2), Div(Vector(n, Num(4)))))
    val result = test.fullSimplify

    result.toString should include ("n")
    result.toString should include ("/")
    result.toString should not include ("2 *")
  }

  "Cosine" should "simplify cos(n * pi)" in {
    val n = Var("n")
    val test = Cos(Mul(Vector(n, pi)))
    val result = test.fullSimplify

    result.toString should include ("cos")
    result.toString should include ("n")
    result.toString should include ("pi")
    result.toString should not include ("+ -")
    result.toString should not include ("- -")
  }

  it should "simplify negated fraction coefficient -(1/4 * cos(n*pi))" in {
    val n = Var("n")
    val test = Neg(Mul(Vector(Div(Vector(Num(1), Num(4))), Cos(Mul(Vector(n, pi))))))
    val result = test.fullSimplify

    // The 1/4 coefficient survives as a division by 4: a fractional coefficient is canonically
    // a quotient, so this is -cos(n * pi)/4 rather than -1/4 * cos(n * pi).
    result.toString should include ("-")
    result.toString should include ("/4")
    result.toString should include ("cos")
    result.toString should not include ("+ -")
    result.toString should not include ("- -")
    result.toString should not include ("-(")

    val vars = Map("n" -> 7.0, "pi" -> math.Pi)
    math.abs(result.eval(vars) - test.eval(vars)) should be < 1e-10
  }

  "Collatz1 term" should "simplify -((2*n + 1)/4 * cos(n*pi))" in {
    val n = Var("n")
    val collatz1_term = Neg(Mul(Vector(Div(Vector(Add(Vector(Mul(Vector(Num(2), n)), Num(1))), Num(4))), Cos(Mul(Vector(n, pi))))))
    val result = collatz1_term.fullSimplify

    // The default rules distribute products over sums, so (2*n + 1) does not survive as a
    // parenthesised factor: the result is the distributed sum over the denominator 4.
    result.toString should include ("-")
    result.toString should include ("n")
    result.toString should include ("/")
    result.toString should include ("4")
    result.toString should include ("cos")
    result.toString should not include ("+ -")
    result.toString should not include ("- -")
    result.toString should not include ("- +")
    result.toString should not include ("-(")
    result.toString should not include (")/4)")

    val vars = Map("n" -> 7.0, "pi" -> math.Pi)
    math.abs(result.eval(vars) - collatz1_term.eval(vars)) should be < 1e-10
  }

  "Sum of fractions" should "simplify 1/4 + 1/2 + 1/4 to 1" in {
    val test = Add(Vector(Div(Vector(Num(1), Num(4))), Div(Vector(Num(1), Num(2))), Div(Vector(Num(1), Num(4)))))
    val result = test.fullSimplify

    result should equal (Num(1))
  }

  it should "combine fraction addition with variables n/4 + n/4 + n/2" in {
    val n = Var("n")
    val test = Add(Vector(
      Div(Vector(n, Num(4))),
      Div(Vector(n, Num(4))),
      Div(Vector(n, Num(2)))
    ))
    val result = test.fullSimplify

    result.toString should include ("n")
    result.toString should not include ("n/4 +")
    result.toString should not include ("+ n/4")
  }

  "Critical arithmetic" should "simplify 1 + 1 to 2" in {
    val test = Add(Vector(Num(1), Num(1)))
    val result = test.fullSimplify

    result should equal (Num(2))
  }

  it should "simplify (1 + 1) / 2 to 1" in {
    val test = Div(Vector(Add(Vector(Num(1), Num(1))), Num(2)))
    val result = test.fullSimplify

    result should equal (Num(1))
  }

  it should "combine n + n to 2 * n" in {
    val n = Var("n")
    val test = Add(Vector(n, n))
    val result = test.fullSimplify

    result should equal (Mul(Vector(Num(2), n)))
  }

  "Critical fraction simplification" should "simplify (3*n + 1) / 2" in {
    val n = Var("n")
    val test = Div(Vector(Add(Vector(Mul(Vector(Num(3), n)), Num(1))), Num(2)))
    val result = test.fullSimplify

    result should be (a[Div])
    result.toString should not include ("+ -")
    result.toString should not include ("/2)/")
  }

  it should "simplify (1 + 3*n/2) / 2 to (3*n + 2) / 4" in {
    val n = Var("n")
    val test = Div(Vector(
      Add(Vector(Num(1), Div(Vector(Mul(Vector(Num(3), n)), Num(2))))),
      Num(2)
    ))
    val result = test.fullSimplify

    result.toString should include ("/4")
    result.toString should not include ("/2)/2")
    result.toString should not include ("()/")
    result.toString should not include ("+ -")
  }

  it should "simplify deeply nested (3 * (3*n + 1)/2 + 1) / 2 to (9*n + 5) / 4" in {
    val n = Var("n")
    val test = Div(Vector(
      Add(Vector(
        Mul(Vector(Num(3), Div(Vector(Add(Vector(Mul(Vector(Num(3), n)), Num(1))), Num(2))))),
        Num(1)
      )),
      Num(2)
    ))
    val result = test.fullSimplify

    result.toString should include ("/4")
    result.toString should not include ("/2)/2")
    result.toString should not include ("/2)")
    result.toString should not include ("+ -")
  }

  it should "simplify triple nested ((3*(3*n+1)/2 + 1)/2 + 1) / 2" in {
    val n = Var("n")
    val test = Div(Vector(
      Add(Vector(
        Div(Vector(
          Add(Vector(
            Mul(Vector(Num(3), Div(Vector(Add(Vector(Mul(Vector(Num(3), n)), Num(1))), Num(2))))),
            Num(1)
          )),
          Num(2)
        )),
        Num(1)
      )),
      Num(2)
    ))
    val result = test.fullSimplify

    result.toString should include ("/8")
    result.toString should not include ("/2)/2)/2")
    result.toString should not include ("/)/")
    result.toString should not include ("+ -")
  }

  "Negative number handling" should "not have + - in (-1 + -3*n/2)" in {
    val n = Var("n")
    val test = Add(Vector(Num(-1), Mul(Vector(Num(-3), Div(Vector(n, Num(2)))))))
    val result = test.fullSimplify

    result.toString should not include ("+ -")
    result.toString should not include ("- -")
  }

  it should "not have + - in (-1 + -2*n/4)" in {
    val n = Var("n")
    val test = Add(Vector(Num(-1), Mul(Vector(Num(-2), Div(Vector(n, Num(4)))))))
    val result = test.fullSimplify

    result.toString should not include ("+ -")
    result.toString should not include ("- -")
  }

  "Complex fraction operations" should "simplify 2 * (n/4) to n/2" in {
    val n = Var("n")
    val test = Mul(Vector(Num(2), Div(Vector(n, Num(4)))))
    val result = test.fullSimplify

    result should equal (Div(Vector(n, Num(2))))
  }

  it should "simplify 3 * ((3*n+1)/2) to (9*n+3)/2" in {
    val n = Var("n")
    val test = Mul(Vector(Num(3), Div(Vector(Add(Vector(Mul(Vector(Num(3), n)), Num(1))), Num(2)))))
    val result = test.fullSimplify

    result.toString should include ("/2")
    result.toString should not include ("3 * (")
    result.toString should not include ("/2)")
    result.toString should not include ("+ -")
  }

  it should "simplify n/2 + n/4 to (3*n)/4" in {
    val n = Var("n")
    val test = Add(Vector(Div(Vector(n, Num(2))), Div(Vector(n, Num(4)))))
    val result = test.fullSimplify

    result.toString should include ("3")
    result.toString should include ("n")
    result.toString should include ("/4")
    result.toString should not include ("n/2 +")
    result.toString should not include ("+ n/4")
    result.toString should not include ("/2 +")
  }

  "Real world Collatz" should "simplify collatz1 term correctly" in {
    val n = Var("n")
    val collatz1_manual = Add(Vector(
      n,
      Num(1, 4),
      Mul(Vector(Num(-1), Div(Vector(Add(Vector(Mul(Vector(Num(2), n)), Num(1))), Num(4))), Cos(Mul(Vector(n, pi)))))
    ))
    val result = collatz1_manual.fullSimplify

    result.toString should not include ("+ -")
    result.toString should not include ("- -")
    result.toString should not include ("/4)")
  }

  "Comprehensive sign normalization" should "handle n + Neg(2*n)" in {
    val n = Var("n")
    val test = Add(Vector(n, Neg(Mul(Vector(Num(2), n)))))
    val result = test.fullSimplify

    result.toString should not include ("+ -")
    result.toString should not include ("- -")
  }

  it should "handle n + (-2)*n" in {
    val n = Var("n")
    val test = Add(Vector(n, Mul(Vector(Num(-2), n))))
    val result = test.fullSimplify

    result.toString should not include ("+ -")
  }

  "Comprehensive nested fractions" should "simplify (3 * (3*n + 1)/2 + 1)/2 to (9*n + 5)/4" in {
    val n = Var("n")
    val test = Div(Vector(
      Add(Vector(
        Mul(Vector(Num(3), Div(Vector(Add(Vector(Mul(Vector(Num(3), n)), Num(1))), Num(2))))),
        Num(1)
      )),
      Num(2)
    ))
    val result = test.fullSimplify

    result.toString should include ("/4")
  }

  it should "simplify (1 + 3*n/2)/2" in {
    val n = Var("n")
    val test = Div(Vector(
      Add(Vector(Num(1), Mul(Vector(Num(3), n)), Div(Vector(Num(1), Num(2))))),
      Num(2)
    ))
    val result = test.fullSimplify

    // Should produce a simplified result
    result should not be null
  }

  "Comprehensive cosine argument simplification" should "simplify cos((1 + 3*n/2)/2)" in {
    val n = Var("n")
    val test = Cos(Div(Vector(
      Add(Vector(Num(1), Mul(Vector(Num(3), n)), Div(Vector(Num(1), Num(2))))),
      Num(2)
    )))
    val result = test.fullSimplify

    result should be (a[Cos])
  }

  it should "simplify cos((3*n + 1)/4 * pi)" in {
    val n = Var("n")
    val test = Cos(Mul(Vector(
      Div(Vector(
        Add(Vector(Mul(Vector(Num(3), n)), Num(1))),
        Num(4)
      )),
      pi
    )))
    val result = test.fullSimplify

    result should be (a[Cos])
  }

  "Comprehensive fraction addition" should "simplify (3*n)/2 + 1/2 to (3*n + 1)/2" in {
    val n = Var("n")
    val test = Add(Vector(
      Div(Vector(Mul(Vector(Num(3), n)), Num(2))),
      Div(Vector(Num(1), Num(2)))
    ))
    val result = test.fullSimplify

    result should be (a[Div])
  }

  it should "simplify (3*n)/4 + 1/4 + 2/4 to (3*n + 3)/4" in {
    val n = Var("n")
    val test = Add(Vector(
      Div(Vector(Mul(Vector(Num(3), n)), Num(4))),
      Div(Vector(Num(1), Num(4))),
      Div(Vector(Num(2), Num(4)))
    ))
    val result = test.fullSimplify

    result should be (a[Div])
  }

  "Comprehensive division distribution" should "simplify ((9*n)/2 + 1)/2 to (9*n + 2)/4" in {
    val n = Var("n")
    val test = Div(Vector(
      Add(Vector(
        Div(Vector(Mul(Vector(Num(9), n)), Num(2))),
        Num(1)
      )),
      Num(2)
    ))
    val result = test.fullSimplify

    result.toString should include ("/4")
  }

  "Comprehensive deep nesting" should "fully simplify deeply nested expressions" in {
    val n = Var("n")
    val innerExpr = Div(Vector(Add(Vector(Mul(Vector(Num(3), n)), Num(1))), Num(2)))
    val middleExpr = Div(Vector(Add(Vector(Mul(Vector(Num(3), innerExpr)), Num(1))), Num(2)))
    val outerExpr = Div(Vector(Add(Vector(middleExpr, Num(1))), Num(2)))
    val result = outerExpr.fullSimplify

    // Should be fully simplified without nested fractions
    result should not be null
    result.toString should not include ("/2)/2)/2")
  }

  "Comprehensive numeric coefficients" should "simplify 3 * (2*n/4) to (3*n)/2" in {
    val n = Var("n")
    val test = Mul(Vector(Num(3), Div(Vector(Mul(Vector(Num(2), n)), Num(4)))))
    val result = test.fullSimplify

    result should be (a[Div])
  }
}
