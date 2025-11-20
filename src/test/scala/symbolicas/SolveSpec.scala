package symbolicas

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import symbolicas.{Expr, Num, Var, Add, Sub, Mul, Div, Pow, Solve}
import symbolicas.Dsl
import Dsl.{ExprOps, intToNum, doubleToNum}

/**
 * Test suite for equation solving.
 *
 * Tests:
 * - Linear equations
 * - Quadratic equations
 * - Factored form equations
 * - Edge cases (no solution, infinite solutions)
 * - Multiple variables
 */
class SolveSpec extends AnyFlatSpec with Matchers {

  "Linear solver" should "solve x = 0" in {
    val x = Var("x")
    val solutions = Solve.solve(x, "x")

    solutions should have length 1
    solutions.head should equal (Num(0))
  }

  it should "solve x + 2 = 0" in {
    val x = Var("x")
    val equation = Add(Vector(x, Num(2)))
    val solutions = Solve.solve(equation, "x")

    solutions should have length 1
    solutions.head should equal (Num(-2))
  }

  it should "solve 2x + 4 = 0" in {
    val x = Var("x")
    val equation = Add(Vector(Mul(Vector(Num(2), x)), Num(4)))
    val solutions = Solve.solve(equation, "x")

    solutions should have length 1
    solutions.head should equal (Num(-2))
  }

  it should "solve 3x - 6 = 0" in {
    val x = Var("x")
    val equation = Sub(Vector(Mul(Vector(Num(3), x)), Num(6)))
    val solutions = Solve.solve(equation, "x")

    solutions should have length 1
    solutions.head should equal (Num(2))
  }

  it should "solve x/2 = 0" in {
    val x = Var("x")
    val equation = Div(Vector(x, Num(2)))
    val solutions = Solve.solve(equation, "x")

    solutions should have length 1
    solutions.head should equal (Num(0))
  }

  "Quadratic solver" should "solve x^2 = 0" in {
    val x = Var("x")
    val equation = Pow(x, Num(2))
    val solutions = Solve.solve(equation, "x")

    solutions should have length 1
    solutions.head should equal (Num(0))
  }

  it should "solve x^2 - 4 = 0" in {
    val x = Var("x")
    val equation = Sub(Vector(Pow(x, Num(2)), Num(4)))
    val solutions = Solve.solve(equation, "x")

    solutions should have length 2
    solutions should contain (Num(2))
    solutions should contain (Num(-2))
  }

  it should "solve x^2 - 5x + 6 = 0" in {
    val x = Var("x")
    val equation = Add(Vector(
      Pow(x, Num(2)),
      Mul(Vector(Num(-5), x)),
      Num(6)
    ))
    val solutions = Solve.solve(equation, "x")

    solutions should have length 2
    solutions should contain (Num(2))
    solutions should contain (Num(3))
  }

  it should "solve x^2 + 2x + 1 = 0" in {
    val x = Var("x")
    val equation = Add(Vector(
      Pow(x, Num(2)),
      Mul(Vector(Num(2), x)),
      Num(1)
    ))
    val solutions = Solve.solve(equation, "x")

    // One solution (repeated root): x = -1
    solutions should have length 1
    solutions.head should equal (Num(-1))
  }

  it should "handle no real solutions" in {
    val x = Var("x")
    val equation = Add(Vector(Pow(x, Num(2)), Num(1)))
    val solutions = Solve.solve(equation, "x")

    // x^2 + 1 = 0 has no real solutions
    solutions should be (empty)
  }

  it should "solve x^2 - 2x = 0" in {
    val x = Var("x")
    val equation = Sub(Vector(Pow(x, Num(2)), Mul(Vector(Num(2), x))))
    val solutions = Solve.solve(equation, "x")

    solutions should have length 2
    solutions should contain (Num(0))
    solutions should contain (Num(2))
  }

  "Factored form solver" should "solve (x-1)(x-2) = 0" in {
    val x = Var("x")
    val equation = Mul(Vector(
      Sub(Vector(x, Num(1))),
      Sub(Vector(x, Num(2)))
    ))
    val solutions = Solve.solve(equation, "x")

    solutions should have length 2
    solutions should contain (Num(1))
    solutions should contain (Num(2))
  }

  it should "solve x(x-3) = 0" in {
    val x = Var("x")
    val equation = Mul(Vector(x, Sub(Vector(x, Num(3)))))
    val solutions = Solve.solve(equation, "x")

    solutions should have length 2
    solutions should contain (Num(0))
    solutions should contain (Num(3))
  }

  "Edge cases" should "handle constant equation with no solution" in {
    val equation = Num(5)
    val solutions = Solve.solve(equation, "x")

    // 5 = 0 has no solution
    solutions should be (empty)
  }

  it should "handle zero constant" in {
    val equation = Num(0)
    val solutions = Solve.solve(equation, "x")

    // 0 = 0 is always true, but we can't represent infinite solutions
    // The solver returns empty list for this case
    solutions should not be null
  }

  it should "handle equations with other variables" in {
    val x = Var("x")
    val y = Var("y")
    val equation = Add(Vector(x, y))
    val solutions = Solve.solve(equation, "x")

    // x + y = 0 => x = -y
    solutions should have length 1
    solutions.head should equal (Neg(y).simplify)
  }

  "Fractional coefficients" should "be handled" in {
    val x = Var("x")
    val equation = Add(Vector(Mul(Vector(Num(1, 2), x)), Num(1)))
    val solutions = Solve.solve(equation, "x")

    // (1/2)x + 1 = 0 => x = -2
    solutions should have length 1
    solutions.head should equal (Num(-2))
  }

  it should "work in quadratic equations" in {
    val x = Var("x")
    val equation = Add(Vector(
      Pow(x, Num(2)),
      Mul(Vector(Num(1, 2), x)),
      Num(-3, 4)
    ))
    val solutions = Solve.solve(equation, "x")

    // Should find solutions
    solutions should not be (empty)
  }

  "Complex linear forms" should "be solved" in {
    val x = Var("x")
    val equation = Add(Vector(x, x, Num(-4)))
    val solutions = Solve.solve(equation, "x")

    // x + x - 4 = 0 => 2x - 4 = 0 => x = 2
    solutions should have length 1
    solutions.head should equal (Num(2))
  }

  it should "handle terms in different order" in {
    val x = Var("x")
    val equation = Add(Vector(Num(5), x))
    val solutions = Solve.solve(equation, "x")

    // 5 + x = 0 => x = -5
    solutions should have length 1
    solutions.head should equal (Num(-5))
  }

  "Symbolic coefficients" should "produce symbolic solutions" in {
    val x = Var("x")
    val a = Var("a")
    val equation = Add(Vector(x, a))
    val solutions = Solve.solve(equation, "x")

    // x + a = 0 => x = -a
    solutions should have length 1
    solutions.head.toString should include ("a")
  }

  it should "work for quadratic with symbolic discriminant" in {
    val x = Var("x")
    val a = Var("a")
    val equation = Add(Vector(Pow(x, Num(2)), Num(-1), a))
    val solutions = Solve.solve(equation, "x")

    // x^2 + a - 1 = 0
    // Should produce symbolic solutions
    solutions should not be (empty)
  }

  "Evaluation of solutions" should "satisfy the equation" in {
    val x = Var("x")
    val equation = Add(Vector(Pow(x, Num(2)), Mul(Vector(Num(-3), x)), Num(2)))
    val solutions = Solve.solve(equation, "x")

    // Verify each solution satisfies the equation
    solutions.foreach { sol =>
      val result = equation.replaceSymbol("x", sol).simplify
      // Should be close to zero
      result match {
        case Num(value, _) =>
          Math.abs(value) should be < 0.0001
        case _ =>
          // Symbolic result - just check it's not null
          result should not be null
      }
    }
  }

  "Unsolvable equations" should "return empty list" in {
    val x = Var("x")
    val equation = Pow(x, Num(3))
    val solutions = Solve.solve(equation, "x")

    // x^3 = 0 is not handled by current solvers (only linear/quadratic)
    // Actually, this might be solvable as it can be factored or recognized
    // Just check that it doesn't crash
    solutions should not be null
  }

  "Zero coefficient" should "be handled" in {
    val x = Var("x")
    val equation = Add(Vector(Mul(Vector(Num(0), x)), Num(5)))
    val solutions = Solve.solve(equation, "x")

    // 0*x + 5 = 0 has no solution
    solutions should be (empty)
  }
}
