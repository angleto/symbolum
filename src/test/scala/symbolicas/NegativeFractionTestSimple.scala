package symbolicas

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Simple focused test to debug negative fraction simplification issue.
 */
class NegativeFractionTestSimple extends AnyFlatSpec with Matchers {

  "Negative fraction simplification" should "work for (-1 - 1 * n)/8" in {
    // Build the expression: (-1 - 1 * n)/8
    val n = Var("n")
    val minusOne = Num(-1)
    val minusOneTimesN = Mul(Vector(Num(-1), n))
    val numerator = Add(Vector(minusOne, minusOneTimesN))
    val denominator = Num(8)
    val division = Div(Vector(numerator, denominator))

    println("=== Original Expression ===")
    println(s"Structure: $division")
    println(s"Display: ${division.toString}")

    // Simplify
    val simplified = division.simplify(SimplificationConfig.Default)
    println("\n=== After simplify() ===")
    println(s"Structure: $simplified")
    println(s"Display: ${simplified.toString}")
    println(s"Type: ${simplified.getClass.getSimpleName}")

    // Full simplify
    val fullSimplified = division.fullSimplify(SimplificationConfig.Default)
    println("\n=== After fullSimplify() ===")
    println(s"Structure: $fullSimplified")
    println(s"Display: ${fullSimplified.toString}")
    println(s"Type: ${fullSimplified.getClass.getSimpleName}")

    // Check if it's a Mul with -1 as first factor
    fullSimplified should be (a[Mul])
    val mulExpr = fullSimplified.asInstanceOf[Mul]
    mulExpr.factors.head should equal (Num(-1))
  }

  "Negative fraction in larger multiplication" should "work for (-1 - 1 * n)/8 * x * y" in {
    // Build: (-1 - 1 * n)/8 * x * y
    val n = Var("n")
    val x = Var("x")
    val y = Var("y")
    val numerator = Add(Vector(Num(-1), Mul(Vector(Num(-1), n))))
    val division = Div(Vector(numerator, Num(8)))
    val multiplication = Mul(Vector(division, x, y))

    println("\n=== Original Mul Expression ===")
    println(s"Structure: $multiplication")
    println(s"Display: ${multiplication.toString}")

    // Full simplify
    val fullSimplified = multiplication.fullSimplify(SimplificationConfig.Default)
    println("\n=== After fullSimplify() ===")
    println(s"Structure: $fullSimplified")
    println(s"Display: ${fullSimplified.toString}")

    // Should have -1 as a factor
    fullSimplified should be (a[Mul])
    val mulExpr = fullSimplified.asInstanceOf[Mul]
    mulExpr.factors should contain (Num(-1))

    // Should NOT contain the original Div with negative numerator
    println("\n=== Checking factors ===")
    mulExpr.factors.foreach { factor =>
      println(s"Factor: $factor (${factor.getClass.getSimpleName})")
      factor match {
        case Div(Vector(Add(terms), _)) =>
          // If there's a Div with Add numerator, check if all terms are negative
          val allNegative = terms.forall {
            case Num(n, _) if n < 0 => true
            case Mul(factors) if factors.nonEmpty && factors.head.isInstanceOf[Num] =>
              factors.head.asInstanceOf[Num].numerator < 0
            case _ => false
          }
          allNegative should be (false) // Should NOT have all negative terms
        case _ => // OK
      }
    }
  }
}
