package garden.xeno.symbolum

import org.scalacheck.Gen
import org.scalatest.matchers.should.Matchers
import org.scalatest.propspec.AnyPropSpec
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

/**
 * Simplification over the part of the language [[CanonicalFormSpec]] does not generate:
 * quotients by an expression, logarithms, exponentials, and fractional powers.
 *
 * That spec's generator covers sums, products, division by a numeral, integer powers and the two
 * trigonometric functions, and asserts that simplification preserves value over them. The rules
 * for the functions below were never reached by it, so nothing measured whether they preserve
 * value at all.
 *
 * == Where the claim holds, and where it does not ==
 *
 * Several of these rules hold only under a hypothesis the simplifier does not have and cannot
 * record: `exp(log x) = x` needs `x > 0`, `(x^2)^(1/2) = x` needs `x >= 0`, and cancelling a
 * common factor needs that factor to be non-zero.
 *
 * Sampling the variables at positive values is not enough to stay clear of them, which the
 * property demonstrated by failing on `(cos(x)^2)^(1/2)`: the hypothesis is about a subterm, and
 * a subterm of a positive variable is not positive. So the generator does not produce fractional
 * exponents at all, and where a rule turns a defined value into an undefined one the case is
 * skipped by evaluation. What remains is a real check on everything else, and the rules that were
 * excluded are pinned below as examples, which is the only form in which a limit stays true.
 *
 * The limits are then pinned below as examples rather than described in prose, because a limit
 * nobody executes drifts. They are not defects to be fixed here: this is a simplifier, and under
 * the proof assistant it is an oracle whose output is re-proved through the kernel, so a rewrite
 * that needs a side condition costs a failed proof and never a false theorem. They would be
 * defects the moment anything trusted them.
 */
class ValuePreservationSpec extends AnyPropSpec with ScalaCheckPropertyChecks with Matchers {

  /** The properties are cheap and their value is in the shapes they reach. */
  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 2000)

  private val Tolerance = 1e-8
  private val sample = Map("x" -> 1.7, "y" -> 2.3)

  private val atom: Gen[Expr] = Gen.oneOf(
    Gen.choose(1, 5).map(Num(_)),
    Gen.oneOf(Var("x"), Var("y"))
  )

  /**
   * Depth three rather than four.
   *
   * An exponential of an exponential of a sum leaves the range of a double in two levels, and a
   * skipped case measures nothing. Three keeps most samples finite.
   */
  private def expression(depth: Int): Gen[Expr] =
    if (depth <= 0) atom
    else {
      val child = expression(depth - 1)
      Gen.oneOf(
        atom,
        Gen.listOfN(2, child).map(cs => Add(cs.toVector)),
        Gen.listOfN(2, child).map(cs => Mul(cs.toVector)),
        Gen.listOfN(2, child).map(cs => Div(cs.toVector)),
        child.map(Log(_)),
        child.map(Exp(_)),
        // Whole exponents only. A fractional one meets the rewrite `(b^i)^o = b^(i*o)`, which is
        // false for a negative base, and no choice of sample fixes that: the first counterexample
        // the property found was `(cos(x)^2)^(1/2)`, whose base is negative at a positive x. The
        // rule's limit is pinned as an example below instead, where it can be stated exactly.
        child.flatMap(c => Gen.oneOf(Num(2), Num(3), Num(-1)).map(e => Pow(c, e))),
        child.map(Cos(_)),
        child.map(Sin(_))
      )
    }

  private val expressions: Gen[Expr] = expression(3)

  private def attempt(body: => Expr): Option[Expr] =
    try Some(body)
    catch {
      case _: IllegalArgumentException => None
      case _: ExpressionError => None
      case _: ArithmeticException => None
    }

  private def valueAt(e: Expr): Option[Double] =
    try {
      val v = e.eval(sample)
      if (v.isNaN || v.isInfinite) None else Some(v)
    } catch {
      case _: ArithmeticException => None
      case _: ExpressionError => None
    }

  /** See [[EvaluationBounds]]: a trigonometric function of something enormous is not comparable. */
  private def comparable(e: Expr): Boolean = EvaluationBounds.comparable(e, sample)

  private def scale(value: Double): Double = math.max(1.0, math.abs(value))

  property("simplification preserves value over quotients, logarithms and exponentials") {
    forAll(expressions) { expr =>
      for {
        simplified <- attempt(expr.simplify)
        if comparable(expr) && comparable(simplified)
        original <- valueAt(expr)
        result <- valueAt(simplified)
      } withClue(s"$expr  ->  $simplified\n") {
        math.abs(original - result) should be < Tolerance * scale(original)
      }
    }
  }

  property("full simplification preserves value over the same expressions") {
    forAll(expressions) { expr =>
      for {
        simplified <- attempt(expr.fullSimplify)
        if comparable(expr) && comparable(simplified)
        original <- valueAt(expr)
        result <- valueAt(simplified)
      } withClue(s"$expr  ->  $simplified\n") {
        math.abs(original - result) should be < Tolerance * scale(original)
      }
    }
  }

  property("expansion preserves value over the same expressions") {
    forAll(expressions) { expr =>
      for {
        expanded <- attempt(expr.expand)
        if comparable(expr) && comparable(expanded)
        original <- valueAt(expr)
        result <- valueAt(expanded)
      } withClue(s"$expr  ->  $expanded\n") {
        math.abs(original - result) should be < Tolerance * scale(original)
      }
    }
  }

  property("simplification is idempotent over the same expressions") {
    forAll(expressions) { expr =>
      attempt(expr.simplify).foreach(once => once.simplify should equal(once))
    }
  }

  /* ------------------------------------------------------------------- limits */

  property("a power of a power drops the sign of a negative base") {
    // (x^2)^(1/2) is |x|, not x. The rewrite is stated without the hypothesis x >= 0, so at a
    // negative value the two sides differ by a sign rather than by rounding.
    val expr = Pow(Pow(Var("x"), Num(2)), Num(1, 2))
    val simplified = expr.simplify()
    val at = Map("x" -> -2.0)

    expr.eval(at) shouldBe 2.0 +- 1e-9
    simplified.eval(at) shouldBe -2.0 +- 1e-9
  }

  property("cancelling a common factor drops the case where that factor is zero") {
    // (a*x)/(a*y) becomes x/y with no record that a must not be zero. At a = 0 the original is
    // undefined and the simplified form is a perfectly good number.
    val expr = Div(Vector(
      Mul(Vector(Var("a"), Var("x"))),
      Mul(Vector(Var("a"), Var("y")))
    ))
    val simplified = expr.simplify(SimplificationConfig.Default.withRule(SimplificationRule.CancelCommonFactors))
    val at = Map("a" -> 0.0, "x" -> 1.7, "y" -> 2.3)

    an[DivisionByZeroError] should be thrownBy expr.eval(at)
    simplified.eval(at) shouldBe (1.7 / 2.3) +- 1e-9
  }

  property("the inverse of a logarithm drops the case where the argument is not positive") {
    // exp(log x) becomes x, which is defined everywhere while the original is defined only for
    // positive arguments.
    val expr = Exp(Log(Var("x")))
    val simplified = expr.simplify()
    val at = Map("x" -> -2.0)

    an[ArithmeticException] should be thrownBy expr.eval(at)
    simplified.eval(at) shouldBe -2.0 +- 1e-9
  }
}
