package garden.xeno.symbolum

import org.scalacheck.Gen
import org.scalatest.propspec.AnyPropSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

/**
 * Properties the canonical form must hold for every expression, not only for the ones somebody
 * thought to write down.
 *
 * Each of these guards an assumption the simplifier is built on, and each of them was false
 * before the rewrite:
 *
 *  - simplification is idempotent, so `fullSimplify` converges instead of oscillating;
 *  - it preserves value, so no rule is silently wrong;
 *  - it is invariant under the order of commutative operands, so like terms cannot be missed
 *    because the factors arrived in a different order;
 *  - it is reproducible, so the same input never prints two ways.
 */
class CanonicalFormSpec extends AnyPropSpec with ScalaCheckPropertyChecks with Matchers {

  /** Well above the default of 10: these properties are cheap and their value is in coverage. */
  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 5000)

  private val Tolerance = 1e-8
  private val sample = Map("x" -> 1.7, "y" -> 2.3)

  private val atom: Gen[Expr] = Gen.oneOf(
    Gen.choose(-6, 6).map(Num(_)),
    Gen.choose(-6, 6).flatMap(n => Gen.choose(1, 6).map(d => Num(n, d))),
    Gen.oneOf(Var("x"), Var("y"))
  )

  /** Bounded depth keeps the number of terms after distribution well under the default ceiling. */
  private def expression(depth: Int): Gen[Expr] =
    if (depth <= 0) atom
    else {
      val child = expression(depth - 1)
      Gen.oneOf(
        atom,
        Gen.listOfN(2, child).map(cs => Add(cs.toVector)),
        Gen.listOfN(2, child).map(cs => Sub(cs.toVector)),
        Gen.listOfN(2, child).map(cs => Mul(cs.toVector)),
        child.flatMap(c => Gen.choose(1, 6).map(d => Div(Vector(c, Num(d))))),
        child.map(Neg(_)),
        child.flatMap(c => Gen.choose(0, 3).map(e => Pow(c, Num(e)))),
        child.map(Cos(_)),
        child.map(Sin(_))
      )
    }

  private val expressions: Gen[Expr] = expression(4)

  /**
   * A generated tree can be one the algebra system refuses, and refusing is not a failure here.
   *
   * `ExpressionError` is the live case: simplification can reach a division by zero that the tree
   * did not contain. The `IllegalArgumentException` arm covers the `require`s on the node
   * constructors, none of which this generator can currently trip; it stays because a property test
   * that dies with a stack trace instead of skipping a sample is the harder failure to read.
   */
  private def attempt(body: => Expr): Option[Expr] =
    try Some(body)
    catch {
      case _: IllegalArgumentException => None
      case _: ExpressionError => None
    }

  /**
   * Whether the two sides can be compared at all: see [[EvaluationBounds]]. A trigonometric
   * function applied to something enormous makes both sides correct and unequal.
   */
  private def comparable(e: Expr): Boolean = EvaluationBounds.comparable(e, sample)

  private def valueAt(e: Expr): Option[Double] =
    try {
      val v = e.eval(sample)
      if (v.isNaN || v.isInfinite) None else Some(v)
    } catch {
      case _: ArithmeticException => None
      case _: ExpressionError => None
    }

  /**
   * How much floating-point error the comparison must allow.
   *
   * Expansion is exact in the coefficients but not in the evaluation: `(x - 3)^18` expands to
   * nineteen terms of order 1e10 whose sum is of order 1, and no double arithmetic recovers the
   * cancelled digits. The bound for summation error is proportional to the sum of the term
   * magnitudes, so that, and not the magnitude of the result, is the right scale.
   */
  private def errorScale(e: Expr): Double = e match {
    case Add(terms) =>
      terms.foldLeft(1.0)((acc, t) => acc + valueAt(t).fold(0.0)(math.abs))

    // A cancelling sum keeps its conditioning when it is negated or divided: the digits are lost
    // in the sum, and dividing the result afterwards does not recover them. Matching only `Add`
    // at the top read the scale off the small final value instead, which is the magnitude of the
    // result and precisely what the paragraph above says is the wrong scale.
    //
    // Found on 2026-09-07 by a generated case, `(-6/5 + y)^3^2^3`, whose simplified form is a sum
    // with a term for every power of `y` it reaches, coefficients up to 1e18, over the numeral
    // 3814697265625. Seed -1600853951632219810.
    case Neg(inner) => errorScale(inner)

    // And through a product, where the error of each factor is multiplied by the size of the
    // others: a cancelling sum times a large coefficient loses the sum's digits at the
    // coefficient's scale. Found on 2026-10-22 by a generated case, `(x + 1^0 + y - 5) *
    // -5^2^3^2`, whose sum is exactly zero at the sample point and whose evaluation left one unit
    // in the last place of it, 2^-52, times 5^12 = 244140625: 5.4e-8 against a tolerance of 1e-8,
    // because a product fell through to the case below and read the scale off its own value.
    case Mul(factors) if factors.nonEmpty => factors.foldLeft(1.0)((acc, f) => acc * errorScale(f))

    case Div(parts) if parts.nonEmpty =>
      val divisor = parts.tail.foldLeft(1.0)((acc, p) => acc * valueAt(p).fold(1.0)(math.abs))

      if (divisor == 0.0 || divisor.isNaN || divisor.isInfinite) errorScale(parts.head)
      else math.max(1.0, errorScale(parts.head) / divisor)

    case other => math.max(1.0, valueAt(other).fold(0.0)(math.abs))
  }

  /**
   * The case that made this suite fail at random, pinned so that it cannot come back unseen.
   *
   * `(-6/5 + y)^3^2^3` is `(-6/5 + y)` raised to the eighteenth, and its simplified form is a sum
   * with a term for every power of `y` from the zeroth to that one, coefficients reaching 1e18,
   * over the numeral 3814697265625. At the sample point the terms are of order 1e9 and their sum
   * is about 5.6, so roughly nine digits go in the cancellation and no double arithmetic recovers
   * them. Before 2026-09-08 the value property scaled its tolerance by the magnitude of the
   * result, which asserted a precision the arithmetic cannot deliver and failed for a reason that
   * has nothing to do with whether simplification preserved the value.
   *
   * The two bounds below are measured, not deduced. Reading them off the printed coefficients gave
   * 1e15 and was wrong by six orders of magnitude: the coefficients are divided by a numeral and
   * evaluated at y = 2.3, and neither of those is visible in the printed form.
   *
   * Kept as a named case rather than as a seed because a seed pins the generator and this pins the
   * shape: any future generator that reaches a cancelling sum under a division meets the same
   * question, and the answer is here.
   */
  property("a cancelling sum under a division is compared at the precision it can deliver") {
    val base = Add(Vector(Num(-6, 5), Var("y")))
    val expr = Pow(Pow(Pow(base, Num(3)), Num(2)), Num(3))
    val simplified = expr.fullSimplify

    val original = valueAt(expr).getOrElse(fail("the compact form does not evaluate"))
    val result = valueAt(simplified).getOrElse(fail("the expanded form does not evaluate"))

    // The two facts that make the case what it is, asserted rather than described: the expansion
    // really does carry terms astronomically larger than the result, and the scale the comparison
    // now uses really does see them through the division.
    withClue(s"$simplified\n") {
      errorScale(simplified) should be > 1e9
      math.max(1.0, math.abs(result)) should be < 1e3

      math.abs(original - result) should be < Tolerance * errorScale(simplified)
    }
  }

  /**
   * The case that made the value property fail on 2026-10-22, pinned for the reason the one above
   * is: a cancelling sum, here exactly zero at the sample point, multiplied by a coefficient of
   * 244140625, so one unit in the last place of the sum is 5.4e-8 after the product. The scale has
   * to see the coefficient through the product, which is what the `Mul` case of `errorScale` is for.
   *
   * Simplified under `Minimal`, because that is a rule set keeping the product the generator found,
   * `244140625 * (x + y - 4)`; `factoring` keeps it too. The default rules distribute it into
   * `244140625 * x + 244140625 * y - 976562500`, a sum whose `Add` case sees the coefficient on its
   * own, and the first version of this pin simplified that way: measured on 2026-11-05, it stayed
   * green with the `Mul` case deleted. So the pin asserts the shape first, both sides a product,
   * and then that the scale of each side sees the coefficient, which is what fails without the case.
   */
  property("a cancelling sum under a product is compared at the precision it can deliver") {
    val x = Var("x")
    val y = Var("y")
    val expr = Mul(Vector(
      Sub(Vector(Add(Vector(x, Pow(Num(1), Num(0)), y)), Num(5))),
      Pow(Pow(Pow(Num(-5), Num(2)), Num(3)), Num(2))
    ))
    val simplified = expr.fullSimplify(SimplificationConfig.Minimal)
    val original = valueAt(expr).getOrElse(fail("the compact form does not evaluate"))
    val result = valueAt(simplified).getOrElse(fail("the simplified form does not evaluate"))
    withClue(s"$expr  ->  $simplified\n") {
      // what makes the case: both sides are products, so no `Add` at the top supplies the scale
      simplified shouldBe a[Mul]
      expr shouldBe a[Mul]
      // the result is zero to within rounding, and the scale of each side sees the coefficient
      math.abs(result) should be < 1e-6
      errorScale(simplified) should be > 2e8
      errorScale(expr) should be > 2e8
      math.abs(original - result) should be < Tolerance * math.max(errorScale(expr), errorScale(simplified))
    }
  }

  /**
   * The shape a generated property found and this spec's own generator cannot reach: it divides
   * only by numerals, so a quotient with a symbolic denominator never appeared here. Pinned by
   * name because a random property tells you that something is wrong, and a named case tells the
   * next reader what was wrong.
   */
  property("a coefficient is collected through a symbolic denominator") {
    val x = Var("x")
    val expr = Pow(Add(Vector(Div(Vector(Num(3), x)), Pow(x, Num(-1)))), Num(3))
    val once = expr.simplify

    once.toString shouldBe "64/x^3"
    once.simplify should equal (once)
  }

  property("simplification is idempotent") {
    forAll(expressions) { expr =>
      attempt(expr.simplify).foreach { once =>
        once.simplify should equal (once)
      }
    }
  }

  property("fullSimplify reaches a fixpoint") {
    forAll(expressions) { expr =>
      attempt(expr.fullSimplify).foreach { settled =>
        settled.fullSimplify should equal (settled)
      }
    }
  }

  property("expansion is idempotent") {
    forAll(expressions) { expr =>
      attempt(expr.expand).foreach { once =>
        once.expand should equal (once)
      }
    }
  }

  property("simplification preserves value") {
    forAll(expressions) { expr =>
      for {
        simplified <- attempt(expr.simplify)
        if comparable(expr) && comparable(simplified)
        original <- valueAt(expr)
        result <- valueAt(simplified)
      } withClue(s"$expr  ->  $simplified\n") {
        math.abs(original - result) should be < Tolerance * errorScale(simplified)
      }
    }
  }

  property("full simplification preserves value") {
    forAll(expressions) { expr =>
      for {
        simplified <- attempt(expr.fullSimplify)
        if comparable(expr) && comparable(simplified)
        original <- valueAt(expr)
        result <- valueAt(simplified)
      } withClue(s"$expr  ->  $simplified\n") {
        // The same scale its sibling above uses, and for the same reason. This property was
        // scaling by the magnitude of the result, which is what makes a cancelling sum fail for a
        // reason that has nothing to do with whether simplification preserved the value.
        math.abs(original - result) should be < Tolerance * errorScale(simplified)
      }
    }
  }

  // Compared with approxEqual rather than ==: a literal outside the exact rational regime, such
  // as sin(-3), makes coefficient arithmetic non-associative, so the two orders can differ in the
  // last bit of a double. That is a property of floating point, not of the canonical form, and no
  // ordering can remove it. Structure and every exact coefficient must still agree exactly.
  property("the order of the terms of a sum does not matter") {
    forAll(expressions, expressions) { (left, right) =>
      for {
        forwards <- attempt(Add(Vector(left, right)).simplify)
        backwards <- attempt(Add(Vector(right, left)).simplify)
      } withClue(s"$forwards\n$backwards\n") {
        forwards.approxEqual(backwards) should be (true)
      }
    }
  }

  property("the order of the factors of a product does not matter") {
    forAll(expressions, expressions) { (left, right) =>
      for {
        forwards <- attempt(Mul(Vector(left, right)).simplify)
        backwards <- attempt(Mul(Vector(right, left)).simplify)
      } withClue(s"$forwards\n$backwards\n") {
        forwards.approxEqual(backwards) should be (true)
      }
    }
  }

  /**
   * The case that `property("the order of the factors of a product does not matter")` found by
   * sampling, written down so that it is checked on every run and not on the runs where the
   * generator happens to reach it.
   *
   * It is here rather than as a pinned seed because a seed pins the whole population: the
   * properties above are meant to keep sampling, and what has to stop being a matter of luck is
   * this pair of expressions. The seed that produced it was -1627756496053566947, recorded in case
   * somebody wants the rest of that run.
   *
   * What makes it the interesting case rather than one more pair: `cos(-2 + 4/3)` is irrational,
   * so its coefficient lands in [[Rational]]'s inexact regime and every operation on it afterwards
   * is plain double arithmetic. The two `y^2` coefficients are then the same quantity reached by
   * two routes, 0x1.db405eb27add4p-2 and 0x1.db405eb27add0p-2, and adding the contributions in
   * arrival order left 2^-52 of one of them standing. That is a term present in one canonical form
   * and absent from the other, which `approxEqual` cannot see past, because the two forms differ in
   * shape and not in value.
   *
   * The assertion is equality of the two canonical forms and not `approxEqual`, deliberately:
   * approximate agreement is what the property above asks for and it is the weaker question. What
   * broke here is that one ordering produced a term the other did not, and only equality says that
   * did not happen.
   *
   * It was watched failing on 2026-09-16 against the unrepaired `collectLikeTerms`, with this file
   * exactly as it is and only that function's fold put back: it printed
   * `+ 2.220446049250313E-16 * y^2` on one side and nothing on the other, which is the difference
   * the report carries and not a nearby one. Written down because a guard seen only passing is a
   * guard nobody has pointed at the defect it names.
   */
  property("a product whose coefficients cancel inexactly is the same both ways round") {
    // The trees the generator actually built, not a rebuild from the printed form. The printer is
    // lossy about shape -- `y - cos(x) - -1 + x` does not say how it nests -- and a rebuild from it
    // simplified to something that agreed both ways round, so the first version of this test passed
    // against the unrepaired code. These came out of a run with the seed, dumped structurally.
    val left = Mul(Vector(
      Sub(Vector(
        Var("y"),
        Sub(Vector(Cos(Var("x")), Add(Vector(Num(-1), Var("x")))))
      )),
      Add(Vector(
        Cos(Add(Vector(Num(-2), Num(4, 3)))),
        Add(Vector(Mul(Vector(Var("y"), Num(4))), Div(Vector(Num(-5), Num(4)))))
      ))
    ))
    val right = Sub(Vector(
      Pow(Sub(Vector(Var("y"), Div(Vector(Num(-4), Num(4))))), Num(2)),
      Var("y")
    ))

    Mul(Vector(left, right)).simplify should equal (Mul(Vector(right, left)).simplify)
  }

  /**
   * The residual the first repair left, found by permuting multisets of coefficients rather than
   * by sampling expressions: 20000 multisets drawn from a population deliberately holding both
   * regimes, 2091 of them summing two ways under an order that was the value alone.
   *
   * A stable sort leaves arrival order standing on a tie, and a tie between two DIFFERENT
   * fractions is reachable across the exactness limit: `2^54 / 2^55` normalises to the inexact
   * `(0.5, 1.0)` and one half to the exact `(1.0, 2.0)`, one double and two numbers. Summed with a
   * second exact half the total is `1.5` where the inexact one arrives in the middle and `3/2`
   * where it arrives last, and those are two canonical forms of one expression.
   *
   * The assertion is equality for the reason the test above gives: the two sums agree as values
   * and differ as terms, so anything approximate calls them the same and the reproducibility this
   * file exists for does not.
   *
   * Watched failing on 2026-09-16 against the order that was the value alone, with this file as it
   * is: `Vector(1.5 * y, 3 * y/2) had size 2 instead of expected size 1`, which names both shapes.
   */
  property("a coefficient tie across the exactness limit is summed the same way round") {
    val big = math.pow(2, 54)
    val inexactHalf = Num.fromFraction(Rational.normalize(big, big * 2))
    val exactHalf = Num.fromFraction(Rational.normalize(1.0, 2.0))
    Rational.value(inexactHalf.fraction) shouldEqual Rational.value(exactHalf.fraction)
    inexactHalf.fraction should not equal exactHalf.fraction

    val y = Var("y")
    def scaled(c: Num): Expr = Mul(Vector(c, y))
    val terms = Vector(exactHalf, inexactHalf, exactHalf).map(scaled)

    terms.permutations.map(p => Add(p).simplify).toVector.distinct should have size 1
  }

  property("the order of exact terms does not matter, exactly") {
    val exact = Gen.oneOf(
      Gen.choose(-6, 6).map(n => Num(n): Expr),
      Gen.choose(-6, 6).flatMap(n => Gen.choose(1, 6).map(d => Num(n, d): Expr)),
      Gen.oneOf(Var("x"), Var("y"))
    )
    forAll(exact, exact, exact) { (a, b, c) =>
      Add(Vector(a, b, c)).simplify should equal (Add(Vector(c, a, b)).simplify)
      Mul(Vector(a, b, c)).simplify should equal (Mul(Vector(c, a, b)).simplify)
    }
  }

  property("simplification is reproducible") {
    forAll(expressions) { expr =>
      for {
        first <- attempt(expr.fullSimplify)
        second <- attempt(expr.fullSimplify)
      } first.toString should equal (second.toString)
    }
  }

  /**
   * The rule sets whose combinations are most likely to fight each other: factoring is the
   * inverse of distribution, and the cosine product-to-sum identity rewrites a product into a sum
   * that the sum rules then rearrange.
   */
  private val ruleSets: List[(String, SimplificationConfig)] = List(
    "default" -> SimplificationConfig.Default,
    "minimal" -> SimplificationConfig.Minimal,
    "aggressive" -> SimplificationConfig.Aggressive,
    "collatz0" -> SimplificationConfig.Collatz0,
    "none" -> SimplificationConfig.None,
    "factoring" -> SimplificationConfig.Default.withoutRule(SimplificationRule.DistributeProduct)
  )

  property("a sum whose terms share two factors is factored in one pass, not two") {
    // The generated counterexample, kept as an example because a seed is not a regression test.
    // `CanonicalFormSpec` found this after some thousands of random cases on 2026-09-12 and the
    // next run would have had a different seed; what has to survive is the CASE.
    //
    // `factorCommonTerms` pulled one common factor per call, so terms sharing two needed two
    // passes and `simplify`, which is one pass and whose docstring promises that applying it again
    // changes nothing, was not idempotent. It predates the two rewrites of `Canonical.scala` that
    // landed earlier the same day: the identical output came back from a build at `f2d4c8e`, which
    // is how it was attributed rather than guessed at.
    val x = Var("x")
    val y = Var("y")
    val config = SimplificationConfig.Default.withoutRule(SimplificationRule.DistributeProduct)
    val counterexample = Add(
      Vector(
        Pow(Mul(Vector(Div(Vector(Num(-4), Pow(Num(5), Num(3)))), y, x)), Num(1)),
        Mul(Vector(Neg(Mul(Vector(x, y))), Sub(Vector(Num(-6), x))))
      )
    )

    val once = counterexample.simplify(config)
    once.simplify(config) should equal (once)
  }

  property("factoring a shared factor does not take one a term has not got") {
    // The repair's own hazard, asserted because the obvious version of it is wrong. `shared` is
    // built with `contains` and carries no multiplicity, so for `x*x*y + x*y` it reads `[x, x, y]`;
    // pulling all of it at once would take an `x` the second term has not got and give `2*x*x*y`
    // for `x*y*(x + 1)`. The fix recurses instead, recomputing the shared set against the actual
    // remainders, and this is the case that tells the two apart.
    val x = Var("x")
    val y = Var("y")
    val config = SimplificationConfig.Default.withoutRule(SimplificationRule.DistributeProduct)
    val shared = Add(Vector(Mul(Vector(x, x, y)), Mul(Vector(x, y))))

    val simplified = shared.simplify(config)
    simplified.eval(Map("x" -> 2.0, "y" -> 3.0)) shouldBe 18.0 +- Tolerance
    simplified.simplify(config) should equal (simplified)
  }

  property("simplification is idempotent under every rule set") {
    forAll(expressions) { expr =>
      ruleSets.foreach { case (name, config) =>
        attempt(expr.simplify(config)).foreach { once =>
          withClue(s"[$name] $expr\n") {
            once.simplify(config) should equal (once)
          }
        }
      }
    }
  }

  property("simplification preserves value under every rule set") {
    forAll(expressions) { expr =>
      ruleSets.foreach { case (name, config) =>
        for {
          simplified <- attempt(expr.fullSimplify(config))
          if comparable(expr) && comparable(simplified)
          original <- valueAt(expr)
          result <- valueAt(simplified)
        } withClue(s"[$name] $expr  ->  $simplified\n") {
          // both sides are evaluated in floating point, so the allowance is the worse of the two
          math.abs(original - result) should be < Tolerance * math.max(errorScale(expr), errorScale(simplified))
        }
      }
    }
  }

  property("a simplified numeric literal is in lowest terms") {
    forAll(Gen.choose(-40, 40), Gen.choose(1, 40)) { (numerator: Int, denominator: Int) =>
      val n = Num(numerator, denominator)
      n.denominator should be > 0.0
      Rational.gcd(n.numerator, n.denominator) should (equal (1.0) or equal (0.0))
    }
  }
}
