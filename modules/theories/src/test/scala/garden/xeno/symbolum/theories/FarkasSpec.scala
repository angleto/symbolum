package garden.xeno.symbolum.theories

import org.scalacheck.Gen
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks

/**
 * The untrusted half of linear arithmetic, tested on its own terms.
 *
 * Nothing here can make a false theorem: a wrong answer from this search is refused by the ring
 * step downstream, and the worst it can do is lose a proof. So the assertions are about the two
 * ways it can lose one. A solution that does not solve the system loses it loudly, at the ring
 * step, and the property in the middle is what pins that; a system it declares infeasible when it
 * is not loses it silently, which is why the property generates the solution first and then asks
 * for one back.
 */
class FarkasSpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {

  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 200)

  private def whole(values: Int*): Vector[Rational] = values.toVector.map(v => Rational.of(BigInt(v)))

  private def applied(
    columns: Vector[Vector[Rational]],
    solution: Vector[Rational]
  ): Vector[Rational] =
    columns.zip(solution).foldLeft(Vector.fill(columns.head.length)(Rational.zero)) {
      case (acc, (column, factor)) => acc.zip(column).map { case (a, c) => a + c * factor }
    }

  "A rational" should "stay in lowest terms with the sign on the numerator" in {
    Rational.of(4, 8) shouldBe Rational(1, 2)
    Rational.of(3, -6) shouldBe Rational(-1, 2)
    Rational.of(0, 5) shouldBe Rational.zero
    (Rational.of(1, 3) + Rational.of(1, 6)).toString shouldBe "1/2"
    (Rational.of(2, 3) * Rational.of(3, 2)) shouldBe Rational.one
  }

  it should "refuse a zero denominator rather than carry one" in {
    an[ArithmeticException] should be thrownBy Rational.of(1, 0)
  }

  "The search" should "find the multiplier a single hypothesis needs" in {
    // One unknown, one row: `2 * lambda = 1`, so a half. This is the shape that made the subset
    // enumeration insufficient, in its smallest form.
    Farkas.nonNegativeSolution(Vector(whole(2)), whole(1)) shouldBe Some(Vector(Rational(1, 2)))
  }

  it should "combine two hypotheses when neither will do alone" in {
    // Columns are the hypotheses: `x` and `y`, and the target is `x + 2y`.
    val solution = Farkas.nonNegativeSolution(Vector(whole(1, 0), whole(0, 1)), whole(1, 2))

    solution shouldBe Some(Vector(Rational.one, Rational.of(BigInt(2))))
  }

  it should "give back the same certificate and not merely a valid one" in {
    // `x + y = 1` is solved by every pair between `(1, 0)` and `(0, 1)`, so "it solves the system"
    // is an assertion all of them pass. Bland's rule decides both the entering column and the
    // leaving row, so which one comes back is fixed by the system that was handed in rather than by
    // how the tableau is held, and a caller that stores a certificate and compares it later rests on
    // that. This is what fails if the pivoting order is ever changed, which is a change of
    // behaviour and not of style: the rewrite on 2026-09-12 was checked against the version before
    // it on 78000 answers for exactly this and not for validity.
    val pair = Vector(Vector(Rational.one), Vector(Rational.one))
    val one = Vector(Rational.one)

    Farkas.nonNegativeSolution(pair, one) shouldBe Some(Vector(Rational.one, Rational.zero))

    // And the weighted question leaves that vertex only when the weights give it a reason to.
    Farkas.nonNegativeSolution(pair, one, Vector(Rational.zero, Rational.one)) shouldBe
      Some(Vector(Rational.zero, Rational.one))
    Farkas.nonNegativeSolution(pair, one, Vector(Rational.one, Rational.zero)) shouldBe
      Some(Vector(Rational.one, Rational.zero))
  }

  it should "refuse what would need a negative multiplier" in {
    Farkas.nonNegativeSolution(Vector(whole(1)), whole(-1)) shouldBe None
  }

  it should "refuse a system with no solution at all" in {
    // `lambda = 1` on the first row and `lambda = 2` on the second.
    Farkas.nonNegativeSolution(Vector(whole(1, 1)), whole(1, 2)) shouldBe None
  }

  it should "answer the empty system" in {
    Farkas.nonNegativeSolution(Vector.empty, whole(0, 0)) shouldBe Some(Vector.empty)
    Farkas.nonNegativeSolution(Vector.empty, whole(1)) shouldBe None
  }

  "Clearing the denominators" should "give whole multipliers and the factor they scale by" in {
    Farkas.cleared(Vector(Rational(1, 2), Rational(1, 3))) shouldBe
      ((Vector(BigInt(3), BigInt(2)), BigInt(6)))
    Farkas.cleared(Vector(Rational.one, Rational.zero)) shouldBe
      ((Vector(BigInt(1), BigInt(0)), BigInt(1)))
  }

  "A solution that comes back" should "solve the system it was asked about" in {
    // The generator builds the answer first and multiplies it out, so every system here is
    // feasible by construction and a `None` is a lost proof rather than an honest refusal. Two
    // hundred samples, measured at 140 ms on 2026-09-05; the systems are three rows by four
    // unknowns, which is larger than the goals in `LinarithSpec` and small enough to stay cheap.
    val system = for {
      columns <- Gen.listOfN(4, Gen.listOfN(3, Gen.chooseNum(-4, 4)))
      factors <- Gen.listOfN(4, Gen.chooseNum(0, 3))
    } yield (columns.map(_.toVector.map(v => Rational.of(BigInt(v)))).toVector,
      factors.toVector.map(v => Rational.of(BigInt(v))))

    forAll(system) { case (columns, factors) =>
      val target = applied(columns, factors)
      val solution = Farkas.nonNegativeSolution(columns, target)

      withClue(s"columns $columns, target $target: ") {
        solution shouldBe defined
        solution.foreach { values =>
          values.foreach(value => value.isNegative shouldBe false)
          applied(columns, values) shouldBe target
        }
      }
    }
  }

  it should "clear to whole multipliers that solve the scaled system" in {
    forAll(Gen.listOfN(3, Gen.chooseNum(1, 6))) { denominators =>
      val solution = denominators.toVector.map(d => Rational.of(BigInt(1), BigInt(d)))
      val (whole, scale) = Farkas.cleared(solution)

      whole.zip(solution).foreach { case (value, original) =>
        Rational.of(value) shouldBe original * Rational.of(scale)
      }
    }
  }
  /* ------------------------------------------------------------------ maximising */

  "The largest value of an objective" should "be the vertex the simplex stops at" in {
    // `x + y = 4` with both non-negative: the largest `2x + y` is 8, at the vertex where `y` is
    // nought. Small enough to check by hand, which is the point of having it here as well as in
    // `LinarithSpec`, where the same machinery is asked about a region a caller wrote.
    val columns = Vector(Vector(Rational.one), Vector(Rational.one))
    val target = Vector(Rational.of(4))

    Farkas.maximum(columns, target, Vector(Rational.of(2), Rational.one)) shouldBe
      Farkas.Extreme.At(Rational.of(8))
    Farkas.maximum(columns, target, Vector(Rational.one, Rational.one)) shouldBe
      Farkas.Extreme.At(Rational.of(4))
  }

  it should "say when there is none, and when there is no point at all" in {
    // `x - y = 0` with both non-negative is the ray where they are equal, and `x + y` grows along
    // it for ever. An objective of the wrong length is not a question about a region, so it is
    // refused rather than answered about the columns it does line up with.
    val ray = Vector(Vector(Rational.one), Vector(-Rational.one))

    Farkas.maximum(ray, Vector(Rational.zero), Vector(Rational.one, Rational.one)) shouldBe
      Farkas.Extreme.Unbounded
    Farkas.maximum(ray, Vector(Rational.zero), Vector(Rational.one)) shouldBe
      Farkas.Extreme.Infeasible
  }

}
