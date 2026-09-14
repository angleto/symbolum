package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.*
import garden.xeno.symbolum.Dsl.*

/**
 * The screen a candidate closed form goes through before anyone spends time on it.
 *
 * Three things have to hold and the third is the one a screen usually lacks: it accepts what is
 * true, it refuses what is false with the point, and it says so when it has stopped being exact
 * rather than reporting the rounding as a verdict.
 */
class CollatzScreenSpec extends AnyFlatSpec with Matchers {

  private val n = Var("n")

  "The residue classes" should "cover every parity path, twice each" in {
    // What the screen rests on. Every class mod 2^k appears, with two representatives, so a
    // candidate affine in `n` that agrees on both agrees on the whole class.
    val points = CollatzScreen.residues(3)

    points.size shouldBe 16
    points.map(_ % 8).distinct.sorted shouldBe (0 to 7).map(BigInt(_)).toVector
    points.foreach(point => point should be > BigInt(0))
    points.groupBy(_ % 8).values.foreach(_.size shouldBe 2)
  }

  "The form this repository ships" should "agree with iteration on every class" in {
    // The must-accept half. `CollatzSeries.symbolic(k)` is the cosine sum over all 2^k parity
    // paths, and `CollatzSeriesSpec` checks it against iteration directly; here it goes through the
    // screen, which is the thing being tested rather than the formula.
    (1 to 3).foreach { k =>
      withClue(s"k = $k: ") {
        CollatzScreen.screenByClass(CollatzSeries.symbolic(k), k) shouldBe
          CollatzScreen.Agreed(BigInt(2).pow(k).toInt * 2)
      }
    }
  }

  it should "agree one step at a time as well, through the identity rather than the sum" in {
    CollatzScreen.screenByClass(CollatzSeries.symbolicStep(n), 1) shouldBe CollatzScreen.Agreed(4)
  }

  "A candidate with the wrong slope" should "be caught, which is what two per class is for" in {
    // The error a plausible formula makes: right on one representative of a class and wrong on the
    // next. `T(n)` is `n / 2` on the even classes, and this candidate agrees with it at `n = 2` and
    // nowhere else in that class, so a screen with one point per class would have passed it.
    val candidate = CollatzSeries.symbolicStep(n) + (n - Num(2)) * (Num(1) - cos(n * pi)) * Num(1, 2)

    CollatzScreen.screen(candidate, 1, Vector(BigInt(2))) shouldBe CollatzScreen.Agreed(1)

    CollatzScreen.screenByClass(candidate, 1) match {
      case CollatzScreen.Disagrees(point, expected, got) =>
        point shouldBe BigInt(3)
        expected shouldBe CollatzSeries.iterate(3, 1)
        got should not be expected
      case other => fail(s"expected a disagreement on the odd class, got $other")
    }
  }

  "A candidate that is simply false" should "come back with the point that shows it" in {
    CollatzScreen.screenByClass(n * Num(3) + Num(1), 1) match {
      case CollatzScreen.Disagrees(point, expected, got) =>
        expected shouldBe CollatzSeries.iterate(point, 1)
        got shouldBe point * 3 + 1
      case other => fail(s"expected a disagreement, got $other")
    }
  }

  "A value past what a double holds exactly" should "be refused rather than compared" in {
    // The refusal that keeps this honest. Beyond 2^53 a double no longer holds consecutive integers
    // apart, so a comparison would be reporting the rounding and not the formula. The screen says
    // which point it stopped at instead of returning a verdict it cannot support.
    val huge = CollatzScreen.Exact * 4

    CollatzScreen.screen(n, 0, Vector(huge)) match {
      case CollatzScreen.NotExact(point, _) => point shouldBe huge
      case other => fail(s"expected a refusal about exactness, got $other")
    }
  }

  it should "be told apart from a candidate that cannot be evaluated at all" in {
    // Two absences that are not each other, which is the rule `Refutation` keeps seven outcomes for.
    CollatzScreen.screen(Num(1) / (n - n), 1, Vector(BigInt(3))) match {
      case CollatzScreen.NotEvaluable(point) => point shouldBe BigInt(3)
      case other => fail(s"expected an inevaluable candidate, got $other")
    }
  }
}
