package garden.xeno.symbolum

import org.scalacheck.Gen
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

/**
 * Every closed form of the Collatz iterate against direct integer iteration.
 *
 * This is the harness that decides whether a formula about the map is an identity, and it is
 * build-failing on purpose: the binomial series that used to be in `CollatzSeries` matched
 * iteration at none of the points it was tried at, and nothing in the build said so. A formula
 * that is repaired by fitting it to this range would be the test satisfying itself, so a change
 * to a form here should come from a derivation on paper and then be judged by this file.
 */
class CollatzSeriesSpec extends AnyFlatSpec with Matchers with ScalaCheckPropertyChecks {

  /** Independent of the object under test. */
  private def direct(n: BigInt, k: Int): BigInt =
    (0 until k).foldLeft(n)((current, _) => if (current % 2 == 0) current / 2 else (3 * current + 1) / 2)

  "Direct iteration" should "follow the trajectory of 7 and bring 27 to 1 in 70 steps" in {
    CollatzSeries.trajectory(7, 7) shouldBe Vector[BigInt](7, 11, 17, 26, 13, 20, 10, 5)
    CollatzSeries.iterate(27, 70) shouldBe BigInt(1)
  }

  "Every form" should "return n itself at k = 0" in {
    // The base case the binomial series failed: its single term carried a cosine of the parity
    // of n where the identity carries none, and it returned 1.75 for n = 1.
    for (n <- 1 to 40) {
      CollatzSeries.closedForm(n, 0).value shouldBe BigInt(n)
      CollatzSeries.cosineSum(n.toLong, 0) shouldBe n.toLong
    }
    CollatzSeries.symbolic(0) shouldBe Var("n")
  }

  "The closed form" should "agree with iteration exhaustively on small inputs" in {
    for (k <- 0 to 12; n <- 1 to 300) {
      val form = CollatzSeries.closedForm(n, k)
      withClue(s"n = $n, k = $k: ") {
        form.value shouldBe direct(n, k)
        form.reconstructed(n, k) shouldBe form.value
      }
    }
  }

  it should "give the worked example (7, 5): 20 with s = 4 and c = 73" in {
    CollatzSeries.closedForm(7, 5) shouldBe CollatzSeries.ClosedForm(20, 4, 73)
  }

  it should "agree with iteration on large starts and long runs" in {
    // 200 cases of a 256-bit start over up to 600 steps run in about a second; the range is the
    // one the reference implementation in the Collatz repository checks.
    val starts = Gen.choose(BigInt(1), BigInt(1) << 256)
    val depths = Gen.choose(0, 600)

    forAll(starts, depths, minSuccessful(200)) { (n, k) =>
      val form = CollatzSeries.closedForm(n, k)
      form.value shouldBe direct(n, k)
      form.reconstructed(n, k) shouldBe form.value
    }
  }

  "The cosine sum" should "agree with iteration on the range the reference checks" in {
    for (k <- 0 to 10; n <- 1 to 80) {
      withClue(s"n = $n, k = $k: ") {
        CollatzSeries.cosineSum(n.toLong, k) shouldBe direct(n, k).toLong
      }
    }
  }

  it should "refuse a depth past its limit rather than return a rounded guess" in {
    an[IllegalArgumentException] should be thrownBy
      CollatzSeries.cosineSum(7, CollatzSeries.MaximumCosineDepth + 1)
  }

  "The one-step identity" should "evaluate to T(n) on both parities" in {
    val environment = (n: Int) => Map("n" -> n.toDouble, "pi" -> math.Pi)

    for (n <- 1 to 60) {
      CollatzSeries.symbolicStep(Var("n")).eval(environment(n)) shouldBe
        direct(n, 1).toDouble +- 1e-9
    }
  }

  "The symbolic iterate" should "evaluate to the integer iterate" in {
    // The expression is what the algebra system simplifies; this is the point where the algebra
    // is tied to the integers, and the only check that a simplification of it preserved the map.
    for (k <- 0 to 4; n <- 1 to 50) {
      val expression = CollatzSeries.symbolic(k)
      val value = expression.eval(Map("n" -> n.toDouble, "pi" -> math.Pi))
      withClue(s"n = $n, k = $k: ") {
        value shouldBe direct(n, k).toDouble +- 1e-7
      }
    }
  }

  it should "still evaluate to the integer iterate after simplification" in {
    for (k <- 1 to 3) {
      val simplified = CollatzSeries.symbolic(k).fullSimplify
      for (n <- List(1, 2, 7, 27, 123)) {
        val value = simplified.eval(Map("n" -> n.toDouble, "pi" -> math.Pi))
        withClue(s"n = $n, k = $k: ") {
          value shouldBe direct(n, k).toDouble +- 1e-7
        }
      }
    }
  }
}
