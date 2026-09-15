package garden.xeno.symbolum

import org.scalacheck.{Gen, Shrink}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

/**
 * The Perron root, against matrices whose dominant eigenvalue is known before the code runs.
 *
 * Four kinds of independent answer. A two by two has a closed form, `((a + d) + sqrt((a - d)^2 +
 * 4bc)) / 2`, which this file evaluates itself rather than reading off the decomposition. A
 * row-stochastic matrix has the eigenvalue one exactly, whatever its entries are, because the
 * vector of ones is an eigenvector. The `n` by `n` matrix of ones has the eigenvalue `n` and rank
 * one, so its other eigenvalues are all zero. And a triangular matrix has its eigenvalues on the
 * diagonal, which is where the nilpotent case comes from.
 *
 * The property test uses the bound rather than a closed form: for a matrix with no negative entry
 * the spectral radius lies between the smallest and the largest row sum, which is a theorem about
 * the matrix and knows nothing about how the number was arrived at.
 */
class PerronSpec extends AnyFlatSpec with Matchers with ScalaCheckPropertyChecks {

  private def dominant(outcome: Perron.Outcome): Perron.Dominant = outcome match {
    case found: Perron.Dominant => found
    case other => fail(s"expected a dominant eigenvalue and got $other")
  }

  /** The larger root of the characteristic polynomial of a two by two, written out. */
  private def closedForm(a: Double, b: Double, c: Double, d: Double): Double =
    ((a + d) + math.sqrt((a - d) * (a - d) + 4 * b * c)) / 2

  "The Fibonacci matrix" should "have the golden ratio as its Perron root" in {
    // [[1, 1], [1, 0]] has characteristic polynomial x^2 - x - 1, whose larger root is
    // (1 + sqrt 5) / 2 = 1.6180339887498949. The eigenvector is proportional to (phi, 1).
    val found = dominant(Perron.of(Vector(Vector(1.0, 1.0), Vector(1.0, 0.0))))
    val phi = (1 + math.sqrt(5)) / 2

    found.eigenvalue shouldBe phi +- 1e-14
    found.eigenvector(0) / found.eigenvector(1) shouldBe phi +- 1e-12
    found.eigenvector.forall(_ >= 0) shouldBe true

    // The other root is (1 - sqrt 5) / 2, whose modulus is 1 / phi.
    found.subdominant shouldBe (phi - 1) +- 1e-14
    found.residual should be < 1e-14
  }

  "A row-stochastic matrix" should "have the eigenvalue one, whatever its entries are" in {
    // Every row sums to one, so the vector of ones is an eigenvector for the eigenvalue one, and no
    // eigenvalue of a non-negative matrix exceeds its largest row sum. The answer is one exactly.
    val found = dominant(
      Perron.of(
        Vector(
          Vector(0.1, 0.6, 0.3),
          Vector(0.5, 0.2, 0.3),
          Vector(0.25, 0.25, 0.5))))

    found.eigenvalue shouldBe 1.0 +- 1e-14
    found.eigenvector.foreach(entry => entry shouldBe (1 / math.sqrt(3)) +- 1e-12)
    found.subdominant should be < 1.0
  }

  "The matrix of ones" should "have the eigenvalue n and nothing else at all" in {
    // J_n = 1 1^T has rank one, so its spectrum is n once and zero n - 1 times, and the eigenvector
    // is the vector of ones. n = 64 is here to put a few thousand entries through the library
    // rather than only the four-entry cases above.
    val n = 64
    val found = dominant(Perron.of(Vector.fill(n)(Vector.fill(n)(1.0))))

    found.eigenvalue shouldBe n.toDouble +- 1e-12
    found.subdominant should be < 1e-12
    found.eigenvector.foreach(entry => entry shouldBe (1 / math.sqrt(n.toDouble)) +- 1e-12)

    // Relative to the matrix norm, which for this one is n. Measured at 1.30e-13 absolute, so
    // 2.03e-15 relative, and this is the largest residual any matrix in this file produces: it is
    // the number `Perron.Residual` leaves six orders of magnitude of room above.
    found.residual / n should be < 1e-14
  }

  "A general two by two" should "agree with the closed form" in {
    val cases = Vector(
      (2.0, 3.0, 4.0, 5.0),
      (0.5, 0.25, 1.5, 0.0),
      (10.0, 0.0, 0.0, 3.0),
      (1.0, 1e-6, 1e6, 1.0),
      (0.0, 2.0, 8.0, 0.0)
    )

    for ((a, b, c, d) <- cases) withClue(s"[[$a, $b], [$c, $d]]: ") {
      val found = dominant(Perron.of(Vector(Vector(a, b), Vector(c, d))))
      val expected = closedForm(a, b, c, d)
      found.eigenvalue shouldBe expected +- (math.abs(expected) * 1e-12 + 1e-12)
      found.eigenvector.forall(_ >= -Perron.Negative) shouldBe true
    }
  }

  "A diagonal matrix" should "have its largest diagonal entry, with the axis it sits on" in {
    val found = dominant(Perron.of(Vector(Vector(2.0, 0.0), Vector(0.0, 3.0))))

    found.eigenvalue shouldBe 3.0 +- 1e-14
    found.eigenvector(0) shouldBe 0.0 +- 1e-14
    found.eigenvector(1) shouldBe 1.0 +- 1e-14
    found.subdominant shouldBe 2.0 +- 1e-14
  }

  "A nilpotent matrix" should "come back with an eigenvalue of zero and not with a refusal" in {
    // [[0, 1], [0, 0]] is triangular, so its eigenvalues are both zero: the growth rate really is
    // nothing. That is a computation that SUCCEEDED, and an absent answer is never the same thing
    // as a negative one. A caller that folds it into "no answer" has thrown away a result.
    val found = dominant(Perron.of(Vector(Vector(0.0, 1.0), Vector(0.0, 0.0))))

    found.eigenvalue shouldBe 0.0
    found.subdominant shouldBe 0.0
    found.residual should be < 1e-15
  }

  "The zero matrix" should "do the same" in {
    val found = dominant(Perron.of(Vector(Vector(0.0, 0.0), Vector(0.0, 0.0))))
    found.eigenvalue shouldBe 0.0
    found.eigenvector.forall(_ >= 0) shouldBe true
  }

  "A one by one matrix" should "be its entry, with no subdominant to report" in {
    val found = dominant(Perron.of(Vector(Vector(7.0))))
    found.eigenvalue shouldBe 7.0 +- 1e-14
    found.eigenvector shouldBe Vector(1.0)
    found.subdominant shouldBe 0.0
  }

  "A cyclic permutation matrix" should "have the Perron root one and no separation from it" in {
    // The three by three cycle has the three cube roots of unity as its spectrum, so the Perron
    // root is one and so is the largest modulus among the others. That is not a failure: the
    // eigenvalue is right and the eigenvector is the vector of ones. What the caller learns from
    // `subdominant` is that power iteration on this matrix would never settle.
    val found = dominant(
      Perron.of(
        Vector(
          Vector(0.0, 1.0, 0.0),
          Vector(0.0, 0.0, 1.0),
          Vector(1.0, 0.0, 0.0))))

    found.eigenvalue shouldBe 1.0 +- 1e-14
    found.subdominant shouldBe 1.0 +- 1e-14
    found.eigenvector.foreach(entry => entry shouldBe (1 / math.sqrt(3)) +- 1e-12)
  }

  "The Perron root of a non-negative matrix" should "lie between the smallest and largest row sum" in {
    // 200 matrices of order 2 to 6, which run in about a third of a second. The bound is
    // Frobenius's and is a theorem about the matrix, so it is independent of how the number was
    // computed; the eigenvector's sign is the other half of Perron-Frobenius and is checked with
    // it. Two hundred was chosen by running the same property at 50, 200 and 1000: the coverage of
    // this file stopped moving at 50 and the time was still under a second at 200, so the extra
    // hundred and fifty are sampling the generator rather than the code.
    //
    // Shrinking is off. A shrunk counterexample here is a ragged or empty matrix, which is a
    // refusal rather than the failure that was found, and it would hide the matrix that failed.
    implicit val unshrunk: Shrink[Vector[Vector[Double]]] = Shrink.shrinkAny

    val matrices = for {
      size <- Gen.choose(2, 6)
      entries <- Gen.listOfN(size * size, Gen.choose(0.0, 10.0))
    } yield Vector.tabulate(size, size)((row, column) => entries(row * size + column))

    forAll(matrices, minSuccessful(200)) { (matrix: Vector[Vector[Double]]) =>
      val found = dominant(Perron.of(matrix))
      val sums = matrix.map(_.sum)

      // The residual, computed here rather than read off the outcome: `found.residual` is the
      // implementation's own arithmetic and asserting against it would be asserting that it agrees
      // with itself.
      val v = found.eigenvector
      val worst = matrix.indices.map { row =>
        val applied = v.indices.map(column => matrix(row)(column) * v(column)).sum
        math.abs(applied - found.eigenvalue * v(row))
      }.max

      withClue(s"row sums ${sums.mkString(", ")}, eigenvalue ${found.eigenvalue}: ") {
        found.eigenvalue should be >= (sums.min - 1e-9)
        found.eigenvalue should be <= (sums.max + 1e-9)
        found.eigenvector.min should be >= -Perron.Negative
        worst should be <= (1e-12 * sums.max)
      }
    }
  }

  /* -------------------------------- the gates, driven with decompositions that are wrong */

  /*
   * Everything below goes through `Perron.settle` and `Perron.check` rather than through `of`.
   *
   * It has to. Each of these gates fires only when LAPACK contradicts Perron-Frobenius on a matrix
   * that satisfies its hypotheses, which is not an input a test can supply: `of` refuses every
   * matrix the theorem does not cover before the decomposition runs. The alternative to opening the
   * seam is four branches nothing ever executes, which this repository treats as worse than the
   * code being visible.
   *
   * The matrix reaches those two as the linear map it is, so the identity matrix is `identity` and
   * no test here has to build one.
   */

  private val unchanged: Vector[Double] => Vector[Double] = identity

  "A decomposition with no real eigenvalue at all" should "be undecided rather than answered" in {
    Perron.settle(
      transform = unchanged,
      real = Vector(0.0, 0.0),
      imaginary = Vector(2.0, -2.0),
      vector = _ => Vector(1.0, 0.0),
      scale = 2.0) match {
      case Perron.Undecided(why) =>
        why should include("imaginary part")
        why should include("Perron-Frobenius")
      case other => fail(s"expected an undecided outcome and got $other")
    }
  }

  "A decomposition whose largest modulus is not its largest real eigenvalue" should "be undecided" in {
    // Real eigenvalue 1, complex pair at modulus 5. On a matrix with no negative entry that cannot
    // happen, so if it does the arithmetic is wrong and neither number should be reported.
    Perron.settle(
      transform = unchanged,
      real = Vector(1.0, 3.0, 3.0),
      imaginary = Vector(0.0, 4.0, -4.0),
      vector = _ => Vector(1.0, 0.0),
      scale = 5.0) match {
      case Perron.Undecided(why) =>
        why should include("largest modulus")
        why should include("Perron-Frobenius")
      case other => fail(s"expected an undecided outcome and got $other")
    }
  }

  "A vector that is not an eigenvector" should "be undecided, with the residual it missed by" in {
    // The identity's eigenvalue is 1 and its eigenvectors are everything, so ask for eigenvalue 2
    // instead: the residual is then the whole vector.
    Perron.check(unchanged, eigenvalue = 2.0, raw = Vector(1.0, 1.0), subdominant = 0.0, scale = 1.0) match {
      case Perron.Undecided(why) =>
        why should include("residual")
        why should include("not an eigenvector")
      case other => fail(s"expected an undecided outcome and got $other")
    }
  }

  "An eigenvector with entries of both signs" should "be undecided, because it is not the Perron one" in {
    // (1, -1) is a genuine eigenvector of the identity, and it is not a Perron vector. A degenerate
    // spectral radius is how a matrix with no negative entry could hand one back.
    Perron.check(unchanged, eigenvalue = 1.0, raw = Vector(1.0, -1.0), subdominant = 1.0, scale = 1.0) match {
      case Perron.Undecided(why) =>
        why should include("one sign")
        why should include("Perron vector")
      case other => fail(s"expected an undecided outcome and got $other")
    }
  }

  "A zero eigenvector" should "be undecided rather than normalised into a NaN" in {
    Perron.check(unchanged, eigenvalue = 1.0, raw = Vector(0.0, 0.0), subdominant = 0.0, scale = 1.0) match {
      case Perron.Undecided(why) => why should include("zero vector")
      case other => fail(s"expected an undecided outcome and got $other")
    }
  }

  /* ---------------------------------------------------------------- the refusals */

  "A matrix with a negative entry" should "be refused rather than answered" in {
    // The theorem's hypothesis. Without it this would return the largest-modulus eigenvalue of a
    // matrix the theorem says nothing about, and that number is not a growth rate.
    Perron.of(Vector(Vector(1.0, -2.0), Vector(3.0, 4.0))) match {
      case Perron.Unusable(why) =>
        why should include("(0, 1)")
        why should include("no negative entry")
      case other => fail(s"expected a refusal and got $other")
    }
  }

  "A ragged matrix" should "be refused, naming the row" in {
    Perron.of(Vector(Vector(1.0, 2.0), Vector(3.0))) match {
      case Perron.Unusable(why) =>
        why should include("row 1")
        why should include("square")
      case other => fail(s"expected a refusal and got $other")
    }
  }

  "A matrix with no rows" should "be refused" in {
    Perron.of(Vector.empty[Vector[Double]]) match {
      case Perron.Unusable(why) => why should include("no rows")
      case other => fail(s"expected a refusal and got $other")
    }
  }

  "A matrix with a NaN in it" should "be refused rather than answered with a NaN eigenvalue" in {
    Perron.of(Vector(Vector(1.0, 1.0), Vector(1.0, Double.NaN))) match {
      case Perron.Unusable(why) => why should include("(1, 1)")
      case other => fail(s"expected a refusal and got $other")
    }
  }

  "A matrix with an infinity in it" should "be refused for the same reason" in {
    Perron.of(Vector(Vector(Double.PositiveInfinity, 0.0), Vector(0.0, 1.0))) match {
      case Perron.Unusable(why) => why should include("(0, 0)")
      case other => fail(s"expected a refusal and got $other")
    }
  }

  "The four outcomes" should "be four, so a caller cannot collapse two of them" in {
    // Named rather than counted: the compiler would be happy with three, and the point of this
    // assertion is that a future session reads why there are four before removing one.
    val outcomes: Vector[Perron.Outcome] = Vector(
      Perron.Dominant(1.0, Vector(1.0), 0.0, 0.0),
      Perron.Undecided("the vector is not an eigenvector"),
      Perron.NotConverged("the iteration gave up"),
      Perron.Unusable("there is no matrix here")
    )

    outcomes.map(_.getClass.getSimpleName).distinct should have size 4
  }
}
