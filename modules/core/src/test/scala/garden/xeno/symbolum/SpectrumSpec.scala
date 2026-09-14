package garden.xeno.symbolum

import org.scalacheck.{Gen, Shrink}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

/**
 * The transform, against signals whose spectra are written down rather than computed.
 *
 * Every expected value below comes from the definition, `X[m] = sum_k x[k] exp(-2 pi i m k / n)`,
 * evaluated by hand: a constant signal, an impulse, a shifted impulse, a cosine and a sine at an
 * integer frequency. None of them is the implementation's own output recorded and re-read, which
 * would pass on the day a sign flipped. The shifted impulse in particular is the whole convention
 * in one case: it is the only test here whose expected value changes if the exponent's sign does,
 * and matching `numpy.fft` on it is what makes a spectrum from this repository comparable with one
 * from the work that motivated it.
 *
 * Two structural checks carry the rest. Parseval relates the signal to its spectrum without knowing
 * either, and conjugate symmetry says the second half of a real signal's transform is the first
 * half reflected, which is the fact [[Spectrum.ofReal]] rests on.
 */
class SpectrumSpec extends AnyFlatSpec with Matchers with ScalaCheckPropertyChecks {

  /** Close enough for a transform of this size, where the answer is exact in the reals. */
  private val Tolerance = 1e-10

  private def bins(outcome: Spectrum.Outcome): Spectrum.Bins = outcome match {
    case found: Spectrum.Bins => found
    case other => fail(s"expected a spectrum and got $other")
  }

  "The transform of a constant signal" should "put the whole sum in bin zero and nothing anywhere else" in {
    // sum_k 1 * exp(-2 pi i m k / n) is n at m = 0 and a full turn around the circle otherwise.
    val n = 16
    val spectrum = bins(Spectrum.of(IArray.fill(n)(1.0)))

    spectrum.size shouldBe n
    spectrum.real(0) shouldBe 16.0 +- Tolerance
    spectrum.imaginary(0) shouldBe 0.0 +- Tolerance

    for (m <- 1 until n) withClue(s"bin $m: ") {
      spectrum.magnitude(m) shouldBe 0.0 +- Tolerance
    }
  }

  "The transform of an impulse at the origin" should "be one in every bin" in {
    // x[k] = delta[k], so X[m] = exp(0) = 1 for every m.
    val n = 32
    val spectrum = bins(Spectrum.of(IArray.tabulate(n)(k => if (k == 0) 1.0 else 0.0)))

    for (m <- 0 until n) withClue(s"bin $m: ") {
      spectrum.real(m) shouldBe 1.0 +- Tolerance
      spectrum.imaginary(m) shouldBe 0.0 +- Tolerance
    }
  }

  "The transform of a shifted impulse" should "be the exponential with numpy's sign" in {
    // x[k] = delta[k - 3], so X[m] = exp(-2 pi i m * 3 / n) exactly. This is the convention, and a
    // transform with the opposite sign passes every magnitude test in this file and fails this one.
    val n = 16
    val shift = 3
    val spectrum = bins(Spectrum.of(IArray.tabulate(n)(k => if (k == shift) 1.0 else 0.0)))

    for (m <- 0 until n) withClue(s"bin $m: ") {
      val angle = -2 * math.Pi * m * shift / n
      spectrum.real(m) shouldBe math.cos(angle) +- Tolerance
      spectrum.imaginary(m) shouldBe math.sin(angle) +- Tolerance
    }
  }

  "The transform of a cosine at an integer frequency" should "be n/2 in two bins and zero in the rest" in {
    // cos(t) = (exp(it) + exp(-it)) / 2, so the transform of cos(2 pi q k / n) is n/2 at m = q and
    // n/2 at m = n - q, both real, and exactly zero everywhere else.
    val n = 64
    val q = 5
    val spectrum = bins(Spectrum.of(IArray.tabulate(n)(k => math.cos(2 * math.Pi * q * k / n))))

    spectrum.real(q) shouldBe 32.0 +- Tolerance
    spectrum.imaginary(q) shouldBe 0.0 +- Tolerance
    spectrum.real(n - q) shouldBe 32.0 +- Tolerance
    spectrum.imaginary(n - q) shouldBe 0.0 +- Tolerance

    for (m <- 0 until n if m != q && m != n - q) withClue(s"bin $m: ") {
      spectrum.magnitude(m) shouldBe 0.0 +- Tolerance
    }
  }

  "The transform of a sine at an integer frequency" should "be purely imaginary and antisymmetric" in {
    // sin(t) = (exp(it) - exp(-it)) / 2i, so X[q] = -i n/2 and X[n - q] = +i n/2.
    val n = 64
    val q = 7
    val spectrum = bins(Spectrum.of(IArray.tabulate(n)(k => math.sin(2 * math.Pi * q * k / n))))

    spectrum.real(q) shouldBe 0.0 +- Tolerance
    spectrum.imaginary(q) shouldBe -32.0 +- Tolerance
    spectrum.real(n - q) shouldBe 0.0 +- Tolerance
    spectrum.imaginary(n - q) shouldBe 32.0 +- Tolerance
  }

  "The transform" should "satisfy Parseval on a signal with no closed form at all" in {
    // sum |x|^2 = (1/n) sum |X|^2. It relates the two sides without knowing either, so it holds for
    // a signal nobody can write a spectrum for, which is what makes it worth running.
    val n = 256
    val signal = IArray.tabulate(n)(k => math.sin(k * 0.37) + 0.5 * math.cos(k * 1.9) + 0.01 * k)
    val spectrum = bins(Spectrum.of(signal))

    val energy = signal.map(x => x * x).sum
    val spectral = (0 until n).map(m => math.pow(spectrum.magnitude(m), 2)).sum / n

    spectral shouldBe energy +- (energy * 1e-12)
  }

  it should "be conjugate symmetric, which is the fact the half transform rests on" in {
    val n = 128
    val spectrum =
      bins(Spectrum.of(IArray.tabulate(n)(k => math.exp(-k / 40.0) * math.cos(k * 0.61))))

    for (m <- 1 until n) withClue(s"bin $m against bin ${n - m}: ") {
      spectrum.real(m) shouldBe spectrum.real(n - m) +- Tolerance
      spectrum.imaginary(m) shouldBe -spectrum.imaginary(n - m) +- Tolerance
    }
  }

  "The half transform" should "be the first n/2 + 1 bins of the whole one" in {
    val n = 64
    val signal = IArray.tabulate(n)(k => math.sin(k * 0.29) + k / 17.0)
    val whole = bins(Spectrum.of(signal))
    val half = bins(Spectrum.ofReal(signal))

    half.size shouldBe (n / 2 + 1)
    for (m <- 0 until half.size) withClue(s"bin $m: ") {
      half.real(m) shouldBe whole.real(m)
      half.imaginary(m) shouldBe whole.imaginary(m)
    }
  }

  it should "give (n + 1) / 2 bins at an odd length, which is numpy's rule and not a rounding" in {
    // n = 15 has no Nyquist bin: 15 / 2 + 1 = 8, and the eighth is an ordinary bin rather than the
    // real one an even length ends on.
    val half = bins(Spectrum.ofReal(IArray.tabulate(15)(k => k.toDouble)))
    half.size shouldBe 8
  }

  it should "put the sum of the samples in bin zero" in {
    val signal = IArray(1.0, -2.5, 3.25, 0.5, 7.0, -1.0, 0.0, 2.0)
    val half = bins(Spectrum.ofReal(signal))

    half.real(0) shouldBe signal.sum +- Tolerance
    half.imaginary(0) shouldBe 0.0 +- Tolerance
  }

  "The transform" should "be linear" in {
    // 100 pairs of signals of length 64, which runs in about a third of a second. The transform is
    // linear by construction, so what this probes is the marshalling either side of it, and a
    // hundred samples is where the time stopped being free and the coverage stopped changing.
    //
    // Shrinking is off: a shrunk signal is a shorter one, the three stop agreeing on their length,
    // and what gets reported is an index out of bounds rather than the signals that failed.
    implicit val unshrunk: Shrink[IArray[Double]] = Shrink.shrinkAny

    val samples = Gen
      .listOfN(64, Gen.choose(-10.0, 10.0))
      .map(_.toVector)
      .map(drawn => IArray.tabulate(64)(drawn))

    forAll(samples, samples, Gen.choose(-3.0, 3.0), minSuccessful(100)) {
      (left: IArray[Double], right: IArray[Double], weight: Double) =>
        val combined = bins(Spectrum.of(IArray.tabulate(64)(k => left(k) + weight * right(k))))
        val a = bins(Spectrum.of(left))
        val b = bins(Spectrum.of(right))

        for (m <- 0 until 64) {
          combined.real(m) shouldBe (a.real(m) + weight * b.real(m)) +- 1e-9
          combined.imaginary(m) shouldBe (a.imaginary(m) + weight * b.imaginary(m)) +- 1e-9
        }
    }
  }

  /* ---------------------------------------------------------------- the refusals */

  "An empty signal" should "be refused rather than given an empty spectrum" in {
    Spectrum.of(IArray.empty[Double]) match {
      case Spectrum.Unusable(why) => why should include("none")
      case other => fail(s"expected a refusal and got $other")
    }
  }

  "A signal with a NaN in it" should "be refused, naming the sample" in {
    // The one that matters. Without the scan the transform answers, every bin comes back NaN, and a
    // caller reading magnitudes gets numbers out of a question that was never asked.
    Spectrum.of(IArray(1.0, 2.0, Double.NaN, 4.0)) match {
      case Spectrum.Unusable(why) =>
        why should include("sample 2")
        why should include("every bin")
      case other => fail(s"expected a refusal and got $other")
    }
  }

  "A signal with an infinity in it" should "be refused for the same reason" in {
    Spectrum.ofReal(IArray(0.0, Double.PositiveInfinity)) match {
      case Spectrum.Unusable(why) => why should include("sample 1")
      case other => fail(s"expected a refusal and got $other")
    }
  }

  "A spectrum of zeroes" should "not be a refusal, which is the distinction the outcomes keep" in {
    // The transform of the zero signal is zero in every bin. That is a measurement and it is not
    // the same answer as "there was no measurement", which is the whole shape of this file.
    val spectrum = bins(Spectrum.of(IArray.fill(8)(0.0)))
    spectrum.size shouldBe 8
    for (m <- 0 until 8) spectrum.magnitude(m) shouldBe 0.0
  }

  /* ------------------------------------------------------------ comparing spectra */

  "Two spectra of the same signal" should "agree to nothing at all" in {
    val signal = IArray.tabulate(32)(k => math.cos(k * 0.5))
    val first = bins(Spectrum.of(signal))
    val second = bins(Spectrum.of(signal))

    first.agreesWith(second) shouldBe Some(0.0)
  }

  "Two spectra of different lengths" should "give no comparison rather than a large one" in {
    val short = bins(Spectrum.of(IArray(1.0, 2.0)))
    val long = bins(Spectrum.of(IArray(1.0, 2.0, 3.0, 4.0)))

    short.agreesWith(long) shouldBe None
  }

  "A spectrum that differs in one bin" should "report that difference and no other" in {
    val n = 8
    val flat = bins(Spectrum.of(IArray.fill(n)(1.0)))
    val shifted = bins(Spectrum.of(IArray.tabulate(n)(k => if (k == 0) 1.5 else 1.0)))

    // The two signals differ by half an impulse at the origin, whose transform is 0.5 in every bin.
    flat.agreesWith(shifted).getOrElse(fail("the two spectra are the same length")) shouldBe
      0.5 +- Tolerance
  }
}
