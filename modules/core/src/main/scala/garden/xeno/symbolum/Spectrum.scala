package garden.xeno.symbolum

import org.jtransforms.fft.DoubleFFT_1D

/**
 * The discrete Fourier transform of a real signal, at the sizes a screening loop actually uses.
 *
 * A signal arrives as `n` samples and leaves as `n` complex numbers, `X[m] = sum_k x[k]
 * exp(-2 pi i m k / n)`, unscaled. That is numpy's `fft` convention exactly, sign and all, and the
 * agreement is deliberate rather than incidental: the work this was built for reads its spectra out
 * of `numpy.fft`, and a transform that differed by a conjugation or by a factor of `n` would agree
 * with it on every magnitude and disagree on every phase. [[Spectrum.ofReal]] is `numpy.rfft`, the
 * same numbers with the redundant half not returned.
 *
 * == Why a library, and which one ==
 *
 * Nothing here is written. `org.jtransforms.fft.DoubleFFT_1D` is a split-radix transform with the
 * cache blocking and the twiddle-factor tables that make four million points take under a second;
 * the textbook recursion takes minutes at that size and is not a thing to hand-write for the sake
 * of having written it. What this file adds is the two things a library does not: a refusal
 * surface, and an outcome type that cannot be misread.
 *
 * **It was `breeze.signal.fourierTr` until 2026-09-16, and JTransforms is what that called.** The
 * paragraph that used to be here refused to reach past Breeze to it, on the ground that it would
 * mean depending on a library Breeze is entitled to change underneath. That ground is gone with
 * Breeze: this module no longer depends on it at all, so JTransforms is a declared dependency
 * rather than somebody else's implementation detail, and what was a reach past a library is now a
 * call to the one that is there. What removed Breeze was its weight rather than this file, which is
 * `build.sbt`'s argument and `docs/numerics.md`'s table.
 *
 * The move is numerically free and was measured rather than assumed: over signals at fourteen
 * lengths from 1 to 4096, power-of-two and not, [[of]]'s output is **bit-identical** to what
 * `fourierTr` returned, because `fourierTr` reached the same routine of the same library. At
 * `n = 2^22` it is also faster, 897 ms against 2017 ms best of three on a machine under load,
 * which is what dropping the interleaving and the four million boxed results buys. That pair was
 * timed with the buffer filled by a loop rather than by the copy [[of]] commits to, which the note
 * there measures at 0.9% of the call.
 *
 * The decision is recorded in `build.sbt` beside the dependency. `Relation` stays exact and is not
 * moved onto this: it works at hundreds of digits, where `Double` has sixteen and the whole method
 * stops meaning anything.
 *
 * == This is a measurement, and it is never a proof ==
 *
 * `modules/core` is the untrusted half, and this file is the most untrusted thing in it. A bin is
 * the sum of four million rounded products, so its error grows with `n` and the small bins of a
 * signal with a large one in it carry almost no information at all. Two spectra agreeing bin by
 * bin is **agreement in numbers**, reported as such, and no path exists from here to a theorem: no
 * library anywhere produces `|- det (A * B) = det A * det B`, and the module graph is what stops
 * anyone trying. `NumericIsolationSpec` asserts it rather than trusting it.
 *
 * == What an absent answer is ==
 *
 * Its own outcome. A signal with a `NaN` in it produces a spectrum of `NaN`s from any transform in
 * the world, and a caller reading those magnitudes gets numbers out of a question that was never
 * asked. [[Unusable]] says so and names the sample. It is not the same answer as a bin that came
 * out at zero, which is a measurement: a constant signal has `n` in bin zero and an exact zero in
 * every other, and that is the transform doing its job.
 *
 * == Why `IArray` and not `Vector` ==
 *
 * Because a spectrum of four million bins is two of these, and the difference is not small.
 * Measured on 2026-09-12 at `n = 2^22`, holding one and collecting everything else: an
 * `IArray[Double]` retains **35 MB** where a `Vector[Double]` retains **115 MB**, because the
 * second boxes every sample. Building one took a best of **10.5 ms** against **271 ms**, and
 * reading every entry a best of **43 ms** against **306 ms**, over five rounds each on a machine
 * at load 48. A pair of vectors for one spectrum is therefore 230 MB and half a second of
 * allocation before any transform happens.
 *
 * `IArray` costs nothing for that, because it is the primitive array with no mutation in its
 * surface: immutable in, immutable out, and no caller can write to a bin. The one place a mutable
 * `Array` exists is inside [[of]], where the transform writes its answer over its input; it is
 * built there, handed to the library, and unreachable afterwards.
 *
 * What this does **not** cover is the copy that costs. A caller holding an `Array[Double]` it owns
 * gets in for nothing, since `IArray.unsafeFromArray` wraps rather than copies, but the copy **in**
 * to the transform's buffer is real: the buffer is `2n` doubles because the answer is complex, and
 * no transform in the world reads an immutable sequence, so the alternative is not a cheaper call
 * but no call.
 *
 * == What is not here ==
 *
 * The inverse transform. `DoubleFFT_1D.complexInverse` is one line away and has **zero** named
 * consumers, so it is not built; the number is written down instead. The same for the
 * two-dimensional transform and for windowing.
 */
object Spectrum {

  /** What the transform produced, or why it produced nothing. */
  sealed trait Outcome

  /**
   * The bins, as two immutable arrays of primitives rather than one sequence of pairs.
   *
   * Not a case class, and the reason is the size. A generated `equals` over four million bins walks
   * all four million on a comparison nobody meant to make, and `IArray` compares by reference
   * anyway, so the generated one would be wrong as well as slow. Comparing two spectra is
   * [[agreesWith]], which says what it compares.
   *
   * `real` and `imaginary` always have the same length.
   */
  final class Bins private[symbolum] (
    val real: IArray[Double],
    val imaginary: IArray[Double]
  ) extends Outcome {

    /** How many bins there are. For [[of]] this is `n`; for [[ofReal]] it is `n / 2 + 1`. */
    def size: Int = real.length

    /** The modulus of one bin, by `hypot` rather than by a sum of squares that can overflow. */
    def magnitude(bin: Int): Double = math.hypot(real(bin), imaginary(bin))

    /**
     * The largest absolute difference between this and another spectrum, bin by bin, or nothing
     * when the two are not the same length.
     *
     * A number, reported as a number. What a caller does with it is a judgement about tolerance,
     * and this file has no opinion on where the line is because the answer depends on `n` and on
     * how large the largest bin is.
     */
    def agreesWith(other: Bins): Option[Double] =
      if (other.size != size) None
      else
        Some(real.indices.foldLeft(0.0) { (worst, bin) =>
          math.max(
            worst,
            math.hypot(real(bin) - other.real(bin), imaginary(bin) - other.imaginary(bin)))
        })
  }

  /**
   * The question could not be put, and this says which part of it.
   *
   * **Not** a spectrum of zeroes, and not a spectrum of `NaN`s. Distinguishing the two is the
   * entire reason this outcome exists: a transform that answered `NaN` would be a refusal wearing
   * the costume of a measurement.
   */
  final case class Unusable(why: String) extends Outcome

  /**
   * Every bin, `n` of them, which is `numpy.fft.fft`.
   *
   * The second half is the conjugate of the first for a real signal, so `X[n - m]` is the conjugate
   * of `X[m]` and half of what comes back is redundant. [[ofReal]] is the same numbers without it.
   * This entry point exists because the transform is often indexed over the whole circle and
   * rewriting that indexing at the call site is how a sign error gets in.
   */
  def of(signal: IArray[Double]): Outcome = refuse(signal).getOrElse {
    val length = signal.length

    // The one mutable value in this file, and it does not leave this expression. `realForwardFull`
    // transforms in place and writes `n` complex numbers as `2n` interleaved doubles, so the buffer
    // is twice the signal, the samples go in its first half and the second half starts at zero;
    // nothing here or anywhere else holds a reference to it afterwards. No transform reads an
    // immutable sequence, so the alternative is not a purer call but no call.
    //
    // `copyToArray` rather than a fill loop, which is what keeps this file inside the property
    // `StyleSpec` asserts for every source under `modules/*/src/main`: no `var`, no `while`, no
    // cast. The buffer's second half is left at the zero `new Array` gives it, which is what the
    // transform wants. Three other ways in were measured and rejected: `Array.copy` does not take
    // an `IArray` without a cast, `IArray.toArray` is deprecated as incorrect and the build takes
    // that as an error, and `IArray.genericWrapArray(_).toArray` wraps before it copies.
    //
    // Measured at `n = 2^22` on 2026-09-17, thread CPU time rather than a wall clock because the
    // machine carried other builds, least of seven interleaved rounds, the fill alone: **13.2 ms**
    // written as a loop, **14.8** for this, 23.8 through the wrapper and 28.4 as an
    // `Array.tabulate` with a branch per entry. Four fills in one interleaved run, which is the
    // only comparison that survives this machine: the loop would buy 12% of a fill, and it would
    // cost an entry in that guard's excuse list. The version that reads as the functional one, the
    // tabulate, is the slowest of the four.
    val buffer = new Array[Double](2 * length)
    signal.copyToArray(buffer)
    new DoubleFFT_1D(length.toLong).realForwardFull(buffer)

    new Bins(
      IArray.tabulate(length)(bin => buffer(2 * bin)),
      IArray.tabulate(length)(bin => buffer(2 * bin + 1)))
  }

  /**
   * Bins `0` to `n / 2` inclusive, which is `numpy.fft.rfft`.
   *
   * `n / 2 + 1` of them, by integer division, so an odd `n` gives `(n + 1) / 2` and there is no
   * Nyquist bin: that is numpy's rule and matching it is the point. Bin zero is the sum of the
   * samples and is always real; for even `n` the last bin is the alternating sum and is also always
   * real. Both come back with an imaginary part that is a rounding error rather than an exact zero,
   * because the transform does not know they are special.
   *
   * **It costs what the whole transform costs**, because it is the whole transform with the second
   * half dropped, and that is now a choice rather than a limit. `realForwardFull` exploits the
   * input being real and then writes the redundant half out anyway; `DoubleFFT_1D.realForward`
   * writes only the half this keeps, in `n` doubles rather than `2n`. It is not taken, and the
   * reason is the layout rather than the saving. Measured on 2026-09-16 rather than read off the
   * documentation: `realForward` puts bin zero's real part at index 0 and then, at index **1**,
   * the Nyquist bin's real part when `n` is even and the **imaginary** part of the last bin when
   * `n` is odd, with every other bin an interleaved pair after that. Two layouts, the odd one
   * holding a number the even one does not, and a misread is a wrong spectrum rather than a slow
   * one. [[of]] is the entry point every caller here goes through and it wants the whole circle,
   * so the unpacked layout is read once and this one drops from it.
   *
   * Measured at `n = 2^22` on 2026-09-16, best of three on a machine under load: **897 ms** end to
   * end, against 2017 ms for the Breeze path this replaced, which is the interleaving and the four
   * million boxed `Complex` results it no longer builds. The 2026-09-12 reading of that path, 1179
   * ms of transform plus 1626 ms of unpacking plus a 362 ms copy in, is what the new number is
   * against. `docs/numerics.md` carries the table.
   */
  def ofReal(signal: IArray[Double]): Outcome = of(signal) match {
    case whole: Bins =>
      val kept = signal.length / 2 + 1
      new Bins(whole.real.take(kept), whole.imaginary.take(kept))
    case refusal => refusal
  }

  /**
   * The reasons the question cannot be put, or nothing when it can.
   *
   * Both are about the input rather than about the transform. An empty signal has no bins and no
   * meaningful answer; a non-finite sample poisons every bin, because each one is a sum over all of
   * them. The second is the one worth the scan: it is cheap, it is `O(n)` against the transform's
   * `O(n log n)`, and without it the failure is silent.
   */
  private def refuse(signal: IArray[Double]): Option[Outcome] =
    if (signal.isEmpty) Some(Unusable("a transform wants at least one sample and was given none"))
    else
      signal.indexWhere(sample => sample.isNaN || sample.isInfinite) match {
        case -1 => None
        case bad =>
          Some(
            Unusable(
              s"sample $bad is ${signal(bad)}, and every bin is a sum over every sample, " +
                "so the whole spectrum would come back non-finite"))
      }
}
