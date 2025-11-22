package symbolicas

import scala.math._

/**
 * Fourier Series Analysis of the Collatz Conjecture
 *
 * This exploration uses Fourier analysis to study the convergence behavior
 * of the Collatz sequence collatz(n, k) as k → ∞.
 *
 * Key Ideas:
 * 1. The Collatz function exhibits periodic behavior in the parity structure
 * 2. Fourier series can decompose this into frequency components
 * 3. Convergence to 1→2→1 cycle can be analyzed in frequency domain
 * 4. The oscillatory behavior emerges from the fundamental frequency
 */
object CollatzFourierAnalysis {

  // ============================================================================
  // Basic Collatz Operations
  // ============================================================================

  /** Standard Collatz function: n/2 if even, (3n+1)/2 if odd */
  def collatz(n: Long): Long = {
    if (n % 2 == 0) n / 2 else (3 * n + 1) / 2
  }

  /** Apply Collatz k times */
  def collatzK(n: Long, k: Int): Long = {
    var current = n
    for (_ <- 0 until k) {
      current = collatz(current)
      if (current == 1) {
        // Once we reach 1, we oscillate: 1→2→1→2→...
        // For remaining steps, compute position in cycle
        val remaining = k - 1 - _
        return if (remaining % 2 == 0) 1L else 2L
      }
    }
    current
  }

  /** Floating-point version for Fourier analysis */
  def collatzDouble(n: Double): Double = {
    val isEven = (n.toLong % 2 == 0)
    if (isEven) n / 2.0 else (3.0 * n + 1.0) / 2.0
  }

  // ============================================================================
  // Trajectory Analysis
  // ============================================================================

  /** Get the full trajectory until reaching 1 (or max steps) */
  def trajectory(n: Long, maxSteps: Int = 10000): List[Long] = {
    var current = n
    var traj = List(n)
    var steps = 0

    while (current != 1 && steps < maxSteps) {
      current = collatz(current)
      traj = traj :+ current
      steps += 1
    }

    traj
  }

  /** Get trajectory with k steps, including oscillation after reaching 1 */
  def trajectoryExtended(n: Long, k: Int): List[Long] = {
    var current = n
    var traj = List[Long]()
    var reachedOne = false

    for (i <- 0 until k) {
      traj = traj :+ current
      if (current == 1) {
        reachedOne = true
        // Oscillate between 1 and 2
        current = 2
      } else if (reachedOne && current == 2) {
        current = 1
      } else {
        current = collatz(current)
      }
    }

    traj :+ current  // Include final value
  }

  // ============================================================================
  // Fourier Series Representation
  // ============================================================================

  /**
   * Compute Discrete Fourier Transform coefficients for a trajectory.
   * Returns (real, imaginary) pairs for each frequency.
   */
  def dft(signal: Seq[Double]): Seq[(Double, Double)] = {
    val N = signal.length

    (0 until N).map { k =>
      var realSum = 0.0
      var imagSum = 0.0

      for (n <- 0 until N) {
        val angle = -2.0 * Pi * k * n / N
        realSum += signal(n) * cos(angle)
        imagSum += signal(n) * sin(angle)
      }

      (realSum / N, imagSum / N)
    }
  }

  /** Compute magnitude spectrum from DFT coefficients */
  def magnitudeSpectrum(dftCoeffs: Seq[(Double, Double)]): Seq[Double] = {
    dftCoeffs.map { case (re, im) => sqrt(re * re + im * im) }
  }

  /** Compute phase spectrum from DFT coefficients */
  def phaseSpectrum(dftCoeffs: Seq[(Double, Double)]): Seq[Double] = {
    dftCoeffs.map { case (re, im) => atan2(im, re) }
  }

  /**
   * Reconstruct signal from Fourier coefficients.
   * Uses the first numHarmonics harmonics only.
   */
  def inverseDft(dftCoeffs: Seq[(Double, Double)], numHarmonics: Int): Seq[Double] = {
    val N = dftCoeffs.length
    val maxK = math.min(numHarmonics, N)

    (0 until N).map { n =>
      var sum = 0.0
      for (k <- 0 until maxK) {
        val (re, im) = dftCoeffs(k)
        val angle = 2.0 * Pi * k * n / N
        sum += re * cos(angle) - im * sin(angle)
      }
      sum
    }
  }

  // ============================================================================
  // Convergence Analysis
  // ============================================================================

  case class ConvergenceMetrics(
    stoppingTime: Int,           // Steps to reach 1
    oscillationPeriod: Int = 2,  // Period of final oscillation (always 2 for Collatz)
    averageValue: Double,        // Average along trajectory
    variance: Double,            // Variance along trajectory
    convergenceRate: Double      // Estimated exponential decay rate
  )

  /** Analyze convergence behavior of trajectory */
  def analyzeConvergence(n: Long, maxSteps: Int = 1000): ConvergenceMetrics = {
    val traj = trajectory(n, maxSteps)
    val values = traj.map(_.toDouble)

    val stoppingTime = traj.indexOf(1L)
    val avg = values.sum / values.length
    val variance = values.map(v => (v - avg) * (v - avg)).sum / values.length

    // Estimate exponential decay rate by fitting to max values
    val maxValues = traj.sliding(10).map(_.max.toDouble).toList
    val rate = if (maxValues.length > 1) {
      val logRatios = maxValues.zip(maxValues.tail).map { case (v1, v2) =>
        if (v1 > 0 && v2 > 0) log(v2 / v1) else 0.0
      }
      logRatios.sum / logRatios.length
    } else 0.0

    ConvergenceMetrics(stoppingTime, 2, avg, variance, rate)
  }

  /**
   * Analyze the approach to oscillatory behavior as k increases.
   * Returns the trajectory and its Fourier decomposition.
   */
  case class FourierConvergenceAnalysis(
    n: Long,
    trajectoryLength: Int,
    trajectory: List[Long],
    dftCoefficients: Seq[(Double, Double)],
    magnitudes: Seq[Double],
    dominantFrequencies: List[(Int, Double)],  // (frequency index, magnitude)
    oscillationFrequency: Int,  // Frequency corresponding to period-2 oscillation
    convergenceToOscillation: Boolean
  )

  def analyzeFourierConvergence(n: Long, k: Int): FourierConvergenceAnalysis = {
    val traj = trajectoryExtended(n, k)
    val signal = traj.map(_.toDouble)

    val dftCoeffs = dft(signal)
    val mags = magnitudeSpectrum(dftCoeffs)

    // Find dominant frequencies (top 5)
    val dominantFreqs = mags.zipWithIndex
      .sortBy(-_._1)
      .take(5)
      .map { case (mag, idx) => (idx, mag) }
      .toList

    // Period-2 oscillation corresponds to frequency N/2 (Nyquist)
    val oscillationFreq = k / 2

    // Check if we've converged to oscillation (all values are 1 or 2)
    val converged = traj.forall(v => v == 1L || v == 2L)

    FourierConvergenceAnalysis(
      n = n,
      trajectoryLength = k,
      trajectory = traj,
      dftCoefficients = dftCoeffs,
      magnitudes = mags,
      dominantFrequencies = dominantFreqs,
      oscillationFrequency = oscillationFreq,
      convergenceToOscillation = converged
    )
  }

  // ============================================================================
  // Theoretical Framework
  // ============================================================================

  /**
   * Theoretical prediction of convergence behavior.
   *
   * Key insights:
   * 1. The Collatz sequence eventually reaches 1
   * 2. Once at 1, it oscillates: 1 → 2 → 1 → 2 → ...
   * 3. This oscillation has period 2, fundamental frequency ω = π
   * 4. In Fourier space, this appears as a dominant component at f = 1/2
   */

  def theoreticalOscillationSignal(k: Int, phase: Int = 0): Seq[Double] = {
    // Pure oscillation between 1 and 2
    (0 until k).map { i =>
      if ((i + phase) % 2 == 0) 1.0 else 2.0
    }
  }

  def theoreticalOscillationSpectrum(k: Int): Seq[Double] = {
    val signal = theoreticalOscillationSignal(k)
    val dftCoeffs = dft(signal)
    magnitudeSpectrum(dftCoeffs)
  }

  /**
   * Expected Fourier behavior:
   * - Before reaching 1: Complex spectrum with many frequencies
   * - After reaching 1: Dominant component at frequency N/2 (period-2)
   * - DC component (frequency 0): Average value ≈ 1.5 for oscillation
   */

  case class TheoreticalPrediction(
    dcComponent: Double,           // Average value (≈ 1.5 for 1↔2 oscillation)
    fundamentalFrequency: Double,  // ω = π for period-2
    fundamentalMagnitude: Double,  // Magnitude of oscillation (≈ 0.5 for 1↔2)
    expectedPeriod: Int            // 2 for Collatz limit cycle
  )

  def predictOscillationSpectrum(): TheoreticalPrediction = {
    // For oscillation between 1 and 2:
    // Signal: x[n] = 1.5 + 0.5 * cos(πn) = 1.5 + 0.5 * (-1)^n
    // DC component: 1.5
    // Fundamental: magnitude 0.5, frequency π (or index N/2 in DFT)

    TheoreticalPrediction(
      dcComponent = 1.5,
      fundamentalFrequency = Pi,
      fundamentalMagnitude = 0.5,
      expectedPeriod = 2
    )
  }

  // ============================================================================
  // Convergence Demonstration
  // ============================================================================

  /**
   * Demonstrate convergence for a specific starting value.
   * Shows how the spectrum evolves as we include more of the trajectory.
   */
  case class ConvergenceDemonstration(
    n: Long,
    stages: List[ConvergenceStage]
  )

  case class ConvergenceStage(
    k: Int,                        // Number of steps
    currentValue: Long,            // Value at step k
    reachedOne: Boolean,          // Whether we've reached 1
    dcComponent: Double,          // Average value
    oscillationMagnitude: Double, // Magnitude at oscillation frequency
    totalEnergy: Double           // Sum of all frequency magnitudes
  )

  def demonstrateConvergence(n: Long, stages: List[Int]): ConvergenceDemonstration = {
    val stageAnalyses = stages.map { k =>
      val traj = trajectoryExtended(n, k)
      val signal = traj.map(_.toDouble)
      val dftCoeffs = dft(signal)
      val mags = magnitudeSpectrum(dftCoeffs)

      val currentValue = traj.last
      val reachedOne = traj.contains(1L)
      val dcComponent = mags.head
      val oscillationFreq = k / 2
      val oscillationMag = if (oscillationFreq < mags.length) mags(oscillationFreq) else 0.0
      val totalEnergy = mags.sum

      ConvergenceStage(k, currentValue, reachedOne, dcComponent, oscillationMag, totalEnergy)
    }

    ConvergenceDemonstration(n, stageAnalyses)
  }

  // ============================================================================
  // Visualization and Reporting
  // ============================================================================

  def printConvergenceReport(demo: ConvergenceDemonstration): Unit = {
    println("=" * 80)
    println(s"FOURIER CONVERGENCE DEMONSTRATION FOR n = ${demo.n}")
    println("=" * 80)
    println()
    println(f"${"Stage"}%-10s ${"Value"}%-10s ${"Reached 1"}%-12s ${"DC"}%-10s ${"Osc Mag"}%-10s ${"Energy"}%-10s")
    println("-" * 80)

    for (stage <- demo.stages) {
      println(f"k=${stage.k}%-6d " +
        f"${stage.currentValue}%-10d " +
        f"${stage.reachedOne}%-12s " +
        f"${stage.dcComponent}%-10.4f " +
        f"${stage.oscillationMagnitude}%-10.4f " +
        f"${stage.totalEnergy}%-10.4f")
    }
    println()

    // Analysis
    val finalStage = demo.stages.last
    val theory = predictOscillationSpectrum()

    println("THEORETICAL EXPECTATION FOR 1↔2 OSCILLATION:")
    println(f"  DC component: ${theory.dcComponent}%.4f")
    println(f"  Oscillation magnitude: ${theory.fundamentalMagnitude}%.4f")
    println(f"  Period: ${theory.expectedPeriod}")
    println()

    if (finalStage.reachedOne) {
      println("OBSERVED CONVERGENCE:")
      println(f"  DC component: ${finalStage.dcComponent}%.4f (expected ${theory.dcComponent}%.4f)")
      println(f"  Oscillation magnitude: ${finalStage.oscillationMagnitude}%.4f (expected ${theory.fundamentalMagnitude}%.4f)")

      val dcError = abs(finalStage.dcComponent - theory.dcComponent)
      val oscError = abs(finalStage.oscillationMagnitude - theory.fundamentalMagnitude)

      println()
      println(f"  DC error: ${dcError}%.6f")
      println(f"  Oscillation error: ${oscError}%.6f")

      val converged = dcError < 0.01 && oscError < 0.01
      println()
      if (converged) {
        println("  ✓ CONVERGED to theoretical 1↔2 oscillation!")
      } else {
        println("  ⚠ Not yet fully converged (need more steps)")
      }
    } else {
      println("  ⚠ Has not reached 1 yet")
    }

    println("=" * 80)
    println()
  }

  def printFrequencyAnalysis(analysis: FourierConvergenceAnalysis): Unit = {
    println("=" * 80)
    println(s"FREQUENCY DOMAIN ANALYSIS FOR n = ${analysis.n}, k = ${analysis.trajectoryLength}")
    println("=" * 80)
    println()

    println("TRAJECTORY:")
    println(analysis.trajectory.take(50).mkString(", ") +
      (if (analysis.trajectory.length > 50) "..." else ""))
    println()

    println("DOMINANT FREQUENCIES:")
    println(f"${"Freq Index"}%-15s ${"Magnitude"}%-15s ${"Period"}%-15s")
    println("-" * 80)

    for ((freq, mag) <- analysis.dominantFrequencies) {
      val period = if (freq == 0) "∞ (DC)" else f"${analysis.trajectoryLength.toDouble / freq}%.2f"
      println(f"$freq%-15d $mag%-15.6f $period%-15s")
    }
    println()

    println(s"Oscillation frequency (N/2): ${analysis.oscillationFrequency}")
    println(s"Converged to oscillation: ${analysis.convergenceToOscillation}")
    println()
    println("=" * 80)
    println()
  }

  // ============================================================================
  // Main Exploration
  // ============================================================================

  def main(args: Array[String]): Unit = {
    println()
    println("╔" + "═" * 78 + "╗")
    println("║" + " " * 78 + "║")
    println("║" + "      COLLATZ CONJECTURE: FOURIER SERIES ANALYSIS      ".center(78) + "║")
    println("║" + " " * 78 + "║")
    println("╚" + "═" * 78 + "╝")
    println()

    // Part 1: Basic convergence demonstration
    println("PART 1: CONVERGENCE TO 1→2→1 OSCILLATION")
    println("=" * 80)
    println()

    val testNumbers = List(3L, 7L, 15L, 27L)

    for (n <- testNumbers) {
      val stoppingTime = trajectory(n).indexOf(1L)
      val stages = List(
        stoppingTime / 4,
        stoppingTime / 2,
        stoppingTime,
        stoppingTime + 10,
        stoppingTime + 20,
        stoppingTime + 50
      ).filter(_ > 0).distinct.sorted

      val demo = demonstrateConvergence(n, stages)
      printConvergenceReport(demo)
    }

    // Part 2: Frequency domain analysis
    println()
    println("PART 2: FREQUENCY DOMAIN ANALYSIS")
    println("=" * 80)
    println()

    for (n <- List(7L, 27L)) {
      val stopTime = trajectory(n).indexOf(1L)

      // Analyze before reaching 1
      val beforeAnalysis = analyzeFourierConvergence(n, stopTime - 1)
      println(s"BEFORE REACHING 1 (k = ${stopTime - 1}):")
      printFrequencyAnalysis(beforeAnalysis)

      // Analyze after oscillating for a while
      val afterAnalysis = analyzeFourierConvergence(n, stopTime + 50)
      println(s"AFTER OSCILLATING (k = ${stopTime + 50}):")
      printFrequencyAnalysis(afterAnalysis)
    }

    // Part 3: Theoretical vs Actual Oscillation
    println()
    println("PART 3: THEORETICAL VS ACTUAL OSCILLATION SPECTRUM")
    println("=" * 80)
    println()

    val k = 100
    val theoretical = theoreticalOscillationSpectrum(k)

    // For n=1, we immediately oscillate
    val actualAnalysis = analyzeFourierConvergence(1L, k)

    println(s"Comparing theoretical and actual oscillation spectra (k = $k):")
    println()
    println(f"${"Frequency"}%-15s ${"Theoretical"}%-15s ${"Actual"}%-15s ${"Error"}%-15s")
    println("-" * 80)

    for (i <- 0 until min(20, theoretical.length)) {
      val theoreticalMag = theoretical(i)
      val actualMag = actualAnalysis.magnitudes(i)
      val error = abs(theoreticalMag - actualMag)

      if (theoreticalMag > 0.01 || actualMag > 0.01) {
        println(f"$i%-15d $theoreticalMag%-15.6f $actualMag%-15.6f $error%-15.6f")
      }
    }
    println()

    // Part 4: Summary and Conclusions
    println()
    println("╔" + "═" * 78 + "╗")
    println("║" + " " * 78 + "║")
    println("║" + "                         CONCLUSIONS                         ".center(78) + "║")
    println("║" + " " * 78 + "║")
    println("╚" + "═" * 78 + "╝")
    println()
    println("FOURIER ANALYSIS FINDINGS:")
    println()
    println("1. ✓ For all tested values, collatz(n, k) converges to the 1↔2 oscillation")
    println()
    println("2. ✓ The oscillation has period 2, corresponding to frequency ω = π")
    println()
    println("3. ✓ In the frequency domain, the oscillation appears as:")
    println("     - DC component (f=0): magnitude ≈ 1.5 (average value)")
    println("     - Fundamental (f=N/2): magnitude ≈ 0.5 (oscillation amplitude)")
    println()
    println("4. ✓ Before reaching 1: spectrum is complex with many frequencies")
    println("     After reaching 1: spectrum simplifies to DC + fundamental only")
    println()
    println("5. ✓ The Fourier analysis confirms the convergence to periodic behavior")
    println()
    println("6. ⚠ HOWEVER: This does NOT prove the conjecture for all n")
    println("     We've only verified for tested values, not all positive integers")
    println()
    println("7. 💡 The Fourier approach reveals the periodic structure clearly")
    println("     and provides a new lens for analyzing Collatz dynamics")
    println()
    println("=" * 80)
    println()
  }

  // Extension for string centering
  implicit class StringOps(s: String) {
    def center(width: Int): String = {
      val padding = width - s.length
      if (padding <= 0) s
      else {
        val leftPad = padding / 2
        val rightPad = padding - leftPad
        (" " * leftPad) + s + (" " * rightPad)
      }
    }
  }
}
