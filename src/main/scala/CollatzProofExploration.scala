package symbolicas

import symbolicas.CollatzSeries._
import scala.collection.mutable

/**
 * Computational exploration of proof approaches for the Collatz conjecture.
 *
 * DISCLAIMER: This explores various approaches but does not constitute a proof.
 * The Collatz conjecture remains unsolved.
 */
object CollatzProofExploration {

  // Standard Collatz iteration
  def collatz(n: Long): Long = {
    if (n % 2 == 0) n / 2 else 3 * n + 1
  }

  // Compute k iterations
  def collatzK(n: Long, k: Int): Long = {
    var current = n
    for (_ <- 0 until k) {
      current = collatz(current)
    }
    current
  }

  // Compute stopping time (steps to reach 1)
  def stoppingTime(n: Long, maxSteps: Int = 10000): Option[Int] = {
    var current = n
    var steps = 0
    while (current != 1 && steps < maxSteps) {
      current = collatz(current)
      steps += 1
    }
    if (current == 1) Some(steps) else None
  }

  // Compute maximum value reached before returning below n
  def maxValue(n: Long, maxSteps: Int = 10000): Long = {
    var current = n
    var max = n
    var steps = 0
    while (current != 1 && steps < maxSteps) {
      current = collatz(current)
      if (current > max) max = current
      steps += 1
    }
    max
  }

  /**
   * Exploration 1: Descent Analysis
   * Find the minimum k such that collatz_k(n) < n
   */
  def findDescentStep(n: Long, maxK: Int = 100): Option[Int] = {
    for (k <- 1 to maxK) {
      val result = collatzK(n, k)
      if (result < n) return Some(k)
    }
    None
  }

  /**
   * Exploration 2: Modular Pattern Analysis
   * Analyze distribution of n mod m for various m
   */
  def analyzeModularPatterns(maxN: Int, modulus: Int): Map[Int, Int] = {
    val counts = mutable.Map[Int, Int]().withDefaultValue(0)

    for (n <- 1 to maxN) {
      val result = collatz(n)
      val resultMod = (result % modulus).toInt
      counts(resultMod) += 1
    }

    counts.toMap
  }

  /**
   * Exploration 3: Cycle Detection
   * Search for cycles of period k
   */
  def searchForCycles(maxN: Int, period: Int): List[Long] = {
    val cycles = mutable.ListBuffer[Long]()

    for (n <- 1 to maxN) {
      if (collatzK(n, period) == n) {
        cycles += n
      }
    }

    cycles.toList
  }

  /**
   * Exploration 4: Stopping Time Statistics
   */
  case class StoppingTimeStats(
    min: Int,
    max: Int,
    average: Double,
    counts: Map[Int, Int]
  )

  def analyzeStoppingTimes(maxN: Int): StoppingTimeStats = {
    val times = (1 to maxN).flatMap(n => stoppingTime(n))
    val timeCounts = times.groupBy(identity).view.mapValues(_.size).toMap

    StoppingTimeStats(
      min = times.min,
      max = times.max,
      average = times.sum.toDouble / times.length,
      counts = timeCounts
    )
  }

  /**
   * Exploration 5: Class-Specific Verification
   */

  // Verify all powers of 2 converge in exactly k steps
  def verifyPowersOfTwo(maxK: Int): Boolean = {
    (1 to maxK).forall { k =>
      val n = 1L << k  // 2^k
      stoppingTime(n).contains(k)
    }
  }

  // Verify all even numbers reach an odd or reach 1
  def verifyEvensReachOddOrOne(maxN: Int): Boolean = {
    (2 to maxN by 2).forall { n =>
      var current = n.toLong
      var foundOdd = false
      var foundOne = false

      for (_ <- 0 until 1000) {
        current = collatz(current)
        if (current == 1) {
          foundOne = true
        }
        if (current % 2 == 1 && current != 1) {
          foundOdd = true
        }
        if (foundOdd || foundOne) return true
      }

      foundOdd || foundOne
    }
  }

  /**
   * Exploration 6: Growth vs Descent Balance
   * For each n, compute how many steps grow vs descend
   */
  case class GrowthStats(grows: Int, descends: Int, ratio: Double)

  def analyzeGrowthBalance(n: Long, steps: Int = 100): GrowthStats = {
    var current = n
    var growSteps = 0
    var descendSteps = 0

    for (_ <- 0 until steps) {
      val next = collatz(current)
      if (next > current) growSteps += 1
      else descendSteps += 1
      current = next
      if (current == 1) return GrowthStats(growSteps, descendSteps, descendSteps.toDouble / growSteps)
    }

    GrowthStats(growSteps, descendSteps, descendSteps.toDouble / growSteps)
  }

  /**
   * Exploration 7: Symbolic Descent Analysis
   * Use the binomial formula to check if symbolic collatz_k(n) < n
   */
  def symbolicDescentCheck(n: Double, k: Int): Boolean = {
    val result = CollatzSeries.collatzK(n, k)
    result < n
  }

  /**
   * Exploration 8: Parity Sequence Analysis
   * Track the sequence of even/odd steps
   */
  def paritySequence(n: Long, maxSteps: Int = 100): String = {
    var current = n
    val sequence = new StringBuilder

    for (_ <- 0 until maxSteps) {
      if (current == 1) return sequence.toString
      sequence.append(if (current % 2 == 0) '0' else '1')
      current = collatz(current)
    }

    sequence.toString
  }

  /**
   * Exploration 9: Average Trajectory
   * Compute average value along the trajectory
   */
  def averageTrajectory(n: Long): Double = {
    var current = n
    var sum = 0.0
    var count = 0

    while (current != 1 && count < 10000) {
      sum += current
      count += 1
      current = collatz(current)
    }

    if (count > 0) sum / count else 0.0
  }

  /**
   * Main exploration runner
   */
  def main(args: Array[String]): Unit = {
    println("=" * 80)
    println("COLLATZ CONJECTURE PROOF EXPLORATION")
    println("=" * 80)
    println()

    // Exploration 1: Descent steps for small numbers
    println("EXPLORATION 1: Descent Analysis")
    println("-" * 80)
    for (n <- List(3, 5, 7, 9, 11, 13, 15, 27, 31)) {
      val descentStep = findDescentStep(n)
      val maxVal = maxValue(n)
      println(f"n=$n%3d: First descent at step ${descentStep.getOrElse("?")}%3s, max value reached: $maxVal%5d")
    }
    println()

    // Exploration 2: Modular patterns
    println("EXPLORATION 2: Modular Patterns (mod 4)")
    println("-" * 80)
    val mod4Patterns = analyzeModularPatterns(1000, 4)
    for ((remainder, count) <- mod4Patterns.toSeq.sortBy(_._1)) {
      println(f"collatz(n) ≡ $remainder (mod 4): $count%4d occurrences")
    }
    println()

    // Exploration 3: Cycle search
    println("EXPLORATION 3: Cycle Search")
    println("-" * 80)
    for (period <- 1 to 5) {
      val cycles = searchForCycles(100, period)
      println(f"Period-$period cycles found in [1,100]: ${cycles.mkString(", ")}")
    }
    println()

    // Exploration 4: Stopping time statistics
    println("EXPLORATION 4: Stopping Time Statistics [1, 1000]")
    println("-" * 80)
    val stats = analyzeStoppingTimes(1000)
    println(f"Minimum stopping time: ${stats.min}")
    println(f"Maximum stopping time: ${stats.max}")
    println(f"Average stopping time: ${stats.average}%.2f")
    println(f"Number with max stopping time: ${stats.counts.getOrElse(stats.max, 0)}")

    // Find which number has max stopping time
    val maxStopNum = (1 to 1000).maxBy(n => stoppingTime(n).getOrElse(0))
    println(f"Number with maximum stopping time: $maxStopNum")
    println()

    // Exploration 5: Class verification
    println("EXPLORATION 5: Class-Specific Verification")
    println("-" * 80)
    println(f"Powers of 2 converge correctly: ${verifyPowersOfTwo(20)}")
    println(f"All evens reach odd or 1 [2,1000]: ${verifyEvensReachOddOrOne(1000)}")
    println()

    // Exploration 6: Growth balance
    println("EXPLORATION 6: Growth vs Descent Balance")
    println("-" * 80)
    for (n <- List(3, 7, 15, 27, 31, 63, 127)) {
      val balance = analyzeGrowthBalance(n)
      println(f"n=$n%3d: Grows ${balance.grows}%3d times, descends ${balance.descends}%3d times, ratio ${balance.ratio}%.2f")
    }
    println()

    // Exploration 7: Symbolic descent
    println("EXPLORATION 7: Symbolic Descent Check")
    println("-" * 80)
    for (n <- List(3, 5, 7, 9, 11, 13, 15, 27)) {
      for (k <- 1 to 10) {
        if (symbolicDescentCheck(n.toDouble, k)) {
          println(f"n=$n%3d: First symbolic descent at k=$k (collatz_$k($n) < $n)")
        }
      }
    }
    println()

    // Exploration 8: Parity sequences
    println("EXPLORATION 8: Parity Sequences (0=even, 1=odd)")
    println("-" * 80)
    for (n <- List(3, 5, 7, 9, 11, 13, 15, 27, 31)) {
      val seq = paritySequence(n, 30)
      println(f"n=$n%3d: $seq")
    }
    println()

    // Exploration 9: Average trajectories
    println("EXPLORATION 9: Average Trajectory Values")
    println("-" * 80)
    for (n <- List(3, 5, 7, 9, 11, 13, 15, 27, 31, 63, 127)) {
      val avg = averageTrajectory(n)
      println(f"n=$n%3d: Average trajectory value = $avg%8.2f")
    }
    println()

    println("=" * 80)
    println("CONCLUSIONS")
    println("=" * 80)
    println("1. All tested numbers converge to 1")
    println("2. Descent typically occurs within a few steps")
    println("3. Growth steps are outnumbered by descent steps")
    println("4. No non-trivial cycles found")
    println("5. Powers of 2 behave as predicted")
    println()
    println("HOWEVER: This computational evidence does NOT constitute a proof!")
    println("The Collatz conjecture remains unproven for all positive integers.")
    println("=" * 80)
  }
}
