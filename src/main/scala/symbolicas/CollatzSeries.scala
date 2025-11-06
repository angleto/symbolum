package symbolicas

import scala.math._

object CollatzSeries {

  /**
   * Computes the binomial coefficient C(n, k) = n! / (k! * (n-k)!)
   */
  def binomial(n: Int, k: Int): Long = {
    if (k > n || k < 0) 0L
    else if (k == 0 || k == n) 1L
    else {
      var result = 1L
      for (i <- 1 to math.min(k, n - k)) {
        result = result * (n - i + 1) / i
      }
      result
    }
  }

  /**
   * Computes the k-th iteration of Collatz using the Clean Binomial Series
   *
   * Formula:
   * collatz_k(n) = Σ(m=0 to k) C(k,m) * (1/2^k) * 
   *                [(3^m - 1)/2 + 3^m * n - ((1 + 2*3^m*n)/4) * cos(3^m * n * π / 2^(k-m))]
   *
   * @param n The input number
   * @param k The number of Collatz iterations
   * @return The value after k iterations of Collatz
   */
  def collatzK(n: Double, k: Int): Double = {
    var sum = 0.0

    for (m <- 0 to k) {
      val binomCoeff = binomial(k, m)
      val threePowerM = pow(3, m)
      val twoPowerK = pow(2, k)
      val twoPowerKMinusM = pow(2, k - m)

      // Calculate the terms
      val constantTerm = (threePowerM - 1) / 2
      val linearTerm = threePowerM * n
      val cosineAmplitude = (1 + 2 * threePowerM * n) / 4
      val cosineArgument = (threePowerM * n * Pi) / twoPowerKMinusM

      // Combine all terms
      val termValue = binomCoeff / twoPowerK * (
        constantTerm +
          linearTerm -
          cosineAmplitude * cos(cosineArgument)
        )

      sum += termValue
    }

    sum
  }

  /**
   * Alternative implementation with better numerical stability for large k
   */
  def collatzKStable(n: Double, k: Int): Double = {
    var sum = 0.0

    for (m <- 0 to k) {
      val binomCoeff = binomial(k, m).toDouble

      // Use logarithms for better numerical stability with large powers
      val log3m = m * log(3)
      val log2k = k * log(2)
      val log2km = (k - m) * log(2)

      val threePowerM = exp(log3m)
      val coefficientFactor = binomCoeff * exp(-log2k)

      // Calculate the cosine argument more carefully
      val cosineArgument = if (k - m == 0) {
        threePowerM * n * Pi
      } else {
        threePowerM * n * Pi * exp(-log2km)
      }

      // Calculate the term
      val term = coefficientFactor * (
        (threePowerM - 1) / 2 +
          threePowerM * n -
          (1 + 2 * threePowerM * n) / 4 * cos(cosineArgument)
        )

      sum += term
    }

    sum
  }

  /**
   * Functional implementation using map and sum
   */
  def collatzKFunctional(n: Double, k: Int): Double = {
    (0 to k).map { m =>
      val binomCoeff = binomial(k, m).toDouble
      val threePowerM = pow(3, m)
      val twoPowerK = pow(2, k)
      val twoPowerKMinusM = pow(2, k - m)

      binomCoeff / twoPowerK * (
        (threePowerM - 1) / 2 +
          threePowerM * n -
          (1 + 2 * threePowerM * n) / 4 * cos(threePowerM * n * Pi / twoPowerKMinusM)
        )
    }.sum
  }

  // Test functions to verify correctness
  def main(args: Array[String]): Unit = {
    println("Testing Collatz Series Implementation")
    println("=" * 40)

    // Test for various values of n and k
    val testValues = List(
      (5.0, 1),
      (7.0, 1),
      (10.0, 2),
      (13.0, 3),
      (27.0, 3)
    )

    for ((n, k) <- testValues) {
      val result = collatzK(n, k)
      val resultStable = collatzKStable(n, k)
      val resultFunctional = collatzKFunctional(n, k)

      println(f"collatz_$k($n%.1f) = $result%.6f")
      println(f"  Stable version: $resultStable%.6f")
      println(f"  Functional version: $resultFunctional%.6f")
      println()
    }

    // Compare with actual Collatz iterations for small values
    println("\nComparison with direct Collatz computation:")
    println("-" * 40)

    def directCollatz(n: Int): Int = {
      if (n % 2 == 0) n / 2 else 3 * n + 1
    }

    def directCollatzK(n: Int, k: Int): Int = {
      if (k == 0) n
      else directCollatzK(directCollatz(n), k - 1)
    }

    for (n <- List(5, 7, 10, 13)) {
      val k = 1
      val seriesResult = collatzK(n.toDouble, k)
      val directResult = directCollatz(n)
      println(f"n=$n, k=$k: Series=$seriesResult%.2f, Direct=$directResult")
    }
  }
}
