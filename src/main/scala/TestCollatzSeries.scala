package symbolicas

object TestCollatzSeries {
  def main(args: Array[String]): Unit = {
    println("Testing CollatzSeries.collatzK")
    println("=" * 50)

    // Test the same call as in test2.sc
    val v = CollatzSeries.collatzK(10, 2)
    println(s"Value: $v")
    println()

    // Run additional tests
    println("Additional Tests:")
    println("-" * 50)

    // Test various n and k values
    val testCases = List(
      (10.0, 2, "Test from test2.sc"),
      (5.0, 1, "n=5, k=1"),
      (7.0, 1, "n=7, k=1"),
      (13.0, 3, "n=13, k=3"),
      (27.0, 3, "n=27, k=3")
    )

    for ((n, k, description) <- testCases) {
      val result = CollatzSeries.collatzK(n, k)
      println(f"$description%-25s: collatz_$k($n%.1f) = $result%.6f")
    }

    println()
    println("Comparing three implementations:")
    println("-" * 50)

    for ((n, k, _) <- testCases.take(3)) {
      val result1 = CollatzSeries.collatzK(n, k)
      val result2 = CollatzSeries.collatzKStable(n, k)
      val result3 = CollatzSeries.collatzKFunctional(n, k)

      println(f"n=$n%.1f, k=$k:")
      println(f"  Standard:    $result1%.10f")
      println(f"  Stable:      $result2%.10f")
      println(f"  Functional:  $result3%.10f")
      println()
    }

    // Verify with direct Collatz computation
    println("Verification with direct Collatz:")
    println("-" * 50)

    def directCollatz(n: Int): Int = {
      if (n % 2 == 0) n / 2 else 3 * n + 1
    }

    def directCollatzK(n: Int, k: Int): Int = {
      if (k == 0) n
      else directCollatzK(directCollatz(n), k - 1)
    }

    for (n <- List(5, 7, 10, 13)) {
      for (k <- 1 to 2) {
        val seriesResult = CollatzSeries.collatzK(n.toDouble, k)
        val directResult = directCollatzK(n, k)
        val matches = math.abs(seriesResult - directResult) < 0.001
        val checkMark = if (matches) "✓" else "✗"
        println(f"n=$n%2d, k=$k: Series=$seriesResult%6.2f, Direct=$directResult%3d $checkMark")
      }
    }
  }
}
