package garden.xeno.symbolum.examples

import garden.xeno.symbolum.CollatzSeries

/**
 * The three exact forms of the Collatz iterate, printed side by side with direct iteration.
 *
 * Run with `sbt "examples/runMain garden.xeno.symbolum.examples.TestCollatzSeries"`.
 */
object TestCollatzSeries {
  def main(args: Array[String]): Unit = {
    println("The shortcut Collatz map, T^k(n), in three exact forms")
    println("=" * 60)

    val cases = List((7, 5), (10, 2), (13, 3), (27, 3), (27, 70))

    for ((n, k) <- cases) {
      val iterated = CollatzSeries.iterate(n, k)
      val form = CollatzSeries.closedForm(n, k)
      val cosine = if (k <= CollatzSeries.MaximumCosineDepth) CollatzSeries.cosineSum(n, k).toString else "(k too deep)"

      println(f"n = $n%3d, k = $k%2d")
      println(f"  iteration:    $iterated")
      println(f"  closed form:  (3^${form.oddSteps} * $n + ${form.offset}) / 2^$k = ${form.value}")
      println(f"  cosine sum:   $cosine")
      println()
    }

    println("The trajectory of 27 for its first 12 steps:")
    println("  " + CollatzSeries.trajectory(27, 12).mkString(", "))
    println()

    println("The symbolic iterate T^2(n), before and after simplification:")
    val symbolic = CollatzSeries.symbolic(2)
    println("  " + symbolic)
    println("  " + symbolic.fullSimplify)
    println()

    println("Evaluated at n = 7 (T^2(7) = 17):")
    println("  " + symbolic.eval(Map("n" -> 7.0, "pi" -> math.Pi)))
  }
}
