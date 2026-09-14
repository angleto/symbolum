package garden.xeno.symbolum

import Dsl.*

/**
 * The shortcut Collatz map `T`, its iterates, and three exact forms of the `k`-th iterate.
 *
 * `T(n) = n / 2` for even `n` and `(3n + 1) / 2` for odd `n`. Each form below is checked
 * against direct iteration by `CollatzSeriesSpec`, which is the harness that decides whether a
 * formula about this map is an identity:
 *
 *  - [[closedForm]]: `T^k(n) = (3^s n + c) / 2^k`, where `s` counts the odd steps among the
 *    first `k` and `c` records where they fell. Exact in integers, and affine in `n` once the
 *    parity sequence is fixed.
 *  - [[cosineSum]]: the same value as a sum over all `2^k` parity paths, each weighted by a
 *    product of the projectors `(1 ± cos(pi x)) / 2`, which is `1` along the path `n` takes and
 *    `0` along every other. A formula valid for every `n` at once, at the cost of `2^k` terms;
 *    that cost is a floor and not a waste, because the flat cosine form has full spectral
 *    support.
 *  - [[symbolic]]: the same sum as an expression of this algebra system, built from the one-step
 *    identity `T(x) = x + 1/4 - ((2x + 1)/4) cos(pi x)` by composing with parity projectors, for
 *    the simplifier to work on.
 *
 * == What was here before ==
 *
 * A "binomial series" that grouped the `2^k` paths by the number of odd steps alone:
 * `sum_m C(k, m) 2^-k [ (3^m - 1)/2 + 3^m n - ((1 + 2 3^m n)/4) cos(3^m n pi / 2^(k-m)) ]`.
 * It is not an identity, and no change of sign makes it one: at `k = 0` its single term carries
 * a cosine of the parity of `n`, where `T^0(n) = n` carries none, so it returned `1.75` for
 * `n = 1`. Grouping by weight assumes the parity at a step is independent of the steps before
 * it, and it is not; the exact expansion has one term per path. The forms here follow Angelo
 * Leto's derivation in the Collatz repository, where they are verified in exact arithmetic.
 */
object CollatzSeries {

  /** One shortcut step. */
  def step(n: BigInt): BigInt = if (n.testBit(0)) (3 * n + 1) / 2 else n / 2

  /** `T^k(n)` by iteration: the reference every other form is checked against. */
  def iterate(n: BigInt, k: Int): BigInt = {
    requireArguments(n, k)
    (0 until k).foldLeft(n)((current, _) => step(current))
  }

  /** `n, T(n), ..., T^k(n)`. */
  def trajectory(n: BigInt, k: Int): Vector[BigInt] = {
    requireArguments(n, k)
    (0 until k).scanLeft(n)((current, _) => step(current)).toVector
  }

  /**
   * The closed form `T^k(n) = (3^s n + c) / 2^k`, with its two parameters exposed.
   *
   * `oddSteps` is `s`, and `offset` is `c = sum_i 3^(s - 1 - i) 2^(q_i)` over the positions
   * `q_0 < ... < q_(s-1)` of the odd steps. The reconstruction `(3^s n + c) >> k` equals `value`,
   * and the spec checks that it does; `value` is computed by keeping the running iterate reduced
   * rather than by materialising `3^s`, which is astronomically large even when the iterate is
   * small.
   */
  final case class ClosedForm(value: BigInt, oddSteps: Int, offset: BigInt) {
    def reconstructed(n: BigInt, k: Int): BigInt = (BigInt(3).pow(oddSteps) * n + offset) >> k
  }

  def closedForm(n: BigInt, k: Int): ClosedForm = {
    requireArguments(n, k)
    val (value, oddSteps, offset) =
      (0 until k).foldLeft((n, 0, BigInt(0))) { case ((value, oddSteps, offset), position) =>
        if (value.testBit(0))
          ((3 * value + 1) / 2, oddSteps + 1, 3 * offset + (BigInt(1) << position))
        else (value / 2, oddSteps, offset)
      }

    ClosedForm(value, oddSteps, offset)
  }

  /**
   * The largest `k` [[cosineSum]] accepts.
   *
   * The sum enumerates `2^k` paths in floating point and rounds at the end; past this depth the
   * enumeration is slow and the rounding is no longer safe. The closed form has no such limit.
   */
  val MaximumCosineDepth: Int = 20

  /**
   * `T^k(n)` as the cosine sum over all `2^k` parity paths.
   *
   * Along a path `e` in `{0, 1}^k` the numerator obeys `N_0 = n` and `N_(j+1) = 3 N_j + 2^j` on
   * an odd step, `N_j` on an even one, so that `T^j(n) = N_j / 2^j` on the true path. The path's
   * weight is the product over `j` of `(1 + (-1)^(e_j) cos(pi N_j / 2^j)) / 2`, which is `1` on
   * the path `n` takes and `0` on every other, and the sum of `weight * N_k / 2^k` is therefore
   * `T^k(n)`. Rounded to the nearest integer, because the projectors are computed in doubles.
   */
  def cosineSum(n: Long, k: Int): Long = {
    requireArguments(BigInt(n), k)
    require(k <= MaximumCosineDepth, s"k must be at most $MaximumCosineDepth for the cosine sum")

    // The folds visit the paths and the positions in the same order the loops did, which is what
    // keeps the sum bit-identical: floating-point addition is not associative, so a reordering
    // here would move the last digits of `total` and `CollatzSeriesSpec` pins them.
    val total = (0L until (1L << k)).foldLeft(0.0) { (total, path) =>
      val (numerator, weight) = (0 until k).foldLeft((n, 1.0)) {
        case ((numerator, weight), position) =>
          val odd = ((path >> position) & 1L) == 1L
          val argument = math.Pi * numerator.toDouble / (1L << position).toDouble
          val stepped = weight * 0.5 * (1.0 + (if (odd) -1.0 else 1.0) * math.cos(argument))
          (if (odd) 3 * numerator + (1L << position) else numerator, stepped)
      }
      total + weight * numerator.toDouble
    }

    math.round(total / (1L << k).toDouble)
  }

  /** `T(x) = x + 1/4 - ((2x + 1)/4) cos(pi x)`, the one-step identity as an expression. */
  def symbolicStep(x: Expr): Expr =
    x + Num(1, 4) - ((x * 2 + 1) / 4) * cos(x * pi)

  /**
   * `T^k(n)` as an expression in `variable`, built by composition with parity projectors.
   *
   * `T^(k+1)(n) = E(n) T^k(n/2) + O(n) T^k((3n + 1)/2)` with `E = (1 + cos(pi n))/2` and
   * `O = (1 - cos(pi n))/2`, written as `cos(pi n)/2 (even - odd) + (even + odd)/2`. The
   * expression grows as `2^k`, which is the size of the flat form and cannot be improved; the
   * point of building it is to give the simplifier something true to work on.
   */
  def symbolic(k: Int, variable: Var = Var("n")): Expr = {
    require(k >= 0, "k must be non-negative")
    if (k == 0) variable
    else {
      val previous = symbolic(k - 1, variable)
      val even = previous.replaceSymbol(variable.name, variable / 2)
      val odd = previous.replaceSymbol(variable.name, (variable * 3 + 1) / 2)
      cos(variable * pi) * Num(1, 2) * (even - odd) + Num(1, 2) * (even + odd)
    }
  }

  private def requireArguments(n: BigInt, k: Int): Unit = {
    require(n > 0, "n must be positive")
    require(k >= 0, "k must be non-negative")
  }
}
