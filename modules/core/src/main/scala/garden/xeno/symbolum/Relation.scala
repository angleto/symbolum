package garden.xeno.symbolum

import java.math.{MathContext, RoundingMode}
import scala.annotation.tailrec

/**
 * Integer relation detection: given real numbers, the whole-number coefficients that cancel them.
 *
 * Given `x_1 .. x_n` known to many digits, find integers `a_1 .. a_n`, not all zero, with
 * `a_1 x_1 + ... + a_n x_n = 0`. It is the engine behind the discoveries this repository's purpose
 * names: the BBP formula for pi was found by putting pi and four series into one of these and
 * reading the answer, and so were the Ramanujan-type series. It is also the architecture this
 * system already has, one level down: an untrusted numeric search proposes, and something exact
 * checks.
 *
 * == Why it could not exist before ==
 *
 * It needs digits. A relation among `n` values with coefficients of size `M` happens **by accident**
 * once `n log10(M)` reaches the number of digits the values are known to, and at sixteen digits that
 * is a handful of two-digit coefficients. The method does not become imprecise there; it returns an
 * answer that is noise, and `RelationSpec` measures exactly that: the minimal polynomial of
 * `sqrt2 + sqrt3 + sqrt5` comes back as nine random-looking numbers at sixteen digits and as
 * `x^8 - 40x^6 + 352x^4 - 960x^2 + 576` at forty. [[Arbitrary]] is what made the second possible.
 *
 * == How it works, and why LLL rather than PSLQ ==
 *
 * Build a lattice whose rows are `(e_i, round(N x_i))` for a large `N`. A combination of rows with
 * coefficients `a_i` has `(a_1 .. a_n)` in front and `N times the residual` behind it, so a relation
 * with small coefficients is a **short vector** and lattice reduction is the way to find one.
 * `LLL` is the reduction, it is forty years old, and it is written out below in exact rational
 * arithmetic where the textbook writes it in floating point, because the entries here have hundreds
 * of digits and the whole point is not to lose any.
 *
 * PSLQ is the other answer and is the one the experimental-mathematics literature uses. It is
 * better at this: it works in the reals rather than in a scaled lattice and it gives a bound on what
 * it has excluded. It is also considerably more delicate, and nothing here needs its advantages yet.
 * If the bound ever matters, this file is the thing to replace and [[Relation.Outcome]] is the
 * surface that would not have to change.
 *
 * == What it will not do ==
 *
 * Claim. Everything here is on the untrusted side, like the rest of this module, and a relation it
 * reports is a **conjecture with a confidence attached**: `n` numbers agreeing to a hundred digits
 * is overwhelming evidence and is not a proof, and the difference is the whole reason the kernel is
 * in this repository. [[Relation.NotCredible]] is the answer when the coefficients are the size an
 * accident would be, and it is a different answer from "no relation", which nothing here can give.
 */
object Relation {

  /**
   * How many digits of confirmation a relation needs before it is reported as found.
   *
   * The measurement, over the cases in `RelationSpec`. A relation among `n` values with largest
   * coefficient `M` is an accident once `n log10(M)` reaches the digits the values carry, so what
   * is left over, `digits - n log10(M)`, is what the relation is confirmed by. The negative control
   * of five unrelated constants scores 1 or less at every precision from sixteen digits to a
   * hundred and twenty, while it returns coefficients that grow from three figures to twenty-four.
   * The BBP relation scores 13 at sixteen digits and 197 at two hundred.
   *
   * Ten is above everything the control produced and below everything a real relation produced,
   * with a wide gap on both sides.
   */
  val Confirmation: Int = 10

  /** What the search found, and how sure of it a reader is entitled to be. */
  sealed trait Outcome

  /**
   * Coefficients that cancel the values, with the digits confirming them.
   *
   * `confirmed` is `digits - n log10(max|a|)`, rounded down: the digits the agreement has left over
   * once the size of the coefficients is paid for. `residual` is what the combination actually came
   * to, which is the same fact in the other units and is what a reader checks by eye.
   */
  final case class Found(
    coefficients: Vector[BigInt],
    confirmed: Int,
    residual: BigDecimal
  ) extends Outcome

  /**
   * A shortest vector whose coefficients are the size an accident is at this precision.
   *
   * **Not** "there is no relation", which nothing here can say: a relation with larger coefficients,
   * or one needing more digits, would look exactly like this. What it says is that the search found
   * nothing the precision it was given can support, and the move is more digits.
   */
  final case class NotCredible(coefficients: Vector[BigInt], confirmed: Int) extends Outcome

  /** The question could not be put: fewer than two values, or a value with no digits in it. */
  final case class Unusable(why: String) extends Outcome

  /**
   * Search for a relation among the values, which are assumed good to `digits` significant digits.
   *
   * The scaling is where the caller's precision enters, and it is in **decimal places** rather than
   * significant digits: a value of size `10^5` known to fifty significant digits is known to
   * forty-five places, and scaling by more than that would feed the lattice digits that are not
   * there. Two more are given away on top, for the rounding of the scaled column itself.
   */
  def among(values: Vector[BigDecimal], digits: Int): Outcome = {
    val n = values.length
    if (n < 2) Unusable(s"a relation wants at least two values and was given $n")
    else if (values.forall(_.signum == 0)) Unusable("every value is zero, so every relation holds")
    else {
      val ahead = values.map(value => value.bigDecimal.precision - value.bigDecimal.scale).max
      val places = digits - math.max(0, ahead) - 2

      if (places < 2) Unusable(s"$digits digits leaves $places decimal places to scale by")
      else {
        val context = new MathContext(digits, RoundingMode.HALF_EVEN)
        val scaled = values.map { value =>
          value.bigDecimal.movePointRight(places).setScale(0, RoundingMode.HALF_EVEN).toBigInteger
        }

        val lattice = Vector.tabulate(n, n + 1) { (row, column) =>
          if (column == n) BigInt(scaled(row))
          else if (column == row) BigInt(1)
          else BigInt(0)
        }

        val reduced = reduce(lattice)

        val shortest = reduced.minBy(row => row.map(entry => entry * entry).sum)
        val coefficients = shortest.take(n).toVector
        verdict(coefficients, values, digits, context)
      }
    }
  }

  /* -------------------------------------------------------------------- the verdict */

  private def verdict(
    coefficients: Vector[BigInt],
    values: Vector[BigDecimal],
    digits: Int,
    context: MathContext
  ): Outcome = {
    // The reduction returns a basis of the same lattice, so no row of it is zero and the largest
    // coefficient is at least one. There is no guard for that, for the reason `reduce` gives about
    // vanishing Gram-Schmidt norms: a branch no test can reach is worse than the assumption written
    // down beside the code that relies on it.
    val largest = coefficients.map(_.abs).max
    val spent = coefficients.length.toDouble * math.log10(largest.toDouble)
    val confirmed = math.max(0, math.floor(digits.toDouble - spent).toInt)

    if (confirmed < Confirmation) NotCredible(coefficients, confirmed)
    else {
      val residual = coefficients
        .zip(values)
        .foldLeft(java.math.BigDecimal.ZERO) { case (total, (coefficient, value)) =>
          total.add(
            value.bigDecimal.multiply(new java.math.BigDecimal(coefficient.bigInteger), context),
            context)
        }
      Found(coefficients, confirmed, new BigDecimal(residual.round(context), context))
    }
  }

  /* ------------------------------------------------------------------------- LLL */

  /** The Lovász constant, as the textbooks take it. Three quarters. allow-non-english: a name. */
  private val Delta: Ratio = Ratio(3, 4)

  /**
   * Everything one pass of the reduction carries, so that the pass is a function of it.
   *
   * `basis` is the lattice being reduced; `orthogonal` holds its Gram-Schmidt rows, `norms` their
   * squared lengths and `mu` the coefficients relating the two. `highest` is the largest row index
   * the orthogonalisation has reached, which is what stops a row already orthogonalised from being
   * done again when `k` walks back down.
   *
   * The reduction used to be `Array` mutated in place, and the exchange is not free: one state
   * update here is a `Vector.updated` on a vector of at most ten entries. It was measured against
   * what the same step costs in arbitrary precision before it was made. On the largest case
   * `RelationSpec` builds, the nine powers of `sqrt2 + sqrt3 + sqrt5` at forty digits, the run
   * issues 219370 `BigInt` multiplications and 86357 gcds on operands of up to 5250 bits, against
   * 11562 state updates: twenty-four arbitrary-precision operations for every update, and the ratio
   * grows with the precision because the operands do and the vectors do not. That is the whole
   * argument for writing it this way, and it is an argument about **this** lattice shape: a lattice
   * with thousands of columns rather than ten would have to be measured again.
   */
  private final case class Work(
    basis: Vector[Vector[BigInt]],
    mu: Vector[Vector[Ratio]],
    norms: Vector[Ratio],
    orthogonal: Vector[Vector[Ratio]],
    highest: Int
  )

  /**
   * The reduced basis, by Cohen's formulation of LLL.
   *
   * Exact rationals throughout. The textbook keeps the Gram-Schmidt coefficients in floating point
   * and repairs the damage; the entries here carry hundreds of digits and repairing the damage is
   * the thing this file is supposed to avoid, so `Ratio` is a pair of `BigInt` and nothing rounds.
   *
   * The basis this is ever given contains an identity block, so its rows are independent and no
   * Gram-Schmidt norm is ever zero. That is why there is no guard for it: the guard would be a
   * branch no test could reach, which is worse than the assumption written down here.
   */
  private def reduce(lattice: Vector[Vector[BigInt]]): Vector[Vector[BigInt]] = {
    val n = lattice.length
    val start = Work(
      basis = lattice,
      mu = Vector.fill(n, n)(Ratio.Zero),
      norms = Vector.fill(n)(Ratio.Zero),
      orthogonal = Vector.fill(n, lattice(0).length)(Ratio.Zero),
      highest = 0
    )
    sweep(gramSchmidt(start, 0), 1, n).basis
  }

  /**
   * The main loop of the reduction: reduce row `k` against the one below it, then swap or advance.
   *
   * A swap steps `k` back down, which is why this cannot be a fold: the index is not a range being
   * walked but a state of its own, and the loop terminates on the Lovász condition rather than on
   * having run out of rows. allow-non-english: a surname.
   */
  @tailrec
  private def sweep(work: Work, k: Int, n: Int): Work =
    if (k >= n) work
    else {
      val seen = if (k > work.highest) gramSchmidt(work.copy(highest = k), k) else work
      val reduced = reduceAgainst(seen, k, k - 1)
      val factor = reduced.mu(k)(k - 1)

      if (reduced.norms(k) < (Delta - factor * factor) * reduced.norms(k - 1))
        sweep(exchange(reduced, k, factor), math.max(1, k - 1), n)
      else
        sweep(
          (k - 2 to 0 by -1).foldLeft(reduced)((state, l) => reduceAgainst(state, k, l)),
          k + 1,
          n)
    }

  /** Orthogonalise row `k` against the rows below it, recording the coefficients in `mu`. */
  private def gramSchmidt(work: Work, k: Int): Work = {
    // Converted once, outside the fold. `basis(k)` does not change during the pass, and this
    // conversion was inside the loop until 2026-09-12, where it was redone for every `j`: counted
    // over the four cases `RelationSpec` runs, 1611 needless full-row conversions on the nine
    // powers of `sqrt2 + sqrt3 + sqrt5` at forty digits, 315 and 1159 on the BBP values at fifty
    // and at two hundred, and 1449 on the negative control at a hundred and twenty, each of them
    // allocating one `Ratio` per column. The coefficient is taken against the original row rather
    // than against the running remainder, which is classical Gram-Schmidt rather than the modified
    // variant; hoisting makes that visible instead of implied, and is why the hoist is safe.
    val row = work.basis(k).map(Ratio.of)

    val (vector, factors) =
      (0 until k).foldLeft((row, Vector.empty[Ratio])) { case ((partial, found), j) =>
        val factor = dot(row, work.orthogonal(j)) / work.norms(j)
        (subtractScaled(partial, work.orthogonal(j), factor), found :+ factor)
      }

    work.copy(
      mu = work.mu.updated(k, factors ++ work.mu(k).drop(k)),
      norms = work.norms.updated(k, dot(vector, vector)),
      orthogonal = work.orthogonal.updated(k, vector)
    )
  }

  /** Subtract a whole multiple of row `l` from row `k`, when the coefficient asks for one. */
  private def reduceAgainst(work: Work, k: Int, l: Int): Work =
    if (!(work.mu(k)(l).abs > Ratio.Half)) work
    else {
      val q = work.mu(k)(l).nearest
      val whole = Ratio.of(q)
      work.copy(
        basis = work.basis.updated(
          k,
          work.basis(k).indices.map(i => work.basis(k)(i) - q * work.basis(l)(i)).toVector),
        mu = work.mu.updated(
          k,
          work.mu(k).zipWithIndex.map { case (value, i) =>
            if (i < l) value - whole * work.mu(l)(i)
            else if (i == l) value - whole
            else value
          })
      )
    }

  /**
   * Swap rows `k` and `k - 1` and carry the Gram-Schmidt data across the swap.
   *
   * The two orthogonalisations at the end overwrite most of what the arithmetic above computes.
   * They do not overwrite `mu(i)` for `i` above `k`, which is the part that has to be carried by
   * hand, and recomputing the rest is cheaper than reasoning about which part survives.
   */
  private def exchange(work: Work, k: Int, factor: Ratio): Work = {
    val combined = work.norms(k) + factor * factor * work.norms(k - 1)
    val updated = factor * work.norms(k - 1) / combined
    val below = work.norms(k - 1) * work.norms(k) / combined

    val above = work.mu(k)
    val beneath = work.mu(k - 1)

    val swapped = work.copy(
      basis = work.basis.updated(k, work.basis(k - 1)).updated(k - 1, work.basis(k)),
      mu = work.mu
        .updated(k, (beneath.take(k - 1) ++ above.drop(k - 1)).updated(k - 1, updated))
        .updated(k - 1, above.take(k - 1) ++ beneath.drop(k - 1)),
      norms = work.norms.updated(k, below).updated(k - 1, combined)
    )

    val carriedAcross = (k + 1 to swapped.highest).foldLeft(swapped) { (state, i) =>
      val held = state.mu(i)(k)
      val raised = state.mu(i)(k - 1) - factor * held
      state.copy(
        mu = state.mu.updated(i, state.mu(i).updated(k, raised).updated(k - 1, held + updated * raised))
      )
    }

    gramSchmidt(gramSchmidt(carriedAcross, k - 1), k)
  }

  private def dot(left: Vector[Ratio], right: Vector[Ratio]): Ratio =
    left.indices.foldLeft(Ratio.Zero)((total, i) => total + left(i) * right(i))

  private def subtractScaled(
    from: Vector[Ratio],
    vector: Vector[Ratio],
    factor: Ratio
  ): Vector[Ratio] =
    from.indices.map(i => from(i) - factor * vector(i)).toVector

  /**
   * A rational, held exactly and always in lowest terms.
   *
   * Small and private because it is one file's arithmetic and the repository already has two others:
   * `theories.Rational` carries Farkas certificates over in `modules/theories`, which this module
   * cannot see and must not start depending on, and `garden.xeno.symbolum.Rational` is about the `Double`
   * fractions a `Num` holds and is not exact. Sharing a name with either would be worse than having
   * three, so this one is named for what it is.
   */
  private final case class Ratio(numerator: BigInt, denominator: BigInt) {

    def +(other: Ratio): Ratio =
      Ratio(numerator * other.denominator + other.numerator * denominator,
        denominator * other.denominator)

    def -(other: Ratio): Ratio =
      Ratio(numerator * other.denominator - other.numerator * denominator,
        denominator * other.denominator)

    def *(other: Ratio): Ratio = Ratio(numerator * other.numerator, denominator * other.denominator)

    def /(other: Ratio): Ratio = Ratio(numerator * other.denominator, denominator * other.numerator)

    def abs: Ratio = Ratio(numerator.abs, denominator)

    def <(other: Ratio): Boolean =
      numerator * other.denominator < other.numerator * denominator

    def >(other: Ratio): Boolean =
      numerator * other.denominator > other.numerator * denominator

    /** The nearest whole number, halves going up, which is what the reduction step wants. */
    def nearest: BigInt = {
      val doubled = 2 * numerator + denominator
      val twice = 2 * denominator
      val quotient = doubled / twice
      if (doubled.signum < 0 && quotient * twice != doubled) quotient - 1 else quotient
    }
  }

  private object Ratio {

    val Zero: Ratio = Ratio(0, 1)
    val Half: Ratio = Ratio(1, 2)

    /**
     * In lowest terms, with the sign on top, and without a branch.
     *
     * `gcd` is never negative, so multiplying it by the denominator's sign gives one divisor that
     * both reduces the fraction and moves the sign where it belongs. Written this way rather than
     * as two cases because the second case cannot arise here: every division below is by a
     * Gram-Schmidt norm or by a sum of squares, and both are positive. A branch nothing can reach is
     * a branch nothing checks.
     */
    def apply(numerator: BigInt, denominator: BigInt): Ratio = {
      val common = numerator.gcd(denominator) * denominator.signum
      new Ratio(numerator / common, denominator / common)
    }

    def of(whole: BigInt): Ratio = new Ratio(whole, 1)
  }
}
