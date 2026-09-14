package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.{CollatzSeries, Expr}

/**
 * A candidate closed form for the Collatz iterate, screened against exact integer iteration.
 *
 * `docs/evaluation.md` has this as what is left of the falsification harness: `CollatzSeriesSpec`
 * checks the forms this repository ships, and what was missing is the screen a **new** candidate
 * goes through before anyone spends time on it. The arm this uses is the refutation arm, which is
 * the half of the discovery loop that works on the whole language rather than on the fragment
 * `Translate` reads: a point where a candidate disagrees with iteration is a fact, and no theorem is
 * produced or claimed.
 *
 * == Why the points are residue classes and not a range ==
 *
 * The `k`-th iterate depends on `n` only through the parity of the first `k` steps, and those are
 * fixed by `n mod 2^k`. So a range of the first few hundred integers tests the low classes many
 * times over and the rest not at all, while one representative of each class mod `2^k` tests every
 * parity path exactly once.
 *
 * **Two representatives per class, not one**, and that is the whole reason to say the number out
 * loud. Inside a class the true iterate is `(3^s n + c) / 2^k`, which is affine in `n`, and every
 * closed form anyone proposes here has that shape; a candidate that is also affine and agrees with
 * the truth at two points of a class agrees on the whole class. One point per class would be
 * satisfied by a candidate with the wrong slope, which is exactly the error a plausible-looking
 * formula makes.
 *
 * == Where it stops, by name ==
 *
 * `Expr.eval` is over doubles, and this compares integers, so the screen is exact only while every
 * value it touches is below `2^53`. Beyond that a double no longer holds consecutive integers apart
 * and a comparison would be reporting the rounding rather than the formula. So [[screen]] returns
 * [[CollatzScreen.NotExact]] and names the point, rather than a verdict it cannot support. That is
 * the same rule the tactics keep: a procedure that cannot settle a question refuses and says what it
 * could not do.
 *
 * Exact arithmetic on the candidate would remove the bound and needs an evaluator this repository
 * does not have; `Expr.eval` is the only one, and it is over doubles.
 */
object CollatzScreen {

  /** The largest integer a double holds apart from its neighbours. */
  val Exact: BigInt = BigInt(2).pow(53)

  /** What the screen found. */
  sealed trait Verdict

  /** A point where the candidate and iteration differ, which is a fact about the candidate. */
  final case class Disagrees(n: BigInt, expected: BigInt, got: BigInt) extends Verdict

  /** Agreement at every point tried, with how many, since four points and four hundred differ. */
  final case class Agreed(points: Int) extends Verdict

  /** The refusal: a value past what a double holds exactly, so nothing here can be compared. */
  final case class NotExact(n: BigInt, value: Double) extends Verdict

  /** The candidate could not be evaluated at a point at all, which is not a disagreement. */
  final case class NotEvaluable(n: BigInt) extends Verdict

  /**
   * Representatives of every residue class mod `2^k`, `perClass` of them, all positive.
   *
   * The `j`-th representative of class `c` is `c + j * 2^k`, offset so that nothing is zero: the
   * iteration is defined for positive `n` only, and class zero would otherwise start there.
   */
  def residues(k: Int, perClass: Int = 2): Vector[BigInt] = {
    require(k >= 0, "k must be non-negative")
    require(perClass >= 1, "a class needs at least one representative")

    val modulus = BigInt(2).pow(k)
    for {
      residue <- (BigInt(0) until modulus).toVector
      copy <- (0 until perClass).toVector
    } yield residue + (copy + 1) * modulus
  }

  /**
   * Screen a candidate for `T^k`, written in `variable`, against exact iteration.
   *
   * The first disagreement stops it, because one is enough to settle the candidate and the point is
   * what a reader checks by hand.
   */
  def screen(
    candidate: Expr,
    k: Int,
    points: Vector[BigInt],
    variable: String = "n"
  ): Verdict = {
    val verdicts = points.iterator.map { n =>
      val expected = CollatzSeries.iterate(n, k)
      // `Discovery.Constants` rather than a `pi` of our own: the parity projectors are written with
      // a cosine, so a candidate here almost always mentions it, and two files disagreeing about
      // what a constant is worth is the kind of difference nothing would report.
      val got =
        try Some(candidate.eval(Discovery.Constants + (variable -> n.toDouble)))
        catch { case _: Throwable => None }

      got match {
        case None => NotEvaluable(n)
        case Some(value) if value.isNaN || value.isInfinite => NotEvaluable(n)
        case Some(value) if BigInt(math.abs(value).toLong) > Exact || n > Exact || expected > Exact =>
          NotExact(n, value)
        case Some(value) =>
          val rounded = BigInt(math.round(value))
          if (rounded == expected) Agreed(points.size) else Disagrees(n, expected, rounded)
      }
    }

    verdicts
      .find {
        case _: Agreed => false
        case _ => true
      }
      .getOrElse(Agreed(points.size))
  }

  /** The same, over two representatives of every residue class mod `2^k`. */
  def screenByClass(candidate: Expr, k: Int, variable: String = "n"): Verdict =
    screen(candidate, k, residues(k), variable)
}
