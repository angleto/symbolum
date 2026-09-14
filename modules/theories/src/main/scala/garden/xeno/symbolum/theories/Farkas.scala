package garden.xeno.symbolum.theories

import scala.annotation.tailrec

/**
 * An exact rational, as a pair of `BigInt`s in lowest terms with a positive denominator.
 *
 * It exists for [[Farkas]] and nothing else. A certificate is found by pivoting, so floating point
 * would return a combination that is nearly the goal, the ring step would refuse it, and what the
 * caller would see is a refusal with no rounding error anywhere in it. The cost of being exact is
 * why the search runs over linear forms and not over terms.
 */
final case class Rational(numerator: BigInt, denominator: BigInt) {

  def +(other: Rational): Rational =
    Rational.of(
      numerator * other.denominator + other.numerator * denominator,
      denominator * other.denominator
    )

  def -(other: Rational): Rational = this + -other

  def unary_- : Rational = Rational(-numerator, denominator)

  def *(other: Rational): Rational =
    Rational.of(numerator * other.numerator, denominator * other.denominator)

  def /(other: Rational): Rational =
    Rational.of(numerator * other.denominator, denominator * other.numerator)

  def isZero: Boolean = numerator == 0
  def isPositive: Boolean = numerator > 0
  def isNegative: Boolean = numerator < 0

  def compare(other: Rational): Int =
    (numerator * other.denominator).compare(other.numerator * denominator)

  override def toString: String =
    if (denominator == 1) numerator.toString else s"$numerator/$denominator"
}

object Rational {

  val zero: Rational = Rational(0, 1)
  val one: Rational = Rational(1, 1)

  /** In lowest terms, with the sign on the numerator. */
  def of(numerator: BigInt, denominator: BigInt): Rational =
    if (denominator == 0) throw new ArithmeticException("a rational with a zero denominator")
    else if (numerator == 0) zero
    else {
      val sign = if (denominator < 0) BigInt(-1) else BigInt(1)
      val divisor = numerator.gcd(denominator)
      Rational((sign * numerator) / divisor, (sign * denominator) / divisor)
    }

  def of(value: BigInt): Rational = Rational(value, 1)
}

/**
 * The search for a certificate, in ordinary arithmetic, with no theorem anywhere in it.
 *
 * A linear goal follows from linear hypotheses exactly when it is a non-negative combination of
 * them, which is Farkas' lemma. Finding the combination is a linear program rather than an
 * enumeration, and this is where that program is solved. It is the untrusted half of [[Linarith]]
 * in the sense `docs/adr/0003` gives the word: what comes out is a list of numbers, [[Ring]]
 * checks that the combination is what it claims to be, and a wrong answer here costs a refusal and
 * never a theorem.
 *
 * == Why the simplex and not Fourier-Motzkin ==
 *
 * Eliminating variables would answer whether the goal follows; it would not hand back the
 * multipliers unless every combination made on the way is carried along, which is the same
 * bookkeeping written twice. The question here is feasibility of `A x = b` with `x >= 0`, phase
 * one of the simplex answers exactly that, and its answer is the certificate itself.
 *
 * == Why there is a second phase ==
 *
 * Feasibility is not always enough. A goal that is a strict inequality cannot be proved from
 * hypotheses that are all non-strict, so the certificate has to weigh at least one strict fact
 * above zero, and a feasible point chosen arbitrarily may weigh none of them. The second phase
 * asks for a point where a named subset of the multipliers sums to more than nothing, and stops as
 * soon as it has one rather than maximising, because more than nothing is the whole question.
 *
 * == Why the certificate is a function of the system and nothing else ==
 *
 * Bland's rule decides both the entering column and the leaving row, and the three loops below are
 * the only things that pivot, so the sequence of pivots is fixed by the system that was handed in.
 * Two systems that are equal give the same certificate, not merely two valid ones, and callers
 * that pin a certificate rest on that. Anything that changes the order the columns are searched in
 * or the tie-break on the leaving row changes which certificate comes out, and is a change of
 * behaviour rather than of style.
 */
object Farkas {

  /** A non-negative rational solution of `A x = b`, if there is one. */
  def nonNegativeSolution(
    columns: Vector[Vector[Rational]],
    target: Vector[Rational]
  ): Option[Vector[Rational]] =
    feasible(columns, target).map(_.solution).filter(_.forall(!_.isNegative))

  /**
   * A non-negative solution whose weighted sum is above zero, if there is one.
   *
   * The weights are one on the multipliers that have to carry some weight and zero on the rest, so
   * the sum is non-negative at every feasible point and the question is only whether it can be
   * made positive.
   */
  def nonNegativeSolution(
    columns: Vector[Vector[Rational]],
    target: Vector[Rational],
    weights: Vector[Rational]
  ): Option[Vector[Rational]] =
    if (weights.length != columns.length) None
    else
      feasible(columns, target)
        .flatMap(tableau => push(tableau, unknownsOnly(tableau.unknowns, weights)))
        .filter(_.forall(!_.isNegative))

  /**
   * How far an objective can go over the feasible region, in the three answers that exist.
   *
   * Three and not an `Option[Rational]`, because "no point satisfies the constraints" and "there is
   * no largest value" are different facts and the second is the interesting one: an objective that
   * improves without bound says the region is open in that direction, which is exactly the case
   * where no bound of that shape can be imposed on it. Folding either into `None` would make a
   * caller read them the same way.
   */
  enum Extreme {

    /** No point satisfies `A x = b` with `x >= 0`, so the question about the objective does not
      * arise. What a caller's own constraints had to become to get into that form is the caller's
      * business: `Region.largest` says what it means there, and it is narrower than it sounds. */
    case Infeasible

    /** The objective improves without bound: there is no largest value to report. */
    case Unbounded

    /** The largest value the objective takes, which may or may not be attained at a point of the
      * open region: over a system where the strict inequalities were encoded with a margin, this is
      * the supremum over the closure. */
    case At(value: Rational)
  }

  /**
   * The largest value of a linear objective over `A x = b, x >= 0`.
   *
   * Phase one is the same one [[nonNegativeSolution]] runs; what follows is the ordinary second
   * phase of the simplex with the caller's objective instead of a sum to push above zero. Bland's
   * rule on both the entering column and the leaving row, so it terminates rather than cycling on
   * a degenerate vertex, which is the failure a textbook simplex has and which exact rationals do
   * not prevent.
   *
   * `objective` gives the coefficient of each unknown and is read only at the real ones; the
   * artificial columns phase one introduced carry nothing.
   */
  def maximum(
    columns: Vector[Vector[Rational]],
    target: Vector[Rational],
    objective: Vector[Rational]
  ): Extreme =
    if (objective.length != columns.length) Extreme.Infeasible
    else
      feasible(columns, target) match {
        case None => Extreme.Infeasible
        case Some(tableau) => climb(tableau, unknownsOnly(tableau.unknowns, objective))
      }

  /**
   * The same solution cleared of its denominators: whole multipliers and the factor they scale by.
   *
   * `x` solves `A x = b`; what comes back is `(k, d)` with `k = d * x` whole and `d` the least
   * common multiple of the denominators, so that `A k = d * b`. The theorem built from it proves
   * the goal multiplied by `d`, and `Order.cancelPositive` takes the `d` back off.
   */
  def cleared(solution: Vector[Rational]): (Vector[BigInt], BigInt) = {
    val scale = solution.foldLeft(BigInt(1)) { (acc, value) =>
      acc / acc.gcd(value.denominator) * value.denominator
    }
    (solution.map(value => value.numerator * (scale / value.denominator)), scale)
  }

  /* ------------------------------------------------------------- the tableau */

  /**
   * A simplex tableau, and every step below is a tableau to the next.
   *
   * The rows are the equations in the form the basis puts them, `basis(row)` names the column that
   * stands alone on that row, and the last column of each row holds its right-hand side. Columns
   * below `unknowns` are the caller's; the `rows` above them are the artificials phase one adds.
   *
   * It is a value rather than the pair of arrays it was until 2026-09-12: a pivot is a function
   * from a tableau to a tableau, which is what lets the three loops below be written as the
   * recursions they are and what makes an intermediate tableau something a reader can hold still
   * and check, which is the whole reason the file was rewritten.
   *
   * A pivot does the same rational operations the in-place version did and allocates the rows it
   * rewrites on top of them. Over 20000 random systems of the size this file is actually asked
   * about, up to four rows by five unknowns, the two read the same; over 6000 at six by seven the
   * allocation showed as roughly a fifth more, on a machine at load average 100 where the same
   * reading moved by a factor of two between runs. That is an observation and not a figure, and
   * what decided the shape was the reader rather than either number.
   */
  private final case class Tableau(
    body: Vector[Vector[Rational]],
    basis: Vector[Int],
    unknowns: Int
  ) {

    val rows: Int = basis.length
    val answer: Int = unknowns + rows

    /** Every row paired with the column that is basic on it, built once because the search for an
      * entering column walks it again for every column it considers. */
    private val basics: Vector[(Int, Vector[Rational])] = basis.zip(body)

    /** The cost of a column under an objective given by the cost of each unknown. */
    def value(cost: Int => Rational): Rational =
      basics.foldLeft(Rational.zero) { case (acc, (variable, row)) =>
        acc + cost(variable) * row(answer)
      }

    /** What a unit of the column would add to the objective, which is `c_j - z_j`. */
    def reduced(cost: Int => Rational, column: Int): Rational =
      cost(column) - basics.foldLeft(Rational.zero) { case (acc, (variable, row)) =>
        acc + cost(variable) * row(column)
      }

    /** Bland's rule for the leaving row: least ratio, and least basic index on a tie. */
    def leaving(column: Int): Option[Int] = {
      val candidates = body.indices.filter(row => body(row)(column).isPositive)
      Option.when(candidates.nonEmpty)(candidates.reduceLeft { (best, row) =>
        val ratio = body(row)(answer) / body(row)(column)
        val bestRatio = body(best)(answer) / body(best)(column)
        val comparison = ratio.compare(bestRatio)
        if (comparison < 0 || (comparison == 0 && basis(row) < basis(best))) row else best
      })
    }

    /**
     * The tableau in which `column` is basic on `row`.
     *
     * The row is scaled to a unit in the column and every other row has a multiple of the scaled
     * row taken off it, which is where the new row has to be used and not the old one. A row that
     * is already zero in the column is passed through rather than recomputed: subtracting nothing
     * from it would rebuild every entry to the value it already holds.
     */
    def pivot(row: Int, column: Int): Tableau = {
      val divisor = body(row)(column)
      val unit = body(row).map(_ / divisor)

      val cleared = body.zipWithIndex.map { case (other, index) =>
        if (index == row) unit
        else {
          val factor = other(column)
          if (factor.isZero) other
          else other.zip(unit).map { case (entry, scaled) => entry - factor * scaled }
        }
      }

      Tableau(cleared, basis.updated(row, column), unknowns)
    }

    /** The point this tableau stands at: each basic unknown at its right-hand side, the rest at
      * nought. */
    def solution: Vector[Rational] =
      basics.foldLeft(Vector.fill(unknowns)(Rational.zero)) { case (values, (variable, row)) =>
        if (variable < unknowns) values.updated(variable, row(answer)) else values
      }
  }

  /* ------------------------------------------------------------- the objectives */

  /** The phase-one objective: a unit on every artificial column and nothing on the caller's. */
  private def artificials(unknowns: Int, answer: Int): Int => Rational =
    column => if (column >= unknowns && column < answer) Rational.one else Rational.zero

  /** A caller's objective, read at the real unknowns: the artificial columns carry nothing. */
  private def unknownsOnly(unknowns: Int, coefficients: Vector[Rational]): Int => Rational =
    column => if (column < unknowns) coefficients(column) else Rational.zero

  /* ------------------------------------------------------------- the three loops */

  /**
   * Phase one: a feasible tableau, or nothing.
   *
   * Each right-hand side is made non-negative first, so that the artificial basis is a feasible
   * start and phase one needs no starting point of its own. What comes back has every artificial
   * either out of the basis or basic at zero on a row that is all zeros, which is a redundant
   * equation rather than an obstacle.
   */
  private def feasible(
    columns: Vector[Vector[Rational]],
    target: Vector[Rational]
  ): Option[Tableau] = {
    val rows = target.length
    val unknowns = columns.length

    if (columns.exists(_.length != rows)) None
    else {
      val answer = unknowns + rows
      val flip = target.map(_.isNegative)

      val body = Vector.tabulate(rows, answer + 1) { (row, column) =>
        val value =
          if (column < unknowns) columns(column)(row)
          else if (column < answer) if (column - unknowns == row) Rational.one else Rational.zero
          else target(row)

        if (flip(row) && (column < unknowns || column == answer)) -value else value
      }

      val cost = artificials(unknowns, answer)
      val start = Tableau(body, Vector.tabulate(rows)(unknowns + _), unknowns)
      val settled = descend(start, cost)

      Option.when(settled.value(cost).isZero)(expel(settled))
    }
  }

  /**
   * Pivot while some column would lower the phase-one objective, and stop when none does.
   *
   * Bland's rule for the entering column, over the real unknowns only: an artificial that has left
   * the basis never needs to come back, and letting one back in is how a phase one stops
   * terminating. A column with nothing to pivot on stops the descent too, which is the objective
   * falling without bound and cannot happen here, because a sum of artificials is bounded below by
   * nought.
   */
  @tailrec
  private def descend(tableau: Tableau, cost: Int => Rational): Tableau =
    (0 until tableau.unknowns).find(column => tableau.reduced(cost, column).isNegative) match {
      case None => tableau
      case Some(column) =>
        tableau.leaving(column) match {
          case None => tableau
          case Some(row) => descend(tableau.pivot(row, column), cost)
        }
    }

  /**
   * Drive any artificial still in the basis out of it.
   *
   * Otherwise the second phase could raise one above zero and quietly leave the system it was
   * solving. A row with nothing to pivot on is a redundant equation and is left as it is. Each row
   * is decided against the tableau the rows before it produced, because pivoting for one of them
   * can clear the column another would have used.
   */
  private def expel(tableau: Tableau): Tableau =
    tableau.basis.indices.foldLeft(tableau) { (current, row) =>
      if (current.basis(row) < current.unknowns) current
      else
        (0 until current.unknowns).find(column => !current.body(row)(column).isZero) match {
          case Some(column) => current.pivot(row, column)
          case None => current
        }
    }

  /**
   * Phase two, maximising: pivot while some column improves, and report where it stopped.
   *
   * The two ways out are the two answers. No improving column means the vertex is optimal and its
   * objective value is the maximum. An improving column with nothing to pivot on means the
   * objective grows along that direction for ever, which is [[Extreme.Unbounded]] and is a fact
   * about the region rather than a failure to compute.
   */
  @tailrec
  private def climb(tableau: Tableau, cost: Int => Rational): Extreme =
    (0 until tableau.unknowns).find(column => tableau.reduced(cost, column).isPositive) match {
      case None => Extreme.At(tableau.value(cost))
      case Some(column) =>
        tableau.leaving(column) match {
          case Some(row) => climb(tableau.pivot(row, column), cost)
          case None => Extreme.Unbounded
        }
    }

  /**
   * Phase two: push the weighted sum above zero, or say that it cannot go there.
   *
   * The weights are non-negative and so are the unknowns, so the sum is never below zero and the
   * recursion stops at the first point where it is above it. An objective that improves without
   * bound is not a difficulty here: [[along]] takes one unit in that direction and that point
   * already has the sum positive.
   */
  @tailrec
  private def push(tableau: Tableau, cost: Int => Rational): Option[Vector[Rational]] =
    if (tableau.value(cost).isPositive) Some(tableau.solution)
    else
      (0 until tableau.unknowns).find(column => tableau.reduced(cost, column).isPositive) match {
        case None => None
        case Some(column) =>
          tableau.leaving(column) match {
            case Some(row) => push(tableau.pivot(row, column), cost)
            case None => Some(along(tableau, column))
          }
      }

  /**
   * One unit along a column the tableau cannot pivot on.
   *
   * Nothing in the column is positive, so raising the column by a unit and taking the column off
   * each basic unknown leaves every one of them where it was or higher, and the point stays
   * non-negative. It solves the same system, because the column is what the basis says it is.
   */
  private def along(tableau: Tableau, column: Int): Vector[Rational] = {
    val here = tableau.solution

    tableau.basis.zip(tableau.body).foldLeft(here.updated(column, here(column) + Rational.one)) {
      case (values, (variable, row)) =>
        if (variable < tableau.unknowns) values.updated(variable, values(variable) - row(column))
        else values
    }
  }
}
