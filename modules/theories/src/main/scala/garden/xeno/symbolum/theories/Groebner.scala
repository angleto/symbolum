package garden.xeno.symbolum.theories

import scala.annotation.tailrec

/**
 * Whether a polynomial lies in the ideal a list of polynomials generates, and if so with which
 * cofactors.
 *
 * The search half of [[Ideal]], and it is **not trusted** in the sense the rest of this module is
 * not: nothing here reaches the kernel. What it hands back is a certificate, `target = c1 * g1 +
 * ... + ck * gk`, and [[Ideal]] states that identity and has `Ring` prove it, so a wrong cofactor is
 * a false equation and is refused there. It is the arrangement [[Farkas]] has with [[Linarith]], for
 * the equational half of the same question.
 *
 * == Why here and not in `core` ==
 *
 * `core` is the algebra system and would be the obvious home for a Groebner basis, and the reason
 * it is not is arithmetic: `core`'s rational is a pair of `Double`s that falls back to a quotient
 * past 2^53, and a certificate is an identity that has to hold exactly. The exact rational is
 * [[Rational]], here, and a second copy of it in `core` would be two implementations of one rule.
 *
 * == The algorithm, and what it does not do ==
 *
 * Buchberger's, over the rationals, in graded reverse lexicographic order, with the product
 * criterion and nothing else: the systems the corpus asks about have up to four unknowns and degree
 * five, where the refinements that matter at scale (the chain criterion, F4's linear algebra) buy
 * nothing measurable and cost a second argument for soundness of the search. Every polynomial
 * carries, beside itself, its expression in the generators it started from, which is the whole of
 * what turns a basis into a certificate. That tracking is what makes this more expensive than a
 * plain basis, and [[Budget]] is stated in the work it counts for that reason.
 *
 * It decides membership in the ideal, which is a question about every commutative ring at once. A
 * polynomial **not** in the ideal can still vanish wherever the generators do, over the reals or
 * even over the complex numbers (`x` is not in the ideal of `x * x`), so [[Membership.NotMember]]
 * is a decision about the ideal and never about the equations' common zeros. Saying more is the
 * radical, which is not here.
 */
object Groebner {

  /** Exponents, one per unknown, all of one length within a computation. */
  type Monomial = Vector[Int]

  /** A polynomial: its monomials and their non-zero coefficients. */
  type Poly = Map[Monomial, Rational]

  /**
   * How much work one membership question may do, counted in coefficient multiplications.
   *
   * A bound in the resource it protects rather than in a count of steps, because steps do not cost
   * the same: one reduction by a long basis element is a hundred of the work of one by a short one.
   *
   * Measured on 2026-11-10, `IdealSpec` printing what `Ideal.search` spent: `aime_1990_p15`, the
   * largest system the corpus asks this about, spent 10103; `mathd_algebra_338` 80 and
   * `mathd_algebra_478` 28. The bound is about two hundred times the largest, so a question that
   * reaches it is a different kind of question rather than a slightly bigger one. What it takes in
   * wall clock to reach it has not been measured.
   */
  val Budget: Long = 2000000L

  /** What a membership question came to. */
  enum Membership {

    /** `target = sum of cofactors(i) * generators(i)`, exactly, and `spent` is what it cost. */
    case Member(cofactors: Vector[Poly], spent: Long)

    /**
     * The target reduces to a non-zero remainder modulo a complete basis, which **decides** that it
     * is not in the ideal. Not a statement about common zeros: see the comment on the object.
     */
    case NotMember(remainder: Poly, spent: Long)

    /** The budget ran out before the basis was complete, so nothing was decided. */
    case Exhausted(spent: Long, budget: Long)
  }

  /**
   * The membership of `target` in the ideal of `generators`, over `arity` unknowns.
   *
   * A generator that is the zero polynomial is kept in the list and given a zero cofactor, so the
   * cofactors stay aligned with what the caller passed.
   */
  def membership(
    generators: Vector[Poly],
    target: Poly,
    arity: Int,
    budget: Long = Budget
  ): Membership = {
    val meter = Meter(0L, budget)
    val k = generators.length
    val unit = (i: Int) => Vector.tabulate(k)(j => if (i == j) one(arity) else zero)
    val seeds = generators.indices.toVector
      .filter(i => generators(i).nonEmpty)
      .map(i => Tracked(generators(i), unit(i)))

    basis(seeds, meter).flatMap((complete, m) => reduce(Tracked(target, Vector.fill(k)(zero)), complete, m)) match {
      case Left(spent) => Membership.Exhausted(spent, budget)
      // `reduced.poly = target + sum cofactors(i) * g(i)` and it is zero, so the target is the
      // negated combination.
      case Right((reduced, charged)) if reduced.poly.isEmpty =>
        Membership.Member(reduced.cofactors.map(negate), charged.spent)
      case Right((reduced, charged)) => Membership.NotMember(reduced.poly, charged.spent)
    }
  }

  /* -------------------------------------------------------------- polynomial arithmetic */

  val zero: Poly = Map.empty

  def one(arity: Int): Poly = Map(Vector.fill(arity)(0) -> Rational.one)

  def constant(value: Rational, arity: Int): Poly =
    if (value.isZero) zero else Map(Vector.fill(arity)(0) -> value)

  def variable(index: Int, arity: Int): Poly =
    Map(Vector.tabulate(arity)(i => if (i == index) 1 else 0) -> Rational.one)

  def add(left: Poly, right: Poly): Poly =
    right.foldLeft(left) { case (acc, (monomial, c)) =>
      val total = acc.getOrElse(monomial, Rational.zero) + c
      if (total.isZero) acc - monomial else acc.updated(monomial, total)
    }

  def negate(polynomial: Poly): Poly = polynomial.map((m, c) => m -> -c)

  def subtract(left: Poly, right: Poly): Poly = add(left, negate(right))

  def multiply(left: Poly, right: Poly): Poly =
    left.foldLeft(zero) { case (acc, (m, c)) => add(acc, term(m, c, right)) }

  /** `c * x^m * polynomial`. */
  def term(monomial: Monomial, coefficient: Rational, polynomial: Poly): Poly =
    if (coefficient.isZero) zero
    else polynomial.map((m, c) => times(monomial, m) -> coefficient * c)

  /**
   * Graded reverse lexicographic order: higher total degree first, and between two of one degree
   * the one with the smaller exponent in the last unknown where they differ is the larger.
   */
  def compare(left: Monomial, right: Monomial): Int = {
    val degrees = left.sum.compare(right.sum)
    if (degrees != 0) degrees
    else left.indices.reverse.find(i => left(i) != right(i)) match {
      case Some(i) => right(i).compare(left(i))
      case None => 0
    }
  }

  /** The largest monomial, which a non-zero polynomial has and the zero polynomial does not. */
  def leading(polynomial: Poly): Option[(Monomial, Rational)] =
    polynomial.reduceOption((a, b) => if (compare(a._1, b._1) >= 0) a else b)

  private def times(left: Monomial, right: Monomial): Monomial =
    left.indices.map(i => left(i) + right(i)).toVector

  private def divides(divisor: Monomial, dividend: Monomial): Boolean =
    divisor.indices.forall(i => divisor(i) <= dividend(i))

  private def quotient(dividend: Monomial, divisor: Monomial): Monomial =
    dividend.indices.map(i => dividend(i) - divisor(i)).toVector

  private def lcm(left: Monomial, right: Monomial): Monomial =
    left.indices.map(i => math.max(left(i), right(i))).toVector

  /* -------------------------------------------------------------- the tracked search */

  /**
   * A polynomial and an account of it: `poly = K + sum cofactors(i) * g(i)`, where `K` is zero for
   * everything derived from the generators and is the target for the target. Subtracting a multiple
   * of a basis element keeps the account, which is all reduction ever does.
   */
  private final case class Tracked(poly: Poly, cofactors: Vector[Poly])

  /**
   * Work done so far against a fixed budget, threaded through every step rather than held in a
   * variable: a step returns the work it leaves spent, or `Left` with what was spent when it ran out.
   */
  private final case class Meter(spent: Long, budget: Long) {
    def charge(work: Long): Either[Long, Meter] =
      if (spent + work > budget) Left(spent + work) else Right(copy(spent = spent + work))
  }

  /** `t - c * x^m * b`, with the account kept, or `Left` once the budget is gone. */
  private def eliminate(
    t: Tracked,
    monomial: Monomial,
    coefficient: Rational,
    b: Tracked,
    meter: Meter
  ): Either[Long, (Tracked, Meter)] =
    meter.charge(b.poly.size.toLong + b.cofactors.map(_.size.toLong).sum).map { charged =>
      val poly = subtract(t.poly, term(monomial, coefficient, b.poly))
      val cofactors =
        t.cofactors.indices.map(i => subtract(t.cofactors(i), term(monomial, coefficient, b.cofactors(i)))).toVector
      (Tracked(poly, cofactors), charged)
    }

  /**
   * The remainder of `t` modulo `basis`, fully reduced: no monomial of it is divisible by a leading
   * monomial of the basis. The division algorithm, with the terms that cannot be reduced moved
   * aside so that the loop always works on the largest term left.
   */
  private def reduce(t: Tracked, basis: Vector[Tracked], meter: Meter): Either[Long, (Tracked, Meter)] = {
    val leads = basis.map(b => leading(b.poly).get)

    @tailrec
    def go(current: Tracked, kept: Poly, meter: Meter): Either[Long, (Tracked, Meter)] =
      leading(current.poly) match {
        case None => Right((Tracked(kept, current.cofactors), meter))
        case Some((m, c)) =>
          basis.indices.find(j => divides(leads(j)._1, m)) match {
            case Some(j) =>
              eliminate(current, quotient(m, leads(j)._1), c / leads(j)._2, basis(j), meter) match {
                case Left(spent) => Left(spent)
                case Right((next, charged)) => go(next, kept, charged)
              }
            case None =>
              go(Tracked(current.poly - m, current.cofactors), kept.updated(m, c), meter)
          }
      }

    go(t, zero, meter)
  }

  /** The S-polynomial of two basis elements, which cancels their leading terms. */
  private def sPolynomial(left: Tracked, right: Tracked, meter: Meter): Either[Long, (Tracked, Meter)] = {
    val (lm, lc) = leading(left.poly).get
    val (rm, rc) = leading(right.poly).get
    val common = lcm(lm, rm)
    val start = Tracked(zero, Vector.fill(left.cofactors.length)(zero))
    // `start - (-1/lc) x^(common/lm) left - (1/rc) x^(common/rm) right`, whose leading terms cancel.
    for {
      withLeft <- eliminate(start, quotient(common, lm), -(Rational.one / lc), left, meter)
      both <- eliminate(withLeft._1, quotient(common, rm), Rational.one / rc, right, withLeft._2)
    } yield both
  }

  /**
   * A Groebner basis of the seeds' ideal, every element with its account, or `Left` once the
   * budget is gone. Pairs whose leading monomials are coprime are skipped by Buchberger's product
   * criterion, which is the one refinement here and is sound without further argument.
   */
  private def basis(seeds: Vector[Tracked], meter: Meter): Either[Long, (Vector[Tracked], Meter)] = {
    @tailrec
    def go(current: Vector[Tracked], pairs: List[(Int, Int)], meter: Meter): Either[Long, (Vector[Tracked], Meter)] =
      pairs match {
        case Nil => Right((current, meter))
        case (i, j) :: rest =>
          val li = leading(current(i).poly).get._1
          val lj = leading(current(j).poly).get._1
          if (times(li, lj) == lcm(li, lj)) go(current, rest, meter)
          else
            sPolynomial(current(i), current(j), meter).flatMap((s, m) => reduce(s, current, m)) match {
              case Left(spent) => Left(spent)
              case Right((reduced, charged)) if reduced.poly.isEmpty => go(current, rest, charged)
              case Right((reduced, charged)) =>
                val index = current.length
                go(current :+ reduced, rest ++ current.indices.map(_ -> index), charged)
            }
      }

    val initial = for { j <- seeds.indices.toList; i <- (0 until j).toList } yield (i, j)
    go(seeds, initial, meter)
  }
}
