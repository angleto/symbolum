package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * What a coefficient and a degree cost in each of the two ring normal forms, stated so that a
 * machine can check it.
 *
 * The expanding form unfolds `BIT0` and `BIT1`, so `2` becomes `1 + 1` and a coefficient of `n`
 * becomes `n` copies of the term it multiplies. The collecting form does not: a coefficient stays a
 * numeral and the arithmetic on it is the binary procedure in `Arithmetic`. Both are here because
 * the change from one to the other is the point, and a change measured only on the side it improved
 * is not measured.
 *
 * == Why size and not time ==
 *
 * A timing is a fact about a machine on a day. The size of the normal form is a fact about the
 * normal form: deterministic, identical everywhere, and the actual cause of the timings rather than
 * evidence about them. So the assertions here are sizes and the timings are reported beside them,
 * which also means this suite cannot fail because somebody's laptop was busy. The two runs behind
 * the numbers below differed by about a factor of four in time and not at all in size.
 *
 * == This file used to be only the before column ==
 *
 * It was written on 2026-09-04 as the control for replacing the expanding normal form, and it said
 * that when the replacement landed it would fail and that the right response was to record the new
 * numbers rather than to relax the assertion. That is what happened, and both columns are asserted
 * now: the old law is still true of the form it was measured on, and that form is still what proves
 * the lemmas the new one runs on.
 */
class RingCostSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val reals = Real.standard
  private val arithmetic = Arithmetic.standard
  private val collecting = Ring.standard
  private val expanding = force(Ring.expanding(arithmetic))

  /**
   * The ladder, and what it costs to run it.
   *
   * Stops at 32 on purpose. Inside the suite on 2026-09-04 the rungs of the expanding form took 1,
   * 2, 14, 52 and 292 ms in one run and up to four times that in another, and each one costs about
   * what all the ones below it cost together, so a sixth rung would double this file's price to show
   * a shape five rungs already show.
   */
  private val Ladder: Vector[Int] = Vector(1, 2, 4, 8, 16, 32)

  private def size(term: Term): Int = term match {
    case App(function, argument) => 1 + size(function) + size(argument)
    case Abs(_, body) => 1 + size(body)
    case _ => 1
  }

  /** The monomials of a collected normal form: the summands of a right-nested sum. */
  private def monomials(term: Term): Int = term match {
    case App(App(Const(Real.Addition, _), _), rest) => 1 + monomials(rest)
    case _ => 1
  }

  private def read(text: String): Term =
    reals.term(text).fold(error => fail(s"could not read $text: ${error.message}"), identity)

  /** The size of the normal form, and how long it took to get there. */
  private def normalised(ring: Ring, text: String): (Term, Long) = {
    val term = read(text)
    val start = System.nanoTime()
    val theorem = ring
      .normalise(term)
      .fold(error => fail(s"could not normalise $text: ${error.message}"), identity)
    val elapsed = (System.nanoTime() - start) / 1000000

    val form = Term
      .destEq(theorem.conclusion)
      .map(_._2)
      .getOrElse(fail(s"normalising $text did not give an equation"))

    (form, elapsed)
  }

  /** The product of `degree` copies of `x + 1`, since neither form has a power to expand. */
  private def power(degree: Int): String = Vector.fill(degree)("(x:real + 1)").mkString(" * ")

  /* ------------------------------------------------------------ the coefficient */

  "The expanding normal form of a coefficient times an atom" should "grow with the coefficient's value" in {
    val measured = Ladder.map(coefficient => coefficient -> normalised(expanding, s"$coefficient * x:real"))

    info(
      measured
        .map { case (coefficient, (form, elapsed)) => s"$coefficient * x -> ${size(form)} nodes, $elapsed ms" }
        .mkString("; ")
    )

    // Exactly four nodes per copy of the atom, less the three the first copy does not need. The
    // formula matters less than what it says: the normal form is linear in the **value** of the
    // coefficient. Written as an assertion rather than a table so that a reader cannot mistake it
    // for six separate observations.
    measured.foreach { case (coefficient, (form, _)) =>
      withClue(s"$coefficient * x: ") { size(form) shouldBe 4 * coefficient - 3 }
    }
  }

  "The collecting normal form of the same term" should "grow with the coefficient's length" in {
    val measured = (Ladder :+ 1000).map(coefficient =>
      coefficient -> normalised(collecting, s"$coefficient * x:real")
    )

    info(
      measured
        .map { case (coefficient, (form, elapsed)) => s"$coefficient * x -> ${size(form)} nodes, $elapsed ms" }
        .mkString("; ")
    )

    // A numeral of `b` binary digits is `1` under `b - 1` bit constructors, so it has `2b - 1`
    // nodes, and the monomial adds the product and the atom. The whole content of the change is in
    // the contrast with the assertion above: there the size follows the value of the coefficient,
    // here it follows the number of digits it is written with, which is the size of the input. A
    // coefficient of one is absorbed and leaves the atom alone.
    measured.foreach { case (coefficient, (form, _)) =>
      withClue(s"$coefficient * x: ") {
        size(form) shouldBe (if (coefficient == 1) 1 else 2 * BigInt(coefficient).bitLength + 3)
      }
    }

    // The rung neither form was asked for before: `1000 * x` is what `docs/proving.md` named as out
    // of reach, and it is now twenty-three nodes.
    size(normalised(collecting, "1000 * x:real")._1) shouldBe 23
  }

  "A product of two numerals" should "be computed rather than expanded" in {
    val (expandedForm, expandedTime) = normalised(expanding, "12 * 12")
    val (collectedForm, collectedTime) = normalised(collecting, "12 * 12")

    info(s"12 * 12 -> ${size(expandedForm)} nodes in $expandedTime ms expanding, " +
      s"${size(collectedForm)} nodes in $collectedTime ms collecting")

    // 144 in unary, which is what `docs/evaluation.md` records as seconds where the dedicated
    // numeral procedure takes milliseconds.
    size(expandedForm) shouldBe 4 * 144 - 3

    // Two documents quote the node count, and until 2026-09-24 neither was compared with this. The
    // count is spelled from the form rather than from the formula above, so the two documents
    // follow the measurement even where the formula is what moved.
    val nodes = size(expandedForm)
    def flowed(path: String): String =
      new String(java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(path)), "UTF-8")
        .replaceAll("\\s+", " ")
    withClue(s"12 * 12 expands to $nodes nodes: ") {
      flowed("docs/evaluation.md") should include(s"| `12 * 12` | $nodes nodes |")
      flowed("docs/proving.md") should include(s"`12 * 12` reached $nodes nodes")
    }

    // And 144 as the numeral 144, which is eight binary digits: the collecting form reaches the
    // same answer the numeral procedure reaches, because it is the numeral procedure that computes
    // it. This is the one goal in the repository where the two forms differ by a factor of a
    // thousand rather than by a factor.
    reals.show(collectedForm) shouldBe "144"
    size(collectedForm) shouldBe 2 * BigInt(144).bitLength - 1

    arithmetic.multiply(12, 12) match {
      case Right(theorem) => reals.show(theorem.conclusion) shouldBe "12 * 12 = 144"
      case Left(error) => fail(s"the numeral procedure could not multiply: ${error.message}")
    }
  }

  /* ------------------------------------------------------------------ the degree */

  "The expanding normal form of a power" should "double with every degree" in {
    // Stops at four. Degree five took 863 ms and degree six 13.8 s in the run these numbers come
    // from, and the law is established by three rungs as well as by six; the sentence under this
    // one is what the remaining rungs would have said.
    val measured = (2 to 4).map(degree => degree -> normalised(expanding, power(degree)))

    info(
      measured
        .map { case (degree, (form, elapsed)) => s"degree $degree -> ${size(form)} nodes, $elapsed ms" }
        .mkString("; ")
    )

    // The normal form of `(x + 1)^k` is the expansion with every binomial coefficient written in
    // unary, so it has `k * 2^(k+1) + 1` nodes. Measured beyond what this test runs: 769 nodes at
    // degree six, and 98305 at degree twelve, which is why degree six was the ceiling.
    measured.foreach { case (degree, (form, _)) =>
      withClue(s"degree $degree: ") { size(form) shouldBe degree * (1 << (degree + 1)) + 1 }
    }
  }

  "The collecting normal form of a power" should "have one monomial per term of the polynomial" in {
    // Runs to twelve, which is the degree the change was asked for, and cost about 1.2 seconds of
    // this suite to do it when it was written, no later than 2026-09-14. That was most of what this
    // file cost, and it is the assertion the whole change exists for, so it is asserted rather than
    // described.
    val measured = (2 to 12).map(degree => degree -> normalised(collecting, power(degree)))

    info(
      measured
        .map { case (degree, (form, elapsed)) => s"degree $degree -> ${size(form)} nodes, $elapsed ms" }
        .mkString("; ")
    )

    // `(x + 1)^k` has `k + 1` terms, and the normal form has `k + 1` monomials: it is the
    // polynomial rather than its expansion. The node count follows from that and from how each
    // coefficient is written, and it is asserted as measured because it has no short closed form.
    val nodes = Vector(19, 37, 65, 97, 133, 181, 233, 293, 355, 429, 507)

    measured.foreach { case (degree, (form, _)) =>
      withClue(s"degree $degree: ") {
        monomials(form) shouldBe degree + 1
        size(form) shouldBe nodes(degree - 2)
      }
    }
  }

  /* ---------------------------------------------------------- what did not change */

  "A coefficient over a sum" should "still pay for every summand it distributes to" in {
    // Distribution happens in both forms; what changed is what a coefficient costs once it is
    // there. The expanding numbers are the ones this file was written with.
    size(normalised(expanding, "3 * (x:real + 1)")._1) shouldBe 21
    size(normalised(expanding, "x:real + x:real")._1) shouldBe 5

    reals.show(normalised(collecting, "3 * (x:real + 1)")._1) shouldBe "3 + 3 * x"
    reals.show(normalised(collecting, "x:real + x:real")._1) shouldBe "2 * x"
  }
}
