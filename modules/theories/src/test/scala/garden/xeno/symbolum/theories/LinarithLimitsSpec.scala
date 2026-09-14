package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.logic.*

/**
 * What the two bounds on the escalation cut, which nothing measured until this file.
 *
 * `Linarith.Facts` and `Linarith.Cubes` were introduced on 2026-09-11 with a measurement behind
 * them — one statement of miniF2F took 439 seconds and then refused — and with only half of the
 * question answered. The half that was missing is the one that matters when somebody later wants to
 * move them: **which proofs does the line cost.** Neither vendored corpus reaches either bound, so
 * the numbers were calibrated against a body of goals that cannot tell them apart from any other
 * numbers.
 *
 * The corpus here is generated rather than chosen, and that is the point. A goal with `n`
 * positivity hypotheses gives a pool of `n` and `n * (n + 1) / 2` pairs, so the fact count is a
 * known function of one parameter and the bound has an exact crossing rather than an anecdote
 * either side of it. Choosing two statements that happen to cross it would measure the statements.
 *
 * == Why a bound is safe to get wrong, and what it costs ==
 *
 * Raising one can only add proofs and lowering one can only remove them: a manufactured product is
 * a theorem like any other and the ring step checks the combination, so the answer is never wrong,
 * only absent. What moves is time and reach, and this file is about the exchange rate.
 */
class LinarithLimitsSpec extends AnyFlatSpec with Matchers {

  private val order = Order.standard

  private def procedure(facts: Int, cubes: Int): Linarith =
    Linarith.at(order, facts, cubes).fold(error => fail(error.message), identity)

  private val standard = procedure(Linarith.Facts, Linarith.Cubes)

  /** Wide enough that neither bound is reached at any size this file asks about. */
  private val unbounded = procedure(400, 400)

  /**
   * `0 < x1 /\ ... /\ 0 < xn ==> 0 < x1 * x2`, which the pair round settles at every size.
   *
   * The extra hypotheses take no part in the certificate: only `0 < x1` times `0 < x2` is needed.
   * They are there to make the fact count grow, which is what the bound is on, so the goal's
   * difficulty is constant and its size is not. Anything this refuses, it refuses for the size.
   */
  private def family(n: Int, conclusion: String): String = {
    val variables = (1 to n).map(index => s"x$index:real").mkString(" ")
    val hypotheses = (1 to n).map(index => s"0 < x$index").mkString(" /\\ ")
    s"!$variables. $hypotheses ==> $conclusion"
  }

  /**
   * Which bound a goal reached, and at what count, or nothing when it reached neither.
   *
   * The count is read off the refusal rather than predicted from the number of hypotheses, and the
   * first version of this file predicted it and was wrong: `n + n * (n + 1) / 2` says 54 facts for
   * nine hypotheses and the procedure reports 76, because the pool is not only the hypotheses. A
   * formula in a test is a second implementation of the thing under test, and this one disagreed
   * with it on the first run.
   */
  private def bound(text: String): Option[(String, Int, Int)] =
    standard.prove(text).left.toOption.collect { case BoundReached(limit, reached, allowed, _) =>
      (limit, reached, allowed)
    }

  "The fact bound" should "cut proofs, and the smallest one it cuts is nine hypotheses" in {
    // The measurement the card asked for, and it is an exact crossing rather than an estimate.
    // Both sides are asserted, because a bound that cut nothing would pass a test that only
    // checked the far side.
    standard.prove(family(8, "0 < x1 * x2")).isRight shouldBe true
    standard.prove(family(9, "0 < x1 * x2")).isRight shouldBe false

    // And it is the bound that refuses it, not the goal: the same goal to the same procedure with
    // the line elsewhere is a theorem.
    unbounded
      .prove(family(9, "0 < x1 * x2"))
      .fold(error => fail(error.message), _.hypotheses shouldBe empty)
  }

  it should "say that it stopped, rather than that the goal does not follow" in {
    // The half of this that is a defect rather than a trade. `0 < x1 /\ ... ==> 0 < x1 * x2` IS a
    // non-negative combination of its hypotheses, and until 2026-09-11 the refusal said it is not.
    // A caller told that stops believing a true claim; a caller told the search stopped raises the
    // line or accepts the wait. `NotNormalised` is the same case one procedure over and is the
    // precedent this follows.
    bound(family(9, "0 < x1 * x2")) match {
      case Some((limit, reached, allowed)) =>
        limit shouldBe "Linarith.Facts"
        allowed shouldBe Linarith.Facts
        reached should be > allowed
        info(s"nine hypotheses reach $reached facts against a bound of $allowed")
      case None => fail("expected a bound")
    }
  }

  it should "not be reached by a small problem, whose refusal is about the goal" in {
    // The control. A goal that is simply false and small enough to be fully explored gets the
    // ordinary refusal, so the case above is about the size and not about every refusal becoming a
    // bound.
    standard.prove(family(3, "1 < x1 * x2")) match {
      case Left(_: BoundReached) => fail("a three-hypothesis problem reached a bound")
      case Left(_) => succeed
      case Right(theorem) => fail(s"a false goal was proved: ${theorem.conclusion}")
    }
  }

  "The cubic bound" should "cut proofs too, and be reached only by a goal the pairs do not reach" in {
    // The second bound, and it takes a different conclusion to reach it. The two guards compare the
    // **same quantity** — the facts plus the manufactured products — against different numbers, so
    // the window in which the cubic one can act at all is between them, and a goal past the fact
    // bound never gets as far as the cubic round. What decides which of the two a goal meets is
    // therefore not its size but whether its conclusion names an atom the pairs already reach: a
    // product of two is reached and refuses on the facts, a product of three is not and gets the
    // cubic round, which then refuses on its own bound.
    //
    // Measured rather than reasoned about: the first version of this test asserted that the cubic
    // bound is reached first because it is the smaller number, and every size in the family above
    // reported the fact bound.
    Linarith.Cubes should be < Linarith.Facts

    val reached = (3 to 8).map(n => (n, bound(family(n, "0 < x1 * x2 * x3"))))

    info(
      "a product of three: " + reached
        .map {
          case (n, Some((limit, at, allowed))) => s"$n->$limit($at/$allowed)"
          case (n, None) => s"$n->none"
        }
        .mkString(", ")
    )

    reached.collect { case (n, Some(("Linarith.Cubes", _, _))) => n } should not be empty

    // And the cubic bound cuts a provable goal exactly as the fact bound does, which is the point
    // of measuring it: six hypotheses and a product of three is refused here and is a theorem with
    // the line elsewhere.
    val six = family(6, "0 < x1 * x2 * x3")
    bound(six).map(_._1) shouldBe Some("Linarith.Cubes")
    unbounded.prove(six).fold(error => fail(error.message), _.hypotheses shouldBe empty)
  }

  "What the bounds buy" should "be reported, since the exchange rate is the whole question" in {
    // Printed rather than asserted: these are wall-clock figures on one machine and they move. The
    // assertion is elsewhere; what a reader wants here is the order of magnitude, because the
    // argument for a bound is that it trades reach for time and neither half means anything alone.
    Vector(
      (6, "0 < x1 * x2 * x3"),
      (8, "0 < x1 * x2"),
      (9, "0 < x1 * x2"),
      (12, "0 < x1 * x2")
    ).foreach { case (n, conclusion) =>
      val goal = family(n, conclusion)

      val bounded = timed(standard.prove(goal))
      val free = timed(unbounded.prove(goal))

      info(
        s"$n hypotheses, $conclusion: at the bounds ${bounded._1} in ${bounded._2} ms, " +
          s"unbounded ${free._1} in ${free._2} ms"
      )
    }

    // What that says on its own is that the bounds buy nothing, and it would be the wrong
    // conclusion to draw from it. The cost they were introduced against is not one call: it is
    // `Abduce`, which runs this procedure once per candidate premise, so a goal that costs twenty
    // milliseconds more here costs that many times over there. Measured through the whole surface
    // on 2026-09-11 over the six heaviest statements of miniF2F: 20.0 seconds at the bounds against
    // 40.6 seconds with them at 400, buying one proof. `docs/evaluation.md` carries it.
    succeed
  }

  private def timed(body: => Either[LogicError, ?]): (String, Long) = {
    val started = System.nanoTime()
    val result = body
    val elapsed = (System.nanoTime() - started) / 1000000L
    (if (result.isRight) "proved" else "refused", elapsed)
  }
}
