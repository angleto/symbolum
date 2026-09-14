package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.theories.{Linarith, Real}

/**
 * What would have to be assumed, and the three ways answering that could mislead.
 *
 * Every assertion here is about which of four things came back, because the value of this tool is
 * entirely in telling them apart: a premise to assume, a premise that closes the goal by making the
 * premises impossible, a premise whose effect on the premises nobody decided, and nothing at all. A
 * test that checked only that something was proposed would pass against a tool that proposed a
 * contradiction.
 *
 * The third of those was not a case until 2026-09-11 and its members were reported as the first,
 * and that is why the test below about it asserts a *count* over the corpus rather than one
 * example: the defect was invisible on every goal anybody had typed in by hand, because the goals
 * one types in are linear and the satisfiability question is decided for those.
 */
class AbduceSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val abduce = Abduce.standard
  private val linarith = Linarith.standard
  private val reals = Real.standard

  private def gapOf(text: String): Abduce.Gap = force(abduce.missing(text))
  private def shown(gap: Abduce.Gap): Vector[String] = gap.found.map(reals.show)

  /* ------------------------------------------------------------- what it proposes */

  "A conclusion that does not follow" should "come back with the premise that would give it" in {
    // The question a hostile reviewer asks, on the goal that was the border of the fragment until
    // this morning. Nothing about `x` alone gives the sign of a product.
    shown(gapOf("!x:real y:real. 0 < x ==> 0 < x * y")) shouldBe Vector("0 < y")

    // A bound on a combination, which was outside the language until 2026-09-10 and is the shape a
    // missing premise usually has. A bound on `z` is found as well and neither implies the other,
    // so both are reported: what the weakest filter drops is a candidate stronger than another
    // candidate.
    //
    // **The two thresholds moved on 2026-09-11, from `z < 0` and `x + y < 3` to these**, and the
    // direction is the finding. Both old ones close the goal and both are stronger than the truth:
    // with `x + y <= 10` in hand, `z <= 2` is what is needed and `z < 0` asks an author for three
    // units more than the argument uses. They were what the file could offer while its candidates
    // were bounds at the numerals the goal happened to write; they are the supremum now, because
    // the region where the premises hold and the conclusion fails is a polyhedron and the simplex
    // is asked how far each form can go on it.
    shown(gapOf("!x:real y:real z:real. x + y <= 10 /\\ z <= 3 ==> x + y + z <= 12")) shouldBe
      Vector("z <= 2", "x + y <= 9")
  }

  it should "not offer the conclusion back as the premise" in {
    // `0 < x ==> 1 < x` needs `1 < x` and nothing weaker, and `0 < e ==> 1 < e / 3` needs `3 < e`,
    // which is the same statement as its conclusion. Both were reported under `found` until
    // 2026-09-10, where they read as something learned; they close the goal without the premises
    // taking any part, so what they say is that the premises do no work, and that belongs in a list
    // of its own for the reason `vacuous` has one.
    val bound = gapOf("!x:real. 0 < x ==> 1 < x")
    bound.found shouldBe empty
    bound.circular.map(reals.show) shouldBe Vector("1 < x")

    val quotient = gapOf("!e:real. 0 < e ==> 1 < e / 3")
    quotient.found shouldBe empty
    quotient.circular.map(reals.show) shouldBe Vector("3 < x")

    // The one that made this visible: the conclusion proposed verbatim, on a goal whose premise
    // points the other way.
    val plain = gapOf("!x:real. x < 1 ==> 0 < x")
    plain.found shouldBe empty
    plain.circular.map(reals.show) shouldBe Vector("0 < x")

    // And the boundary: a premise that needs the hypotheses to reach the conclusion is not this.
    gapOf("!x:real y:real. x < y ==> 2 * x < y").circular shouldBe empty
  }

  it should "come back with the weakest of them, not the strongest" in {
    // `x < 0` and `y < 0` both close this one, and `y < 0` is the stronger: with `x < y` it gives
    // `x < 0` and more besides. Asking an author for the stronger is asking for more than the
    // argument needs.
    //
    // Pinned because the first version of the filter had the direction backwards and reported
    // `y < 0`. The mistake was invisible on every goal where only one candidate survived, which
    // was all of them except this one.
    //
    // `x <= 0` and not `x < 0` since 2026-09-11: the supremum of `x` on the region is nought and it
    // is not attained there, so the bound at it closes the goal and is weaker than the bound above
    // it. Both strictnesses are offered and the same check that judges every other candidate is
    // what decides between them.
    shown(gapOf("!x:real y:real. x < y ==> 2 * x < y")) shouldBe Vector("x <= 0")
  }

  it should "name a threshold nobody wrote, which is what solving buys over proposing" in {
    // The measurement this change was made from, kept as the test. Before 2026-09-11 the candidates
    // were bounds at zero and at the numerals the goal writes, so a goal whose missing premise sits
    // at two thirds could only be offered something at a whole number. Each line below is the exact
    // weakest premise, and the one in the middle is the case that could not be reached at all:
    // `2 <= 3 * x` is `x >= 2/3`, and neither `2/3` nor anything equivalent appears in the goal.
    shown(gapOf("!x:real y:real. 0 < x ==> 2 < x + y")) shouldBe Vector("2 <= y")
    shown(gapOf("!x:real y:real. 0 < x /\\ 3 * y < 2 ==> y < x")) shouldBe
      Vector("2 <= 3 * x", "y <= 0")
    shown(gapOf("!x:real y:real. 2 * x < 5 ==> x < y")) shouldBe Vector("5 <= 2 * y")
    shown(gapOf("!x:real y:real z:real. x < y ==> x + 1 < y + z")) shouldBe Vector("1 <= z")
  }

  it should "write a threshold below zero, which the numerals of this theory cannot" in {
    // A numeral here is non-negative by construction, so a solved threshold below zero has to be
    // built as a negation. Both strictnesses are here on purpose and they come out differently,
    // which is the check earning its keep: the supremum of `y` is `-3` in both, and it is attained
    // at `x = 0` when the premise is `0 <= x`, so the bound **at** it closes the second goal and
    // not the first.
    shown(gapOf("!x:real y:real. 0 <= x ==> 0 - 3 < x + y")) shouldBe Vector("-3 < y")
    shown(gapOf("!x:real y:real. 0 <= x ==> 0 - 3 <= x + y")) shouldBe Vector("-3 <= y")
  }

  it should "keep drawing bounds from the goal where the region is not a polyhedron" in {
    // The fallback, and the reason it stays. A conclusion that is an equality has no single denial
    // to build a region from, since `~(a = b)` is a disjunction, so there is nothing for the
    // simplex to maximise over and the old candidates are what there is. This asserts the path is
    // alive rather than that its answer is the best one: bounds at the numerals a goal writes are
    // what a goal like this can be offered.
    val gap = gapOf("!x:real y:real. 0 < x ==> x * y = x")

    gap.point should not be empty
    (gap.found ++ gap.circular ++ gap.vacuous) should not be empty
  }

  "Everything proposed" should "be checked by proving the goal with it, not by looking plausible" in {
    // The property that makes the proposal safe to guess. Re-derived here from the report rather
    // than trusted: each premise is put back with the original hypothesis and the goal is proved
    // again, so a report this suite accepts is one a caller could have verified itself.
    val cases = Vector(
      ("!x:real y:real. 0 < x ==> 0 < x * y", "0 < x"),
      ("!x:real y:real. x < y ==> 2 * x < y", "x:real < y:real")
    )

    cases.foreach { case (goal, hypothesis) =>
      val gap = gapOf(goal)
      withClue(s"$goal: ") { gap.found should not be empty }

      gap.found.foreach { premise =>
        val conclusion = goal.substring(goal.indexOf("==>") + 3).trim
        val restated = s"$hypothesis /\\ ${reals.show(premise)} ==> $conclusion"

        withClue(s"$restated: ") {
          force(reals.proposition(restated).flatMap(linarith.prove)).hypotheses shouldBe empty
        }
      }
    }
  }

  /* --------------------------------------------------------- the two ways to mislead */

  "A premise that closes the goal by contradicting the others" should "never be offered as an answer" in {
    // The failure this file exists for, and the one the prototype produced. `x < 0` closes
    // `0 < x ==> anything` because it makes the premises impossible, and an impossible premise set
    // gives every conclusion. It proves the goal, so a tool that stopped at "does it prove the
    // goal" would report it as the thing to assume.
    val gap = gapOf("!x:real. 0 < x ==> 1 < x")

    gap.vacuous.map(reals.show) should contain("x < 0")
    gap.found.map(reals.show) should not contain "x < 0"
  }

  it should "still be reported, because it is worth seeing" in {
    // Kept rather than dropped: a premise set one assumption away from impossible is a fact about
    // the argument, and a reader who is shown nothing cannot tell that case from a goal where no
    // candidate closed anything.
    gapOf("!x:real y:real. 0 < x ==> 0 < x * y").vacuous should not be empty
  }

  "A premise whose effect on the others was never decided" should "be told from one that was" in {
    // The third way to mislead, and the one that was in `found` until 2026-09-11. The premises here
    // carry an equality between reals that is not a linear system, so `Refutation` declines the
    // satisfiability question twice over: the solver cannot read the set, and the sampler will not
    // answer a question whose witnesses lie on a set of measure zero. What came back before was
    // every candidate in `found`, indistinguishable from one the check had passed.
    //
    // `x < 0` is the witness on purpose: with `0 < x` assumed it is impossible, exactly like the
    // case above, and the only difference between the two goals is whether anything could decide
    // that. One says "impossible" and the other has to say "not decided", never "assume it".
    val gap = gapOf("!x:real y:real. 0 < x /\\ x * y = 1 ==> 2 < x")

    gap.unchecked.map(reals.show) should contain("x < 0")
    gap.found.map(reals.show) should not contain "x < 0"
    gap.vacuous shouldBe empty
  }

  it should "be why the answer is cheap, since comparing unchecked candidates is what cost the time" in {
    // What this guards is a shape and not a duration: the filter that keeps only the weakest of the
    // candidates runs a decision procedure per pair, and under premises that may be impossible every
    // pair comes back equivalent, so it is quadratic work over a list that collapses to one.
    // `Abduce.Gap.unchecked` carries the measurement that found it: 111 seconds on one statement of
    // miniF2F, of which about eleven were the candidates.
    //
    // **The shape is what is asserted, since 2026-09-11.** It used to be the elapsed time under a
    // twenty-second bound, which is the kind of number another program on the machine moves: the
    // same suite has read 41 seconds and 6 minutes 39 on one tree in one afternoon. What the
    // quadratic comparison would do is put the unchecked candidates through `weakest` and so into
    // `found`; the assertion is that they are not there, which is the same defect seen from the
    // side a machine cannot move, and it is checked at a goal that has many of them.
    val started = System.nanoTime()
    val gap = gapOf("!x:real y:real. 0 < x /\\ x * y = 1 ==> 2 < x")
    val elapsed = (System.nanoTime() - started) / 1000000L

    gap.unchecked.size should be > 1
    gap.found shouldBe empty

    info(s"the gap took $elapsed ms, which is a reading and not an assertion")
  }

  "A goal nothing in the language closes" should "come back empty rather than with a guess" in {
    // What this needs is `~(x = y)`, and the candidates are bounds. Reporting nothing is the right
    // answer: a tool that widened its language until it always found something would be guessing,
    // and a guess presented as the missing premise is worse than silence.
    val gap = gapOf("!x:real y:real. x <= y ==> x < y")

    gap.found shouldBe empty
    gap.point should not be empty
  }

  "A goal that already follows" should "be refused, not answered with an empty list" in {
    // "Nothing is missing" and "nothing was found" are opposite answers, and an empty list reads as
    // the second. So the first is a refusal.
    abduce.missing("!x:real y:real. 0 < x /\\ 0 < y ==> 0 < x * y") match {
      case Left(error) => Remedy.of(reals, error) shouldBe a[RestateTheProblem]
      case Right(gap) => fail(s"expected a refusal, got $gap")
    }
  }

  "A goal with a quantifier inside it" should "come back with an answer rather than an exception" in {
    // Found on 2026-09-10 by `Cost`, which asks this of every claim no procedure settled and so
    // reached a shape no caller had handed it before. `stripForall` takes the leading quantifiers
    // off and a nested one stays as a lambda, whose body is made of loose indices; the search for
    // candidate premises walked into it and asked the kernel for the type of one. That is
    // `KernelInvariantViolation` thrown out of a tactic whose contract is to refuse, and a caller
    // gathering answers from several procedures loses the ones it already had.
    noException should be thrownBy abduce.missing("?y:real. !x:real. x < y")
    noException should be thrownBy abduce.missing("!x:real. ?y:real. x < y /\\ y < x")
  }

  "The point where the claim fails" should "come back beside the premise, since it is what the premise excludes" in {
    // The only part of this answer a reader can check without trusting anything here: the premises
    // hold at that point and the conclusion does not, so whatever is missing has to rule it out.
    val gap = gapOf("!x:real. 0 < x ==> 1 < x")

    gap.point.getOrElse(fail("no point")) should include("x = 1")
  }
}
