package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.OutsideTheIdeal

/**
 * `Prove` asks IDEAL at the equation address, after RING and LINARITH, and only for a theorem.
 *
 * Two directions, because the route has two promises and either can break alone. It must reach a
 * goal only an ideal reaches, which is what it was added for; and its refusal must never be the one
 * reported, because "not in the ideal" is unread, and a goal RING and LINARITH both refused keeps
 * the refusal it had before IDEAL existed. The second is the rule `AGENTS.md` states for every
 * search: it may add a theorem and must never take a refusal away.
 */
class IdealRouteSpec extends AnyFlatSpec with Matchers {

  private val prove = Prove.standard

  private def read(text: String): Term =
    prove.reals.proposition(text).fold(error => fail(s"could not read $text: ${error.message}"), identity)

  "A conclusion in the ideal of the hypotheses' equations" should "be settled by the whole surface" in {
    val goal = read(
      "!a b x y:real. a * x + b * y = 3 /\\ a * (x * x) + b * (y * y) = 7 /\\ " +
        "a * (x * x * x) + b * (y * y * y) = 16 /\\ a * (x * x * x * x) + b * (y * y * y * y) = 42 ==> " +
        "a * (x * x * x * x * x) + b * (y * y * y * y * y) = 20"
    )
    prove(goal) match {
      case Right(Prove.Outcome.Settled(theorem)) =>
        theorem.conclusion shouldBe goal
        theorem.hypotheses shouldBe empty
      case other => fail(s"aime_1990_p15 came back $other")
    }
  }

  "A conclusion outside the ideal" should "keep the refusal it had, and never report IDEAL's" in {
    // FALSE, at x = -1, so no route can ever prove it and the test cannot be broken by the prover
    // getting stronger. The first witness here was `x * x = 0 ==> x = 0`, true and outside the
    // ideal, and the whole surface proves it by another route, which the first run of this file
    // found on 2026-11-10. `x - 1` is not in the ideal of `x * x - 1`, so IDEAL refuses it too,
    // and what comes back must be the refusal of a procedure that read the shape.
    prove(read("!x:real. x * x = 1 ==> x = 1")) match {
      case Left(refusal) =>
        info(refusal.message)
        refusal match {
          case FromLogic(_: OutsideTheIdeal) => fail("IDEAL's refusal was reported")
          case _ => succeed
        }
      case Right(outcome) => fail(s"a false claim was proved: $outcome")
    }
  }
}
