package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The goals this repository writes its own lemmas in, put to the entry point that could not read
 * them.
 *
 * `Prove.addressOf` and `Linarith.split` each peeled exactly one antecedent, so a curried
 * implication was addressed by its second antecedent rather than by its conclusion. The corpus is
 * `Order`'s own statements, deliberately: they were written by this repository for its own use, not
 * chosen by me to pass.
 */
class CurriedGoalSpec extends AnyFlatSpec with Matchers {

  private val linarith = Linarith.standard

  private def proved(text: String): Unit =
    withClue(s"$text: ") {
      linarith.prove(text).fold(error => fail(error.message), _ => succeed)
    }

  "A curried implication" should "be the same goal as the conjoined one" in {
    proved("!x:real y:real. 0 < x /\\ 0 < y ==> 0 < x + y")
    proved("!x:real y:real. 0 < x ==> 0 < y ==> 0 < x + y")
  }

  it should "hold at three antecedents and at the mixed shape" in {
    proved("!x:real y:real z:real. 0 < x ==> 0 < y ==> 0 < z ==> 0 < x + y + z")
    proved("!x:real y:real z:real. 0 < x /\\ 0 < y ==> 0 < z ==> 0 < x + y + z")
  }

  "The shape Order writes its own lemmas in" should "be readable, which is what this is about" in {
    // `Order.addPositive` is literally the first of these, and `==>` runs through `Order.scala`
    // from end to end. The entry point could not be handed the statements of the theorems
    // standing beside it.
    proved("!x:real y:real. 0 < x ==> 0 < y ==> 0 < x + y")
    proved("!x:real y:real. x < y ==> 0 < y - x")
    proved("!x:real y:real z:real. x < y ==> y < z ==> x < z")
  }

  /* --------------------------------------------- the conclusion that is a denial */

  "A conclusion that denies something" should "be decided, which it was not" in {
    // `!x. 0 < x ==> ~(x = 0)` is a fact this development HAS as a lemma (`Positivity.NonZero`)
    // and could not decide as a goal: the reader fell through to the contradiction search, which
    // was handed `~(x = 0)` itself and could make nothing of it.
    proved("!x:real. 0 < x ==> ~(x = 0)")
    proved("!x:real y:real. x < y ==> ~(x = y)")
    proved("!x:real y:real. x < y ==> ~(y < x)")
  }

  it should "need no lemma that did not exist, and no new axiom" in {
    // The denial is assumed, falsity is what the search is asked for, and `notIntro` discharges.
    // Same shape as the refutation route one rule along.
    val theorem = linarith
      .prove("!x:real. 0 < x ==> ~(x = 0)")
      .fold(error => fail(error.message), identity)

    theorem.hypotheses shouldBe empty
    garden.xeno.symbolum.kernel.Derivation.axiomsOf(theorem).size should be <= 16
  }

  it should "refuse a denial the hypotheses do not force" in {
    // The must-refuse half: assuming the denied thing and failing to find a contradiction is a goal
    // that does not follow, and the answer is a refusal rather than a shape complaint.
    linarith.prove("!x:real y:real. x < y ==> ~(x < y)").isLeft shouldBe true
    linarith.prove("!x:real. ~(x = 0)").isLeft shouldBe true
  }

  "A curried goal that does not follow" should "still be refused, and not by the reader" in {
    // The must-refuse half: peeling further must not make anything provable that is not.
    linarith.prove("!x:real y:real. 0 < x ==> 0 < y ==> 1 < x + y").isLeft shouldBe true
  }

  "The rebuilt theorem" should "be the goal as stated, which is what catches a peel done backwards" in {
    // `prove` compares what it built against the goal. Discharging the antecedents in the wrong
    // order would give a theorem about a different statement, and this is what makes that a `Left`
    // rather than a wrong answer.
    val goal = "!x:real y:real. 0 < x ==> 0 < y ==> 0 < x + y"
    val theorem = linarith.prove(goal).fold(error => fail(error.message), identity)

    Real.standard.show(theorem.conclusion) shouldBe "!x:real. !y:real. 0 < x ==> 0 < y ==> 0 < x + y"
    theorem.hypotheses shouldBe empty
  }
}
