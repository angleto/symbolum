package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * `notElim` on a mismatched pair, which used to return a theorem.
 *
 * The rules here move a caller's theorem into a schema with `proveHyp`, a cut that is deliberately
 * lenient: aimed at a hypothesis the theorem does not prove, it leaves that hypothesis standing
 * rather than failing. For most rules the shape of the argument is checked first and the leniency
 * is never exercised. `notElim` checked only that its first argument was a negation, so a caller
 * who passed a proof of the wrong proposition got falsity back with an unintended hypothesis
 * attached: sound, not the rule, and invisible to anything that does not count hypotheses.
 *
 * The test is here rather than in the file that found it because the defect is the rule's, and a
 * guard that lived with its first victim would not cover the next caller.
 */
class NotElimSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val logic = Logic.standard
  private val rules = logic.rules

  private val p = Term.variable("p", Type.Bool)
  private val q = Term.variable("q", Type.Bool)

  "Negation elimination" should "give falsity where the two sides are the same proposition" in {
    val negated = force(logic.mkNot(p))
    val settled = force(rules.notElim(
      force(LogicError.lift(Kernel.assume(negated))),
      force(LogicError.lift(Kernel.assume(p)))
    ))

    settled.conclusion shouldBe logic.falsity
    settled.hypotheses should contain theSameElementsAs Vector(negated, p)
  }

  it should "refuse a proof of something else rather than carry it as a hypothesis" in {
    // What this used to return: falsity, with `p` still standing as a hypothesis because the cut
    // could not discharge it, and `q` added beside it. Nothing about the result said the caller
    // had made a mistake.
    val outcome = rules.notElim(
      force(LogicError.lift(Kernel.assume(force(logic.mkNot(p))))),
      force(LogicError.lift(Kernel.assume(q)))
    )

    outcome.isLeft shouldBe true
  }

  it should "still refuse a first argument that is not a negation at all" in {
    // The check that was already there, asserted so that adding the new one cannot remove it.
    rules
      .notElim(
        force(LogicError.lift(Kernel.assume(p))),
        force(LogicError.lift(Kernel.assume(p)))
      )
      .isLeft shouldBe true
  }
}
