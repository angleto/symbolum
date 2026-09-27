package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * RING and FIELD decide a refusal only over atoms that are free variables, Mycelium card `7bf9d8a2`.
 *
 * Two normal forms that differ over independent atoms differ as functions, which is why a ring
 * refusal was decided. `inv 0` is an atom of that reading and is not independent of anything: the
 * constructed reals prove `inv 0 = 0`, and until 2026-09-27 RING refused that equation and
 * `x / 0 = 0` with standing `Decided`, a decision against two theorems of the chain. Seen red on
 * the tree before the change, both refusals reading `Decided`.
 *
 * The derivation of `inv 0 = 0` is the one the verification of card `8fb6da8b` wrote, repeated
 * here so that this file asserts the claim is a theorem rather than citing a file that is not on
 * the line.
 */
class RingDecidesOnlyFreeAtomsSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(error.toString), identity)

  private val reals = Real.standard

  private def refusal(result: Either[LogicError, Kernel.Thm]): LogicError =
    result.fold(identity, theorem => fail(s"proved ${reals.show(theorem.conclusion)}"))

  "inv 0 = 0" should "be a theorem of the chain with nothing assumed" in {
    val goal = force(reals.proposition("inv (0:real) = 0"))
    val aliases = Vector(force(reals.definition(Real.Inverse)), force(reals.definition(Real.Zero)))
    val unfold = Rewrite.normaliser(
      force(Rewrite.Rule.all(reals.logic, aliases)), Vector.empty, Ordering.by[Term, String](_.toString)
    )
    val onCuts = force(Real.constructed.cuts.fact(Cut.InverseZero))
    val theorem = force(Conv.sym(force(unfold(goal))).flatMap(back => LogicError.lift(Kernel.eqMp(back, onCuts))))
    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe goal
  }

  it should "be refused by RING without a decision, naming the atom that is not free" in {
    Vector("inv (0:real) = 0", "!x:real. x / 0 = 0").foreach { text =>
      val error = refusal(Ring.standard.prove(text))
      withClue(s"$text: ${error.message}\n") {
        error.standing should not be LogicError.Standing.Decided
        error match {
          case NotEqualAsRead(_, _, bound) => bound.map(reals.show) should contain("inv 0")
          case other => fail(s"expected the reading's refusal, got $other")
        }
      }
    }
  }

  it should "be refused by FIELD without a decision too" in {
    val error = refusal(Field.standard.prove("!x:real. x / 0 = 0"))
    error.standing should not be LogicError.Standing.Decided
  }

  "A difference over free variables" should "still be decided, which is the control" in {
    // Without this the lines above are satisfied by a RING that never decides anything.
    Vector("!x:real y:real. x * y = y + x", "!x:real. x + 1 = x", "(2:real) = 3").foreach { text =>
      val error = refusal(Ring.standard.prove(text))
      withClue(s"$text: ${error.message}\n") {
        error shouldBe a[NotEqualTo]
        error.standing shouldBe LogicError.Standing.Decided
      }
    }
  }

  "A symbolic inverse" should "not be decided either, since inv x and x are not independent" in {
    // True of the reals with `inv 0 = 0`, at zero and away from it, and a difference over `x` and
    // `inv x` as a ring reads them.
    val error = refusal(Ring.standard.prove("!x:real. x * inv x * x = x"))
    error.standing should not be LogicError.Standing.Decided
  }
}
