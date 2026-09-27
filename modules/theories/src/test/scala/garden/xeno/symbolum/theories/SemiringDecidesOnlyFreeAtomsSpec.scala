package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.logic.*

/**
 * The semiring over `num` decides a refusal only over atoms that are free variables, which is the
 * closing criterion of Mycelium card `7bf9d8a2` read beyond RING and FIELD: no refusal standing
 * `Decided` against a statement the chain proves.
 *
 * `Semiring.prove` goes through `Rewrite.proveEquation` and nothing reads its refusal again, so a
 * difference over an atom such as `NUM_SUB n n` comes out as `NotEqualTo`, standing `Decided`. Its
 * own docstring says an identity true only because a subtraction truncates "is refused rather than
 * decided"; `NUM_SUB n n = 0` is that identity, and it is `NUM_SUB_REFL` in the library.
 *
 * Written by the verification of that card on 2026-09-27 at `fced4c8f`, and seen red there: the
 * refusal read `NotEqualTo`, standing `Decided`.
 */
class SemiringDecidesOnlyFreeAtomsSpec extends AnyFlatSpec with Matchers {

  private lazy val chain = Chain.standard

  private lazy val semiring: Semiring =
    Semiring.construct(chain.peano).fold(error => fail(error.message), identity)

  private def refusal(text: String): LogicError =
    semiring.prove(text).fold(identity, theorem => fail(s"proved $text"))

  "NUM_SUB n n = 0" should "be a theorem the library holds" in {
    Library.of(chain).entries.map(_.name) should contain("NUM_SUB_REFL")
  }

  it should "be refused by the semiring without a decision" in {
    val error = refusal("NUM_SUB n n = 0")
    withClue(s"${error.getClass.getSimpleName}: ${error.message}\n") {
      error.standing should not be LogicError.Standing.Decided
    }
  }

  "A difference over free variables" should "still be decided, which is the control" in {
    // Without this the line above is satisfied by a semiring that never decides anything.
    val error = refusal("NUM_ADD n 1 = n")
    error shouldBe a[NotEqualTo]
    error.standing shouldBe LogicError.Standing.Decided
  }
}
