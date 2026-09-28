package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.logic.*

/**
 * The semiring over `num` decides a refusal only over atoms that are free variables, Mycelium card
 * `22eb8f25`: no refusal standing `Decided` against a statement the chain proves.
 *
 * `Semiring.prove` went through `Rewrite.proveEquation` and nothing read its refusal again, so a
 * difference over an atom such as `NUM_SUB n n` came out as `NotEqualTo`, standing `Decided`, while
 * the library holds `NUM_SUB_REFL`. `CommutativeRing.prove` reads it again now, and the semiring is
 * that ring's instance.
 *
 * Written by the verification of card `7bf9d8a2` on 2026-09-27 at `fced4c8f`, and seen red there
 * before the change: `NotEqualTo: ((NUM_SUB n) n) is not equal to ZERO`. Seen red again on
 * 2026-09-28 with the change in place and `CommutativeRing.prove` stripped of its re-reading, on
 * both statements at once, each `NotEqualTo, Decided`; `tools/verify/perturb-semiring-reading.sh`
 * is that perturbation.
 */
class SemiringDecidesOnlyFreeAtomsSpec extends AnyFlatSpec with Matchers {

  private lazy val chain = Chain.standard

  private lazy val semiring: Semiring =
    Semiring.construct(chain.peano).fold(error => fail(error.message), identity)

  private lazy val names: Set[String] = Library.of(chain).entries.map(_.name).toSet

  private def refusal(text: String): LogicError =
    semiring.prove(text).fold(identity, theorem => fail(s"proved $text"))

  /** Each true statement, with the library lemma that makes it one, and the atom it is read over. */
  private val theorems = Vector(
    ("NUM_SUB n n = 0", "NUM_SUB_REFL", "NUM_SUB"),
    // A successor under a sum, which the semiring leaves as an atom.
    ("NUM_ADD n (SUC m) = SUC (NUM_ADD n m)", "NUM_ADD_SUC", "SUC")
  )

  "A statement the library proves" should "be refused by the semiring without a decision, naming the atom" in {
    // Every case is asked before anything is asserted, so a red names all the misses at once rather
    // than hiding the ones after the first.
    theorems.flatMap { case (text, lemma, head) =>
      val error = refusal(text)
      error match {
        case NotEqualAsRead(_, _, bound)
            if names.contains(lemma) && bound.map(_.toString).exists(_.contains(head)) &&
              error.standing != LogicError.Standing.Decided => None
        case other => Some(s"$text ($lemma held: ${names.contains(lemma)}): ${other.getClass.getSimpleName}, " +
            s"${other.standing}: ${other.message}")
      }
    } shouldBe empty
  }

  "A difference over free variables" should "still be decided, which is the control" in {
    // Without this the line above is satisfied by a semiring that never decides anything.
    Vector("NUM_ADD n 1 = n", "NUM_MUL n m = NUM_ADD n m").foreach { text =>
      val error = refusal(text)
      withClue(s"$text: ${error.message}\n") {
        error shouldBe a[NotEqualTo]
        error.standing shouldBe LogicError.Standing.Decided
      }
    }
  }
}
