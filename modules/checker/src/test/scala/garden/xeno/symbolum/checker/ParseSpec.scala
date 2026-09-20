package garden.xeno.symbolum.checker

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * What the reader says when a table does not read as a proof.
 *
 * `SerialisedSpec` is the other half of this file's subject and the one that carries the argument:
 * a proof that left this process as text and came back checked. This one is about a text that does
 * **not** read, because a refusal is the only thing a second reader of a proof produces when the
 * writer is wrong, and the words of it are what a person acts on.
 *
 * The proofs here are written by hand rather than produced by `Proof.write`, and that is the point:
 * what is under test is the reader's message on a table no writer would produce.
 */
class ParseSpec extends AnyFlatSpec with Matchers {

  /**
   * The smallest preamble a step record can stand on: the version line, one type, one free
   * variable of it, and one step that reads, so that what the test reaches is the arity check and
   * not the header.
   */
  private val preamble = Vector(Parse.Version, "y 0 v A", "t 0 f x 0", "s 0 refl 0 ; ; ; 0")

  private def refusal(step: String): String =
    Parse.proof((preamble :+ step).mkString("\n")) match {
      case Left(why) => why
      case Right(_) => fail(s"expected `$step` to be refused")
    }

  /**
   * The premise count in the arity refusal, at one and elsewhere.
   *
   * `checker` sees `kernel` and nothing else, which is what makes it a second reading rather than
   * a second opinion, so it cannot reach the counter the rest of the repository uses and carries
   * its own. This is what holds the copy.
   *
   * One premise is not a corner: `Step.arity` is **1** for `Abstraction`, `Instantiation`,
   * `TypeInstantiation` and `TypeDefinition`, which is four of the rules this reader knows, and
   * until 2026-09-20 a table giving one of them two premises was refused with `1 premises for abs`.
   *
   * Both directions in one test, because a counter stuck in the plural and a counter stuck in the
   * singular are the same defect twice and a test on one of them reports the other as repaired.
   */
  "The refusal about a step's premises" should "take the singular at one and the plural elsewhere" in {
    refusal("s 1 abs 0 ; 0 0 ; ; 0") should include("1 premise for abs, not 2")
    refusal("s 1 trans ; 0 ; ; 0") should include("2 premises for trans, not 1")
  }
}
