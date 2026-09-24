package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The series procedure answers inside its fragment in both directions, and outside it refuses in
 * the one of three ways that says what was learned.
 *
 * The three refusals are the file's subject as much as the answers are, for the reason
 * `Refutation` keeps seven apart: a caller that reads "not in the fragment" as "decided against"
 * publishes a divergence nobody proved, and one that reads a refutation as "not in the fragment"
 * throws a theorem away. Each is asserted by its **standing**, which is what a caller branches on,
 * and not only by its sentence.
 */
class ConvergenceSpec extends AnyFlatSpec with Matchers {

  private val chain: Chain = Chain.standard
  private val procedure: Convergence =
    Convergence.construct(chain).fold(error => fail(error.message), identity)

  private def proposition(text: String): Term =
    chain.widest.proposition(text).fold(error => fail(error.message), identity)

  private def proved(text: String): Kernel.Thm =
    procedure.prove(text).fold(error => fail(s"$text: ${error.message}"), identity)

  private def refused(text: String): LogicError =
    procedure.prove(text).fold(identity, theorem => fail(s"$text was proved: ${theorem.conclusion}"))

  "A geometric series" should "be decided in both directions at a numeral ratio" in {
    Vector(
      "?l:real. converges (Sum (\\i:num. Power ((1:real) / 2) i)) l",
      "?l:real. converges (Sum (\\i:num. Power ((0 - 1:real) / 3) i)) l",
      "diverges (Sum (\\i:num. Power (2:real) i))",
      // Magnitude exactly one, from both sides: the ratio test says nothing here and the term test
      // says everything, since the terms stay at magnitude one.
      "diverges (Sum (\\i:num. Power (1:real) i))",
      "diverges (Sum (\\i:num. Power (0 - (1:real)) i))"
    ).foreach { text =>
      withClue(s"$text: ") {
        val theorem = proved(text)
        theorem.conclusion shouldBe proposition(text)
        theorem.hypotheses shouldBe empty
      }
    }
  }

  it should "prove the value it converges to, and answer a wrong value with the right one" in {
    proved("converges (Sum (\\i:num. Power ((1:real) / 2) i)) 2").hypotheses shouldBe empty

    refused("converges (Sum (\\i:num. Power ((1:real) / 2) i)) 3") match {
      case NotEqualTo(wanted, found) =>
        wanted shouldBe chain.widest.term("3:real", TyApp(Real.TypeName, Nil)).fold(e => fail(e.message), identity)
        chain.widest.show(found) should include("inv")
      case other => fail(s"expected the value, got ${other.message}")
    }
  }

  it should "refuse, as a decision, the convergence of a series it proves divergent" in {
    val error = refused("?l:real. converges (Sum (\\i:num. Power (2:real) i)) l")
    error shouldBe a[Denied]
    error.standing shouldBe LogicError.Standing.Decided
    error.asInstanceOf[Denied].proved shouldBe proposition("diverges (Sum (\\i:num. Power (2:real) i))")

    refused("diverges (Sum (\\i:num. Power ((1:real) / 3) i))").standing shouldBe LogicError.Standing.Decided
  }

  "The exponential's, the cosine's and the sine's series" should "converge at a symbolic argument, to the function" in {
    Vector(
      "converges (Sum (\\i:num. Power (x:real) i / real_of_num (NUM_FACT i))) (exp x)",
      "?l:real. converges (Sum (\\k:num. " + Trigonometric.cosineTerm("k") + ")) l",
      "converges (Sum (\\k:num. " + Trigonometric.sineTerm("k") + ")) (sin x)"
    ).foreach { text =>
      withClue(s"$text: ") { proved(text).hypotheses shouldBe empty }
    }
  }

  "A constant factor" should "be carried into the value and out of a divergence where it is not zero" in {
    proved("converges (Sum (\\i:num. 3 * Power ((1:real) / 2) i)) (3 * inv (1 - 1 / 2))").hypotheses shouldBe empty
    proved("diverges (Sum (\\i:num. 5 * Power (3:real) i))").hypotheses shouldBe empty
    proved("diverges (Sum (\\i:num. (1:real)))").hypotheses shouldBe empty

    // At zero there is nothing to carry out of a divergence, since the scaled series converges:
    // this is `SUM_SCALE_DIVERGES`'s hypothesis failing, and the refusal says which fact it could
    // not establish rather than answering either way.
    val zero = refused("diverges (Sum (\\i:num. 0 * Power (3:real) i))")
    zero.standing shouldBe LogicError.Standing.Unread
    zero.message should include("not zero")
  }

  "A summand outside the fragment" should "be named, and learn nothing" in {
    val symbolic = refused("?l:real. converges (Sum (\\i:num. Power (x:real) i)) l")
    symbolic.standing shouldBe LogicError.Standing.Unread
    symbolic.message should include("sign")

    val unread = refused("?l:real. converges (Sum (f:num -> real)) l")
    unread.standing shouldBe LogicError.Standing.Unread
    unread.message should include("lambda")
  }

  /**
   * The refusal the card that asked for this procedure named separately: at ratio limit one the
   * ratio test decides nothing, so what is refused there is refused for that reason and says so,
   * rather than calling a harmonic summand unreadable. Both of these are that class; the second
   * converges and the first does not, and neither is answered.
   */
  it should "say, where the ratio tends to one, that that is why" in {
    Vector(
      "?l:real. converges (Sum (\\i:num. inv (real_of_num (SUC i)))) l",
      "?l:real. converges (Sum (\\i:num. inv (real_of_num (SUC i) * real_of_num (SUC i)))) l"
    ).foreach { text =>
      withClue(s"$text: ") {
        val error = refused(text)
        error.standing shouldBe LogicError.Standing.Unread
        error.message should include("tends to one")
      }
    }

    // And a summand whose ratio does not tend to one, but which is outside the closed forms, is
    // the other refusal: this one converges by the ratio test and is refused as unread.
    val hypergeometric = refused(
      "?l:real. converges (Sum (\\i:num. real_of_num i * Power ((1:real) / 2) i)) l")
    hypergeometric.message should not include "tends to one"
    hypergeometric.message should include(Convergence.Summands)
  }

  "What an answer rests on" should "be the published fact that settles its shape and no other" in {
    val geometric = proved("?l:real. converges (Sum (\\i:num. Power ((1:real) / 2) i)) l")
    val published = chain.limit.fact(Limit.GeometricConverges).fold(e => fail(e.message), identity)
    Derivation.restingOn(geometric, Set(published.conclusion)) shouldBe Set(published.conclusion)
    Derivation.axiomsOf(geometric) shouldBe Derivation.axiomsOf(published)
  }

  "The questions it is asked" should "be read by the constants and nothing else" in {
    procedure.reads(proposition("?l:real. converges (Sum (\\i:num. Power ((1:real) / 2) i)) l")) shouldBe true
    procedure.reads(proposition("diverges (Sum (\\i:num. (1:real)))")) shouldBe true
    procedure.reads(proposition("converges (Sum (\\i:num. (1:real))) 1")) shouldBe true

    // A convergence of a sequence that is not a series is not this procedure's question.
    procedure.reads(proposition("converges (\\n:num. (1:real)) 1")) shouldBe false
    procedure.reads(proposition("(0:real) < 1")) shouldBe false
  }
}
