package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The semiring on `num`, and the price that was the whole point of building it.
 *
 * Asserted here: the three lemmas this file has to derive before it can run are the statements it
 * publishes; a spread of identities is decided; **every one of them costs two axioms**, which is
 * what `Modular.identity` charged sixteen for; the fragment's edge is where the docstring says it
 * is; and a false identity is refused.
 *
 * That last one is not a formality and the others are worth nothing without it. A procedure that
 * returned a theorem for every equation put to it would satisfy every assertion above, and the
 * cheapest way for this file to become that is a rule set that rewrites both sides to a constant.
 */
class SemiringSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val peano = chain.peano
  private val semiring = force(Semiring.construct(peano))

  "The semiring" should "derive the three rules Peano does not hold" in {
    Semiring.Statements.foreach { case (name, text) =>
      val theorem = force(semiring.prove(text.dropWhile(_ != '.').drop(1).trim))
      withClue(s"$name: ") {
        theorem.hypotheses shouldBe empty
        Derivation.axiomsOf(theorem) should have size 2
      }
    }
  }

  it should "decide identities of the fragment, and reach no axiom of the reals" in {
    val identities = Vector(
      "NUM_MUL (NUM_ADD x:num y:num) z:num = NUM_ADD (NUM_MUL x z) (NUM_MUL y z)",
      "NUM_MUL (NUM_MUL a:num k:num) c:num = NUM_MUL a (NUM_MUL k c)",
      "NUM_ADD (NUM_MUL n:num u:num) (SUC ZERO) = NUM_ADD (SUC ZERO) (NUM_MUL u n)",
      "NUM_MUL x:num 2 = NUM_ADD x x",
      "NUM_MUL (NUM_ADD x:num y:num) (NUM_ADD x y) = " +
        "NUM_ADD (NUM_ADD (NUM_MUL x x) (NUM_MUL (SUC ZERO) (NUM_MUL x y))) " +
        "(NUM_ADD (NUM_MUL x y) (NUM_MUL y y))"
    )

    identities.foreach { text =>
      val theorem = force(semiring.prove(text))
      withClue(s"$text: ") {
        theorem.hypotheses shouldBe empty
        // The claim this development exists for, and pinned as an equality rather than a ceiling:
        // choice and infinity, which the naturals cost anyway, and nothing else. `Modular.identity`
        // decides the first of these at sixteen.
        Derivation.axiomsOf(theorem) should have size 2
      }
    }
  }

  it should "refuse a false identity" in {
    val wrong = Vector(
      "NUM_ADD x:num y:num = NUM_MUL x y",
      "NUM_MUL x:num 2 = NUM_ADD x (SUC ZERO)",
      "NUM_MUL (NUM_ADD x:num y:num) (NUM_ADD x y) = NUM_ADD (NUM_MUL x x) (NUM_MUL y y)"
    )
    wrong.foreach(text => withClue(s"$text: ")(semiring.prove(text) should be a Symbol("left")))
  }

  /**
   * The edge of the fragment, asserted rather than described.
   *
   * A successor of anything but zero is an atom, so a true identity that needs it opened is refused
   * here and is `Peano.SuccessorTimes` one specialisation away. A truncated difference is an atom
   * too, which is not the same thing: identities **about** it are decided, as long as they are true
   * of any atom whatever, and that is exactly what `Modular.identity` does with it.
   */
  it should "open a successor under a product and not under a sum, and treat a difference as an atom" in {
    // A successor multiplied is opened, which was not so until the conversion of `Modular` on
    // 2026-09-13 measured that the six identities outside this fragment were all this one shape.
    force(semiring.prove("NUM_MUL (SUC (x:num)) (y:num) = NUM_ADD (NUM_MUL x y) y"))

    // And a successor added is still an atom, which is the line that did not move: nothing here
    // turns a written bound into a sum, and `Successor` is still what a claim about one wants.
    semiring.prove("SUC (SUC (x:num)) = NUM_ADD (SUC (x:num)) (SUC ZERO)") should be a Symbol("left")

    val overAnAtom = force(
      semiring.prove(
        "NUM_ADD (NUM_SUB (m:num) (SUC ZERO)) k:num = NUM_ADD k (NUM_SUB (m:num) (SUC ZERO))"
      )
    )
    Derivation.axiomsOf(overAnAtom) should have size 2
  }
}
