package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.TyApp
import garden.xeno.symbolum.theories.*

/**
 * Reading wider than deciding, which is what makes the naturals reachable from a caller at all.
 *
 * Until 2026-09-10 every entry point in this module took a `RealTheory`, so nothing a caller drives
 * could parse a goal mentioning `num`, and everything the naturals work bought was reachable only
 * from inside `modules/theories`. The measurement that decided the shape of the repair: the tactics
 * reach for six members of the theory they are handed, `logic` twenty-one times, `proposition` six,
 * `theory` three, `show` three, and `term` and `notation` once. That is `Signature`, and the
 * parameter became the interface rather than a bigger class.
 */
class SignatureSpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard

  private val wide =
    Prove.construct(chain.order, chain.series).fold(error => fail(error.message), identity)

  "A goal mentioning num" should "be unstatable to the standard entry point, which is honest" in {
    // Not a defect and worth pinning: `Prove.standard` decides fragments of the reals and reads in
    // the theory of the reals, where `num` is not a type. The refusal is about the text.
    Prove.standard("!n:num. Sum (\\i:num. Power 2 i) n = Power 2 n - 1").isLeft shouldBe true
  }

  it should "be readable by one built over a signature that has it" in {
    // The capability this repair exists for. Before it, the goal could not be handed to any entry
    // point at all; the answer to "can this be proved" was "I cannot parse that", which is not an
    // answer about the mathematics.
    val goal = wide.reals.proposition("!n:num. Sum (\\i:num. Power 2 i) n = Power 2 n - 1")

    goal.isRight shouldBe true
  }

  it should "then be refused for what it is, rather than for being unreadable" in {
    // Reading wider than deciding is the honest arrangement: the procedures are decision procedures
    // for fragments of the reals and they refuse everything else BY NAME, which is this
    // repository's rule for a tactic. "I cannot parse that" and "that is outside my fragment" are
    // different answers and only the second is true of this goal.
    val refusal = wide("!n:num. Sum (\\i:num. Power 2 i) n = Power 2 n - 1")

    refusal.isLeft shouldBe true
    refusal.fold(error => Remedy.of(wide.reals, error).message, _ => "") should not be empty
  }

  "A real goal" should "still be decided by the wider entry point, unchanged" in {
    // The must-accept half. A repair that widened the reader and lost the decisions would have
    // traded the capability for the point of the thing.
    wide("!x:real y:real. (x + y) * (x + y) = x * x + 2 * (x * y) + y * y").isRight shouldBe true
    wide("!x:real y:real. 0 < x /\\ 0 < y ==> 0 < x * y").isRight shouldBe true
  }

  "The signature" should "be what the tactics were measured to use, and no more" in {
    // `Signature` carries no axioms and no derived facts, deliberately: a tactic that wants
    // `LT_TOTAL` wants the theory of the reals specifically and says so by taking one. Asserted by
    // using every member through the interface, so that a member removed from it fails here.
    val signature: Signature = chain.series

    signature.theory.typeOperators.keySet should contain(Natural.TypeName)
    signature.theory.typeOperators.keySet should contain(Real.TypeName)
    signature.notation.numerals should not be empty
    signature.logic.truth.toString should not be empty
    // `0 < 1` is **refused** here, and the reason moved on 2026-09-15 rather than the behaviour
    // being broken. It used to read with nothing annotated because `<` was the reals' order, so the
    // operator determined both numerals; `docs/adr/0018` made `<` two constants, and a claim whose
    // every leaf is a digit string now says nothing about which order or which encoding is meant.
    //
    // This is the widest signature, which is the one that has both. The same text over a
    // development built on the reals alone still reads, because one candidate is not a choice, and
    // `OrderSpec` is where that is asserted. Both halves are here so that neither the refusal nor
    // the escape can be mistaken for the interface being broken.
    signature.proposition("0 < 1").isLeft shouldBe true
    signature.proposition("(0:real) < 1").isRight shouldBe true
    signature.proposition("(0:num) < 1").isRight shouldBe true
    signature.term("0").isLeft shouldBe true
    signature.term("0", TyApp(Real.TypeName, Nil)).isRight shouldBe true
    signature.show(signature.term("0", TyApp(Real.TypeName, Nil)).toOption.get) shouldBe "0"

    // The two signatures a caller might hold, agreeing. `SignatureSpec` reads numerals off the
    // first and `Ask` off the second, and until that day they read them differently.
    signature.term("0").isLeft shouldBe chain.widest.term("0").isLeft
  }
}
