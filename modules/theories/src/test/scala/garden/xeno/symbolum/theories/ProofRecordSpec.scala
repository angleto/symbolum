package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What a theorem rests on, now that it records how it was obtained.
 *
 * A sequent has always said what was assumed. It has never said what was **believed**: which of the
 * sixteen an ordinary arithmetic identity needs, and which it never touches. That is a question a
 * reader of a formal development asks about every result and that nothing here could answer before
 * 2026-09-10.
 */
class ProofRecordSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val ring = Ring.standard
  private val reals = ring.reals

  private def axiomsOf(theorem: Kernel.Thm): Vector[String] =
    Derivation.axiomsOf(theorem).toVector.map(reals.show).sorted

  "An arithmetic identity" should "name the axioms it needs and no others" in {
    // The five it uses are the ring's, and the list is worth reading for what is absent: the whole
    // of the order, and completeness. A theorem about numerals does not touch them, and until a
    // proof was recorded nobody could say so from the theorem itself.
    val product = force(Arithmetic.standard.multiply(12, 12))

    reals.show(product.conclusion) shouldBe "12 * 12 = 144"
    axiomsOf(product) shouldBe Vector(
      "!x:real. !y:real. !z:real. x * (y + z) = x * y + x * z",
      "!x:real. !y:real. !z:real. x + y + z = x + (y + z)",
      "!x:real. !y:real. x * y = y * x",
      "!x:real. !y:real. x + y = y + x",
      "!x:real. x * 1 = x"
    )
  }

  it should "not rest on completeness, which is the axiom nothing elementary should need" in {
    // Stated on its own because it is the one to notice. `COMPLETENESS` is the axiom that separates
    // the reals from the rationals, it is by far the largest thing on the list, and no identity in
    // the arithmetic goes anywhere near it.
    val completeness = force(reals.axiom("COMPLETENESS")).conclusion
    val identity = force(ring.prove("!x:real. (x + 1) * (x + 1) = x * x + 2 * x + 1"))

    Derivation.axiomsOf(identity) should not contain completeness
    Derivation.axiomsOf(force(Arithmetic.standard.add(1000, 1000))) should not contain completeness
  }

  "An order fact" should "rest on the order axioms, which the arithmetic does not" in {
    // The other side of the same measurement: `0 < 1` is not an axiom here, it is proved, and what
    // it is proved from is exactly the part of the theory the arithmetic never reaches.
    val positive = force(Order.standard.zeroLessOne)

    reals.show(positive.conclusion) shouldBe "0 < 1"
    axiomsOf(positive) should contain("~(1 = 0)")
    axiomsOf(positive) should contain("!x:real. !y:real. x < y \\/ x = y \\/ y < x")
  }

  "The size of a proof" should "be the number of inferences behind it" in {
    // Reported rather than asserted to a figure, since it moves whenever a tactic gets smarter, and
    // the number is only interesting as an order of magnitude. Measured on 2026-09-10: `12 * 12`
    // is about 2600 inferences, `(x + 1)^3` expanded is about 4000, and walking a proof of that
    // size takes under two milliseconds.
    val product = force(Arithmetic.standard.multiply(12, 12))
    val size = Derivation.size(product)

    info(s"12 * 12 = 144 is $size inferences over ${Derivation.axiomsOf(product).size} axioms")
    size should be > 100
  }

  "A theorem proved with no axiom at all" should "say so" in {
    // The logic's own theorems rest on the inference rules and nothing else, which is what makes
    // the connectives definitional extensions rather than assumptions. Now checkable per theorem.
    val logic = Logic.standard
    val p = Term.variable("p", Type.Bool)
    val q = Term.variable("q", Type.Bool)

    val commuted = force(
      for {
        disjunction <- logic.mkDisj(p, q)
        assumed <- LogicError.lift(Kernel.assume(disjunction))
        fromLeft <- LogicError.lift(Kernel.assume(p)).flatMap(logic.rules.disjIntro2(q, _))
        fromRight <- LogicError.lift(Kernel.assume(q)).flatMap(logic.rules.disjIntro1(p, _))
        eliminated <- logic.rules.disjElim(assumed, fromLeft, fromRight)
        theorem <- logic.rules.disch(disjunction, eliminated)
      } yield theorem
    )

    Derivation.axiomsOf(commuted) shouldBe empty
  }
}
