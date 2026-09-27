package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * That a numeral is not zero, proved rather than assumed, below the ring.
 *
 * The fact itself is one line of derivation. What is worth testing is where it lives: it exists at
 * all so that the ring normal form can cancel a numeral denominator, and a normal form cannot use
 * something built on top of it. So the assertions here are half about the theorem and half about
 * the file, and the second half is the one that would rot in silence.
 */
class PositivitySpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val positivity = Positivity.standard
  private val reals = positivity.reals

  "A numeral" should "be proved above zero" in {
    reals.show(force(positivity.positive(12)).conclusion) shouldBe "0 < 12"
  }

  it should "be proved not to be zero, with nothing assumed" in {
    // The whole reason this module exists. `Field` meets the same side condition on a symbolic
    // denominator and can only carry it to the caller; here the denominator is a numeral, so the
    // condition is discharged and what comes back is unconditional.
    val theorem = force(positivity.numeralNonZero(2))

    theorem.hypotheses shouldBe empty
    reals.show(theorem.conclusion) shouldBe "~(2 = 0)"
  }

  it should "follow the length of the numeral and not its value" in {
    // `BIT0 k` is `k + k`, so the climb is one step per bit. A procedure that counted would not
    // return here at all, and that is the difference this asserts: six digits, twenty steps.
    val theorem = force(positivity.numeralNonZero(1000000))

    theorem.hypotheses shouldBe empty
    reals.show(theorem.conclusion) shouldBe "~(1000000 = 0)"
  }

  "Zero and below" should "be refused, naming what could not be done" in {
    positivity.positive(0) match {
      case Left(NotOfForm(expected, _)) => expected shouldBe "a numeral above zero"
      case other => fail(s"expected a refusal naming the shape, got $other")
    }

    positivity.numeralNonZero(-3).isLeft shouldBe true
  }

  "The facts" should "add nothing to what has to be believed" in {
    // The foundation the reals are built on, and nothing added (`docs/adr/0053`).
    reals.theory.axioms.toSet shouldBe (Classical.standard.theory.axioms ++ Natural.standard.theory.axioms).toSet
  }

  it should "be the ones the order reports, rather than a second derivation of them" in {
    // `Order` derives all but three of the facts it holds. The other three are these, and the two
    // sides agreeing is what says so: were `Order` to start deriving them again, the derivations
    // would agree for as long as nobody changed either, which is the failure this catches.
    val order = Order.standard

    force(order.zeroLessOne).conclusion shouldBe force(Ring.standard.positivity.zeroLessOne).conclusion
    force(order.addPositive).conclusion shouldBe force(Ring.standard.positivity.addPositive).conclusion
    force(order.nonZero).conclusion shouldBe force(Ring.standard.positivity.nonZero).conclusion

    Order.ZeroLessOne shouldBe Positivity.ZeroLessOne
    Order.AddPositive shouldBe Positivity.AddPositive
    Order.NonZero shouldBe Positivity.NonZero
  }

  "This module" should "not depend on the ring, which is the whole point of it" in {
    // The claim the file is for: `~(n = 0)` has to be available to the collecting normal form, so
    // it cannot be derived above it. Comments are stripped first because the file explains why it
    // does not depend on the ring, and it has to name the ring in order to say so.
    //
    // `Order` is not on this list and cannot be: `Real.Order` is the name of the `<` constant, so
    // the string appears in the code for a reason that has nothing to do with the module.
    val code = Sources.code(
      "modules/theories/src/main/scala/garden/xeno/symbolum/theories/Positivity.scala"
    )

    code should not include regex("\\bRing\\b")
    code should not include regex("\\bPolynomial\\b")
    code should not include regex("\\bLinarith\\b")
  }
}
