package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What the constructed reals say about `inv 0`, which the sixteen never did.
 *
 * While the sixteen were asserted, `inv 0` was a real nothing constrained: `MUL_INVERSE` holds
 * only away from zero and no other statement mentions `inv`. Since `docs/adr/0053` `inv` is
 * defined as `CUT_INV`, which is zero at zero by its definition, and `Cut` proves
 * `CUT_INV_ZERO`. So the theory the reals live in proves `inv 0 = 0` from the definitions alone,
 * whether or not anything publishes it under a name of the reals.
 *
 * Written by the verification of the card that constructed the reals, because the ADR phrases
 * this as "a theorem of the construction and not yet of the reals", and several comments and
 * documents still argue from `inv 0` being unconstrained. This file is the measurement of which
 * reading holds: the derivation below uses nothing but the two alias definitions and the fact of
 * `Cut`, and rests on the foundation's three.
 */
class InverseAtZeroSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(error.toString), identity)

  private val reals = Real.standard
  private val cuts = Real.constructed.cuts

  /** `inv 0 = 0` in the reals' own vocabulary, derived by unfolding the two aliases. */
  private lazy val inverseAtZero: Kernel.Thm = {
    val goal = force(reals.proposition("inv (0:real) = 0"))
    val aliases = Vector(force(reals.definition(Real.Inverse)), force(reals.definition(Real.Zero)))
    val unfold = Rewrite.normaliser(force(Rewrite.Rule.all(reals.logic, aliases)), Vector.empty, Ordering.by[Term, String](_.toString))
    val unfolded = force(unfold(goal))
    val onCuts = force(cuts.fact(Cut.InverseZero))
    force(Conv.sym(unfolded).flatMap(back => LogicError.lift(Kernel.eqMp(back, onCuts))))
  }

  "The constructed reals" should "prove inv 0 = 0 with nothing assumed" in {
    inverseAtZero.hypotheses shouldBe empty
    reals.show(inverseAtZero.conclusion) shouldBe "inv 0 = 0"
  }

  it should "rest that on the foundation's three and on none of the sixteen" in {
    val foundation = reals.theory.axioms.toSet
    Derivation.axiomsOf(inverseAtZero).diff(foundation) shouldBe empty
    // The positive control: an instrument that saw no axiom anywhere would pass the line above.
    Derivation.axiomsOf(inverseAtZero) should not be empty
    Real.spent(inverseAtZero).intersect(Real.sixteen) shouldBe empty
  }

  it should "be a theorem the sixteen do not publish, which is what the ADR records" in {
    val sixteen = Real.Axioms.map { case (name, _) => force(reals.axiom(name)).conclusion }
    sixteen should not contain inverseAtZero.conclusion
  }

  "RING on a zero denominator" should "be recorded with the standing it answers, now that the value is fixed" in {
    // Measured rather than asserted: `FieldSpec` pins that `x / 0 = 0` is refused, and the refusal's
    // standing says whether a caller is told the question is settled. The claim is a theorem of the
    // chain since the reals were constructed, so a `Decided` standing here reads as a decision
    // against a true statement unless it is read as being about the ring fragment only.
    Ring.standard.prove("!x:real. x / 0 = 0") match {
      case Right(theorem) => info(s"proved: ${reals.show(theorem.conclusion)}")
      case Left(error)    => info(s"refused, ${error.standing}: ${error.message}")
    }
    Ring.standard.prove("inv (0:real) = 0") match {
      case Right(theorem) => info(s"proved: ${reals.show(theorem.conclusion)}")
      case Left(error)    => info(s"refused, ${error.standing}: ${error.message}")
    }
    succeed
  }
}
