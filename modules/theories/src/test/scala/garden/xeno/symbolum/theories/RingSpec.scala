package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Identities of a commutative ring, proved from the sixteen axioms.
 *
 * The refusals at the end matter as much as the proofs. A tactic that proves everything it is
 * given is either complete or wrong, and this one is neither: it is a decision procedure for the
 * fragment it normalises and it says so by failing on the rest.
 */
class RingSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val ring = Ring.standard
  private val reals = ring.reals

  private def proves(text: String): Kernel.Thm = {
    val theorem = force(ring.prove(text))
    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe force(reals.proposition(text))
    theorem
  }

  "The ring tactic" should "prove commutativity of a sum, which is an axiom" in {
    proves("!x:real y:real. x + y = y + x")
  }

  it should "prove distribution on the right, which is not" in {
    proves("!x:real y:real z:real. (x + y) * z = x * z + y * z")
  }

  it should "prove that a product of sums expands" in {
    proves("!x:real y:real. (x + y) * (x + y) = x * x + 2 * (x * y) + y * y")
  }

  it should "prove the square of a successor" in {
    proves("!x:real. (x + 1) * (x + 1) = x * x + 2 * x + 1")
  }

  it should "prove an identity with three variables" in {
    proves("!x:real y:real z:real. (x + y) * z + x = x * z + y * z + x")
  }

  it should "prove one where the two sides are written in a different order" in {
    proves("!x:real y:real. x * y + y * x = 2 * (x * y)")
  }

  it should "prove an identity about numerals alone" in {
    proves("2 * 3 = 6")
  }

  it should "prove a statement with no quantifiers and free variables" in {
    proves("x:real * (y:real + 1) = x * y + x")
  }

  it should "prove an identity with subtraction" in {
    proves("!x:real y:real. (x + y) - y = x")
  }

  it should "prove that a term cancels itself" in {
    proves("!x:real. x - x = 0")
  }

  it should "prove the difference of two squares" in {
    proves("!x:real y:real. (x - y) * (x + y) = x * x - y * y")
  }

  it should "prove that a negation distributes over a sum" in {
    proves("!x:real y:real. -(x + y) = -x + -y")
  }

  it should "prove that two negations undo each other" in {
    proves("!x:real. -(-x) = x")
  }

  it should "prove an identity mixing subtraction and a coefficient" in {
    proves("!x:real. (x + 1) * (x - 1) = x * x - 1")
  }

  "A coefficient" should "be collected, and expanded by the other form" in {
    // This assertion used to read the other way round, and the sentence it pinned was the reason
    // `1000 * x` was out of reach: there was no step that turned `x + x` into `2 * x`, and `2 * x`
    // became `x + x` instead. Both forms still exist, so both directions are pinned here rather
    // than one of them being deleted.
    val term = force(reals.term("2 * x:real"))

    reals.show(force(ring.normalise(term)).conclusion) shouldBe "2 * x = 2 * x"
    reals.show(force(force(Ring.expanding(Arithmetic.standard)).normalise(term)).conclusion) shouldBe
      "2 * x = x + x"
  }

  it should "be collected over an atom the tactic cannot take apart" in {
    // `Linarith` checks its certificates through this tactic and its atoms are arbitrary terms, so
    // the fragment is wider than variables and numerals. Under `Arithmetic.ringOrder` a numeral
    // sorts before `inv x`, which is what makes this the case a collecting rule between neighbours
    // could not have reached.
    proves("!x:real. 2 * inv x + 3 * inv x = 5 * inv x")
  }

  "The goals the collecting form was asked for" should "be settled end to end" in {
    // Named here rather than left for `RingCorpusSpec` to report as a bucket moving, because a
    // tactic is built when it has proved something end to end and not when its unit tests pass.
    //
    // The first is the one goal in Mathlib's own `ring` corpus that this system could state, could
    // not afford, and now proves. The second is the shape the Collatz algebra needs, `3^6 = 729`,
    // written as a product because the theory has no power. The third is what `docs/proving.md`
    // called out of reach for as long as coefficients were expanded.
    proves("876544 * -1 + (1000000 - 123456) = 0")
    proves("3 * 3 * 3 * 3 * 3 * 3 = 729")
    proves("!x:real. 1000 * x + 1000 * x = 2000 * x")
  }

  "The ring tactic" should "refuse an equation that is not an identity" in {
    ring.prove("!x:real y:real. x * y = x + y").left.map(_.getClass) shouldBe
      Left(classOf[NotEqualTo])
  }

  it should "refuse a statement that is not an equation" in {
    ring.prove("!x:real. x < x + 1").left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
  }

  it should "settle where a quotient sits, and refuse to cancel it" in {
    // These two used to be one assertion, refused together, under one sentence: "the axiom for
    // `inv` holds only where its argument is not zero". That is the reason for the second and it
    // was never the reason for the first. Moving a quotient around is the definition of `div`
    // read left to right, an equation with no hypothesis; cancelling one is the axiom, which has
    // a hypothesis this tactic cannot state. Unfolding was withheld from both because the two
    // were written down as one thing.
    ring.prove("!x:real y:real z:real. (z * x) / (2 * y) = z * (x / (2 * y))") should matchPattern {
      case Right(_) =>
    }

    // Still refused, and now for the reason that was always the true one: this is `y * inv y = 1`
    // with the hypothesis missing. `Field` is where it becomes provable, and what it returns
    // carries `~(y = 0)` where a reader can see it.
    ring.prove("!x:real y:real. (x * y) / y = x").left.map(_.getClass) shouldBe
      Left(classOf[NotEqualTo])
  }

  it should "refuse an identity that needs the multiplicative inverse" in {
    // `inv` has an axiom only under the hypothesis that its argument is not zero, so no amount of
    // rewriting settles this one.
    ring.prove("!x:real. x * inv x = 1").left.map(_.getClass) shouldBe Left(classOf[NotEqualTo])
  }

  "The theory it proves in" should "still assert only its sixteen axioms" in {
    reals.theory.axioms.length shouldBe Real.Axioms.length
  }
}
