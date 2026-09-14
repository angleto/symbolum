package garden.xeno.symbolum.theories

import org.scalacheck.Gen
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks
import garden.xeno.symbolum.kernel.*

/**
 * The laws [[LinearForm]] obeys, over generated forms rather than chosen ones.
 *
 * This suite is the reason the linear form was taken out of `Linarith.scala` on 2026-09-11. It was
 * a class nested in a nineteen-hundred-line object about proving, and nothing could be handed to a
 * property test there without dragging a theory in with it. Out here it is what it always was: a
 * map from atoms to rationals with an algebra, and the algebra either obeys its laws on inputs
 * nobody wrote by hand or it does not.
 *
 * **What a failure here would mean, and it is not a wrong theorem.** Everything in this file is on
 * the untrusted side: a form that misreads a term makes the search miss a proof, and `Ring` checks
 * whatever the search returns. So these are laws the search's *reach* depends on, not its
 * soundness. The one that earns the suite is the last group: `times` is what lets
 * `0 < x /\ 0 < y ==> 0 < x * y` be found at all, and it is the only operation here with a
 * non-obvious definition.
 */
class LinearFormSpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {

  /**
   * ScalaTest's default is ten cases, which is a smoke test and not a property check.
   *
   * Two hundred, which is what `TermPropertySpec` settled on for the same reason and measured at
   * under a second per property. Measured here on 2026-09-11: the whole suite is a few hundred
   * thousand `Rational` operations, and the count is reported rather than timed because a wall
   * clock on this machine reads the afternoon it was taken in.
   */
  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 200)

  private val real: Type = Real.realType

  /**
   * Five atoms, which is enough for two forms to overlap and to miss.
   *
   * Not more: what the properties below exercise is the merging of coefficients on a shared key,
   * and a wide alphabet makes a collision rare instead of ordinary. With five and forms of up to
   * four terms, two generated forms share at least one atom about as often as not.
   */
  private val atoms: Vector[Term] =
    Vector("u", "v", "w", "x", "y").map(Term.variable(_, real))

  private val rationals: Gen[Rational] =
    for {
      numerator <- Gen.choose(-12, 12)
      denominator <- Gen.choose(1, 8)
    } yield Rational.of(BigInt(numerator), BigInt(denominator))

  /**
   * A form built through the operations rather than by filling a map.
   *
   * The distinction decides what the canonical-form property below is about. `LinearForm` does not
   * check its own map, so `LinearForm(Map(x -> 0), 0)` exists and answers `isZero` with `false`
   * while denoting zero. Reached through `atom`, `number`, `+` and `scaled`, that value cannot
   * arise, and the property says so rather than the constructor.
   */
  private val forms: Gen[LinearForm] =
    for {
      size <- Gen.choose(0, 4)
      constant <- rationals
      terms <- Gen.listOfN(
        size,
        for {
          atom <- Gen.oneOf(atoms)
          weight <- rationals
        } yield LinearForm.atom(atom).scaled(weight)
      )
    } yield terms.foldLeft(LinearForm.number(constant))(_ + _)

  /**
   * A key for the product of two atoms, symmetric in its arguments.
   *
   * `LinearForm.times` takes this from its caller because a form never builds terms, and the real
   * caller is `LinearForm.productAtom`, which sorts the factors so that `x * y` and `y * x` are one
   * key. This stands in for it without a signature: same contract, same symmetry, no theory.
   */
  private def key(left: Term, right: Term): Term =
    Term.variable(Vector(spell(left), spell(right)).sorted.mkString("*"), real)

  private def spell(term: Term): String = term match {
    case FVar(name, _) => name
    case other => other.toString
  }

  /* ------------------------------------------------------------------- addition */

  "Addition of forms" should "be commutative" in {
    forAll(forms, forms) { (left, right) => (left + right) shouldBe (right + left) }
  }

  it should "be associative" in {
    forAll(forms, forms, forms) { (first, second, third) =>
      ((first + second) + third) shouldBe (first + (second + third))
    }
  }

  it should "have the zero form as its identity" in {
    forAll(forms) { form => (form + LinearForm.zero) shouldBe form }
  }

  it should "cancel a form against its negation" in {
    forAll(forms) { form =>
      (form + -form).isZero shouldBe true
      (form + -form) shouldBe LinearForm.zero
    }
  }

  it should "add coefficients atom by atom, which is what the search reads" in {
    forAll(forms, forms) { (left, right) =>
      atoms.foreach(atom => (left + right).at(atom) shouldBe (left.at(atom) + right.at(atom)))
    }
  }

  /* ------------------------------------------------------- the canonical form */

  "A form reached through the operations" should "never hold a zero coefficient" in {
    // What `isZero` and `atoms` both assume. `+` filters the zeroes out and `scaled` by zero
    // returns the zero form outright; if either stopped doing it, `isZero` would start answering
    // `false` about a form that denotes zero and the contradiction search would stop finding
    // contradictions. Nothing else in the tree asserts this.
    forAll(forms, forms, rationals) { (left, right, factor) =>
      (left + right).coefficients.values.exists(_.isZero) shouldBe false
      left.scaled(factor).coefficients.values.exists(_.isZero) shouldBe false
      left.times(right, key).coefficients.values.exists(_.isZero) shouldBe false
    }
  }

  it should "have exactly its support as its atoms" in {
    forAll(forms) { form =>
      form.atoms.foreach(atom => form.at(atom).isZero shouldBe false)
      atoms.filterNot(form.atoms.contains).foreach(atom => form.at(atom) shouldBe Rational.zero)
    }
  }

  /* -------------------------------------------------------------------- scaling */

  "Scaling" should "distribute over addition" in {
    forAll(forms, forms, rationals) { (left, right, factor) =>
      (left + right).scaled(factor) shouldBe (left.scaled(factor) + right.scaled(factor))
    }
  }

  it should "compose by multiplying the factors" in {
    forAll(forms, rationals, rationals) { (form, first, second) =>
      form.scaled(first).scaled(second) shouldBe form.scaled(first * second)
    }
  }

  it should "leave a form alone at one and flatten it at zero" in {
    forAll(forms) { form =>
      form.scaled(Rational.one) shouldBe form
      form.scaled(Rational.zero) shouldBe LinearForm.zero
    }
  }

  it should "negate exactly as scaling by minus one does" in {
    forAll(forms) { form => -form shouldBe form.scaled(-Rational.one) }
  }

  /* ------------------------------------------------------------------- the product */

  "The product of two forms" should "be commutative when the atom key is" in {
    // The only reason `productAtom` sorts its factors. If the key stopped being symmetric, a
    // hypothesis manufactured from `0 < x` and `0 < y` would land on a different column from the
    // goal's own `x * y` and the pair round would silently stop reaching anything.
    forAll(forms, forms) { (left, right) =>
      left.times(right, key) shouldBe right.times(left, key)
    }
  }

  it should "distribute over addition" in {
    forAll(forms, forms, forms) { (first, second, third) =>
      first.times(second + third, key) shouldBe
        (first.times(second, key) + first.times(third, key))
    }
  }

  it should "agree with the rationals when both forms are constants" in {
    forAll(rationals, rationals) { (left, right) =>
      LinearForm.number(left).times(LinearForm.number(right), key) shouldBe
        LinearForm.number(left * right)
    }
  }

  it should "scale a form when one side is a constant" in {
    forAll(forms, rationals) { (form, factor) =>
      form.times(LinearForm.number(factor), key) shouldBe form.scaled(factor)
    }
  }

  it should "come to nothing against the zero form" in {
    forAll(forms) { form => form.times(LinearForm.zero, key).isZero shouldBe true }
  }

  /* -------------------------------------------------- what the type does not promise */

  "A form built by filling its map" should "be able to hold a zero coefficient, which the operations cannot" in {
    // Asserted rather than repaired, and the reason is the boundary this file sits on. Making the
    // constructor normalise would put a check on the hot path of an untrusted search to rule out a
    // value the search cannot produce. What it would buy is that `isZero` answered about the
    // denotation instead of the representation, and nothing asks it to: the two callers of `isZero`
    // both hold forms that came out of `+`.
    //
    // It is written down because a future caller that builds a form from a map of its own would
    // meet it, and would meet it as a search that quietly stopped finding a contradiction.
    val degenerate = LinearForm(Map(atoms.head -> Rational.zero), Rational.zero)

    degenerate.isZero shouldBe false
    degenerate.atoms should contain(atoms.head)
    degenerate.at(atoms.head) shouldBe Rational.zero

    (degenerate + LinearForm.zero) shouldBe LinearForm.zero
  }
}
