package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Arithmetic on a monomial's coefficient, once the coefficient is allowed to be a fraction.
 *
 * Every theorem here has to come back with no hypotheses, and that is the assertion repeated most
 * often below. It is the whole difference between this and [[Field]]: the denominators are
 * numerals, so the side condition every step needs is discharged rather than carried, and a caller
 * that treats what comes back as proved is right to.
 */
class CoefficientSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val coefficients = Coefficient.standard
  private val reals = coefficients.reals

  private def shown(theorem: Kernel.Thm): String = {
    theorem.hypotheses shouldBe empty
    reals.show(theorem.conclusion)
  }

  private def term(numerator: BigInt, denominator: BigInt): Term =
    force(coefficients.termOf(numerator, denominator))

  private def added(
    leftTop: BigInt,
    leftBottom: BigInt,
    rightTop: BigInt,
    rightBottom: BigInt
  ): String =
    shown(force(coefficients.add(term(leftTop, leftBottom), term(rightTop, rightBottom))))

  private def multiplied(
    leftTop: BigInt,
    leftBottom: BigInt,
    rightTop: BigInt,
    rightBottom: BigInt
  ): String =
    shown(force(coefficients.multiply(term(leftTop, leftBottom), term(rightTop, rightBottom))))

  "A numeral denominator" should "have an inverse, with nothing assumed" in {
    // The line the whole file rests on. It is a theorem and not a hypothesis only because
    // `Positivity` sits below the ring, which is what the previous change was for.
    shown(force(coefficients.inverseOf(2))) shouldBe "2 * inv 2 = 1"
    shown(force(coefficients.inverseOf(1))) shouldBe "1 * inv 1 = 1"
  }

  it should "combine with another one into a single inverse" in {
    shown(force(coefficients.inverseOfProduct(2, 3))) shouldBe "inv 2 * inv 3 = inv 6"
  }

  "Any coefficient that is not zero" should "be inverted into another coefficient" in {
    // The numeral case, and then the two that were atoms until 2026-09-09 because `Positivity`
    // proves `~(d = 0)` for a numeral and for nothing else. Neither `-1` nor `2 / 3` is a numeral,
    // and both are inverted here, because `inverseOfUnit` asks for a factor of one instead.
    def inverted(numerator: BigInt, denominator: BigInt): String =
      shown(force(coefficients.ofInverse(numerator, denominator)))

    inverted(2, 1) shouldBe "inv 2 = 1 * inv 2"
    inverted(-1, 1) shouldBe "inv (-1) = -1"
    inverted(2, 3) shouldBe "inv (2 * inv 3) = 3 * inv 2"

    // The sign stays on the numerator, which is what makes one number one term: `-3/4` inverts to
    // `-4/3` and not to `4 / -3`.
    inverted(-3, 4) shouldBe "inv (-3 * inv 4) = -4 * inv 3"
  }

  it should "leave one alone, rather than making it a fraction" in {
    // `inv 1` is `1`, and it has to be: two normal forms for the number one is the one failure a
    // normal form cannot have. It falls out of the general case rather than being a case.
    shown(force(coefficients.ofInverse(1, 1))) shouldBe "inv 1 = 1"
  }

  "Zero" should "have no inverse here, so that inv 0 stays an atom" in {
    // Not a gap. Nothing this arithmetic holds says what `inv 0` is, and nothing multiplies it to
    // one, so giving it a normal form here would be inventing one; the chain proves it zero through
    // `CUT_INV_ZERO`, which is not a fact of this class.
    coefficients.ofInverse(0, 1).isLeft shouldBe true
  }

  "The lemmas a denominator is taken apart with" should "be the ones stated" in {
    // `Field` composes these to build a reciprocal for a denominator of any shape, so each is
    // stated over the reciprocal as a variable rather than about `inv`: that is what lets the next
    // one be built from the last. Pinned because a caller reading `Field`'s hypotheses is entitled
    // to see what they were derived from.
    val arithmetic = Arithmetic.standard

    reals.show(force(Coefficient.unitOfProduct(arithmetic)).conclusion) shouldBe
      // The letters are the printer's: bound variables have no names in a term, and `Printer`
      // invents them by depth, so the fourth is `u` rather than the `q` the source calls it.
      "!x:real. !y:real. !z:real. !u:real. x * z = 1 ==> y * u = 1 ==> x * y * (z * u) = 1"

    reals.show(force(Coefficient.unitOfNegation(arithmetic)).conclusion) shouldBe
      "!x:real. !y:real. x * y = 1 ==> -x * -y = 1"

    reals.show(force(Coefficient.unitReversed(arithmetic)).conclusion) shouldBe
      "!x:real. !y:real. x * y = 1 ==> y * x = 1"
  }

  it should "carry no hypothesis, since none of them assumes anything" in {
    val arithmetic = Arithmetic.standard

    force(Coefficient.unitOfProduct(arithmetic)).hypotheses shouldBe empty
    force(Coefficient.unitOfNegation(arithmetic)).hypotheses shouldBe empty
    force(Coefficient.unitReversed(arithmetic)).hypotheses shouldBe empty
  }

  "The lemma the inversions rest on" should "be the one stated, and carry no hypothesis" in {
    // Stated here because it is what replaced `~(d = 0)` as the price of an inverse, and a reader
    // who wants to argue with that trade needs to see the statement rather than its consequences.
    val lemma = force(Coefficient.inverseOfUnit(Arithmetic.standard))

    reals.show(lemma.conclusion) shouldBe "!x:real. !y:real. x * y = 1 ==> inv x = y"
    lemma.hypotheses shouldBe empty
  }

  "Two whole coefficients" should "add and multiply as they did before" in {
    // The path that existed before fractions did, unchanged and still taken: a coefficient whose
    // denominator is one never reaches a lemma about inverses.
    added(2, 1, 3, 1) shouldBe "2 + 3 = 5"
    added(-2, 1, 5, 1) shouldBe "-2 + 5 = 3"
    added(2, 1, -2, 1) shouldBe "2 + -2 = 0"
    multiplied(-2, 1, 3, 1) shouldBe "-2 * 3 = -6"
  }

  "Two fractions" should "add over a common denominator and come back in lowest terms" in {
    added(1, 2, 1, 3) shouldBe "1 * inv 2 + 1 * inv 3 = 5 * inv 6"
    added(1, 6, 1, 3) shouldBe "1 * inv 6 + 1 * inv 3 = 1 * inv 2"
  }

  it should "stop being a fraction when the denominator divides out" in {
    // The case that makes `x / 2 + x / 2 = x` possible. Without it the answer would be a fraction
    // spelt `1 * inv 1` and every whole number would have two spellings, which is the one thing a
    // normal form cannot have.
    added(1, 2, 1, 2) shouldBe "1 * inv 2 + 1 * inv 2 = 1"
    added(1, 3, 2, 3) shouldBe "1 * inv 3 + 2 * inv 3 = 1"
    added(1, 2, -1, 2) shouldBe "1 * inv 2 + -1 * inv 2 = 0"
  }

  it should "multiply, and reduce what the multiplication produced" in {
    multiplied(2, 3, 3, 4) shouldBe "2 * inv 3 * (3 * inv 4) = 1 * inv 2"
    multiplied(-1, 2, 1, 3) shouldBe "-1 * inv 2 * (1 * inv 3) = -1 * inv 6"
    multiplied(1, 2, 2, 1) shouldBe "1 * inv 2 * 2 = 1"
  }

  "A whole coefficient and a fraction" should "add either way round" in {
    added(1, 1, 1, 2) shouldBe "1 + 1 * inv 2 = 3 * inv 2"
    added(1, 2, 1, 1) shouldBe "1 * inv 2 + 1 = 3 * inv 2"
    added(-1, 1, 1, 2) shouldBe "-1 + 1 * inv 2 = -1 * inv 2"
  }

  "The canonical form" should "put the sign on the numerator and never on the denominator" in {
    reals.show(term(-1, 2)) shouldBe "-1 * inv 2"
    reals.show(term(3, 1)) shouldBe "3"
    reals.show(term(-3, 1)) shouldBe "-3"
  }

  it should "read back the number a coefficient denotes" in {
    coefficients.valueOf(term(-3, 4)) shouldBe Some((BigInt(-3), BigInt(4)))
    coefficients.valueOf(term(5, 1)) shouldBe Some((BigInt(5), BigInt(1)))
    coefficients.valueOf(force(reals.term("x:real"))) shouldBe None
  }

  it should "refuse a fraction that is not in lowest terms, rather than reduce it quietly" in {
    // `termOf` is what every other use has to reach, so it is the place where two spellings of the
    // same number would get in. Reducing here instead would hide the caller that asked wrongly.
    coefficients.termOf(2, 4).isLeft shouldBe true
    coefficients.termOf(1, 0).isLeft shouldBe true
  }

  "The coefficient arithmetic" should "refuse what is not a coefficient" in {
    val variable = force(reals.term("x:real"))

    coefficients.add(variable, term(1, 2)).isLeft shouldBe true
    coefficients.multiply(term(1, 2), variable).isLeft shouldBe true
  }

  it should "add nothing to what has to be believed" in {
    // The foundation the reals are built on, and nothing added (`docs/adr/0053`).
    reals.theory.axioms.toSet shouldBe (Classical.standard.theory.axioms ++ Natural.standard.theory.axioms).toSet
  }
}
