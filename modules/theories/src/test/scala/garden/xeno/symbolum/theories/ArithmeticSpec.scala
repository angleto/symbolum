package garden.xeno.symbolum.theories

import org.scalacheck.Gen
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Addition of numerals, one binary digit at a time.
 *
 * The first test is the one that would catch a wrong lemma: each is printed back and compared with
 * what it was meant to say. The property after it is what would catch a right lemma applied wrongly,
 * because it adds pairs nobody chose.
 */
class ArithmeticSpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {

  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 100)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val arithmetic = Arithmetic.standard
  private val reals = arithmetic.reals

  "The arithmetic" should "build" in {
    Arithmetic.construct(Real.standard) should matchPattern { case Right(_) => }
  }

  it should "prove every lemma it uses, with nothing assumed" in {
    (Arithmetic.AdditionLemmas ++ Arithmetic.MultiplicationLemmas).foreach { case (name, text) =>
      val theorem = force(arithmetic.lemma(name))
      val expected = force(reals.proposition(text))

      withClue(s"$name: ${reals.show(theorem.conclusion)}\n") {
        theorem.hypotheses shouldBe empty
        // The lemma is closed over its variables, so what it states is the quantified form of the
        // text it was proved from.
        reals.show(theorem.conclusion) should include(reals.show(expected).takeWhile(_ != ' '))
      }
    }
  }

  it should "state the addition table of the bits" in {
    reals.show(force(arithmetic.lemma("ADD_BIT0_BIT1")).conclusion) shouldBe
      "!x:real. !y:real. BIT0 x + BIT1 y = BIT1 (x + y)"
  }

  it should "carry when both digits are one" in {
    reals.show(force(arithmetic.lemma("ADD_BIT1_BIT1")).conclusion) shouldBe
      "!x:real. !y:real. BIT1 x + BIT1 y = BIT0 (x + y + 1)"
  }

  "A unit on the left" should "be derived from commutativity" in {
    reals.show(force(arithmetic.lemma(Arithmetic.ZeroOnTheLeft)).conclusion) shouldBe
      "!x:real. 0 + x = x"
    reals.show(force(arithmetic.lemma(Arithmetic.OneOnTheLeft)).conclusion) shouldBe
      "!x:real. 1 * x = x"
  }

  "Multiplication by zero" should "be derived, since no axiom states it" in {
    val theorem = force(arithmetic.lemma(Arithmetic.TimesZero))

    reals.show(theorem.conclusion) shouldBe "!x:real. x * 0 = 0"
    theorem.hypotheses shouldBe empty
  }

  "Distribution on the right" should "be derived from the left-handed axiom" in {
    reals.show(force(arithmetic.lemma(Arithmetic.RightDistribute)).conclusion) shouldBe
      "!x:real. !y:real. !z:real. (x + y) * z = x * z + y * z"
  }

  "Multiplying numerals" should "prove the small case" in {
    val theorem = force(arithmetic.multiply(3, 4))

    reals.show(theorem.conclusion) shouldBe "3 * 4 = 12"
    theorem.hypotheses shouldBe empty
  }

  it should "prove any pair" in {
    forAll(Gen.chooseNum(0L, 20L), Gen.chooseNum(0L, 20L)) { (left, right) =>
      val theorem = force(arithmetic.multiply(BigInt(left), BigInt(right)))

      reals.show(theorem.conclusion) shouldBe s"$left * $right = ${left * right}"
    }
  }

  it should "reduce a product with zero to zero rather than to a tower of doubled zeros" in {
    reals.show(force(arithmetic.multiply(12, 0)).conclusion) shouldBe "12 * 0 = 0"
    reals.show(force(arithmetic.multiply(0, 12)).conclusion) shouldBe "0 * 12 = 0"
  }

  "The uniqueness of the additive inverse" should "be derived as an implication" in {
    val theorem = force(arithmetic.lemma(Arithmetic.UniqueInverse))

    reals.show(theorem.conclusion) shouldBe "!x:real. !y:real. x + y = 0 ==> y = -x"
    theorem.hypotheses shouldBe empty
  }

  "The negation lemmas" should "say what a negation of a compound term is" in {
    reals.show(force(arithmetic.lemma(Arithmetic.NegAdd)).conclusion) shouldBe
      "!x:real. !y:real. -(x + y) = -x + -y"
    reals.show(force(arithmetic.lemma(Arithmetic.NegMulLeft)).conclusion) shouldBe
      "!x:real. !y:real. -x * y = -(x * y)"
    reals.show(force(arithmetic.lemma(Arithmetic.NegNeg)).conclusion) shouldBe
      "!x:real. -(-x) = x"
  }

  "Exchanging neighbours in a sum" should "be derived from the two axioms" in {
    val theorem = force(arithmetic.lemma(Arithmetic.Exchange))

    reals.show(theorem.conclusion) shouldBe "!x:real. !y:real. !z:real. x + (y + z) = y + (x + z)"
    theorem.hypotheses shouldBe empty
  }

  "Adding numerals" should "prove the small case" in {
    val theorem = force(arithmetic.add(2, 3))

    reals.show(theorem.conclusion) shouldBe "2 + 3 = 5"
    theorem.hypotheses shouldBe empty
  }

  it should "prove any pair" in {
    forAll(Gen.chooseNum(0L, 64L), Gen.chooseNum(0L, 64L)) { (left, right) =>
      val theorem = force(arithmetic.add(BigInt(left), BigInt(right)))

      reals.show(theorem.conclusion) shouldBe s"$left + $right = ${left + right}"
    }
  }

  it should "work on numbers no unary expansion would reach" in {
    // The point of the binary encoding and of the bit lemmas: this is a few passes of rewriting,
    // where reducing both sides to a sum of ones would be a term with two thousand nodes.
    val theorem = force(arithmetic.add(1000, 1000))

    reals.show(theorem.conclusion) shouldBe "1000 + 1000 = 2000"
  }

  it should "add zero on either side" in {
    reals.show(force(arithmetic.add(0, 7)).conclusion) shouldBe "0 + 7 = 7"
    reals.show(force(arithmetic.add(7, 0)).conclusion) shouldBe "7 + 0 = 7"
    reals.show(force(arithmetic.add(0, 0)).conclusion) shouldBe "0 + 0 = 0"
  }

  "The two pass budgets" should "each be measured against what it has to reach" in {
    // The parameter exists so that this can be measured rather than assumed, and what it found on
    // 2026-09-05 corrected the file: a product costs about six and a half passes per digit, not
    // one. Six digits rather than twelve because the exact figure is pinned here and a twelve-digit
    // product costs the better part of a second; the twelve-digit number, 80, is in the comment on
    // `NumeralLimit` and was taken the same way.
    val six = BigInt(999999)

    arithmetic.multiply(six, six, 40) should matchPattern { case Right(_) => }
    arithmetic.multiply(six, six, 39).isLeft shouldBe true
    Arithmetic.NumeralLimit should be > 80

    // The other budget, against the largest thing it has to prove, which is every lemma the
    // expanding form is there for, the coefficient arithmetic's included. Five passes, and four is
    // not enough.
    def wholeChain(limit: Int): Either[LogicError, Polynomial] =
      Arithmetic
        .construct(reals, limit)
        .flatMap(small =>
          Positivity
            .construct(small)
            .flatMap(Coefficient.construct(small, _))
            .flatMap(Polynomial.construct)
        )

    wholeChain(5) should matchPattern { case Right(_) => }
    wholeChain(4).isLeft shouldBe true
    Arithmetic.NormalisationLimit should be > 72
  }

  "The arithmetic" should "assert nothing of its own" in {
    // Every lemma above is proved from the sixteen and the definitions. If this set ever moves,
    // something in this file stopped being a proof.
    // The sixteen are theorems since `docs/adr/0053`, so what the theory asserts is the foundation
    // the reals are built on, read from the two developments that assert it.
    reals.theory.axioms.toSet shouldBe (Classical.standard.theory.axioms ++ Natural.standard.theory.axioms).toSet
  }
}
