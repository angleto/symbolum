package garden.xeno.symbolum.theories

import org.scalacheck.Gen
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Numerals: how they are written, what they are made of, and the one arithmetic fact the current
 * rules can prove about them.
 *
 * The property in the middle is the one worth having. Reading a numeral and printing one are
 * separate pieces of code, written in different modules from different directions, and the claim
 * that one is the inverse of the other is exactly the kind of thing that holds for the examples
 * someone picks and fails at 1024.
 */
class NumeralSpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {

  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 300)

  private val reals = Real.standard

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  "A numeral" should "be built from the binary encoding" in {
    // 12 is 1100 in binary, read from the least significant bit outwards.
    val twelve = force(Numeral.of(reals, 12))
    val expected = force(reals.term("BIT0 (BIT0 (BIT1 1))"))

    twelve shouldBe expected
  }

  it should "be zero and one when it is written that way" in {
    force(Numeral.of(reals, 0)) shouldBe force(reals.term("0"))
    force(Numeral.of(reals, 1)) shouldBe force(reals.term("1"))
  }

  it should "print as digits" in {
    reals.show(force(Numeral.of(reals, 12))) shouldBe "12"
    reals.show(force(Numeral.of(reals, 0))) shouldBe "0"
  }

  it should "be refused for a negative value" in {
    Numeral.of(reals, -1).left.map(_.getClass) shouldBe Left(classOf[TypeError])
  }

  "Reading and printing a numeral" should "be inverse over any value" in {
    forAll(Gen.chooseNum(0L, 100000L)) { value =>
      val numeral = force(Numeral.of(reals, BigInt(value)))

      Numeral.valueOf(reals, numeral) shouldBe Some(BigInt(value))
      reals.show(numeral) shouldBe value.toString
      force(reals.term(value.toString)) shouldBe numeral
    }
  }

  it should "grow with the number of digits rather than with the value" in {
    // The point of a binary encoding: a term for a million is not a million nodes.
    def size(term: Term): Int = term match {
      case App(fn, argument) => 1 + size(fn) + size(argument)
      case _ => 1
    }

    size(force(Numeral.of(reals, 1000000))) should be < 60
  }

  "A numeral written in a formula" should "read as arithmetic" in {
    val statement = force(reals.proposition("2 + 2 = 4"))

    reals.show(statement) shouldBe "2 + 2 = 4"
  }

  "Doubling" should "prove that a numeral added to itself is twice it" in {
    val two = force(Numeral.of(reals, 2))
    val theorem = force(Numeral.doubling(reals, two))

    reals.show(theorem.conclusion) shouldBe "2 + 2 = 4"
    theorem.hypotheses shouldBe empty
  }

  it should "hold for any numeral, not only for two" in {
    // From one: doubling zero gives `BIT0 0`, which denotes zero without being the canonical
    // spelling of it, and the case below says what that looks like.
    forAll(Gen.chooseNum(1L, 500L)) { value =>
      val numeral = force(Numeral.of(reals, BigInt(value)))
      val theorem = force(Numeral.doubling(reals, numeral))

      reals.show(theorem.conclusion) shouldBe s"$value + $value = ${value * 2}"
    }
  }

  it should "leave a doubled zero unreduced, and print it as what it is" in {
    val zero = force(Numeral.of(reals, 0))
    val theorem = force(Numeral.doubling(reals, zero))

    // `BIT0 0` is zero, but reducing it to the numeral `0` is a proof step nobody has taken here,
    // so the printer does not pretend it has been taken.
    reals.show(theorem.conclusion) shouldBe "0 + 0 = BIT0 0"
  }

  "The odd half of the encoding" should "prove that BIT1 is one more than BIT0" in {
    val three = force(Numeral.of(reals, 3))
    val theorem = force(Numeral.successorOfDouble(reals, force(Numeral.of(reals, 1))))

    // BIT1 1 is 3, and its definition says it is (1 + 1) + 1.
    Numeral.valueOf(reals, three) shouldBe Some(BigInt(3))
    reals.show(theorem.conclusion) shouldBe "3 = 1 + 1 + 1"
  }

  "Defining the numerals" should "add nothing to the trusted base" in {
    reals.theory.axioms.length shouldBe Real.Axioms.length
    reals.theory.definitions.keySet should contain allOf (Real.Bit0, Real.Bit1)
  }
}
