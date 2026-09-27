package garden.xeno.symbolum.theories

import org.scalacheck.Gen
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks
import garden.xeno.symbolum.kernel.*

/**
 * [[SumOfSquares]] over generated forms: a sum of squares is found again, and nothing that is not
 * one is decomposed into one.
 *
 * Untrusted, like [[LinearFormSpec]]'s subject: a wrong decomposition makes `Linarith` miss a proof
 * and cannot make it produce one, because every square it offers is `SQUARE_NONNEG` at a term and
 * `Ring` checks the combination. So these are properties of the procedure's **reach**. The one that
 * matters is the first: a form built as a positive combination of squares of linear forms is
 * decomposed exactly, with nothing left over but a non-negative constant, which is what lets the
 * certificate search find it again.
 */
class SumOfSquaresSpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {

  /**
   * Two hundred cases, `LinearFormSpec`'s count and for its reason: ScalaTest's default of ten is a
   * smoke test. Each case is a decomposition of a matrix of at most four rows, a few hundred
   * `Rational` operations, so the count is bounded by patience rather than by cost.
   */
  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 200)

  private val real: Type = Real.realType

  /** Three unknowns, so a generated square usually shares a cross term with another. */
  private val unknowns: Vector[Term] = Vector("x", "y", "z").map(Term.variable(_, real))

  /** A product key spelt `x*y`, symmetric, as `LinearFormSpec` spells one without a theory. */
  private def key(left: Term, right: Term): Term =
    Term.variable(Vector(spell(left), spell(right)).sorted.mkString("*"), real)

  private def spell(term: Term): String = term match {
    case FVar(name, _) => name
    case other => other.toString
  }

  /** The factors of a key, which is what `LinearForm.factorsOf` is for a caller with a theory. */
  private def factors(term: Term): Vector[Term] =
    spell(term).split('*').toVector.map(Term.variable(_, real))

  private val rationals: Gen[Rational] =
    for {
      numerator <- Gen.choose(-9, 9)
      denominator <- Gen.choose(1, 4)
    } yield Rational.of(BigInt(numerator), BigInt(denominator))

  private val linear: Gen[LinearForm] =
    for {
      weights <- Gen.listOfN(unknowns.length, rationals)
      constant <- rationals
    } yield unknowns.zip(weights).foldLeft(LinearForm.number(constant)) { case (acc, (unknown, weight)) =>
      acc + LinearForm.atom(unknown).scaled(weight)
    }

  private val positive: Gen[Rational] =
    Gen.choose(1, 9).map(value => Rational.of(BigInt(value), BigInt(1)))

  /** A positive combination of one to three squares, and a non-negative constant beside it. */
  private val sumsOfSquares: Gen[LinearForm] =
    for {
      count <- Gen.choose(1, 3)
      squares <- Gen.listOfN(count, Gen.zip(positive, linear))
      extra <- Gen.choose(0, 5)
    } yield squares.foldLeft(LinearForm.number(Rational.of(BigInt(extra), BigInt(1)))) {
      case (acc, (weight, base)) => acc + base.times(base, key).scaled(weight)
    }

  private def rebuilt(squares: Vector[SumOfSquares.Square]): LinearForm =
    squares.foldLeft(LinearForm.zero) { case (acc, square) =>
      acc + square.base.times(square.base, key).scaled(square.weight)
    }

  /** What is left once the squares are taken away, with the zero coefficients dropped. */
  private def remainder(form: LinearForm, squares: Vector[SumOfSquares.Square]): LinearForm = {
    val left = form + (-rebuilt(squares))
    LinearForm(left.coefficients.filter(!_._2.isZero), left.constant)
  }

  "A positive combination of squares" should "be decomposed with a non-negative constant left over" in {
    forAll(sumsOfSquares) { form =>
      val squares = SumOfSquares.of(form, factors)
      val left = remainder(form, squares)
      // A form that happens to have no product atom, every square having collapsed to a constant,
      // has nothing quadratic to decompose and is declined, which is the second case below.
      whenever(form.atoms.exists(atom => factors(atom).length == 2)) {
        left.coefficients shouldBe empty
        left.constant.isNegative shouldBe false
        squares.foreach(_.weight.isPositive shouldBe true)
      }
    }
  }

  "A form with no product atom" should "get no squares" in {
    forAll(linear) { form =>
      SumOfSquares.of(form, factors) shouldBe empty
    }
  }

  "A form with an atom past degree two" should "get no squares, whatever else it holds" in {
    // The control on the first property from the other side: the decomposition is a statement
    // about degree two, and over a monomial of degree three the Gram matrix is not unique.
    val cubic = Term.variable("x*x*y", real)
    forAll(sumsOfSquares) { form =>
      SumOfSquares.of(form + LinearForm.atom(cubic), factors) shouldBe empty
    }
  }

  "A form that is not a sum of squares" should "never be decomposed into one" in {
    // `x * y`, `x * x - 2 * (x * y)` and `x * x - 1`: negative somewhere, so no decomposition can
    // leave a non-negative constant and nothing else. A decomposition that did would be a proof of
    // a false inequality waiting for the certificate search to find it.
    val x = unknowns(0)
    val y = unknowns(1)
    val xy = LinearForm.atom(key(x, y))
    val xx = LinearForm.atom(key(x, x))
    Vector(
      xy,
      xx + xy.scaled(Rational.of(BigInt(-2), BigInt(1))),
      xx + LinearForm.number(Rational.of(BigInt(-1), BigInt(1)))
    ).foreach { form =>
      val left = remainder(form, SumOfSquares.of(form, factors))
      withClue(s"$form: ") {
        (left.coefficients.isEmpty && !left.constant.isNegative) shouldBe false
      }
    }
  }

  "The square of a difference" should "come back as that square" in {
    val x = unknowns(0)
    val y = unknowns(1)
    val difference = LinearForm.atom(x) + (-LinearForm.atom(y))
    val squares = SumOfSquares.of(difference.times(difference, key), factors)
    squares shouldBe Vector(SumOfSquares.Square(Rational.one, difference))
  }
}
