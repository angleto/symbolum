package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Integer relation detection, calibrated on relations somebody else found first.
 *
 * The criterion the card set is rediscovery: find a known relation that is indistinguishable from
 * noise at sixteen digits. Two cases do that here and they say different things.
 *
 * **The BBP formula** is the one the method is famous for, and it is the reason this exists at all:
 * `pi = 4 S1 - 2 S4 - S5 - S6` over the four sums `S_j = sum_k 1 / (16^k (8k + j))` was found by
 * putting those five numbers into an integer relation search and reading the answer off. It comes
 * back here with a residual of `8e-200`.
 *
 * **The minimal polynomial of `sqrt2 + sqrt3 + sqrt5`** is the one that shows what the digits are
 * for. Nine values and coefficients up to 960, so it is an accident until about thirty digits: at
 * sixteen the search returns nine plausible-looking small numbers that mean nothing, and it is the
 * same code that at forty returns `x^8 - 40x^6 + 352x^4 - 960x^2 + 576`.
 *
 * And a **negative control**, because a detector that always reports a relation has said nothing:
 * pi with four square roots of primes, at four precisions, never credible.
 */
class RelationSpec extends AnyFlatSpec with Matchers {

  /** `S_j = sum_k 1 / (16^k (8k + j))`, to the arithmetic's precision. */
  private def bbpSum(arithmetic: Arbitrary, j: Int, terms: Int): BigDecimal = {
    var total = BigDecimal(0)
    var k = 0
    while (k < terms) {
      val power = arithmetic.power(BigDecimal(16), BigDecimal(k)).get
      val denominator = arithmetic.product(Vector(power, BigDecimal(8 * k + j)))
      total = arithmetic.sum(Vector(total, arithmetic.over(Vector(BigDecimal(1), denominator)).get))
      k += 1
    }
    total
  }

  /** The five values the BBP relation holds among, computed to `digits` and a margin. */
  private def bbpValues(digits: Int): Vector[BigDecimal] = {
    val arithmetic = Arbitrary.to(digits + 20)
    // Each term is a sixteenth of the one before, so a term buys about 1.2 digits and this buys
    // the margin as well. Too few and the values are wrong past the twentieth digit, at which point
    // there is no relation to find and the search truthfully says so.
    val terms = (digits * 9) / 10 + 12
    Vector(
      arithmetic.pi,
      bbpSum(arithmetic, 1, terms),
      bbpSum(arithmetic, 4, terms),
      bbpSum(arithmetic, 5, terms),
      bbpSum(arithmetic, 6, terms)
    )
  }

  private def rootOf(arithmetic: Arbitrary, n: Int): BigDecimal =
    arithmetic.power(BigDecimal(n), BigDecimal("0.5")).get

  /** The nine powers of `sqrt2 + sqrt3 + sqrt5`, which its minimal polynomial is a relation among. */
  private def surdPowers(digits: Int): Vector[BigDecimal] = {
    val arithmetic = Arbitrary.to(digits + 20)
    val alpha = arithmetic.sum(Vector(rootOf(arithmetic, 2), rootOf(arithmetic, 3), rootOf(arithmetic, 5)))
    (0 to 8).toVector.map(power => arithmetic.power(alpha, BigDecimal(power)).get)
  }

  /* ---------------------------------------------------------------------- the BBP */

  "The BBP formula" should "come back out of five numbers, which is how it went in" in {
    // Not a simulation of the discovery: these are the five numbers, computed here, and the
    // coefficients are what the search returns without being told what to look for.
    Relation.among(bbpValues(200), 200) match {
      case Relation.Found(coefficients, confirmed, residual) =>
        coefficients shouldBe Vector(BigInt(1), BigInt(-4), BigInt(2), BigInt(1), BigInt(1))
        confirmed should be > 150
        residual.abs should be < BigDecimal("1e-190")
        info(s"pi - 4 S1 + 2 S4 + S5 + S6 = $residual, confirmed by $confirmed digits")

      case other => fail(s"expected the BBP relation, got $other")
    }
  }

  it should "be found at fifty digits too, since five values and small coefficients are easy" in {
    // The honest half of the calibration. BBP is the famous case and it is **not** the case that
    // needs the digits: five values with coefficients under five are confirmed by twelve digits at
    // sixteen. What needed hundreds of digits historically was searching a much longer vector of
    // candidate terms, which is a different run from checking a relation among five.
    Relation.among(bbpValues(50), 50) match {
      case Relation.Found(coefficients, _, _) =>
        coefficients shouldBe Vector(BigInt(1), BigInt(-4), BigInt(2), BigInt(1), BigInt(1))
      case other => fail(s"expected the BBP relation, got $other")
    }
  }

  /* ------------------------------------------------------- what the digits are for */

  "A relation with nine terms and three-figure coefficients" should "be noise until it is not" in {
    // The measurement the card asked for, as a ladder. The same call at four precisions: nonsense,
    // nonsense, the right answer with no evidence behind it, and the right answer confirmed.
    val ladder = Vector(16, 25, 30, 40).map(digits => (digits, Relation.among(surdPowers(digits), digits)))

    ladder.foreach { case (digits, outcome) =>
      val shown = outcome match {
        case Relation.Found(coefficients, confirmed, _) =>
          s"Found ${coefficients.mkString(", ")}, confirmed by $confirmed"
        case Relation.NotCredible(coefficients, confirmed) =>
          s"NotCredible ${coefficients.mkString(", ")}, confirmed by $confirmed"
        case Relation.Unusable(why) => s"Unusable: $why"
      }
      info(s"$digits digits: $shown")
    }

    val minimal = Vector(576, 0, -960, 0, 352, 0, -40, 0, 1).map(BigInt.apply)

    // Sixteen digits: an answer, and it is not this one. That is the whole claim about sixteen
    // digits, and it is why this file could not have been written before `Arbitrary`.
    ladder.toMap.apply(16) match {
      case Relation.NotCredible(coefficients, _) => coefficients should not be minimal
      case other => fail(s"expected sixteen digits to produce noise, got $other")
    }

    // Thirty: the right coefficients, and the search says it cannot support them. Reporting this as
    // a find would be right by luck, and luck is not what the confirmation count measures.
    ladder.toMap.apply(30) match {
      case Relation.NotCredible(coefficients, confirmed) =>
        coefficients shouldBe minimal
        confirmed should be < Relation.Confirmation
      case other => fail(s"expected the right answer with no evidence, got $other")
    }

    // Forty: the same answer, and now it is earned.
    ladder.toMap.apply(40) match {
      case Relation.Found(coefficients, confirmed, residual) =>
        coefficients shouldBe minimal
        confirmed should be >= Relation.Confirmation
        residual.abs should be < BigDecimal("1e-30")
      case other => fail(s"expected the minimal polynomial, got $other")
    }
  }

  /* ------------------------------------------------------------- the negative control */

  "Numbers with no relation among them" should "never come back credible, at any precision" in {
    // A detector that always finds something has said nothing. The signature of no relation is in
    // the second column: the coefficients grow with the precision, because what the search returns
    // is the smallest accident the digits allow rather than a fact about the numbers.
    val outcomes = Vector(16, 60, 120).map { digits =>
      val arithmetic = Arbitrary.to(digits + 20)
      val values = Vector(
        arithmetic.pi,
        rootOf(arithmetic, 2),
        rootOf(arithmetic, 3),
        rootOf(arithmetic, 5),
        rootOf(arithmetic, 7)
      )
      (digits, Relation.among(values, digits))
    }

    val sizes = outcomes.map {
      case (digits, Relation.NotCredible(coefficients, confirmed)) =>
        info(s"$digits digits: largest coefficient ${coefficients.map(_.abs).max}, confirmed by $confirmed")
        coefficients.map(_.abs).max

      case (digits, other) => fail(s"at $digits digits, expected no credible relation, got $other")
    }

    sizes shouldBe sizes.sorted
    sizes.head should be < sizes.last
  }

  /* ------------------------------------------------------------------ the easy cases */

  "A relation anybody can see" should "be found" in {
    Relation.among(Vector(BigDecimal(2), BigDecimal(3)), 20) match {
      case Relation.Found(coefficients, _, residual) =>
        coefficients shouldBe Vector(BigInt(3), BigInt(-2))
        residual shouldBe BigDecimal(0)
      case other => fail(s"expected 3 times 2 less 2 times 3, got $other")
    }
  }

  "A question that cannot be put" should "be refused rather than answered" in {
    Relation.among(Vector(BigDecimal(1)), 20) shouldBe a[Relation.Unusable]
    Relation.among(Vector(BigDecimal(0), BigDecimal(0)), 20) shouldBe a[Relation.Unusable]

    // Three digits of precision on a number with five figures in front of the point leaves no
    // decimal places to scale by, and scaling by places that are not there is how a search comes
    // back confident about rounding.
    Relation.among(Vector(BigDecimal(12345), BigDecimal(67890)), 3) shouldBe a[Relation.Unusable]
  }
  /**
   * The two counts of the precision refusal, at one and elsewhere.
   *
   * `core` depends on nothing, so it carries its own counter in `Plural` and this holds one of its
   * two sites. Both numbers in this sentence reach one and they reach it independently: the digits
   * asked for, and the decimal places left after the integer part is paid for. The second is why
   * the guard is `places < 2` rather than `places < 1`.
   */
  "The refusal about precision" should "take the singular at one digit and at one place" in {
    def why(values: Vector[BigDecimal], digits: Int): String =
      Relation.among(values, digits) match {
        case Relation.Unusable(message) => message
        case other => fail(s"expected a refusal and got $other")
      }

    val small = Vector(BigDecimal(1), BigDecimal(2))

    why(small, 1) should startWith("1 digit leaves")
    why(small, 3) should startWith("3 digits leaves")
    why(small, 4) should include("leaves 1 decimal place to scale by")
    why(small, 1) should include("leaves -2 decimal places to scale by")
  }
}
