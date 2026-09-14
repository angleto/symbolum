package garden.xeno.symbolum

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Arithmetic to a stated number of digits, checked against digits somebody else computed.
 *
 * The reference values below are the published expansions of pi, e, log 2, log 10, sin 1, cos 1,
 * tan 1 and the square root of two, rounded to fifty significant digits. They are here rather than
 * computed, because a test that checks a series against itself checks nothing: the whole point of
 * this file is that the series are written by hand and might be wrong, and only a source outside
 * this repository can say that they are not.
 *
 * The `Double` comparisons are the second half of the same argument and they answer a different
 * question. A published constant says the implementation is right where somebody has tabulated it;
 * agreement with `math.exp` over a spread of ordinary arguments says it is right in between, which
 * is where the screening will actually use it.
 */
class ArbitrarySpec extends AnyFlatSpec with Matchers {

  private val fifty = Arbitrary.to(50)

  /** Agreement to within one part in `1e-13`, which is where two `Double` paths part company. */
  private def matchesDouble(got: Option[BigDecimal], want: Double): Unit = {
    got should not be empty
    val value = got.get.toDouble
    withClue(s"got $value, wanted $want: ") {
      math.abs(value - want) should be <= 1e-13 * math.max(1.0, math.abs(want))
    }
  }

  /* ------------------------------------------------------------------ the constants */

  "The constants" should "be the digits everybody else publishes" in {
    fifty.pi.toString shouldBe "3.1415926535897932384626433832795028841971693993751"

    // Fifty significant digits of `e` is `...7247093699|95957`, which rounds up and carries: the
    // last three digits are 000 and the truncation everybody quotes ends 999. The rounding is the
    // right answer and the truncation is the familiar one, which is why this is written out.
    fifty.e.toString shouldBe "2.7182818284590452353602874713526624977572470937000"

    fifty.logTwo.toString shouldBe "0.69314718055994530941723212145817656807550013436026"
  }

  it should "be right at two hundred digits as well, which is where the point of this begins" in {
    // Sixteen digits is what `Double` gives and this file exists because sixteen is not enough for
    // integer relation detection. A constant that were right at fifty and wrong at two hundred
    // would pass every other test here and fail at the only job.
    val wide = Arbitrary.to(200)

    wide.pi.toString shouldBe
      "3." +
      "14159265358979323846264338327950288419716939937510" +
      "58209749445923078164062862089986280348253421170679" +
      "82148086513282306647093844609550582231725359408128" +
      "4811174502841027019385211055596446229489549303820"
  }

  /* ------------------------------------------------------------------- the functions */

  "The exponential" should "agree with the published digits, and with Double in between" in {
    fifty.exp(BigDecimal(-1)).map(_.toString) shouldBe
      Some("0.36787944117144232159552377016146086744581113103177")

    matchesDouble(fifty.exp(BigDecimal(1)), math.exp(1))
    matchesDouble(fifty.exp(BigDecimal("-3.5")), math.exp(-3.5))
    matchesDouble(fifty.exp(BigDecimal(20)), math.exp(20))
    matchesDouble(fifty.exp(BigDecimal("0.0001")), math.exp(0.0001))
    fifty.exp(BigDecimal(0)) shouldBe Some(BigDecimal(1))
  }

  it should "decline an argument whose answer would not fit in memory" in {
    // Not a failure to compute. `exp(200000)` has eighty-six thousand digits in front of the point,
    // and a screen that built one of those per candidate would stop being a screen.
    fifty.exp(BigDecimal(200000)) shouldBe None
    fifty.exp(BigDecimal(-200000)) shouldBe None
    fifty.exp(BigDecimal(100000)) should not be empty
  }

  "The logarithm" should "agree with the published digits, and with Double in between" in {
    fifty.log(BigDecimal(10)).map(_.toString) shouldBe
      Some("2.3025850929940456840179914546843642076011014886288")

    matchesDouble(fifty.log(BigDecimal(2)), math.log(2))
    matchesDouble(fifty.log(BigDecimal("0.5")), math.log(0.5))
    matchesDouble(fifty.log(BigDecimal(1000)), math.log(1000))
    matchesDouble(fifty.log(BigDecimal("0.0000001")), math.log(1e-7))
    matchesDouble(fifty.log(BigDecimal("123456789.987654321")), math.log(123456789.987654321))
    fifty.log(BigDecimal(1)) shouldBe Some(BigDecimal(0))
  }

  it should "have nothing to say at zero or below" in {
    fifty.log(BigDecimal(0)) shouldBe None
    fifty.log(BigDecimal(-1)) shouldBe None
  }

  "The circular functions" should "agree with the published digits, and with Double in between" in {
    fifty.sin(BigDecimal(1)).map(_.toString) shouldBe
      Some("0.84147098480789650665250232163029899962256306079837")
    fifty.cos(BigDecimal(1)).map(_.toString) shouldBe
      Some("0.54030230586813971740093660744297660373231042061792")
    fifty.tan(BigDecimal(1)).map(_.toString) shouldBe
      Some("1.5574077246549022305069748074583601730872507723815")

    // Each quadrant, and past a full turn: the reduction picks a series and a sign from the
    // quadrant, and getting either wrong is invisible in the first one.
    Vector(0.3, 2.0, 3.5, 5.0, 7.5, 100.0, -2.5, -8.0).foreach { argument =>
      withClue(s"at $argument: ") {
        matchesDouble(fifty.sin(BigDecimal(argument)), math.sin(argument))
        matchesDouble(fifty.cos(BigDecimal(argument)), math.cos(argument))
      }
    }
  }

  it should "hold the identity they are usually checked by, to every digit computed" in {
    val argument = BigDecimal("1.2345678901234567890123456789")
    val sine = fifty.sin(argument).get
    val cosine = fifty.cos(argument).get

    fifty.agreeingDigits(fifty.sum(Vector(sine * sine, cosine * cosine)), BigDecimal(1)) shouldBe
      None
  }

  it should "decline an argument too large to reduce, and say where that is" in {
    // Reducing an argument of `10^n` costs `n` digits of working precision. Past the limit the
    // refusal is worth more than the answer; a caller that needs it reduces its own argument.
    fifty.sin(BigDecimal("1e30")) should not be empty
    fifty.sin(BigDecimal("1e31")) shouldBe None
    fifty.cos(BigDecimal("1e31")) shouldBe None
  }

  "The tangent" should "refuse where the cosine cannot be told from zero at the precision asked" in {
    // A finite decimal is never exactly a quarter turn, so this tangent has a value. What it does
    // not have is a value with digits in it: at ten digits the cosine of a quarter turn computed to
    // forty comes out zero, and a quotient by that would be a number-shaped object.
    val quarterTurn = Arbitrary.to(40).pi / 2

    Arbitrary.to(10).tan(quarterTurn) shouldBe None
    Arbitrary.to(10).tan(BigDecimal(1)) should not be empty
  }

  "The power" should "be exact for a whole exponent and go through the logarithm otherwise" in {
    fifty.power(BigDecimal(2), BigDecimal(10)) shouldBe Some(BigDecimal(1024))
    fifty.power(BigDecimal(-2), BigDecimal(3)) shouldBe Some(BigDecimal(-8))
    fifty.power(BigDecimal(2), BigDecimal(-3)) shouldBe Some(BigDecimal("0.125"))
    fifty.power(BigDecimal(0), BigDecimal(3)) shouldBe Some(BigDecimal(0))

    // Three to the thousandth, whose first fifty digits are a fact about integers and not about
    // this file.
    fifty.power(BigDecimal(3), BigDecimal(1000)).map(_.toString) shouldBe
      Some("1.3220708194808066368904552597521443659654220327521E+477")

    // The square root of two, which is the case that caught the defect this comment is about: a
    // `BigDecimal` a caller builds from a literal carries thirty-four digits of context, and going
    // through the public `exp(exponent * log(base))` rounded the product there. It printed fifty
    // digits of which thirty-two were right.
    fifty.power(BigDecimal(2), BigDecimal("0.5")).map(_.toString) shouldBe
      Some("1.4142135623730950488016887242096980785696718753769")
  }

  it should "have nothing to say where there is no real value" in {
    fifty.power(BigDecimal(-2), BigDecimal("0.5")) shouldBe None
    fifty.power(BigDecimal(0), BigDecimal(-1)) shouldBe None

    // Two to the two millionth is sayable and enormous: past the whole-exponent limit it goes
    // through `exp`, whose own ceiling then refuses it.
    fifty.power(BigDecimal(2), BigDecimal(2000000)) shouldBe None
  }

  /* ----------------------------------------------------------------- the comparisons */

  "The comparison" should "count the digits two values have in common" in {
    // The measured false positive of the precision corpus, and the reason this file exists: seven
    // and seven plus a billionth of seven agree to nine digits, which is inside the `Double`
    // screen's tolerance of `1e-8` and nowhere near fifty.
    val value = BigDecimal(7)
    val nudged = fifty.sum(Vector(value, fifty.over(Vector(value, BigDecimal(1000000000))).get))

    fifty.agreeingDigits(value, nudged) shouldBe Some(9)
    fifty.agree(value, nudged, slack = 2) shouldBe false
    fifty.agreeingDigits(value, value) shouldBe None
    fifty.agree(value, value, slack = 0) shouldBe true
  }

  it should "give away the digits the caller asks it to and no more" in {
    val value = BigDecimal(1)
    val nudged = fifty.sum(Vector(value, BigDecimal("1e-45")))

    fifty.agreeingDigits(value, nudged) shouldBe Some(45)
    fifty.agree(value, nudged, slack = 4) shouldBe false
    fifty.agree(value, nudged, slack = 5) shouldBe true
  }

  /* ------------------------------------------------------------------- the arithmetic */

  "The arithmetic" should "be offered here, because doing it outside this file loses digits" in {
    // `BigDecimal("0.1") * x` in a caller rounds to thirty-four digits, silently. Every operation
    // an expression needs is here so that nothing outside has to know that.
    val third = fifty.over(Vector(BigDecimal(1), BigDecimal(3))).get

    third.toString shouldBe "0.33333333333333333333333333333333333333333333333333"
    fifty.product(Vector(third, BigDecimal(3))).toString shouldBe
      "0.99999999999999999999999999999999999999999999999999"
    fifty.less(Vector(BigDecimal(10), BigDecimal(3), BigDecimal(2))) shouldBe BigDecimal(5)
    fifty.sum(Vector(BigDecimal(1), BigDecimal(2), BigDecimal(3))) shouldBe BigDecimal(6)
    fifty.negated(BigDecimal(3)) shouldBe BigDecimal(-3)
    fifty.fraction(1.0, 4.0) shouldBe Some(BigDecimal("0.25"))
  }

  it should "have nothing to say where a divisor is zero" in {
    fifty.over(Vector(BigDecimal(1), BigDecimal(0))) shouldBe None
    fifty.over(Vector(BigDecimal(1), BigDecimal(2), BigDecimal(0))) shouldBe None
    fifty.over(Vector.empty) shouldBe None
    fifty.fraction(1.0, 0.0) shouldBe None
  }

  "A precision" should "be a precision" in {
    an[IllegalArgumentException] should be thrownBy Arbitrary.to(0)
    an[IllegalArgumentException] should be thrownBy Arbitrary.to(-5)
  }

  /* ------------------------------------------------------------------------- the cost */

  "The cost" should "be reported, since it is what decided against taking a dependency" in {
    // The card asked for the choice between `BigDecimal` and an arbitrary-precision library to be
    // made by measuring. This is the measurement: six hundred transcendental evaluations at two
    // hundred digits. A dependency would have to beat this by enough to be worth being a
    // dependency, and at half a millisecond each it does not.
    val wide = Arbitrary.to(200)
    wide.pi

    val started = System.nanoTime()
    (0 until 200).foreach { n =>
      wide.sin(BigDecimal(n))
      wide.log(BigDecimal(n + 1))
      wide.exp(fifty.over(Vector(BigDecimal(n), BigDecimal(100))).get)
    }
    val elapsed = (System.nanoTime() - started) / 1000000

    info(s"600 transcendentals at 200 digits: $elapsed ms, which is a reading and not an assertion")

    // **Reported and not asserted**, and the assertion that used to be here is the reason. It read
    // 336 ms on 2026-09-11 and the guard was set at ten seconds, thirty times looser; it failed the
    // same day under the coverage instrumentation on a machine at a load average of a hundred and
    // sixty. A number another program can move by a factor of thirty is not a number anything can
    // be held to, which is what the cost card says about wall clocks and what `CostCorpusSpec` says
    // at greater length.
    //
    // What the reading is for is a decision already taken and recorded: `docs/adr/0011` chose
    // `BigDecimal` over a dependency on the strength of half a millisecond per transcendental, and
    // a reading that moves tells the next person to take the decision again rather than telling a
    // suite to go red.
    elapsed should be > 0L
  }
}
