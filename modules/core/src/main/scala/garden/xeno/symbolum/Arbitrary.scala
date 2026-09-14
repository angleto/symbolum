package garden.xeno.symbolum

import java.math.{BigInteger, MathContext, RoundingMode}
import java.util.concurrent.ConcurrentHashMap
import scala.annotation.tailrec

/**
 * Arithmetic to as many digits as you ask for, including the transcendental functions.
 *
 * The second stage of the numeric screen. `Double` is the first and stays the first: a candidate
 * that already disagrees at sixteen digits does not deserve two hundred, and the shape of this
 * whole system is a cheap filter in front of an expensive one. What the cheap filter cannot do is
 * two things the declared purpose needs.
 *
 * The first is integer relation detection. Finding integer coefficients that annihilate a
 * combination of `k` values costs roughly `k` times the number of digits in the coefficients, and
 * the discoveries in that family (the BBP formula for pi, the Ramanujan-type series) were made at
 * hundreds of digits. At sixteen the method is not imprecise, it is unusable: an accidental
 * agreement to sixteen digits among a handful of values is ordinary.
 *
 * The second is the false positives the first stage already lets through, and there is a measured
 * one: `x + x/1000000000` against `x` differs by one part in a billion, which is under
 * `Discovery.Tolerance`, survives the screen, and is refused by the kernel afterwards. Nobody calls
 * that a discovery today because nothing reports the survivors, but a loop that proposes at volume
 * would, and the noise grows with the volume.
 *
 * == Nothing here can make a theorem ==
 *
 * This is the untrusted half, like everything else in this module. A wrong digit costs a wrong
 * candidate and never a wrong theorem, which is what makes it reasonable to write the series below
 * by hand rather than take a dependency: at a few hundred digits the JDK's `BigDecimal` is fast
 * enough, and `ArbitrarySpec` carries the timing that says so rather than an argument that it
 * should be.
 *
 * == Guard digits, and why the answer is narrower than the work ==
 *
 * Every intermediate is carried at `digits + Guard` and every answer is rounded to `digits`. The
 * guard absorbs what the series lose, which is a constant because every series below is evaluated
 * on an argument already reduced to something of size one. What is **not** constant is what the
 * reductions lose, and the two places that happens buy their own digits and say so: [[exp]] pays
 * for its squarings, and [[sin]] and [[cos]] pay for subtracting a multiple of pi from an argument
 * larger than pi.
 *
 * == What `None` means here ==
 *
 * The same as everywhere else in this repository: no answer, never `false`. The logarithm of a
 * non-positive number, a tangent where the cosine cannot be told from zero at the precision asked
 * for, a power of a negative base at a fractional exponent, an exponential whose argument is so
 * large that the answer would not fit in memory. A caller that reads any of those as a
 * disagreement has turned "I could not ask" into "I asked and it does not hold".
 */
final class Arbitrary private (val digits: Int) {

  import Arbitrary.*

  /** The context every intermediate rounds to. */
  private val working: MathContext = new MathContext(digits + Guard, RoundingMode.HALF_EVEN)

  /** The context an answer is rounded to on its way out. */
  private val reported: MathContext = new MathContext(digits, RoundingMode.HALF_EVEN)

  /**
   * Below this a value cannot be told from zero at the precision asked for.
   *
   * Relative to one, which is the size of a cosine, and used only by [[tan]].
   */
  private val indistinguishable: B = one.movePointLeft(digits)

  /* ------------------------------------------------------------------ the constants */

  /** Pi, by Machin's formula. */
  lazy val pi: BigDecimal = out(piAt(working))

  /** The natural base, which this module otherwise carries as a `Double` literal. */
  lazy val e: BigDecimal = out(expOf(one, working))

  /** The natural logarithm of two, the unit the logarithm's reduction counts in. */
  lazy val logTwo: BigDecimal = out(logTwoAt(working))

  /* ------------------------------------------------------------------- the functions */

  /**
   * `exp(x)`, by halving the argument until the series eats it and squaring back.
   *
   * A negative argument goes through the reciprocal of the positive one: the alternating series at
   * `-x` loses to cancellation exactly the digits the answer is small by, and one division does
   * not.
   */
  def exp(argument: BigDecimal): Option[BigDecimal] = exponential(argument.bigDecimal).map(out)

  /**
   * `log(x)` for a positive `x`, and nothing at all for the rest.
   *
   * Reduced to a mantissa in `[1, 10)` by moving the point, which costs nothing, and then into
   * `[1, 2)` by at most three halvings, where the series in `(m - 1) / (m + 1)` gains about a digit
   * a term. The two constants that buys back, `log 10` and `log 2`, are the same series at a ninth
   * and a third.
   */
  def log(argument: BigDecimal): Option[BigDecimal] = logarithm(argument.bigDecimal).map(out)

  /** `sin(x)`, or nothing when the argument is too large to reduce without losing the answer. */
  def sin(argument: BigDecimal): Option[BigDecimal] = circular(argument, wantSine = true)

  /** `cos(x)`, under the same limit and for the same reason. */
  def cos(argument: BigDecimal): Option[BigDecimal] = circular(argument, wantSine = false)

  /**
   * `tan(x)`, and nothing where the cosine cannot be told from zero at this precision.
   *
   * The refusal is not about the tangent being undefined. A finite decimal is never exactly a
   * quarter turn, so the tangent of one always has a value; what it may not have is a value **this
   * instance knows any digits of**. A cosine computed to fifty digits and coming out at `1e-40`
   * carries ten digits of information, and the quotient by it carries ten as well while looking
   * like fifty. Refusing is the difference between a number and a number-shaped object.
   */
  def tan(argument: BigDecimal): Option[BigDecimal] =
    for {
      s <- sin(argument)
      c <- cos(argument)
      quotient <-
        if (c.bigDecimal.abs.compareTo(indistinguishable) < 0) None
        else Some(out(s.bigDecimal.divide(c.bigDecimal, working)))
    } yield quotient

  /**
   * `base ^ exponent`, two ways, and the split is what makes a negative base usable at all.
   *
   * A whole exponent is repeated squaring, which says something about a negative base. Anything
   * else goes through `exp(exponent * log base)` and therefore wants a positive one; a negative
   * base at a fractional exponent has no real value, which `Double` reports as `NaN` and this
   * reports as nothing.
   */
  def power(base: BigDecimal, exponent: BigDecimal): Option[BigDecimal] =
    whole(exponent) match {
      case Some(n) if math.abs(n) <= WholeExponent =>
        if (base.signum == 0 && n < 0) None
        else Some(out(integerPower(base.bigDecimal, n, working)))

      case _ =>
        // Every step of this one is in `java.math.BigDecimal` under the working context, and that
        // is the whole reason it is not written as `exp(exponent * log(base))` over the public
        // pair. A `BigDecimal` a caller built from a literal carries the default context of
        // thirty-four digits, and multiplying by it rounds to thirty-four: the square root of two
        // came out right to thirty-two digits and wrong after, while printing fifty.
        for {
          logged <- logarithm(base.bigDecimal)
          value <- exponential(exponent.bigDecimal.multiply(logged, working))
        } yield out(value)
    }

  /* ------------------------------------------------------------------- the arithmetic */

  /*
   * Addition and its three neighbours, offered here rather than left to the caller, so that the
   * context every step rounds to lives in one file. A `BigDecimal` a caller built from a literal
   * carries the default context of thirty-four digits and every operation on it silently rounds
   * there, which is how the square root of two came out right to thirty-two digits and wrong after
   * while printing fifty. Nothing outside this file should be doing the arithmetic.
   */

  /** The sum, left to right. */
  def sum(values: Vector[BigDecimal]): BigDecimal =
    out(values.foldLeft(zero)((total, value) => total.add(value.bigDecimal, working)))

  /** The product, left to right. */
  def product(values: Vector[BigDecimal]): BigDecimal =
    out(values.foldLeft(one)((total, value) => total.multiply(value.bigDecimal, working)))

  /** The left-folded difference, which is the shape a subtraction node holds. */
  def less(values: Vector[BigDecimal]): BigDecimal =
    out(values.map(_.bigDecimal).reduceLeft((left, right) => left.subtract(right, working)))

  /** The left-folded quotient, and nothing at all where a divisor is zero. */
  def over(values: Vector[BigDecimal]): Option[BigDecimal] = {
    val terms = values.map(_.bigDecimal)
    if (terms.isEmpty) None
    else
      terms.tail
        .foldLeft[Option[B]](Some(terms.head)) { (running, divisor) =>
          running.flatMap(dividend =>
            if (divisor.signum == 0) None else Some(dividend.divide(divisor, working)))
        }
        .map(out)
  }

  /** The negation, which is exact. */
  def negated(value: BigDecimal): BigDecimal = out(value.bigDecimal.negate)

  /**
   * A literal held as a fraction, at this precision.
   *
   * Exact for a fraction of whole numbers, which is what `Num` holds after reduction, and no better
   * than the literal for anything else: a `Num` built from a `Double` carries sixteen digits and no
   * arithmetic here can recover a seventeenth. That is the one place this file cannot help, and it
   * is why `e` is a constant of [[Arbitrary]] rather than something read out of an expression.
   */
  def fraction(numerator: Double, denominator: Double): Option[BigDecimal] = {
    val below = java.math.BigDecimal.valueOf(denominator)
    if (below.signum == 0) None
    else Some(out(java.math.BigDecimal.valueOf(numerator).divide(below, working)))
  }

  /* ----------------------------------------------------------------- the comparisons */

  /** The signed difference, at this precision. */
  def difference(left: BigDecimal, right: BigDecimal): BigDecimal =
    out(left.bigDecimal.subtract(right.bigDecimal, working))

  /**
   * How many significant digits two values have in common, and `None` when it is all of them.
   *
   * What a screening report says instead of "they differ": a candidate that survived to the
   * fifteenth digit and one that survived to the hundredth are different facts, and the first is
   * what a sixteen-digit screen would have called agreement.
   */
  def agreeingDigits(left: BigDecimal, right: BigDecimal): Option[Int] = {
    val gap = difference(left, right).bigDecimal.abs
    if (gap.signum == 0) None
    else {
      val scale = left.bigDecimal.abs.max(right.bigDecimal.abs).max(one)
      val ratio = scale.divide(gap, working)
      Some(math.max(0, ratio.precision - ratio.scale - 1))
    }
  }

  /**
   * Whether two values agree to this precision, allowing for their size.
   *
   * `slack` is how many of the digits asked for are given away before a difference counts, and it
   * exists because the last digits of a computed value are the guard's business rather than the
   * caller's. A caller comparing two values that each went through a dozen roundings gives away
   * more than one comparing two literals.
   */
  def agree(left: BigDecimal, right: BigDecimal, slack: Int): Boolean =
    agreeingDigits(left, right).forall(_ >= math.max(1, digits - slack))

  /* --------------------------------------------------------------------- internals */

  private def out(value: B): BigDecimal = new BigDecimal(value.round(reported), reported)

  /** `exp`, before the answer is narrowed, so that [[power]] can chain onto the wide value. */
  private def exponential(argument: B): Option[B] =
    if (argument.abs.compareTo(Ceiling) > 0) None else Some(expOf(argument, working))

  /** `log`, before the answer is narrowed, for the same reason. */
  private def logarithm(argument: B): Option[B] =
    if (argument.signum <= 0) None else Some(logOf(argument, working))

  private def circular(argument: BigDecimal, wantSine: Boolean): Option[BigDecimal] =
    if (argument.bigDecimal.abs.compareTo(Reduction) > 0) None
    else {
      // Subtracting a multiple of pi from the argument costs the digits in front of the argument's
      // point, every one of them. They are bought here rather than assumed free.
      val ahead = math.max(0, argument.bigDecimal.precision - argument.bigDecimal.scale)
      val wide = new MathContext(digits + Guard + ahead, RoundingMode.HALF_EVEN)
      Some(out(circularOf(argument.bigDecimal, wantSine, wide)))
    }
}

object Arbitrary {

  /** A `java.math.BigDecimal`, which is what every internal step is written in. */
  private type B = java.math.BigDecimal

  private val zero: B = java.math.BigDecimal.ZERO
  private val one: B = java.math.BigDecimal.ONE
  private val two: B = java.math.BigDecimal.valueOf(2)
  private val four: BigInteger = BigInteger.valueOf(4)

  /**
   * Digits carried beyond the ones asked for and thrown away at the end.
   *
   * Ten, and a constant rather than a bound computed from the caller's argument, because every
   * series here runs on an argument the reduction has already brought down to size one. The part
   * that does depend on the argument is the reduction itself, and the two functions that pay for it
   * widen their own context instead of leaning on this.
   */
  val Guard: Int = 10

  /**
   * The largest argument [[Arbitrary.sin]] and [[Arbitrary.cos]] will reduce.
   *
   * Not a limit of the method, which would go on working at any size for a price. It **is** the
   * price: reducing an argument of `10^n` costs `n` digits of working precision, so `10^40` asks
   * for forty digits of arithmetic to answer a question about a number between minus one and one.
   * Past this the refusal is worth more than the answer, and a caller who needs it can reduce its
   * own argument and say what it did.
   */
  val Reduction: B = java.math.BigDecimal.TEN.pow(30)

  /** Beyond this, `exp` declines rather than building a number with a million digits in front. */
  val Ceiling: B = java.math.BigDecimal.valueOf(100000)

  /** The largest whole exponent [[Arbitrary.power]] does by squaring rather than through `log`. */
  val WholeExponent: Long = 1000000L

  /** How many terms a series may take before this file is wrong about it. */
  private val Terms: Int = 1000000

  /** To `digits` decimal digits. */
  def to(digits: Int): Arbitrary = {
    require(digits > 0, s"a precision of $digits digits is not a precision")
    new Arbitrary(digits)
  }

  /**
   * The precision the discovery loop screens at once `Double` has said yes.
   *
   * Fifty is chosen for what it excludes rather than for a property of fifty: the measured false
   * positive of the precision corpus differs in the ninth digit, an accidental agreement among
   * ordinary numbers is gone long before the fiftieth, and integer relation detection wants far
   * more than this and asks for it by name.
   */
  lazy val standard: Arbitrary = to(50)

  /* ------------------------------------------------------------ the memoised constants */

  // Pi and the two logarithms are wanted by every reduction and depend on nothing but the
  // precision, so they are computed once per precision. A screening run asks for them a few
  // thousand times and the alternative is a few thousand Machin series.
  private val pis = new ConcurrentHashMap[Int, B]()
  private val logTwos = new ConcurrentHashMap[Int, B]()
  private val logTens = new ConcurrentHashMap[Int, B]()

  private def piAt(context: MathContext): B =
    pis.computeIfAbsent(context.getPrecision, _ => machin(context))

  private def logTwoAt(context: MathContext): B =
    logTwos.computeIfAbsent(context.getPrecision, _ => twiceArctanh(1, 3, context))

  private def logTenAt(context: MathContext): B =
    logTens.computeIfAbsent(
      context.getPrecision,
      _ =>
        // log 10 = 3 log 2 + 2 atanh(1/9), and both halves converge at a ninth or better.
        twiceArctanh(1, 3, context)
          .multiply(java.math.BigDecimal.valueOf(3), context)
          .add(twiceArctanh(1, 9, context), context)
    )

  /* ------------------------------------------------------------------ the series */

  /*
   * Every series below is a tail recursion rather than a loop over vars, and the reason is worth a
   * line because this file is the one place in `core` where a hot numeric kernel could have argued
   * for the other style.
   *
   * It was measured before it was rewritten. Each of the seven loops had one shape: an
   * arbitrary-precision accumulator, an `Int` counter and a threshold test. A `@tailrec` twin of
   * each, run on the arguments the callers actually pass (`Precise.standard` asks for fifty digits,
   * `RelationSpec` for two hundred and twenty), issued an identical count of `BigDecimal`
   * operations, to the digit: `atan(1/5)` 166 iterations and 996 operations either way, `atan(1/239)`
   * 49 and 294, `cos` 64 and 448, `exp(1)` 63 and 271, `exp(100)` 69 and 273. A tail recursion
   * compiles to the same jump, and what it costs against the loop is one `Int` and one `B` per
   * frame, which is nothing beside a `BigDecimal` multiply at sixty digits.
   *
   * What the measurement does not cover: an argument far outside that range. Nothing here changes
   * asymptotically, so the ratio cannot move, but the figures above are the ones taken and not a
   * claim about every precision.
   */

  /** `pi = 16 atan(1/5) - 4 atan(1/239)`. */
  private def machin(context: MathContext): B = {
    val wide = new MathContext(context.getPrecision + 5, RoundingMode.HALF_EVEN)
    val first = arctanReciprocal(5, wide).multiply(java.math.BigDecimal.valueOf(16), wide)
    val second = arctanReciprocal(239, wide).multiply(java.math.BigDecimal.valueOf(4), wide)
    first.subtract(second, wide).round(context)
  }

  /**
   * `atan(1/n)` for a whole `n`, by the alternating series.
   *
   * Written for the reciprocal of an integer rather than for a general argument, because that is
   * the only shape Machin's formula ever asks for and it makes every step a division by an exact
   * integer instead of a multiplication by an inexact one.
   */
  private def arctanReciprocal(n: Long, context: MathContext): B = {
    val square = java.math.BigDecimal.valueOf(n).pow(2)
    val threshold = one.movePointLeft(context.getPrecision + 2)

    @tailrec
    def accumulate(power: B, sum: B, k: Int, taken: Int): B =
      if (power.abs.compareTo(threshold) <= 0 || taken >= Terms) sum
      else {
        val next = power.divide(square, context)
        val term = next.divide(java.math.BigDecimal.valueOf(2L * k + 1), context)
        val total = if (k % 2 == 1) sum.subtract(term, context) else sum.add(term, context)
        accumulate(next, total, k + 1, taken + 1)
      }

    val first = one.divide(java.math.BigDecimal.valueOf(n), context)
    accumulate(first, first, 1, 0)
  }

  /** `2 atanh(n / d)`, which is `log((d + n) / (d - n))` and is how both logarithms are got. */
  private def twiceArctanh(numerator: Long, denominator: Long, context: MathContext): B = {
    val z = java.math.BigDecimal
      .valueOf(numerator)
      .divide(java.math.BigDecimal.valueOf(denominator), context)
    atanhSeries(z, context)
  }

  /** `2 atanh(z)` for a `z` at most a third in size, which is where the reductions leave it. */
  private def atanhSeries(z: B, context: MathContext): B = {
    val square = z.multiply(z, context)
    val threshold = one.movePointLeft(context.getPrecision + 2)

    @tailrec
    def accumulate(power: B, sum: B, k: Int, taken: Int): B =
      if (power.abs.compareTo(threshold) <= 0 || taken >= Terms) sum
      else {
        val next = power.multiply(square, context)
        val total = sum.add(next.divide(java.math.BigDecimal.valueOf(2L * k + 1), context), context)
        accumulate(next, total, k + 1, taken + 1)
      }

    accumulate(z, z, 1, 0).multiply(two, context)
  }

  /**
   * `exp(x)` by halving down to something the series eats and squaring back up.
   *
   * The halvings are counted from the size of the argument rather than tried, and the context is
   * widened by a third of them: squaring doubles a relative error, so `h` squarings cost about
   * `h / 3` decimal digits and this is where they are paid for.
   */
  private def expOf(argument: B, context: MathContext): B =
    if (argument.signum == 0) one
    else if (argument.signum < 0) one.divide(expOf(argument.negate, context), context)
    else {
      val decades = math.max(0, argument.precision - argument.scale)
      val halvings = decades * 10 / 3 + 8
      val wide = new MathContext(context.getPrecision + halvings / 3 + 2, RoundingMode.HALF_EVEN)

      val small = argument.divide(two.pow(halvings), wide)
      val threshold = one.movePointLeft(wide.getPrecision + 2)

      @tailrec
      def accumulate(term: B, sum: B, k: Int, taken: Int): B =
        if (term.abs.compareTo(threshold) <= 0 || taken >= Terms) sum
        else {
          val next = term.multiply(small, wide).divide(java.math.BigDecimal.valueOf(k), wide)
          accumulate(next, sum.add(next, wide), k + 1, taken + 1)
        }

      @tailrec
      def square(answer: B, remaining: Int): B =
        if (remaining <= 0) answer else square(answer.multiply(answer, wide), remaining - 1)

      square(accumulate(one, one, 1, 0), halvings).round(context)
    }

  /**
   * `log(x)` by reducing the mantissa into `[1, 2)` and paying the reduction back in constants.
   *
   * Moving the decimal point is free and takes the mantissa into `[1, 10)`; a decade holds at most
   * three halvings, so what is left is `z = (m - 1) / (m + 1)` at a third or less.
   */
  private def logOf(argument: B, context: MathContext): B = {
    val decades = argument.precision - argument.scale - 1

    @tailrec
    def halve(mantissa: B, halvings: Int): (B, Int) =
      if (mantissa.compareTo(two) < 0) (mantissa, halvings)
      else halve(mantissa.divide(two, context), halvings + 1)

    val (mantissa, halvings) = halve(argument.movePointLeft(decades), 0)

    val z = mantissa.subtract(one, context).divide(mantissa.add(one, context), context)

    atanhSeries(z, context)
      .add(logTwoAt(context).multiply(java.math.BigDecimal.valueOf(halvings), context), context)
      .add(logTenAt(context).multiply(java.math.BigDecimal.valueOf(decades), context), context)
  }

  /**
   * `sin` or `cos`, by reducing into the eighth of a turn where both series are short.
   *
   * Two reductions, and the second is what makes the first cheap. Modulo a turn puts the argument
   * in one turn; a multiple of a quarter turn then puts it in `[-pi/4, pi/4]`, and which series
   * answers, with which sign, is read off the quadrant.
   */
  private def circularOf(argument: B, wantSine: Boolean, context: MathContext): B = {
    val piValue = piAt(context)
    val turn = piValue.multiply(two, context)
    val quarter = piValue.divide(two, context)

    val turns = argument.divide(turn, context).setScale(0, RoundingMode.HALF_EVEN)
    val inOneTurn = argument.subtract(turns.multiply(turn, context), context)

    val quarters = inOneTurn.divide(quarter, context).setScale(0, RoundingMode.HALF_EVEN)
    val reduced = inOneTurn.subtract(quarters.multiply(quarter, context), context)

    // Taken through BigInteger rather than `longValue`, which would wrap: an argument near the
    // reduction limit is 10^30 quarter turns and a `Long` holds 10^18 of them.
    val quadrant = quarters.toBigInteger.mod(four).intValue

    val (sineAnswers, negated) =
      if (wantSine)
        quadrant match {
          case 0 => (true, false)
          case 1 => (false, false)
          case 2 => (true, true)
          case _ => (false, true)
        }
      else
        quadrant match {
          case 0 => (false, false)
          case 1 => (true, true)
          case 2 => (false, true)
          case _ => (true, false)
        }

    val value =
      if (sineAnswers) alternating(reduced, reduced, 2, context)
      else alternating(one, reduced, 1, context)

    if (negated) value.negate else value
  }

  /**
   * The shared body of the two circular series, which differ only in where they start.
   *
   * `sin` starts at `x` and steps by `-x^2 / ((2k)(2k+1))`; `cos` starts at `1` and steps by
   * `-x^2 / ((2k-1)(2k))`. One loop with the first denominator as a parameter is the whole
   * difference, and writing it twice would be two chances to get the alternation wrong.
   */
  private def alternating(first: B, argument: B, firstDenominator: Int, context: MathContext): B = {
    val square = argument.multiply(argument, context)
    val threshold = one.movePointLeft(context.getPrecision + 2)

    @tailrec
    def accumulate(term: B, sum: B, k: Int, taken: Int): B =
      if (term.abs.compareTo(threshold) <= 0 || taken >= Terms) sum
      else {
        val next = term
          .multiply(square, context)
          .divide(java.math.BigDecimal.valueOf(k.toLong * (k + 1)), context)
          .negate
        accumulate(next, sum.add(next, context), k + 2, taken + 1)
      }

    accumulate(first, first, firstDenominator, 0)
  }

  /** `base ^ n` for a whole `n`, by squaring, with one reciprocal when `n` is negative. */
  private def integerPower(base: B, n: Long, context: MathContext): B = {
    @tailrec
    def squaring(result: B, factor: B, remaining: Long): B =
      if (remaining <= 0) result
      else
        squaring(
          if ((remaining & 1L) == 1L) result.multiply(factor, context) else result,
          factor.multiply(factor, context),
          remaining >> 1
        )

    val result = squaring(one, base, math.abs(n))
    if (n < 0) one.divide(result, context) else result
  }

  /** The value as a whole number, when it is one. */
  private def whole(value: BigDecimal): Option[Long] =
    try Some(value.bigDecimal.setScale(0, RoundingMode.UNNECESSARY).longValueExact)
    catch { case _: ArithmeticException => None }
}
