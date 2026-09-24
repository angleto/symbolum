package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.{Expr, ExpressionError, Precise, Symbols}
import garden.xeno.symbolum.kernel.Kernel
import garden.xeno.symbolum.logic.NotNormalised

/**
 * Conjecture and proof, in that order: screen candidate identities numerically, then certify the
 * survivors through the kernel.
 *
 * This is the loop that makes the oracle worth having. Numerical agreement at a hundred points is
 * evidence and nothing more, and the history of the subject is full of identities that hold to
 * fifty digits and fail at the fifty-first. A proof is a different thing, and the point of putting
 * the two together is that the cheap step throws away almost everything and the expensive step is
 * then run only on what survived.
 *
 * == The third outcome is the interesting one, and only one quarter of it ==
 *
 * A pair comes out proved, or disproved with the point where it fails, or [[Discovery.Unsettled]]:
 * true at every point tried and not turned into a theorem. That last bucket used to be one thing
 * and is four, which matters because only one of the four is a lead and the other three are the
 * machinery describing itself. [[Discovery.Why]] says which, and a reader who cannot tell them
 * apart cannot read the output of a run at all.
 *
 * The lead is [[Discovery.Why.NotProvableHere]]: both sides reached a normal form, the forms
 * differ, and the candidate agreed at every point anyway. That is either an identity needing
 * mathematics this system does not have or a coincidence over the sample, and neither is
 * discoverable by running the tactics alone. The other three say the fragment was too narrow, the
 * numerals too large, or the rewriter out of steps, and each names its own remedy.
 */
final class Discovery private (val oracle: Oracle, val screen: Discovery.Screen) {

  /**
   * Screen every pair of candidates numerically and certify the ones that survive.
   *
   * Quadratic in the number of candidates, and deliberately so: the screening is arithmetic on
   * doubles and the certification runs only on pairs that passed it.
   */
  def identities(
    candidates: Vector[Expr],
    samples: Vector[Map[String, Double]]
  ): Vector[Discovery.Outcome] = {
    val pairs =
      for {
        i <- candidates.indices.toVector
        j <- (i + 1) until candidates.length
      } yield (candidates(i), candidates(j))

    pairs.map { case (left, right) => settle(left, right, samples) }
  }

  /** Screen one pair and, if it survives, certify it. */
  def settle(
    left: Expr,
    right: Expr,
    samples: Vector[Map[String, Double]]
  ): Discovery.Outcome =
    disagreement(left, right, samples) match {
      case Some((point, difference)) => Discovery.Disproved(left, right, point, difference)

      case None =>
        separation(left, right, samples) match {
          case Some((point, agreed)) => Discovery.Separated(left, right, point, agreed)
          case None => certify(left, right, samples)
        }
    }

  /** The budget check and the kernel, which is what a pair reaches once both screens are silent. */
  private def certify(
    left: Expr,
    right: Expr,
    samples: Vector[Map[String, Double]]
  ): Discovery.Outcome =
    // Asked before the attempt rather than after it, because the attempt is what there is no
    // coming back from: `500 * x = 500 * x` had not returned after two hundred seconds, and a
    // loop that has stopped returning has stopped being a loop. See `Oracle.NumeralBudget`.
    Oracle.affordable(left, right) match {
      case Left(largest) =>
        Discovery.Unsettled(
          left,
          right,
          Discovery.Why.BeyondTheBudget,
          BeyondBudget(s"$left = $right", largest),
          samples.length
        )

      case Right(_) =>
        oracle.certifyIdentity(left, right) match {
          case Right(theorem) => Discovery.Proved(left, right, theorem)
          case Left(reason) =>
            Discovery.Unsettled(left, right, Discovery.why(reason), reason, samples.length)
        }
    }

  /**
   * The first sample point where the two disagree, if there is one.
   *
   * A point where either side is undefined proves nothing and is skipped: `log` of a negative
   * number is not a counterexample to anything, it is a place where the question was not asked.
   */
  private def disagreement(
    left: Expr,
    right: Expr,
    samples: Vector[Map[String, Double]]
  ): Option[(Map[String, Double], Double)] =
    samples.iterator
      .flatMap { point =>
        (valueAt(left, point), valueAt(right, point)) match {
          case (Some(a), Some(b)) =>
            val scale = math.max(1.0, math.max(math.abs(a), math.abs(b)))
            if (math.abs(a - b) > screen.tolerance * scale) Some((point, a - b)) else None
          case _ => None
        }
      }
      .nextOption()

  /**
   * The first sample point where the second stage tells the two apart, if there is one.
   *
   * Run only on a pair the first stage could not separate, which is what makes it affordable: a
   * candidate that already differs at sixteen digits never reaches this, and one that agrees at
   * fifty is a lead rather than a cost.
   *
   * The named constants are taken at **this** stage's precision rather than carried over from the
   * sample, and that is not a refinement. `Discovery.Constants` binds `pi` to a `Double`, and
   * `sin(pi)` at a sixteen-digit pi is `1.2e-16`, which at fifty digits is a difference and not a
   * rounding: the stage would report a separation for every true identity that mentions the
   * constant. The point is the same point; the constants in it are known better.
   */
  private def separation(
    left: Expr,
    right: Expr,
    samples: Vector[Map[String, Double]]
  ): Option[(Map[String, BigDecimal], Int)] = {
    val bar = math.max(1, screen.precise.digits - screen.slack)

    samples.iterator
      .flatMap { sample =>
        val point = sample.map { case (name, value) => (name, BigDecimal(value)) } ++
          screen.constants
        for {
          a <- screen.precise.at(left, point)
          b <- screen.precise.at(right, point)
          agreed <- screen.precise.arithmetic.agreeingDigits(a, b)
          if agreed < bar
        } yield (point, agreed)
      }
      .nextOption()
  }

  private def valueAt(expression: Expr, point: Map[String, Double]): Option[Double] =
    try {
      val value = expression.eval(point)
      if (value.isNaN || value.isInfinite) None else Some(value)
    } catch {
      case _: ArithmeticException => None
      case _: ExpressionError => None
    }
}

object Discovery {

  /**
   * How far apart two values may be and still count as agreeing.
   *
   * Relative, and loose on purpose: the screening step is meant to throw away what is obviously
   * different, not to decide anything. A pair that agrees to eight digits and is not an identity
   * costs one certification attempt, which is the cheap kind of mistake here.
   */
  val Tolerance: Double = 1e-8

  /**
   * How many of the second stage's digits are given away before a difference counts.
   *
   * Every step of an expression rounds, so a true identity does not come back agreeing to every
   * digit. Measured over the twenty-one labelled candidates of `DiscoveryPrecisionSpec`, at a
   * hundred points each and fifty digits, and read again on 2026-09-24: every true one agrees to
   * **49 or 50** digits at its worst point, and the only false one the first stage lets through
   * agrees to **9**. There is nothing in between, and the six false ones the first stage already
   * catches agree to none of them.
   *
   * So one would do, and this is four. The margin is for the candidates nobody has written yet: a
   * deeper expression rounds more times, and that corpus is shallow because it was written to
   * calibrate a tolerance rather than a depth.
   *
   * It is the counterpart of [[Tolerance]] and it counts digits rather than taking a ratio, because
   * counting is what the second stage reports: a pair that agreed to nine digits and a pair that
   * agreed to forty-nine are different leads, and a ratio flattens them into one number.
   */
  val Slack: Int = 4

  /**
   * The two numeric stages a candidate passes before the kernel is asked.
   *
   * Held as a value rather than written into [[Discovery]] because the two are asked different
   * questions and a caller may want to move either: a screening run over a hundred thousand
   * candidates wants the first stage and hardly any of the second, and a run looking for an integer
   * relation wants hundreds of digits in the second and does not care what the first costs.
   *
   * `constants` is what the second stage substitutes for the named constants of
   * [[Discovery.Constants]], at its own precision. See `Discovery.separation` for why that is not
   * optional.
   */
  final case class Screen(
    tolerance: Double,
    precise: Precise,
    slack: Int,
    constants: Map[String, BigDecimal]
  )

  object Screen {

    /** The two stages as the loop uses them: `Double` at `1e-8`, then fifty digits. */
    lazy val standard: Screen = at(Precise.standard)

    /** The same first stage, and a second at whatever precision a caller has a use for. */
    def at(precise: Precise): Screen =
      Screen(Tolerance, precise, Slack, Map("pi" -> precise.arithmetic.pi))
  }

  sealed trait Outcome {
    def left: Expr
    def right: Expr
  }

  /** True at every point tried, and proved. */
  final case class Proved(left: Expr, right: Expr, theorem: Kernel.Thm) extends Outcome

  /** False, with the point that shows it, at sixteen digits. */
  final case class Disproved(
    left: Expr,
    right: Expr,
    witness: Map[String, Double],
    difference: Double
  ) extends Outcome

  /**
   * Agreed at every point the first stage could ask about, and told apart by the second.
   *
   * Kept apart from [[Disproved]] rather than folded into it, and the reason is the one this
   * repository keeps repeating: they are different facts about a candidate and only one of them is
   * interesting. A pair the `Double` screen separates is a candidate somebody wrote wrongly. A pair
   * that needed fifty digits agreed to forty-something everywhere it was asked, which is either a
   * near-identity worth looking at or the exact false positive this stage was built to catch, and
   * `agreement` is the number that tells a reader which.
   *
   * The measured example is `x + x/1000000000` against `x`: it agrees to nine digits, which is
   * inside the first stage's tolerance of `1e-8`, and it used to reach the kernel and come back
   * refused. That is the right answer arrived at expensively, and this is the same answer arrived
   * at for the price of a hundred evaluations.
   */
  final case class Separated(
    left: Expr,
    right: Expr,
    witness: Map[String, BigDecimal],
    agreement: Int
  ) extends Outcome

  /**
   * Why a candidate that survived the screening did not become a theorem.
   *
   * Four situations arrived as one before this existed, and three of them are the machinery talking
   * about itself. Reading a run means separating them, and each carries a different next move.
   */
  enum Why:

    /** `Translate` refused by name: a cosine, a quotient, an exponent it will not expand. */
    case OutsideTheFragment

    /** Sayable and too expensive to attempt. See `Oracle.NumeralBudget`. */
    case BeyondTheBudget

    /** The normalisation stopped at its step limit, so the sides differing means nothing. */
    case RewriterRanOut

    /**
     * Both sides reached a normal form, the forms differ, and the candidate agreed at every point.
     *
     * The only one of the four worth a person's attention. Either the identity needs mathematics
     * this system does not have, or the agreement was a coincidence over the sample.
     */
    case NotProvableHere

  /**
   * True at every point tried and not proved.
   *
   * Carries how many points it survived, because that is what tells a reader whether to look at it:
   * agreement at three points is nothing, agreement at three hundred is a lead. And [[Why]], because
   * a lead and a refusal are both "not proved" and only one of them is worth the reader's time.
   */
  final case class Unsettled(
    left: Expr,
    right: Expr,
    why: Why,
    reason: TacticError,
    pointsTried: Int
  ) extends Outcome

  /**
   * Which of the four a refusal was.
   *
   * `BeyondTheBudget` is not here because it is decided before the attempt rather than read off
   * one. The rewriter running out arrives as a `NotNormalised` wrapped by the certification, and
   * everything else is the case worth reading.
   */
  private[tactics] def why(error: TacticError): Why = error match {
    case _: OutsideFragment => Why.OutsideTheFragment
    case NotCertified(_, _: NotNormalised) => Why.RewriterRanOut
    case _ => Why.NotProvableHere
  }

  def apply(oracle: Oracle): Discovery = new Discovery(oracle, Screen.standard)

  /** With a screen of the caller's own, which is what the precision of the second stage lives in. */
  def apply(oracle: Oracle, screen: Screen): Discovery = new Discovery(oracle, screen)

  /** Over the standard theory. */
  lazy val standard: Discovery = new Discovery(Oracle.standard, Screen.standard)

  /**
   * Named constants a candidate may mention, with the value each takes at every sample point.
   *
   * `Dsl.pi` is a variable as far as the algebra system is concerned, and a grid that did not know
   * that sampled it like any other: every trigonometric candidate was judged at a made-up pi, in
   * both directions. A benchmark review found it.
   */
  val Constants: Map[String, Double] = Map("pi" -> math.Pi)

  /**
   * A deterministic set of sample points over the variables of the given expressions.
   *
   * Deterministic because a lead that appears once and cannot be reproduced is worse than no lead.
   * Each variable follows its own Kronecker sequence, the fractional parts of the multiples of the
   * square root of a prime, so the points fill the box `(-3, 3)^n` rather than lying on a line.
   * The first version set every coordinate to an affine function of the point's index, which is a
   * line in any number of dimensions, and a polynomial that vanishes on that line, of which there
   * is one in every dimension above one, agreed at every point however many were tried.
   *
   * A name in `constants` is not sampled: it takes the value given, at every point.
   */
  def grid(
    expressions: Vector[Expr],
    points: Int,
    constants: Map[String, Double] = Constants
  ): Vector[Map[String, Double]] = {
    val names = expressions.flatMap(Symbols.of).distinct.sorted
    val fixed = constants.filter { case (name, _) => names.contains(name) }
    val variables = names.filterNot(constants.contains)

    (1 to points).toVector.map { step =>
      val sampled = variables.indices.map { position =>
        variables(position) -> coordinate(position, step)
      }
      sampled.toMap ++ fixed
    }
  }

  /**
   * The value the `step`-th sample gives the variable in the `position`-th place.
   *
   * One implementation, because the same rule is wanted over `Term` as over `Expr` and two copies
   * of a sampling scheme are two chances to reintroduce the defect this one was written to fix:
   * see [[grid]] for what that defect was. [[Refutation]] is the other caller.
   */
  def coordinate(position: Int, step: Int): Double = {
    val fraction = (step * math.sqrt(prime(position).toDouble)) % 1.0
    Low + (High - Low) * fraction
  }

  private val Low: Double = -3.0
  private val High: Double = 3.0

  private def prime(index: Int): Int = Iterator.from(2).filter(isPrime).drop(index).next()

  private def isPrime(n: Int): Boolean = (2 to math.sqrt(n.toDouble).toInt).forall(n % _ != 0)
}
