package garden.xeno.symbolum.tactics

import org.scalacheck.{Gen, Test as CheckTest}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.*

/**
 * How much of what the algebra system says the kernel will certify.
 *
 * Track O of `docs/evaluation.md`, and the closest thing this project has to a check against
 * something it did not choose. Every other suite compares the code with itself or with a document
 * in the same repository: `DocumentationSpec` runs our own examples, `RealSpec` pins our own
 * axioms, `TrustBoundarySpec` checks our own boundaries. None of them could notice the system being
 * wrong in a self-consistent way. This one takes expressions nobody wrote down, hands each to the
 * simplifier, and asks the kernel whether the answer is equal to what went in.
 *
 * == The three buckets, and why only one of them is an assertion ==
 *
 *  - **certified**: the oracle proposed and [[Ring]] proved it. This is the number to report.
 *  - **outside the fragment**: [[Translate]] refused by name, because the expression mentions a
 *    cosine, a logarithm or a division. Not a failure of anything, and the generator below avoids
 *    it on purpose so that the third bucket means something.
 *  - **in the fragment and unproved**: the expression is sayable, the oracle produced an answer,
 *    and the kernel would not agree. **This must be empty.** A member is either an algebra system
 *    that rewrote something it should not have, or a RING that cannot see an identity it should,
 *    and a finding either way. It is the only assertion here.
 *
 * == The sample, and the measurement that chose it ==
 *
 * Forty expressions at depth two, which cost about 480 ms when this suite was written on 2026-09-04
 * and 48 ms by the end of that day. What changed in between is RING, and the reason is worth
 * keeping because the sample was chosen against the old cost.
 *
 * **The old cost.** The mean was the wrong number to quote: the distribution was savagely skewed,
 * and in the run that sized this sample one expression took 424 of the 476 ms while five took under
 * a millisecond. The expensive one was `-3^2^2`, whose simplified form carries the numeral 81, and
 * the mechanism was that RING expanded a numeral unarily, so what a certification cost tracked
 * **the largest numeral in the simplified form**. Depth and the coefficient bound mattered only
 * through the chance that they produced a big one by exponentiation: `(y + 2) * (-3 + x)` was seven
 * nodes and 6 ms, `-3^2^2` was five nodes and seventy times that.
 *
 * **What is left.** RING collects coefficients instead of expanding them, so a numeral in the
 * simplified form now costs its digits rather than its value and the mechanism above is gone. The
 * skew was not re-measured, so nothing here claims the distribution is now flat; what is measured
 * is the total, and the test below still pins the expression that used to dominate, because a
 * structural pin is what tells a reader whether this paragraph is still describing the code.
 *
 * A first version of this comment carried a table of milliseconds indexed by depth and coefficient
 * bound, from an unwarmed run, and read a 17x cost of depth out of it. Those factors were the tail
 * moving, not the shape. The table is gone rather than corrected, because indexing a heavy-tailed
 * quantity by the wrong variable is worse than not measuring it. The same caution applies to the
 * two totals above: warm and cold runs of the same work on this machine differ by a factor of ten.
 */
class OracleCertificationSpec extends AnyFlatSpec with Matchers {

  /** Forty at depth two: about half a second before RING collected coefficients, 48 ms after. */
  private val Samples: Int = 40
  private val Depth: Int = 2
  private val Coefficient: Int = 3

  /**
   * A generator over the fragment [[Translate]] accepts, and nothing else.
   *
   * Restricted on purpose. The interesting bucket is the one that must be empty, and it only means
   * something if every expression reaching it could have been certified: a generator that produced
   * cosines would fill the outside-the-fragment bucket and prove nothing about the other two.
   *
   * Transcribed from the shape of `CanonicalFormSpec`'s generator rather than shared with it,
   * because a module's test scope is not visible to the module above and the build does not wire
   * one. The exponent starts at one so that a draw is not spent collapsing a subtree to the numeral
   * 1, which is what a zero exponent does. It used to start there because `Pow` refused `0^0` at
   * construction; that guard is gone, and the sample is left as it was because the timings recorded
   * below were measured on it.
   */
  private val atom: Gen[Expr] =
    Gen.oneOf(
      Gen.choose(-Coefficient, Coefficient).map(Num(_)),
      Gen.oneOf(Var("x"), Var("y"))
    )

  private def expression(depth: Int): Gen[Expr] =
    if (depth <= 0) atom
    else {
      val child = Gen.lzy(expression(depth - 1))
      Gen.oneOf(
        atom,
        Gen.listOfN(2, child).map(parts => Add(parts.toVector)),
        Gen.listOfN(2, child).map(parts => Sub(parts.toVector)),
        Gen.listOfN(2, child).map(parts => Mul(parts.toVector)),
        child.map(Neg(_)),
        child.flatMap(base => Gen.choose(1, 2).map(power => Pow(base, Num(power))))
      )
    }

  private val oracle = Oracle.standard

  /** A fixed seed, because a sample that costs fifteen seconds should be the same one every run. */
  private val sample: Vector[Expr] = {
    val parameters = CheckTest.Parameters.default
    val start = org.scalacheck.rng.Seed(20260904L)
    Vector.tabulate(Samples) { index =>
      expression(Depth)
        .pureApply(Gen.Parameters.default, start.reseed(index.toLong))
    }
  }

  private enum Outcome:
    case Certified, Outside, Unproved

  private def outcomeOf(expression: Expr): Outcome =
    oracle.certifySimplification(expression) match {
      case Right(_) => Outcome.Certified
      case Left(_: OutsideFragment) => Outcome.Outside
      case Left(_) => Outcome.Unproved
    }

  "The oracle" should "certify the algebra system's own answers, and leave nothing unproved" in {
    val results = sample.map(expression => expression -> outcomeOf(expression))
    val counted = results.groupBy(_._2).view.mapValues(_.size).toMap

    info(
      s"$Samples expressions at depth $Depth, coefficients within +-$Coefficient: " +
        s"certified ${counted.getOrElse(Outcome.Certified, 0)}, " +
        s"outside the fragment ${counted.getOrElse(Outcome.Outside, 0)}, " +
        s"unproved ${counted.getOrElse(Outcome.Unproved, 0)}"
    )

    val unproved = results.collect { case (expression, Outcome.Unproved) => expression }
    withClue(s"in the fragment and not certified: ${unproved.mkString("; ")}\n") {
      unproved shouldBe empty
    }
  }

  it should "reach the fragment rather than sit outside it" in {
    // Without this the assertion above would pass on a generator that produced nothing sayable,
    // which is the way a must-be-empty bucket goes quietly wrong.
    val outside = sample.count(expression => outcomeOf(expression) == Outcome.Outside)

    outside shouldBe 0
  }

  it should "still certify the expression that used to dominate the run" in {
    // The example the comment above rests on, pinned structurally rather than by its timing. Five
    // nodes, no numeral above three written anywhere in it, and a simplified form carrying 81: that
    // is how a modest expression reached RING's unary expansion without anyone asking. It no longer
    // does, and this pin is what tells a reader whether the paragraph above still describes the
    // code: if the simplifier ever stops producing the numeral, the story it tells about where the
    // cost used to be has lost its example and should be re-measured rather than believed.
    val expensive = Neg(Pow(Pow(Num(3), Num(2)), Num(2)))

    expensive.simplify.toString should include("81")
    oracle.certifySimplification(expensive) should matchPattern { case Right(_) => }
  }

  it should "refuse what the theory has no constant for, by name" in {
    // The other half of the same point: the bucket exists and is reachable, so its being empty
    // above is a fact about the generator rather than about the classifier.
    val transcendental = Cos(Var("x"))

    oracle.certifySimplification(transcendental).left.map(_.getClass) shouldBe
      Left(classOf[OutsideFragment])
  }
}
