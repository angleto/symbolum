package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.*
import garden.xeno.symbolum.Dsl.*

/**
 * Track D of `docs/evaluation.md`: what the numeric screen catches and what it lets through.
 *
 * The discovery loop screens candidates by evaluating both sides at points and certifies whatever
 * survives. Two numbers decide whether that arrangement is worth anything, and neither is visible
 * from a run of unlabelled candidates: how much of what is false the screen throws away, and how
 * much of what it throws away was true. So the candidates here carry their labels, written by hand
 * rather than generated, and the suite reports the two rates and asserts the one that must not
 * slip.
 *
 * == Precision is the assertion and recall is the report ==
 *
 * A false identity that survives the screen costs one certification attempt and then a refusal,
 * which is the cheap mistake this loop is built to absorb. A **true** identity thrown away by the
 * screen is the expensive one: the candidate is gone, nothing downstream sees it, and the run
 * reports a witness that is really a rounding error. `Discovery.Tolerance` is relative and loose
 * for exactly that reason, and this is where the looseness is measured rather than argued.
 *
 * So a true identity coming back `Disproved` fails this suite, and a near-miss surviving the screen
 * is reported and listed. The two are not symmetric and the file should not pretend they are.
 *
 * == Why three labels and not two ==
 *
 * A candidate that is true and outside the fragment is the bucket the whole loop is aimed at, and
 * it is not a failure of anything: `Translate` refuses `sin`, `cos` and `exp` by name, so such a
 * candidate can only come back unsettled. Counting it with the ones that failed to certify would
 * say the loop proved a third less than it did, and counting it with the successes would say the
 * kernel had certified something it never saw.
 */
class DiscoveryPrecisionSpec extends AnyFlatSpec with Matchers {

  private val x = Var("x")
  private val y = Var("y")

  private enum Label {

    /** True, and inside the fragment `Translate` reads: RING should certify it. */
    case TrueInside

    /** False, and by one coefficient or one sign: the screen should find a point. */
    case NearMiss

    /** True, and outside the fragment by name: unsettled is the only honest answer. */
    case TrueOutside
  }

  private final case class Candidate(name: String, label: Label, left: Expr, right: Expr)

  private val Corpus: Vector[Candidate] = Vector(
    Candidate("square of a sum", Label.TrueInside, (x + Num(1)) * (x + Num(1)), x * x + Num(2) * x + Num(1)),
    Candidate("difference of squares", Label.TrueInside, (x - y) * (x + y), x * x - y * y),
    Candidate("distributing a constant", Label.TrueInside, Num(2) * (x + Num(3)), Num(2) * x + Num(6)),
    Candidate("cube of a sum", Label.TrueInside, (x + Num(1)) * (x + Num(1)) * (x + Num(1)),
      x * x * x + Num(3) * x * x + Num(3) * x + Num(1)),
    Candidate("halves", Label.TrueInside, x / Num(2) + x / Num(2), x),
    Candidate("cancelling to nothing", Label.TrueInside,
      (x + y) * (x + y) - x * x - Num(2) * x * y, y * y),
    // Catastrophic cancellation on purpose: at the sampled points both sides of the subtraction are
    // around 1e8 and the answer is the difference of two numbers that nearly agree, which is where a
    // screen with an absolute tolerance would report a witness that is a rounding error.
    Candidate("cancellation at scale", Label.TrueInside,
      (x + Num(10000)) * (x + Num(10000)) - x * x - Num(20000) * x, Num(100000000)),

    Candidate("square of a sum, one coefficient", Label.NearMiss,
      (x + Num(1)) * (x + Num(1)), x * x + Num(3) * x + Num(1)),
    Candidate("square of a sum, one constant", Label.NearMiss,
      (x + Num(1)) * (x + Num(1)), x * x + Num(2) * x + Num(2)),
    Candidate("difference of squares, one sign", Label.NearMiss, (x - y) * (x + y), x * x + y * y),
    Candidate("distributing a constant, one term", Label.NearMiss,
      Num(2) * (x + Num(3)), Num(2) * x + Num(5)),
    Candidate("cube of a sum, one coefficient", Label.NearMiss,
      (x + Num(1)) * (x + Num(1)) * (x + Num(1)),
      x * x * x + Num(3) * x * x + Num(2) * x + Num(1)),
    Candidate("halves, one denominator", Label.NearMiss, x / Num(2) + x / Num(3), x),
    // False by one part in a thousand million, which is under `Discovery.Tolerance` of 1e-8. It must
    // survive the screen, and the point of having it is that the certifying step is what catches it:
    // this is the loop's whole argument, written as a candidate.
    //
    // Written as a quotient by a whole numeral rather than as a fractional literal, and the
    // difference is not cosmetic: measured on 2026-09-10, `Translate` refuses `Num(1, 1000)` by name
    // ("a fractional literal is not a numeral of this theory, whose numerals are integers") while it
    // reads `x / Num(1000)`. A fractional literal here would have left the fragment and tested the
    // reader instead of the screen.
    Candidate("false under the tolerance", Label.NearMiss,
      x + x / Num(1000000000), x),

    Candidate("the Pythagorean identity", Label.TrueOutside,
      sin(x) * sin(x) + cos(x) * cos(x), Num(1)),
    Candidate("the double angle", Label.TrueOutside, cos(Num(2) * x), Num(1) - Num(2) * sin(x) * sin(x)),
    Candidate("the exponential of a sum", Label.TrueOutside, exp(x + y), exp(x) * exp(y)),
    Candidate("the sine of a sum", Label.TrueOutside,
      sin(x + y), sin(x) * cos(y) + cos(x) * sin(y)),
    Candidate("the exponential of a difference", Label.TrueOutside, exp(x - y), exp(x) / exp(y)),
    Candidate("cosine is even", Label.TrueOutside, cos(Num(0) - x), cos(x)),
    Candidate("the sine of a double angle", Label.TrueOutside,
      sin(Num(2) * x), Num(2) * sin(x) * cos(x))
  )

  /**
   * Near-misses neither stage of the screen catches, with the reason each is here.
   *
   * **Empty since 2026-09-11**, and it held one entry until then. `false under the tolerance` is
   * false by one part in a thousand million, which is under the first stage's `1e-8`; it used to
   * survive the whole screen, reach the kernel, and come back refused, and this file's last
   * assertion was the record of that. The second stage tells it apart at the ninth digit, which is
   * where it is now caught.
   *
   * The list stays, and it fails when a member stops failing as well as when one starts. A member
   * would be a false identity that agrees at every sampled point to fifty digits, and it would be
   * evidence about the grid rather than about the loop.
   */
  private val KnownSurvivors: Set[String] = Set.empty

  private val samples =
    Discovery.grid(Corpus.flatMap(candidate => Vector(candidate.left, candidate.right)), 100)

  private lazy val outcomes: Vector[(Candidate, Discovery.Outcome)] =
    Corpus.map(candidate =>
      (candidate, Discovery.standard.settle(candidate.left, candidate.right, samples))
    )

  private def labelled(label: Label): Vector[(Candidate, Discovery.Outcome)] =
    outcomes.filter(_._1.label == label)

  "The screen" should "throw away nothing that is true, which is the expensive mistake" in {
    // The assertion this file exists for. A false candidate that survives costs one certification
    // and a refusal; a true one thrown away is gone, and the run reports a witness that is really a
    // rounding error. `Discovery.Tolerance` is 1e-8 and relative, and this is where that choice is
    // measured rather than argued.
    //
    // Both stages are read, and the second is the one that could newly break this: a true identity
    // does not agree to every digit, because every step of an expression rounds. Measured here, the
    // worst true candidate agrees to 49 of 50 and `Discovery.Slack` gives away 4.
    val wronglyDisproved = outcomes.collect {
      case (candidate, Discovery.Disproved(_, _, witness, difference)) if candidate.label != Label.NearMiss =>
        s"${candidate.name} (${candidate.label}): differs by $difference at $witness"
      case (candidate, Discovery.Separated(_, _, witness, agreement)) if candidate.label != Label.NearMiss =>
        s"${candidate.name} (${candidate.label}): agreed to $agreement digits at $witness"
    }

    withClue(s"true identities the screen threw away:\n${wronglyDisproved.mkString("\n")}\n") {
      wronglyDisproved shouldBe empty
    }
  }

  it should "leave the true ones agreeing to nearly every digit, which is the margin it rests on" in {
    // The measurement `Discovery.Slack` is set from, asserted rather than described. What makes the
    // second stage safe is not that true identities agree to fifty digits, which they do not, but
    // that the gap between the worst true one and the best false one is forty digits wide.
    val screen = Discovery.Screen.standard
    val precise = screen.precise

    def worstAgreement(candidate: Candidate): Int =
      samples.flatMap { sample =>
        val point = sample.map { case (name, value) => (name, BigDecimal(value)) } ++ screen.constants
        for {
          left <- precise.at(candidate.left, point)
          right <- precise.at(candidate.right, point)
        } yield precise.arithmetic.agreeingDigits(left, right).getOrElse(precise.digits)
      }.min

    val trueOnes = Corpus.filter(_.label != Label.NearMiss).map(worstAgreement)
    val falseOnes = Corpus.filter(_.label == Label.NearMiss).map(worstAgreement)

    info(
      s"at 50 digits: the true candidates agree to ${trueOnes.min}..${trueOnes.max} at their worst " +
        s"point, the false ones to ${falseOnes.min}..${falseOnes.max}"
    )

    trueOnes.min should be >= precise.digits - Discovery.Slack
    falseOnes.max should be < precise.digits - Discovery.Slack
  }

  it should "catch the near-misses, and say which it did not" in {
    val caught = labelled(Label.NearMiss).collect {
      case (candidate, _: Discovery.Disproved) => candidate.name
      case (candidate, _: Discovery.Separated) => candidate.name
    }
    val missed = labelled(Label.NearMiss).map(_._1.name).filterNot(caught.contains)

    info(
      s"${Corpus.size} labelled candidates: ${labelled(Label.TrueInside).size} true and inside, " +
        s"${labelled(Label.NearMiss).size} near-misses, ${labelled(Label.TrueOutside).size} true and " +
        s"outside; screen caught ${caught.size} of ${labelled(Label.NearMiss).size}, " +
        s"threw away ${outcomes.count { case (c, o) => c.label != Label.NearMiss && o.isInstanceOf[Discovery.Disproved] }} " +
        "that were true"
    )

    val unexplained = missed.filterNot(KnownSurvivors.contains)
    withClue(s"near-misses the screen let through:\n${unexplained.mkString("\n")}\n") {
      unexplained shouldBe empty
    }

    // And the list fails when an entry stops failing, which is what keeps it honest.
    (KnownSurvivors -- missed.toSet) shouldBe empty
  }

  "What survives the screen" should "be certified when it is inside the fragment" in {
    val certified = labelled(Label.TrueInside).collect { case (candidate, _: Discovery.Proved) => candidate.name }
    val rest = labelled(Label.TrueInside).collect {
      case (candidate, outcome) if !outcome.isInstanceOf[Discovery.Proved] =>
        s"${candidate.name}: $outcome"
    }

    info(s"certified ${certified.size} of ${labelled(Label.TrueInside).size} that are true and inside")

    withClue(s"true, inside the fragment, and not certified:\n${rest.mkString("\n")}\n") {
      rest shouldBe empty
    }
  }

  it should "come back unsettled and outside when the candidate is outside, never proved" in {
    // The third of the corpus that the loop exists for, and the row a reader most easily
    // misreads. None of these can be certified, because `Translate` refuses the constants by name,
    // so the only wrong answers available are `Proved`, which would mean the kernel had seen
    // something it cannot state, and `Disproved`, which the first assertion already forbids.
    val wrong = labelled(Label.TrueOutside).collect {
      case (candidate, Discovery.Unsettled(_, _, why, _, _)) if why != Discovery.Why.OutsideTheFragment =>
        s"${candidate.name}: unsettled for $why"
      case (candidate, outcome) if !outcome.isInstanceOf[Discovery.Unsettled] =>
        s"${candidate.name}: $outcome"
    }

    info(
      s"unsettled bucket: ${outcomes.count(_._2.isInstanceOf[Discovery.Unsettled])}, of which " +
        s"${labelled(Label.TrueOutside).size} are outside the fragment by label"
    )

    withClue(s"outside the fragment and not reported as such:\n${wrong.mkString("\n")}\n") {
      wrong shouldBe empty
    }
  }

  it should "be caught by the second stage, where the certifying step used to catch it" in {
    // The assertion that moved on 2026-09-11, and it is worth reading against what it said before.
    //
    // `false under the tolerance` differs by one part in a thousand million, which is below the
    // first stage's 1e-8. Until the second stage existed it passed the whole screen, RING refused
    // it, and it landed in the bucket that means "agreed everywhere and did not become a theorem" —
    // which is the bucket a reader is supposed to look at. This file's comment said in as many
    // words that a loop which screened and reported would have called it a discovery, and that was
    // the argument for having a certifying step at all.
    //
    // It is still the argument, and it is no longer this candidate's job to make it. The second
    // stage tells the pair apart at the ninth digit for the price of a hundred evaluations, which
    // is the difference between a screen that hands a person a false lead and one that does not.
    // What the kernel is still for is everything neither stage can separate at any precision.
    val outcome = outcomes.collectFirst { case (candidate, o) if candidate.name == "false under the tolerance" => o }

    outcome match {
      case Some(Discovery.Separated(_, _, _, agreement)) => agreement shouldBe 9
      case other => fail(s"expected the second stage to separate it, got $other")
    }
  }

  "The corpus" should "be balanced, since a rate over an unbalanced one says little" in {
    // Not decoration: precision and recall over a corpus that is nine-tenths one label are numbers
    // about the corpus. Thirds, and the assertion is what keeps a later addition from tilting it
    // without anyone deciding to.
    Label.values.foreach { label =>
      withClue(s"$label: ") { labelled(label).size shouldBe Corpus.size / Label.values.length }
    }
  }
}
