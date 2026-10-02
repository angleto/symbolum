package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path}
import java.time.Instant
import scala.jdk.CollectionConverters.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Add, Cos, Div, Expr, Mul, Num, Pow, Sin, Var}
import garden.xeno.symbolum.kernel.{Term, Type}

/**
 * The memory the loop did not have.
 *
 * What is asserted here is mostly that the second run is cheaper than the first, because that is
 * the only reason the file exists. Everything else, the format and the verdicts, is in service of
 * a reader coming back to it later: a ledger nobody can read with `less` is a cache, and a cache
 * that answers a question nobody asked twice is nothing at all.
 */
class LedgerSpec extends AnyFlatSpec with Matchers {

  private val x = Var("x")
  private val square: Expr = Mul(Vector(Add(Vector(x, Num(1))), Add(Vector(x, Num(1)))))
  private val expanded: Expr = Add(Vector(Pow(x, Num(2)), Mul(Vector(Num(2), x)), Num(1)))
  private val different: Expr = Add(Vector(Pow(x, Num(2)), Num(1)))

  private val discovery = Discovery.standard
  private val reals = discovery.oracle.reals

  private def samplesFor(expressions: Expr*): Vector[Map[String, Double]] =
    Discovery.grid(expressions.toVector, 12)

  /** A fresh ledger with a clock that counts how often it was asked, which is how often it wrote. */
  private def freshLedger(): (Ledger, Path, () => Int) = {
    val directory = Files.createTempDirectory("symbolum-ledger")
    val file = directory.resolve("run.tsv")
    var ticks = 0
    val ledger = Ledger.at(
      file,
      () => {
        ticks += 1
        Instant.ofEpochSecond(1000L + ticks)
      }
    )
    (ledger, file, () => ticks)
  }

  "A ledger over a file that does not exist" should "be empty rather than an error" in {
    val (ledger, file, _) = freshLedger()

    Files.exists(file) shouldBe false
    ledger.entries shouldBe empty
    ledger.settled("x = x") shouldBe None
  }

  "An entry" should "survive being written and read back" in {
    val (ledger, _, _) = freshLedger()
    val written = ledger.record("x + 1 = 1 + x", Ledger.Verdict.Open, "12 points tried")

    ledger.entries shouldBe Vector(written)
    ledger.settled("x + 1 = 1 + x") shouldBe Some(written)
    written.at shouldBe Instant.ofEpochSecond(1001L)
  }

  it should "be one line, with a header naming the columns" in {
    // The file is meant to be read by a person with `less` and searched with `grep`, which is why
    // it is a line per entry and not a serialisation format.
    val (ledger, file, _) = freshLedger()
    ledger.record("x = x", Ledger.Verdict.Proved, "certified by the kernel")
    ledger.record("x = y", Ledger.Verdict.Open, "12 points tried")

    val lines = Files.readAllLines(file).asScala.toVector

    lines should have length 3
    lines.head should startWith("#statement")
    lines(1) should startWith("x = x\tProved\t")
    lines(2) should startWith("x = y\tOpen\t")
  }

  it should "stay one line even when the evidence carries a newline" in {
    // An error message could arrive with one, and an entry that spans lines is one the next reader
    // cannot parse. The message is evidence for a person, so folding it is a fair trade.
    val (ledger, file, _) = freshLedger()
    ledger.record("x = y", Ledger.Verdict.Open, "first\nsecond\tthird")

    Files.readAllLines(file).asScala should have length 2
    ledger.entries.head.evidence shouldBe "first second third"
  }

  "The verdicts" should "say what each outcome means for asking again" in {
    val (ledger, _, _) = freshLedger()

    ledger.record(discovery.settle(square, expanded, samplesFor(square, expanded)), reals).verdict shouldBe
      Ledger.Verdict.Proved
    ledger.record(discovery.settle(square, different, samplesFor(square, different)), reals).verdict shouldBe
      Ledger.Verdict.Disproved

    // `(2 * x) / 2 = x` was the witness here and is proved since 2026-09-09, when a numeral
    // denominator became a coefficient. A SYMBOLIC denominator still is not: cancelling `x`
    // against `inv x` costs `~(x = 0)`, which RING has nowhere to put. So it is Open, not Outside:
    // the ledger's distinction between "nobody can state this" and "this is stated and unsettled"
    // is what the witness has to sit on, and it moved one construction along.
    val quotient = Div(Vector(Mul(Vector(Num(2), x)), x))
    ledger.record(discovery.settle(quotient, Num(2), samplesFor(quotient, Num(2))), reals).verdict shouldBe
      Ledger.Verdict.Open

    // True at every point and unstateable here: the theory has no trigonometric constant. The
    // witness has to be an identity that *holds*, or sampling disproves it and the pair never
    // reaches the reader at all.
    val trig = Add(Vector(Pow(Sin(x), Num(2)), Pow(Cos(x), Num(2))))
    ledger.record(discovery.settle(trig, Num(1), samplesFor(trig, Num(1))), reals).verdict shouldBe
      Ledger.Verdict.Outside

    val large = Mul(Vector(Num(1e13), x))
    ledger.record(discovery.settle(large, large, samplesFor(large)), reals).verdict shouldBe
      Ledger.Verdict.TooLarge

    // The lead: `x * x = x` holds at 1 and a sample of one point lets it past the screening.
    ledger.record(discovery.settle(Mul(Vector(x, x)), x, Vector(Map("x" -> 1.0))), reals).verdict shouldBe
      Ledger.Verdict.Open

    // The one no input produces, mapped where the mapping happens. See `DiscoverySpec`.
    ledger
      .record(
        Discovery.Unsettled(
          x,
          x,
          Discovery.Why.RewriterRanOut,
          OutsideFragment(x, "stands in for a rewriter that ran out"),
          12
        ),
        reals
      )
      .verdict shouldBe Ledger.Verdict.Unfinished
  }

  "The evidence" should "be what the answer rested on, which differs by answer" in {
    val (ledger, _, _) = freshLedger()

    val disproved = ledger.record(discovery.settle(square, different, samplesFor(square, different)), reals)
    // Worth nothing without the point: a disproof a reader cannot check is a rumour.
    disproved.evidence should include("differs by")
    disproved.evidence should include("x=")

    val open = ledger.record(discovery.settle(Mul(Vector(x, x)), x, Vector(Map("x" -> 1.0))), reals)
    // Agreement at one point is not a lead and agreement at three hundred is, so the count is the
    // evidence and the reader needs it to know whether to look.
    //
    // This line read `"1 points tried"` until 2026-09-18, which is the defect pinned as the
    // expected output by the one test written for the count: a sample of exactly one point is the
    // shape this assertion exists to describe, so the singular was the only reading it ever took
    // and it was the wrong one.
    open.evidence should startWith("1 point tried")

    // The plural on the same noun, which is what keeps the repair from being a helper that has gone
    // singular everywhere. A DIFFERENT candidate pair rather than the same one at more points: the
    // ledger answers a repeated candidate from what it already wrote, which is the property the
    // test below this one exists for, so asking again about `x * x` would read back the entry with
    // one point in it and assert nothing. `x^3` and `x` agree at 0 and at 1 and are not equal.
    val cube = Pow(x, Num(3))
    val two = ledger.record(discovery.settle(cube, x, Vector(Map("x" -> 0.0), Map("x" -> 1.0))), reals)

    withClue(s"the fixture was meant to be unsettled at two points and read ${two.verdict}: ") {
      two.verdict shouldBe Ledger.Verdict.Open
    }
    two.evidence should startWith("2 points tried")
  }

  // The file's OTHER pair of counters, and the one the census of 2026-09-18 named here: the
  // evidence written for a reading is `<standing>: N inferences over M axioms`, and it is a
  // different line from the `points tried` above, which is why the test above it covers nothing
  // of this. A reading that cost one inference and reached one axiom is not a corner: the page
  // `Ask` prints was measured saying "77 inferences over 1 axioms" on commutativity of addition,
  // which is the same shape one module over.
  //
  // BOTH DIRECTIONS IN ONE TEST, for the reason `CostSpec` and `EssaySpec` give at the same shape:
  // the condition is one shared helper, so a wrong comparison inside it turns every count on every
  // page singular and a test written on the singular alone reports that as repaired. The reading
  // is BUILT here rather than obtained from the tactic surface, because what is under test is the
  // rendering and a proof exactly one inference long is a fixture to hunt for rather than a fact
  // about this file.
  //
  // SEEN RED, which for a guard written after its repair is the only way to know it guards
  // anything: `tools/verify/perturb-plural-counters.sh` puts this one site back to the bare
  // interpolation and leaves the other two repaired, and on 2026-09-19 at 66dd288 this assertion
  // failed with `1 axioms` while the eleven other tests in this file stayed green.
  "The two counts on the evidence of a reading" should "take the singular at one and the plural elsewhere" in {
    val (ledger, _, _) = freshLedger()
    val claim = Term.variable("p", Type.Bool)

    def evidence(inferences: Int, axioms: Int): String =
      ledger
        .record(
          s"claim at $inferences and $axioms",
          Novelty.Reading(
            claim = claim,
            standing = Novelty.Standing.Earned,
            address = Prove.Address.Equation,
            inferences = inferences,
            axioms = axioms,
            report = Cost.Report(claim = claim, outcome = Cost.Outcome.Proved)
          )
        )
        .evidence

    evidence(1, 1) shouldBe "Earned: 1 inference over 1 axiom"
    evidence(77, 1) shouldBe "Earned: 77 inferences over 1 axiom"
    evidence(1, 2) shouldBe "Earned: 1 inference over 2 axioms"
    // Zero takes the plural, which is the reading of a claim the kernel settled without reaching an
    // axiom at all, and the case somebody picturing the condition does not picture.
    evidence(4, 0) shouldBe "Earned: 4 inferences over 0 axioms"
  }

  // The file's THIRD counter, on the other way in: `record(outcome)` writes the evidence of a
  // screened pair, and a pair the first stage could not separate and the second could is written
  // `agreed to N digits at <point>`. The census of 2026-09-18 reached the two above and not this
  // one, because it read `} steps|} inferences|} axioms|} facts` and this noun is none of the four.
  //
  // One digit is not a corner here: `agreement` is how far down two values stayed equal, and a
  // candidate separated at the first digit after the point is the ordinary case of a pair somebody
  // wrote wrongly. The outcome is BUILT rather than obtained from a run, for the reason the test
  // above gives: what is under test is the rendering, and a pair that agrees to exactly one digit
  // is a fixture to hunt for rather than a fact about this file.
  "The digits on the evidence of a separated pair" should "take the singular at one and the plural elsewhere" in {
    val (ledger, _, _) = freshLedger()

    def evidence(agreement: Int): String =
      ledger
        .record(Discovery.Separated(square, expanded, Map("x" -> BigDecimal(2)), agreement), reals)
        .evidence

    evidence(1) should startWith("agreed to 1 digit at ")
    evidence(9) should startWith("agreed to 9 digits at ")
    // Zero takes the plural, as it does two counters up: a pair the second stage separated at the
    // first digit it looked at agreed to none of them.
    evidence(0) should startWith("agreed to 0 digits at ")
  }

  "The second run of a candidate" should "cost a lookup instead of a certification" in {
    // The whole reason the file exists. The clock counts writes, so one tick after two calls means
    // the second one did not settle anything, and the entry it returns is the first one.
    val (ledger, _, ticks) = freshLedger()
    val samples = samplesFor(square, expanded)

    val first = ledger.settle(discovery, square, expanded, samples)
    val second = ledger.settle(discovery, square, expanded, samples)

    ticks() shouldBe 1
    second shouldBe first
    ledger.entries should have length 1
  }

  it should "not confuse a different pair for one it has seen" in {
    val (ledger, _, ticks) = freshLedger()

    ledger.settle(discovery, square, expanded, samplesFor(square, expanded))
    ledger.settle(discovery, square, different, samplesFor(square, different))

    ticks() shouldBe 2
    ledger.entries.map(_.verdict) shouldBe
      Vector(Ledger.Verdict.Proved, Ledger.Verdict.Disproved)
  }

  it should "match by the printed statement and nothing cleverer" in {
    // The limit, pinned so that it is a decision rather than a surprise. `x + 1 = 1 + x` and
    // `1 + x = x + 1` are one question and two entries. Keying by a canonical form would join them
    // and would put the untrusted simplifier in charge of deciding what counts as already answered,
    // where a wrong answer hides a question instead of producing a wrong theorem.
    val (ledger, _, _) = freshLedger()
    val left = Add(Vector(x, Num(1)))
    val right = Add(Vector(Num(1), x))

    ledger.settle(discovery, left, right, samplesFor(left, right))
    ledger.settled(Ledger.statementFor(left, right)) should not be None
    ledger.settled(Ledger.statementFor(right, left)) shouldBe None
  }

  "A line the file should not contain" should "be skipped rather than take the run down" in {
    // The file is meant to be read and searched by a person, so sooner or later a person edits it.
    // A line they got wrong costs that line: the alternative is a loop that dies at startup because
    // of a typo in its own memo, which is a worse trade than losing one entry.
    //
    // `NoSuchVerdict` below is also the forward-compatibility case, and that is not the same story
    // told twice. A verdict was added on 2026-09-11 and the file is a format, so an older reader
    // will one day meet a word a newer writer produced. What it does then is this: drop the line,
    // read the question as never asked, and do the work again. That is the safe direction — a
    // repeated certification rather than a verdict nobody could interpret — and `Ledger`'s own
    // comment says so in those words.
    val (ledger, file, _) = freshLedger()
    ledger.record("x = x", Ledger.Verdict.Proved, "certified by the kernel")

    Files.write(
      file,
      "\nnot four fields\nx = y\tNoSuchVerdict\tevidence\t1970-01-01T00:00:00Z\nx = z\tOpen\tevidence\tnot a date\n"
        .getBytes("UTF-8"),
      java.nio.file.StandardOpenOption.APPEND
    )

    ledger.entries.map(_.statement) shouldBe Vector("x = x")
    ledger.settled("x = y") shouldBe None
  }

  "A ledger reopened over the same file" should "read what the first one wrote" in {
    // Two runs against one file, which is what accumulation means: the second process starts from
    // where the first stopped rather than from nothing.
    val (first, file, _) = freshLedger()
    first.record("x = x", Ledger.Verdict.Proved, "certified by the kernel")

    Ledger.at(file).entries.map(_.statement) shouldBe Vector("x = x")
  }

  "The evidence for a pair left open" should "write the refusal's terms in the reals' notation" in {
    // Card 7405215c. The ledger holds no theory, so it printed the refusal with the kernel's:
    // `1 point tried: could not certify x * x = x: ((real_mul x) x) is not equal to x`, seen red at
    // 7.0 2b8f266e. The positive is the refusal's own sentence and not the statement, which the
    // evidence carried in the reader's notation before the repair as well.
    val ledger = Ledger.at(Files.createTempFile("ledger-notation", ".tsv"))
    val open = ledger.record(discovery.settle(Mul(Vector(x, x)), x, Vector(Map("x" -> 1.0))), reals)
    info(open.evidence)
    open.verdict shouldBe Ledger.Verdict.Open
    KernelSpelling.in(open.evidence) shouldBe empty
    open.evidence should include("x * x is not equal to x")
  }
}
