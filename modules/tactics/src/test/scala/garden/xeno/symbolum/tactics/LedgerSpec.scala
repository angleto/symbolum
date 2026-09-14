package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path}
import java.time.Instant
import scala.jdk.CollectionConverters.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Add, Cos, Div, Expr, Mul, Num, Pow, Sin, Var}

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

    ledger.record(discovery.settle(square, expanded, samplesFor(square, expanded))).verdict shouldBe
      Ledger.Verdict.Proved
    ledger.record(discovery.settle(square, different, samplesFor(square, different))).verdict shouldBe
      Ledger.Verdict.Disproved

    // `(2 * x) / 2 = x` was the witness here and is proved since 2026-09-09, when a numeral
    // denominator became a coefficient. A SYMBOLIC denominator still is not: cancelling `x`
    // against `inv x` costs `~(x = 0)`, which RING has nowhere to put. So it is Open, not Outside:
    // the ledger's distinction between "nobody can state this" and "this is stated and unsettled"
    // is what the witness has to sit on, and it moved one construction along.
    val quotient = Div(Vector(Mul(Vector(Num(2), x)), x))
    ledger.record(discovery.settle(quotient, Num(2), samplesFor(quotient, Num(2)))).verdict shouldBe
      Ledger.Verdict.Open

    // True at every point and unstateable here: the theory has no trigonometric constant. The
    // witness has to be an identity that *holds*, or sampling disproves it and the pair never
    // reaches the reader at all.
    val trig = Add(Vector(Pow(Sin(x), Num(2)), Pow(Cos(x), Num(2))))
    ledger.record(discovery.settle(trig, Num(1), samplesFor(trig, Num(1)))).verdict shouldBe
      Ledger.Verdict.Outside

    val large = Mul(Vector(Num(1e13), x))
    ledger.record(discovery.settle(large, large, samplesFor(large))).verdict shouldBe
      Ledger.Verdict.TooLarge

    // The lead: `x * x = x` holds at 1 and a sample of one point lets it past the screening.
    ledger.record(discovery.settle(Mul(Vector(x, x)), x, Vector(Map("x" -> 1.0)))).verdict shouldBe
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
        )
      )
      .verdict shouldBe Ledger.Verdict.Unfinished
  }

  "The evidence" should "be what the answer rested on, which differs by answer" in {
    val (ledger, _, _) = freshLedger()

    val disproved = ledger.record(discovery.settle(square, different, samplesFor(square, different)))
    // Worth nothing without the point: a disproof a reader cannot check is a rumour.
    disproved.evidence should include("differs by")
    disproved.evidence should include("x=")

    val open = ledger.record(discovery.settle(Mul(Vector(x, x)), x, Vector(Map("x" -> 1.0))))
    // Agreement at one point is not a lead and agreement at three hundred is, so the count is the
    // evidence and the reader needs it to know whether to look.
    open.evidence should startWith("1 points tried")
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
}
