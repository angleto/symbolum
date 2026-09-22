package garden.xeno.symbolum.mark

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import java.nio.file.{Files, Paths}

/**
 * What `docs/logo.md` asks of a copy of the mark, asserted instead of described.
 *
 * The document has always carried the checks. Until this suite existed it carried them as
 * instructions to a reader, which is a procedure somebody performs once and then believes. The
 * three below are the ones the document names, plus the agreement between the two files it says
 * cannot drift, plus the figures the prose quotes.
 */
class MarkSpec extends AnyFlatSpec with Matchers {

  private def read(path: String): String =
    new String(Files.readAllBytes(Paths.get(path)), "UTF-8")

  private val document = read(Mark.Document)
  private val rows = Mark.art(document)

  "the operator stream" should "cover every filled cell in reading order, and no empty one" in {
    val faults = Mark.streamFaults(rows)
    withClue(s"cells where the art and the stream disagree: ${faults.take(5)} of ${faults.length}; ") {
      faults shouldBe empty
    }
  }

  "the mark" should "be one connected region" in {
    Mark.pieces(rows) shouldBe 1
  }

  it should "enclose exactly one empty region, the counter" in {
    withClue("a second enclosed region is the slot beside the folded tip having closed; ") {
      Mark.counters(rows) should have length 1
    }
  }

  "the committed art" should "be what the description draws at the reference size" in {
    withClue(s"regenerate with ${Mark.Command}; ") {
      rows shouldBe Figure.at(Figure.Reference)
    }
  }

  /**
   * The claim that the figure now has a size at all, and the claim that it does not have every size.
   *
   * Both are asserted because both are load-bearing. The first is the whole reason the description
   * exists; the second is why the command refuses rather than writing whatever it drew. Twenty-six
   * rows is the size where the counter leaks, not an arbitrary one, and if a change makes it hold,
   * this fails and the sentence in `docs/logo.md` is what has to move.
   */
  "the figure" should "hold together at other sizes" in {
    Mark.complaints(Figure.at(33)) shouldBe empty
    Mark.complaints(Figure.at(20)) shouldBe empty
  }

  it should "not hold at every size, and say so rather than draw it" in {
    Mark.complaints(Figure.at(26)) should not be empty
    Mark.complaints(Figure.at(46)) should not be empty
  }

  /**
   * The one that catches an edit to either file alone.
   *
   * It names the command in the failure because the moment this breaks is the moment somebody has
   * changed a cell of the art, and what they need then is the way to regenerate rather than the
   * knowledge that two files differ.
   */
  "docs/logo.svg" should "be what the art generates, so the two cannot drift" in {
    withClue(s"regenerate with ${Mark.Command}; ") {
      read(Mark.Drawing) shouldBe Mark.svg(rows)
    }
  }

  /**
   * The figures in the prose, against the figure itself.
   *
   * The document spells its dimensions and writes its counts in digits, which is its own style and
   * not something a test should reform. The table below is what lets a worded dimension be checked
   * at all; a size whose number is missing from it fails here saying so, which is the right failure:
   * it means the mark has been redrawn at a size nobody updated the sentence for.
   */
  private val Words = Map(
    20 -> "twenty", 21 -> "twenty-one", 22 -> "twenty-two", 23 -> "twenty-three", 24 -> "twenty-four",
    25 -> "twenty-five", 70 -> "seventy", 75 -> "seventy-five", 78 -> "seventy-eight",
    79 -> "seventy-nine", 80 -> "eighty", 81 -> "eighty-one", 82 -> "eighty-two",
    83 -> "eighty-three", 84 -> "eighty-four", 85 -> "eighty-five"
  )

  "the prose" should "quote the figure's own measurements" in {
    val h = Mark.height(rows)
    val w = Mark.width(rows)
    withClue(s"no word for $h or $w in this suite's table; ") {
      Words.keySet should contain allOf (h, w)
    }
    val dimensions = s"${Words(h).capitalize} rows by ${Words(w)} columns"
    withClue(s"the document should say `$dimensions`; ") {
      document.replaceAll("\\s+", " ") should include(dimensions)
    }
    val flat = document.replaceAll("\\s+", " ")
    flat should include(s"${Mark.cells(rows).size} cells")
    flat should include(s"${Mark.counters(rows).head} cells")
  }
  /**
   * The cell count in the first complaint, at one and elsewhere.
   *
   * `mark` depends on nothing, so it carries its own counter and this is what holds it. One
   * uncovered cell is the ordinary case rather than a corner: it is what a figure one character
   * out of step with the operator stream produces.
   *
   * The other two complaints of this file are NOT of this class and are left alone: both sit
   * behind a `!= 1` guard, so the number they print is never one, which is the same thing that
   * keeps `Linarith`'s count out of it.
   */
  "The complaint about the stream" should "take the singular at one cell and the plural elsewhere" in {
    def complaint(rows: Vector[String]): String =
      Mark.complaints(rows).find(_.contains("does not cover the art")).getOrElse(
        fail(s"expected a complaint about the stream, got ${Mark.complaints(rows)}"))

    complaint(Vector("X")) should include("art: 1 cell,")
    complaint(Vector("XY")) should include("art: 2 cells,")
  }

  /**
   * The three counts `main` prints are not of that class either, and this is the measurement that
   * says so rather than a reading.
   *
   * Card db67b658 listed them as **not established** and named them so they would not be found
   * again: a figure of one row is not a mark anybody draws, and nobody had measured it. Swept
   * over sizes 1 to 30, the floors are 2 rows, 5 columns and 4 cells, and size 1 does not print
   * at all -- the mask at radius 0.5 is empty and `Figure.cells` raises `empty.min` before any
   * count is rendered. So none of the three reaches one and none takes `Plural`.
   *
   * It is an assertion and not a comment because the reason is a measurement: a change to what
   * `Figure.cells` does under a radius of one would move it, and a sentence saying "measured on
   * 2026-09-22" would not notice.
   */
  it should "print no count of one at any size it can draw" in {
    val drawn = (2 to 30).map { size =>
      val rows = Figure.at(size)
      (Mark.height(rows), Mark.width(rows), Mark.cells(rows).size)
    }

    drawn.map(_._1).min shouldBe 2
    drawn.map(_._2).min shouldBe 5
    drawn.map(_._3).min shouldBe 4

    // The size below the smallest one that draws. It is a refusal rather than a figure of one
    // row, which is what keeps the floor above from being the accident of where the sweep began.
    an[UnsupportedOperationException] should be thrownBy Figure.at(1)
  }
}
