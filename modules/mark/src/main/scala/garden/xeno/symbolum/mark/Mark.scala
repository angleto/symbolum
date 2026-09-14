package garden.xeno.symbolum.mark

import java.nio.file.{Files, Paths}
import scala.collection.mutable
import scala.util.matching.Regex

/**
 * The command that writes `docs/logo.svg` from the character art in `docs/logo.md`, and the
 * measurements that say a copy of either one is intact.
 *
 * The mark is a mask placed cell by cell rather than the output of a formula, and that is a finding
 * `docs/logo.md` records rather than something this file changes: a fold drawn as a spiral wants
 * four to five times the stroke's own width of clear counter to turn in, and this one has two and a
 * half. What this file does change is that the art was the only source and the drawing beside it
 * was a transcription made once. The document says of the two that they "cannot drift without it
 * being visible in a diff", which is true and is not a check: a diff is something a person has to
 * read, and the moment somebody edits one cell of the art is the moment they have least appetite
 * for finding out how the drawing is produced.
 *
 * The three properties the document asks of a copy are measured here rather than described. They
 * were checked once, by hand, on the day the figure was drawn, and a check that runs once is a
 * claim about that day.
 *
 * == Why this module depends on nothing ==
 *
 * Not tidiness. This is a check over two files under `docs/`, and putting it where it could only
 * run after the prover compiled would make it a check that stops running on exactly the days the
 * prover is broken, which are the days a document is most likely to be edited in a hurry.
 */
object Mark {

  /** The document that holds the art, relative to the repository root. */
  val Document: String = "docs/logo.md"

  /** The drawing written from it. */
  val Drawing: String = "docs/logo.svg"

  /** The command that runs this, written here so that the message and the document cannot drift. */
  val Command: String = "sbt \"mark/runMain garden.xeno.symbolum.mark.Mark\""

  /**
   * The eleven operators of the notation, concatenated.
   *
   * Nineteen characters: the turnstile, the two quantifiers, negation, the two junctions,
   * implication, equivalence, equality, the lambda and the function arrow. `docs/logo.md` says why
   * these and not others.
   */
  val Stream: String = "|-!?~/\\\\/==><=>=\\->"

  /** A filled cell, by row and column, counting from the top left of the art. */
  type Cell = (Int, Int)

  private val ArtBlock: Regex = raw"(?s)## The art\n\n```\n.*?\n```".r

  private val ArtBody: Regex = raw"(?s)## The art\n\n```\n(.*?)\n```".r

  /**
   * The art as the document holds it, which is what the checks are run against.
   *
   * Refused by name rather than guessed at. This reads somebody's document to write over another
   * file, and a heading that has moved is a reason to stop rather than to take the first fenced
   * block in the file.
   */
  def art(markdown: String): Vector[String] =
    ArtBody.findFirstMatchIn(markdown) match {
      case Some(m) => m.group(1).split("\n", -1).toVector
      case None =>
        sys.error(s"$Document has no fenced block under a `## The art` heading; refusing to write $Drawing")
    }

  def cells(rows: Vector[String]): Set[Cell] =
    (for {
      (line, r) <- rows.zipWithIndex
      (ch, c) <- line.zipWithIndex
      if ch != ' '
    } yield (r, c)).toSet

  def height(rows: Vector[String]): Int = rows.length

  def width(rows: Vector[String]): Int = rows.map(_.length).max

  /**
   * Every cell where the stream does not say what the art says, as (row, column, found, expected).
   *
   * The stream is continuous and advances only over the cells that are filled: it does not restart
   * at each row, and it skips the counter and the slot rather than counting them. One cell wrong
   * anywhere moves every cell after it, so this returns the whole list rather than the first: a
   * single edit shows up as one entry and a shifted copy shows up as hundreds, and the two want
   * different repairs.
   */
  def streamFaults(rows: Vector[String]): Vector[(Int, Int, Char, Char)] = {
    val faults = Vector.newBuilder[(Int, Int, Char, Char)]
    var k = 0
    for (r <- rows.indices; c <- 0 until width(rows)) {
      val ch = if (c < rows(r).length) rows(r)(c) else ' '
      if (ch != ' ') {
        val expected = Stream(k % Stream.length)
        if (ch != expected) faults += ((r, c, ch, expected))
        k += 1
      }
    }
    faults.result()
  }

  private def components(inside: Set[Cell]): Vector[Set[Cell]] = {
    val seen = mutable.Set.empty[Cell]
    val groups = Vector.newBuilder[Set[Cell]]
    for (start <- inside.toVector.sorted if !seen(start)) {
      val group = mutable.Set(start)
      val queue = mutable.Queue(start)
      seen += start
      while (queue.nonEmpty) {
        val (r, c) = queue.dequeue()
        for ((dr, dc) <- Seq((1, 0), (-1, 0), (0, 1), (0, -1))) {
          val next = (r + dr, c + dc)
          if (inside(next) && !seen(next)) { seen += next; group += next; queue.enqueue(next) }
        }
      }
      groups += group.toSet
    }
    groups.result()
  }

  /** How many separate regions the ink forms. The mark is one. */
  def pieces(rows: Vector[String]): Int = components(cells(rows)).length

  /**
   * The sizes of the enclosed empty regions, smallest first. The mark has exactly one, the counter.
   *
   * Everything touching the frame is the outside, and the outside can be several regions without
   * anything being wrong: the ink reaches three edges, so it cuts the page around it into pieces.
   * What must not appear is a second enclosed region. When the slot beside the folded tip closes it
   * leaves sealed pockets of three and two cells, which read as dirt rather than as drawing, and
   * that is not hypothetical: it is what the first hand-drawn version of this figure did.
   */
  def counters(rows: Vector[String]): Vector[Int] = {
    val ink = cells(rows)
    val h = height(rows)
    val w = width(rows)
    val empty = (for (r <- 0 until h; c <- 0 until w if !ink((r, c))) yield (r, c)).toSet
    components(empty)
      .filterNot(_.exists { case (r, c) => r == 0 || r == h - 1 || c == 0 || c == w - 1 })
      .map(_.size)
      .sorted
  }

  private def escape(text: String): String =
    text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

  private def runs(line: String): Vector[(Int, String)] = {
    val out = Vector.newBuilder[(Int, String)]
    var start = -1
    for (j <- 0 to line.length) {
      val filled = j < line.length && line(j) != ' '
      if (filled && start < 0) start = j
      if (!filled && start >= 0) { out += ((start, line.substring(start, j))); start = -1 }
    }
    out.result()
  }

  /**
   * The drawing: one `<text>` element per visible run, at ten units a column and twenty a row.
   *
   * A transcription and not a redrawing, so row *n* of the file is row *n* of the art. The colour
   * is three values rather than two because the file is read inside an `<img>`, where it gets no
   * colour from the page around it; `docs/logo.md` carries that argument, and the two queries below
   * are its conclusion.
   */
  def svg(rows: Vector[String]): String = {
    val w = 6 + 10 * width(rows) + 6
    val h = 20 * height(rows) + 12
    val body = for {
      (line, r) <- rows.zipWithIndex
      (col, text) <- runs(line)
    } yield {
      val y = 21.6 + 20 * r
      f"""    <text x="${6 + 10 * col}%d" y="$y%.1f" textLength="${10 * text.length}%d" """ +
        s"""lengthAdjust="spacingAndGlyphs">${escape(text)}</text>"""
    }
    val head =
      s"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 $w $h" width="$w" height="$h" role="img" aria-label="Symbolum">
         |  <title>Symbolum</title>
         |  <!-- Inside an <img> this file gets no colour from the page around it, so `currentColor`
         |       alone resolves to black and the mark is black on black wherever the page is dark.
         |       The attribute stays, because it is the right answer when the file is inlined; the
         |       rule below is what answers when it is not. -->
         |  <style>
         |    /* The bare value is a mid grey rather than either extreme, because a media query that
         |       does not resolve has to leave the mark legible on a white page AND on a black one.
         |       The two below are the good answer where the preference is expressed. */
         |    .ink { fill: #7d8590; }
         |    @media (prefers-color-scheme: light) { .ink { fill: #1f2328; } }
         |    @media (prefers-color-scheme: dark)  { .ink { fill: #e6edf3; } }
         |  </style>
         |  <g class="ink" fill="currentColor" font-family="ui-monospace, SFMono-Regular, Menlo, Consolas, monospace" font-size="17" letter-spacing="0" xml:space="preserve">""".stripMargin
    (head +: body :+ "  </g>" :+ "</svg>" :+ "").mkString("\n")
  }

  /** What the three checks say about a figure, in the words the failure needs. */
  def complaints(rows: Vector[String]): Vector[String] = {
    val faults = streamFaults(rows)
    val holes = counters(rows)
    Vector(
      Option.when(faults.nonEmpty)(s"the stream does not cover the art: ${faults.length} cells, first ${faults.head}"),
      Option.when(pieces(rows) != 1)(s"the mark is in ${pieces(rows)} pieces"),
      Option.when(holes.length != 1)(s"the mark encloses ${holes.length} empty regions, sizes $holes")
    ).flatten
  }

  /** The art block of the document, replaced in place. The prose around it is left alone. */
  def withArt(markdown: String, rows: Vector[String]): String =
    ArtBlock.replaceFirstIn(markdown,
      java.util.regex.Matcher.quoteReplacement("## The art\n\n```\n" + rows.mkString("\n") + "\n```"))

  /**
   * Write both files from the description, refusing if what it draws does not hold up.
   *
   * With a size in rows, print that one instead and write nothing: another size is a thing to look
   * at before it is a thing to commit, and the reference size is the only one either file holds.
   *
   * A generator that emitted a drawing of a broken figure would put the defect in two files instead
   * of one, and the second is the file nobody reads.
   */
  def main(args: Array[String]): Unit = {
    val size = args.headOption.map(_.toInt).getOrElse(Figure.Reference)
    val rows = Figure.at(size)
    val bad = complaints(rows)
    if (size != Figure.Reference) {
      rows.foreach(println)
      println(s"${height(rows)} rows by ${width(rows)} columns, ${cells(rows).size} cells")
      if (bad.isEmpty) println("holds: one region, one counter, the stream covers it")
      else bad.foreach(c => println(s"does NOT hold: $c"))
    } else {
      require(bad.isEmpty, bad.mkString("; "))
      val markdown = new String(Files.readAllBytes(Paths.get(Document)), "UTF-8")
      Files.write(Paths.get(Document), withArt(markdown, rows).getBytes("UTF-8"))
      Files.write(Paths.get(Drawing), svg(rows).getBytes("UTF-8"))
      println(s"$Document and $Drawing written: ${height(rows)} rows by ${width(rows)} columns, " +
        s"${cells(rows).size} cells, one counter of ${counters(rows).head}")
    }
  }
}
