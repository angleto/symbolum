package garden.xeno.symbolum.theories

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

/**
 * A section of a document that is written by the code rather than by hand, and where it begins.
 *
 * `Lemmas` had this mechanism to itself until 2026-09-12: a pair of markers, a splice that replaces
 * what lies between them, a command that does the splicing and a test that compares the file with
 * what the command would write and fails naming it. The arrangement works, and the measurement that
 * asked for a second user of it is in `docs/evaluation.md`: one change to `Conv.refl` made seventeen
 * figures stale across five documents, of which three were caught by a test and fourteen were found
 * by hand with `grep`. Every one of the fourteen was a table or a figure that is a function of the
 * code, copied by hand into a document.
 *
 * So the mechanism is here rather than in `Lemmas`, and it is the same one rather than a second one
 * that resembles it.
 *
 * == The markers name their section ==
 *
 * `docs/lemmas.md` has one generated region and could get away with an anonymous marker.
 * `docs/evaluation.md` has three, they are pages apart, and an anonymous marker would make the
 * second splice start at the first region's opening line. The name is in the marker for that
 * reason, and it is also what a refusal can point at.
 *
 * == What it does not cover, which is the half worth knowing ==
 *
 * This mechanism removes the second place a fact is written. What it can only do that for is a
 * **region of a document**, and by 2026-09-14 the same defect had been found in five places and
 * only three of them were that. The five, in the order they were found:
 *
 *   - `docs/naming.md`, two counts of the library in prose, stale by forty.
 *   - `docs/naming.md` again, a count of how often a small number occurs **inside the sentence
 *     that argues against counts maintained by hand**.
 *   - `docs/evaluation.md`, a percentage in prose contradicting the dated table three lines below.
 *   - `Chain.scala`, the field `logic`, reading `magnitude.logic` while `widest` read `coding`.
 *   - `README.md`, the first table a reader meets, stale since eta landed on 2026-09-10, which is
 *     what asked for the fourth user of this mechanism.
 *
 * **The fourth is the one this cannot reach, and it is the worst.** The other four are a figure
 * that disagrees with another figure, so a reader comparing two numbers finds them and a generated
 * region prevents them. That one was not a figure at all, and the prose beside it was **not stale**:
 * it described the correct repair, "read the field off `widest` rather than off whichever
 * development happens to be last", next to a line that named one by hand. Anybody checking the
 * prose against the intent found everything in order; it needed the prose read against the line.
 * It came back the day `Coding` became the last link, and what reopened it was a correct change.
 *
 * So the rule this mechanism serves is larger than this mechanism: **a fact written twice drifts,
 * and the repair is to take away the second place rather than keep the two in step.** Here that is
 * a generated region. In `Chain.scala` it is `val logic = widest.logic`. In `docs/naming.md` it was
 * deleting a number the argument did not need. Reaching for a generated region where the second
 * copy is a field, or a count the prose could simply not make, is reaching for the wrong one.
 *
 * Of the three, **deleting the number is the one met most often and chosen least**, because
 * generating it always looks like the more serious answer. `docs/naming.md` carries the example: a
 * count of how often a small number occurs in a document was written to support an argument that
 * only needed such a number to be **possible**, so the repair was to stop counting, and generating
 * that figure would have been work whose only available outcome was to become wrong.
 *
 * == What it will not do ==
 *
 * Guess. A document with no markers, with only one of them, or with them the wrong way round is
 * refused by name and left alone: this writes over somebody's document, and the prose above the
 * marker is worth more than the table below it.
 *
 * @param name    the section's name, which appears in both markers
 * @param document the path of the document it lives in, relative to the repository root
 * @param command the one command that rewrites it, so that a failure can say what to run
 */
final case class Generated(name: String, document: String, command: String) {

  /** The line above the generated body. */
  val start: String = s"<!-- generated: $name, do not edit below this line -->"

  /** The line below it. */
  val end: String = s"<!-- end generated: $name -->"

  /**
   * The document with this section's body replaced, or why it could not be.
   *
   * Separated from the writing so that a test can ask the same question without a file on disk
   * being involved, which is the whole of what makes the check and the command one thing.
   */
  def spliced(text: String, body: String): Either[String, String] = {
    val opening = text.indexOf(start)
    val closing = text.indexOf(end)

    if (opening < 0) Left(s"$document has no `$start` marker, and this will not guess where to write")
    else if (closing < 0) Left(s"$document has no `$end` marker, and this will not guess where to stop")
    else if (closing < opening) Left(s"$document has the `$name` markers the wrong way round")
    else
      Right(
        text.substring(0, opening + start.length) + "\n\n" + body.trim + "\n\n" +
          text.substring(closing)
      )
  }

  /** What the section currently holds in a document, for a caller comparing the two. */
  def partOf(text: String): Either[String, String] =
    spliced(text, "").map { _ =>
      text.substring(text.indexOf(start) + start.length, text.indexOf(end)).trim
    }

  /** The clue a failing comparison carries, which is the command and not a description of it. */
  def clue: String = s"$document is not what the code says; run:\n  $command\n"
}

object Generated {

  /** Every document a generator writes is read and written as UTF-8, here and in the tests. */
  def read(path: Path): Either[String, String] =
    if (!Files.exists(path))
      Left(s"$path does not exist; this replaces a section, it does not create a file")
    else Right(new String(Files.readAllBytes(path), StandardCharsets.UTF_8))

  /**
   * Rewrite every section of one document in one pass, and say what happened.
   *
   * One pass rather than one per section, because a document with three generated regions would
   * otherwise be read and written three times and a failure halfway would leave it part-written.
   * The message comes back rather than being printed so that this is testable; the callers'
   * `main` methods print it and choose the exit code.
   */
  def rewrite(path: Path, sections: Vector[(Generated, String)]): Either[String, String] =
    for {
      before <- read(path)
      after <- sections.foldLeft[Either[String, String]](Right(before)) {
        case (document, (section, body)) => document.flatMap(section.spliced(_, body))
      }
      message <-
        if (after == before) Right(s"$path is already what the code says")
        else
          try {
            Files.write(path, after.getBytes(StandardCharsets.UTF_8))
            Right(s"$path rewritten")
          } catch {
            case failure: java.io.IOException => Left(s"$path could not be written: ${failure.getMessage}")
          }
    } yield message

  /**
   * The body of a `main` that rewrites one document: the argument is the path, the default is its
   * own, and a refusal is a message on the error stream and a non-zero exit.
   */
  def run(arguments: Array[String], document: String, sections: Vector[(Generated, String)]): Unit =
    rewrite(Paths.get(if (arguments.isEmpty) document else arguments(0)), sections) match {
      case Left(why) =>
        System.err.println(why)
        sys.exit(1)
      case Right(message) => println(message)
    }

  /** A markdown table from its header and its rows, with the alignment row the renderers want. */
  def table(headings: Vector[String], rows: Vector[Vector[String]]): String = {
    val header = headings.mkString("| ", " | ", " |")
    val rule = headings.map(_ => "---").mkString("|", "|", "|")
    (header +: rule +: rows.map(_.mkString("| ", " | ", " |"))).mkString("\n")
  }
}
