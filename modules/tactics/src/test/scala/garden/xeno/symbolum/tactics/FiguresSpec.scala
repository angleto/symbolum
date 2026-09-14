package garden.xeno.symbolum.tactics

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.checker.{Check, Replayed}
import garden.xeno.symbolum.kernel.*

/**
 * The figures of `docs/evaluation.md`, each one either generated or spelled out of the code.
 *
 * The card this file answers states the criterion: *a number with no test binding it is a number
 * that will be wrong, and it is written that way or not written at all.* The measurement that said
 * the criterion was not met is on the record. One change to `Conv.refl` on 2026-09-11 made
 * seventeen figures stale across five documents; three were caught by a test and fourteen were
 * found by hand with `grep`.
 *
 * There are two mechanisms here and they answer different questions.
 *
 *   - A **table** is generated, and this compares the document with what the command would write.
 *     A failure names the command, because the moment it fails is the moment somebody has changed
 *     what a proof costs and the thing they need then is what to run.
 *   - A **figure inside a sentence** cannot be generated, so the sentence is searched for with the
 *     measured number already substituted into it. That fails in both directions: when the code
 *     moves and when somebody edits the sentence.
 *
 * What is left over is marked in the document as hand-measured on a date, and the section "Which
 * figures here are alive, and which are a photograph" is where a reader is told which is which.
 */
class FiguresSpec extends AnyFlatSpec with Matchers {

  private def read(relative: String): String =
    new String(Files.readAllBytes(Paths.get(relative)), StandardCharsets.UTF_8)

  /**
   * The same document with its line breaks taken out, for matching a sentence rather than a table.
   *
   * A sentence in these documents is wrapped where the column ran out, so a figure quoted in prose
   * lands on either side of a break with no warning and an assertion against the file as written
   * fails on typography. Tables are compared unflattened, since their shape is part of what is
   * generated.
   */
  private def flowed(relative: String): String = read(relative).replaceAll("\\s+", " ")

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  /** The counts for one replayed proof, as the second reader computes them. */
  private def verdict(label: String): Check.Holds = {
    val entry = Replayed.entry(label)
    Check.proof(entry.theorem, entry.theory) match {
      case holds: Check.Holds => holds
      case other => fail(s"$label: the checker did not accept its own proof: $other")
    }
  }

  /* ------------------------------------------------------------ the generated tables */

  "The generated tables of docs/evaluation.md" should "be what the command produces, not something that resembles it" in {
    // Whole-file comparison per section, which is what catches a hand-pasted row carrying the right
    // label and last week's number. The clue is the command.
    val document = read(Evaluation.Document)

    val sections = Vector(
      Evaluation.Replay -> force(Evaluation.replayTable()),
      Evaluation.Serialisation -> force(Evaluation.serialisationTable()),
      Evaluation.Census -> force(Evaluation.censusTable())
    )

    sections.foreach { case (section, generated) =>
      withClue(section.clue) {
        force(section.partOf(document)) shouldBe generated.trim
      }
    }
  }

  it should "hold a row for every proof the checker replays, and name it" in {
    // Asserted by name as well as whole, because the two failures are read differently: this one
    // says which proof is missing from the document, and it is the assertion that would have caught
    // the table reporting six theorems while the suite replayed ten.
    val section = force(Evaluation.Replay.partOf(read(Evaluation.Document)))

    val missing = Replayed.entries.map(_.label).filterNot(section.contains)
    withClue(s"replayed and not in the table: ${missing.mkString(", ")}\n") { missing shouldBe empty }

    section should include(s"| theorems replayed here | ${Replayed.entries.size} |")
  }

  it should "add its census up to the total it prints beside it" in {
    // The defect this replaces, stated as a test: the per-rule census summed to 196623 while the
    // total line next to it said 153953, two hand copies each stale from a different day, and
    // nothing in the repository could tell. They are one measurement now, and this says so.
    val census = force(Evaluation.censusTable())

    val counted = census.linesIterator
      .filter(line => line.startsWith("| ") && !line.startsWith("| rule"))
      .flatMap(_.split('|').lastOption)
      .flatMap(cell => cell.trim.toIntOption)
      .sum

    counted shouldBe RingCost.inferences
    census should include(s"They add up to ${RingCost.inferences} inferences")

    // And the same total is quoted a few hundred lines further down, in the table of what the
    // corpus is believed on. One measurement, two places, so the second is spelled from the
    // measurement rather than left to agree by luck.
    withClue(s"the corpus is ${RingCost.inferences} inferences over ${RingCost.proved.size} proofs: ") {
      val evaluation = flowed(Evaluation.Document)
      evaluation should include(s"| inferences, all proofs together | ${RingCost.inferences} |")
      evaluation should include(s"**${RingCost.inferences} inferences is what a second checker has to replay**")
    }
  }

  /* ----------------------------------------------------- the figures inside sentences */

  "`12 * 12 = 144`" should "be the same proof everywhere the documents quote it" in {
    // Four documents quote this one proof, and on 2026-09-11 every one of them was wrong. Each
    // sentence is searched for with the measured number in it rather than asserted to contain a
    // literal, which is the arrangement `DocumentationSpec` uses for the axiom counts and the
    // reason those have never gone stale.
    val entry = Replayed.entry(Replayed.Serialised)
    val holds = verdict(Replayed.Serialised)
    val text = Proof.write(entry.theorem)
    val terms = text.linesIterator.count(_.startsWith("t "))

    val evaluation = flowed(Evaluation.Document)
    withClue(s"the inference count is ${holds.steps} over ${holds.axioms.size} axioms: ") {
      evaluation should include(
        s"`12 * 12 = 144` is ${holds.steps} inferences over ${FiguresSpec.spelled(holds.axioms.size)} of the sixteen"
      )
    }

    val architecture = flowed("docs/architecture.md")
    withClue(s"the text is ${text.length} characters over $terms terms: ") {
      architecture should include(s"`12 * 12 = 144` is ${holds.steps} steps over $terms distinct terms")
      architecture should include(s"${text.length / 1024} KB")
    }
  }

  "The sharing the serialised format buys" should "be the figure measured, not the one it had" in {
    // The sentence under the table, which is a figure a table cannot hold: what a writer without
    // sharing would have emitted. It is in prose because it is an argument about the format rather
    // than a column of it, and the number is spelled from the same walk the generator uses.
    val entry = Replayed.entry(Replayed.Serialised)
    val written = Replayed.nodesOf(entry.theorem)

    withClue(s"a writer without sharing would have emitted $written nodes: ") {
      flowed(Evaluation.Document) should include(s"**$written** term nodes")
    }
  }

  "Every figure in the evaluation document" should "be alive or marked as a photograph" in {
    // The table that tells a reader which is which, extended on 2026-09-12 with the rows this
    // change created. It is the honest half of the repair: three tables are generated and the rest
    // of the document's numbers are hand-measured, and a reader who cannot tell them apart weighs
    // a photograph as though somebody were still checking it.
    val evaluation = flowed(Evaluation.Document)

    Vector(
      "The second reading, the serialised figures and the ring corpus census",
      "Generated by",
      "Hand-measured",
      "a number without a test that ties it to the code is a number"
    ).foreach { phrase =>
      withClue(s"the table does not say `$phrase`: ") { evaluation should include(phrase) }
    }

    // The command is quoted where the generated sections are, so a reader meeting a stale table
    // does not have to find this file to learn what to run.
    evaluation should include(Evaluation.Command)
  }
}

private object FiguresSpec {

  /**
   * A small number as a document writes it, so that a sentence can be searched for with it in.
   *
   * Only as far as the documents need. A figure past that is one nobody is spelling out in words.
   */
  private val Words: Vector[String] =
    Vector("no", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten")

  def spelled(number: Int): String =
    if (number >= 0 && number < Words.size) Words(number) else number.toString
}
