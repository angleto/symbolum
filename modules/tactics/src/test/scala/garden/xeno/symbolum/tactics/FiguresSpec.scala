package garden.xeno.symbolum.tactics

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.checker.{Check, Replayed}
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.NumericConstants
import garden.xeno.symbolum.logic.{Intuitionistic, Rewrite}
import garden.xeno.symbolum.theories.Domain

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

  /**
   * [[flowed]], where the text may be a Scala comment: the leading `*` of every line of a doc
   * comment is taken out first, so a sentence wrapped inside one reads as it does in a document.
   */
  private def flowedComment(relative: String): String =
    if (relative.endsWith(".scala"))
      read(relative).replaceAll("(?m)^\\s*\\*(?![*/])", " ").replaceAll("\\s+", " ")
    else flowed(relative)

  /** How `tools/coverage-delta.sh` writes its default floor, the one place that declares it. */
  private val CoverageDeltaFloor = "COVERAGE_DELTA_MIN:-([0-9]+)".r

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
    // The records the format did write stand beside it in the same sentence, and were a digit
    // nothing compared until 2026-09-24: the table above holds the same count, generated, and a
    // reader comparing the two would have found them agreeing only because nothing had moved.
    val terms = Proof.write(entry.theorem).linesIterator.count(_.startsWith("t "))

    withClue(s"$terms records stand in for $written nodes a writer without sharing would emit: ") {
      flowed(Evaluation.Document) should include(
        s"those $terms records stand in for **$written** term nodes"
      )
    }
  }

  "The replayed counts quoted in prose beside the table" should "be what the checker replays" in {
    // Two sentences quote a row of the generated replay table by its number, one in this document
    // and one in the guide, and neither was compared with anything before 2026-09-24. The second
    // half of the first sentence, `it measured 625 then`, is a photograph of 2026-09-12 and is
    // held as written, so a change to the count makes the sentence say that it moved.
    val induction = verdict("induction over the naturals").steps
    withClue(s"induction over the naturals replays in $induction inferences: ") {
      flowed(Evaluation.Document) should include(s"it measures $induction and it measured 625 then")
    }

    val quotient = verdict("`(x * y) / y = x`").steps
    withClue(s"`(x * y) / y = x` replays in $quotient inferences: ") {
      flowed("docs/proving.md") should include(s"it cost **$quotient inferences**")
    }
  }

  "A constant the prose restates" should "be spelled from its declaration wherever it is" in {
    // Each of these is a present-tense sentence about a value the code declares, in a document or a
    // docstring away from the declaration, and until 2026-09-24 each was a digit compared with
    // nothing. The ones in decision records are the record's decision rather than a copy of it:
    // `docs/adr/0031` decided that the fuel stays where it is, and a change to the constant is a
    // change to that decision, which this makes a reader of the red build find.
    val fuel = Intuitionistic.Fuel
    val instances = Domain.Instances
    val floor = CoverageDeltaFloor.findFirstMatchIn(read("tools/coverage-delta.sh")) match {
      case Some(found) => found.group(1).toInt
      case None => fail("tools/coverage-delta.sh no longer names its floor as COVERAGE_DELTA_MIN:-N")
    }

    val sentences = Vector(
      "docs/adr/0023-the-propositional-address-is-served-by-the-calculus.md" ->
        s"`Intuitionistic.Fuel` is $fuel and is a net",
      "docs/adr/0026-an-exhausted-free-route-is-reported-not-hidden.md" ->
        s"the deepest needs **7** of the $fuel",
      "docs/adr/0026-an-exhausted-free-route-is-reported-not-hidden.md" ->
        s"bounded by `Domain.Instances`, which is $instances.",
      "docs/adr/0026-an-exhausted-free-route-is-reported-not-hidden.md" ->
        s"the quantity `Domain.Instances` bounds at $instances:",
      "docs/adr/0031-a-price-a-bound-chose-is-not-a-price-the-claim-asked-for.md" ->
        s"the answer is that it stays at $fuel**",
      "docs/adr/0031-a-price-a-bound-chose-is-not-a-price-the-claim-asked-for.md" ->
        s"$fuel read forwards is the promise that a goal of at most $fuel nodes is answered",
      "docs/adr/0035-a-change-is-judged-by-what-it-covers.md" ->
        s"**The floor is $floor%, and the number",
      "modules/theories/src/main/scala/garden/xeno/symbolum/theories/Domain.scala" ->
        s"the deepest goal needs 7 of the $fuel,",
      "modules/logic/src/main/scala/garden/xeno/symbolum/logic/Rewrite.scala" ->
        s"`DefaultLimit` is ${Rewrite.DefaultLimit}, which is even;",
      "SIMPLIFICATION_CONFIG_GUIDE.md" ->
        s"`MAX_ITERATIONS` is ${NumericConstants.MAX_ITERATIONS}, in"
    )

    sentences.foreach { case (path, sentence) =>
      withClue(s"$path should say `$sentence`: ") {
        flowedComment(path) should include(sentence)
      }
    }
  }

  "The rewriting limit" should "be even, which is what its docstring argues from" in {
    // The argument is about parity rather than about two hundred, so the parity is asserted as well
    // as the sentence: an odd limit with the docstring edited to match would leave the sentence
    // spelled right and the argument false. A test of its own because a red assertion ends its
    // test, and in the one above this would never run whenever the sentence had moved first.
    Rewrite.DefaultLimit % 2 shouldBe 0
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
