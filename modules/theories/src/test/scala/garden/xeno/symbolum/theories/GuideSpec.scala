package garden.xeno.symbolum.theories

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The generated table of `docs/proving.md`, compared with the code it is a function of.
 *
 * The same arrangement `LibrarySpec` has for `docs/lemmas.md`, for the same reason and after the
 * same failure: the classical statements, what each rests on and what each costs were written
 * by hand into the guide and again into `Classical`'s own docstring, and on 2026-09-11 one change
 * to `Conv.refl` made both copies wrong. `ClassicalSpec` caught three of the numbers because it
 * pins three of them; nothing was looking at the tables.
 *
 * What this adds to `ClassicalSpec` is the document. The sizes are pinned there, which is where a
 * regression should be found; this fails when the document stops agreeing with them, and it says
 * which command to run rather than what to type.
 */
class GuideSpec extends AnyFlatSpec with Matchers {

  private def read(relative: String): String =
    new String(Files.readAllBytes(Paths.get(relative)), StandardCharsets.UTF_8)

  private val classical = Classical.standard

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  "The classical table in docs/proving.md" should "name every statement the extension derives" in {
    // By name as well as whole, and the two are not the same test: the comparison below fails on
    // any difference at all, this one names what a reader of the failure can act on.
    val guide = read(Guide.Document)
    val section = force(Guide.ClassicalTable.partOf(guide))

    val missing = Classical.Statements.map(_._1).filterNot(section.contains)
    withClue(s"in `Classical.Statements` and not in the table: ${missing.mkString(", ")}\n") {
      missing shouldBe empty
    }

    // In the order they are derived, which is the order the file builds them in.
    val positions = Classical.Statements.map { case (name, _) => section.indexOf(name) }
    positions shouldBe positions.sorted
  }

  it should "be what the command produces, not something that resembles it" in {
    // Names alone are not enough, and this is the half that goes red when a derivation gets
    // cheaper: a hand-pasted row carries the right name and the step count it had on the day it
    // was pasted. The clue is the command, because this fails at the moment somebody changes what
    // a proof costs and the thing they need then is what to run.
    val guide = read(Guide.Document)
    val generated = force(Guide.classicalTable(classical))

    withClue(Guide.ClassicalTable.clue) {
      force(Guide.ClassicalTable.partOf(guide)) shouldBe generated.trim
    }
  }

  it should "carry the figures the extension measures rather than a rounding of them" in {
    // The column asserted against its own source, so that a generator quietly printing something
    // else — a bound, a thousand separator, the size of the wrong theorem — is caught here and not
    // by a reader.
    val generated = force(Guide.classicalTable(classical))

    Classical.Statements.foreach { case (name, statement) =>
      val theorem = force(classical.fact(name))
      val row = generated.linesIterator
        .find(_.startsWith(s"| `$name` |"))
        .getOrElse(fail(s"the table has no row for $name"))

      withClue(s"$name: $row\n") {
        row should endWith(s"| ${Derivation.size(theorem)} |")
        row should include(statement)
      }
    }
  }

  "The table's axiom column" should "say nothing where a derivation reaches no axiom" in {
    // Not "0", and not an empty cell. The statements the count below finds are collected by this
    // extension rather than bought by it, and a reader asking what the classical axioms cost has
    // to be able to see that at a glance; `ClassicalSpec` asserts the same division against the
    // derivations.
    val generated = force(Guide.classicalTable(classical))

    generated.linesIterator.count(_.contains("| nothing |")) shouldBe
      Classical.Statements.count { case (name, _) =>
        Derivation.axiomsOf(force(classical.fact(name))).isEmpty
      }
  }

  /* ---------------------------------------------------------------- the mechanism */

  "A generated section" should "rewrite a document in place and leave the prose alone" in {
    // The write itself, which is the half no comparison exercises: `Generated.rewrite` is what the
    // commands run, and a generator that reports success without writing anything is the failure
    // mode a test comparing two strings in memory cannot see.
    val file = Files.createTempFile("symbolum-generated", ".md")
    val section = Generated("probe", file.toString, "a command nobody runs")

    Files.write(
      file,
      s"prose above\n\n${section.start}\n\nold\n\n${section.end}\n\nprose below\n"
        .getBytes(StandardCharsets.UTF_8)
    )

    Generated.rewrite(file, Vector(section -> "new")) shouldBe Right(s"$file rewritten")

    val written = new String(Files.readAllBytes(file), StandardCharsets.UTF_8)
    written should include("prose above")
    written should include("prose below")
    force(section.partOf(written)) shouldBe "new"

    // And a second run writes nothing, which is what makes the command safe to run twice and the
    // comparison above meaningful.
    Generated.rewrite(file, Vector(section -> "new")) shouldBe Right(s"$file is already what the code says")

    Files.delete(file)
  }

  it should "refuse a document that is not there rather than create one" in {
    // A generator that created the file would answer a mistyped path by writing a new document
    // holding a table and nothing else, which is how the prose gets lost.
    val missing = Paths.get("docs/there-is-no-such-document.md")
    val section = Generated("probe", missing.toString, "a command nobody runs")

    Generated.rewrite(missing, Vector(section -> "new")).left.map(_.contains("does not exist")) shouldBe
      Left(true)
    Files.exists(missing) shouldBe false
  }

  it should "refuse a document whose markers are not there, naming which one" in {
    // A document missing the closing marker and a document missing the opening one are repaired
    // differently, so the refusals are different sentences.
    val section = Generated("probe", "nowhere.md", "a command nobody runs")

    section.spliced("no markers here", "x").left.map(_.contains("no `")) shouldBe Left(true)
    section.spliced(s"${section.start}\nbody", "x").left.map(_.contains(section.end)) shouldBe Left(true)
    section
      .spliced(s"${section.end}\nbody\n${section.start}", "x")
      .left
      .map(_.contains("wrong way round")) shouldBe Left(true)
  }

  it should "not find another section's markers, which is why they are named" in {
    // The reason the marker carries the section's name. `docs/evaluation.md` has several generated
    // regions pages apart, and an anonymous opening marker would make every splice after the first
    // start at the first one.
    val first = Generated("first", "nowhere.md", "a command nobody runs")
    val second = Generated("second", "nowhere.md", "a command nobody runs")

    val document =
      s"${first.start}\none\n${first.end}\nbetween\n${second.start}\ntwo\n${second.end}\n"

    force(first.partOf(document)) shouldBe "one"
    force(second.partOf(document)) shouldBe "two"

    val rewritten = force(second.spliced(force(first.spliced(document, "ONE")), "TWO"))
    force(first.partOf(rewritten)) shouldBe "ONE"
    force(second.partOf(rewritten)) shouldBe "TWO"
    rewritten should include("between")
  }
}
