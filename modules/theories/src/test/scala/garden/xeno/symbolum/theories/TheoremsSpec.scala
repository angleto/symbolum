package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The showcase against the code that writes it.
 *
 * `docs/theorems.md` is the first document that consumes `Essay`. The renderer was complete and had
 * two consumers, `Session` and `Notebook`, and neither leaves anything behind that a reader arrives
 * at, so the pages existed and nothing published them.
 *
 * Three things can go wrong with a generated showcase and each has an assertion of its own. The
 * document can stop being what the command produces, which is the comparison every generated
 * document here carries. The **selection** can name a lemma that no longer exists, which no
 * comparison catches because the generator would refuse before writing and the committed document
 * would simply go stale. And the one transformation this file does, pushing every heading down a
 * level, can eat a line inside a fenced block, which would corrupt a command a reader pastes.
 */
class TheoremsSpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val library = Library.of(chain)

  private def document(): String =
    new String(
      java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(Theorems.Document)),
      "UTF-8"
    )

  /* ------------------------------------------------------------------ the selection */

  "Every theorem in the showcase" should "be one the library holds" in {
    // The half a comparison cannot do. `Theorems.listing` refuses rather than writing a page with a
    // hole in it, so a renamed lemma leaves the committed document intact and stale, and the only
    // sign is a command that somebody has to run before they see it. This is that sign.
    val absent = Theorems.Showcase.map(_._1).filterNot(name => library.named(name).nonEmpty)

    withClue(s"in the showcase and not in the library: ${absent.mkString(", ")}\n") {
      absent shouldBe empty
    }
  }

  it should "say why it is there, since a name does not" in {
    // `NUM_SQUARE_NOT_DOUBLE` is the arithmetic content of the irrationality of the square root of
    // two and nothing in the name says so. The sentence is the whole difference between a showcase
    // and a listing, so an entry without one is an entry that belongs in `docs/lemmas.md`.
    val silent = Theorems.Showcase.filter { case (_, why) => why.trim.length < 40 }.map(_._1)

    withClue(s"in the showcase with nothing said about them: ${silent.mkString(", ")}\n") {
      silent shouldBe empty
    }

    // And not vacuous: there is a showcase to be silent about. A floor rather than a number,
    // because entries are added; twelve on 2026-09-15.
    Theorems.Showcase.size should be >= 8
  }

  it should "be distinct, so the document does not carry a page twice" in {
    val names = Theorems.Showcase.map(_._1)
    names.distinct.size shouldBe names.size
  }

  /* ------------------------------------------------------- the one transformation */

  "Pushing a heading down a level" should "leave a fenced block alone" in {
    // The hazard, asserted on the shape that carries it. The pages hold fenced blocks with shell
    // commands in them, and a shifter that counted no fences would rewrite a line beginning with
    // `#` into something that is not the command any more. There is no such line in the pages
    // today, which is exactly why this is a test and not a reading: the day one appears, nobody
    // will be looking at the shifter.
    val page =
      """# ABS_TRIANGLE
        |
        |## What it rests on
        |
        |```
        |# a comment, inside a fence
        |sbt "tactics/runMain ... Ask x = x"
        |```
        |
        |## How to get it""".stripMargin

    Theorems.demoted(page).linesIterator.toVector shouldBe Vector(
      "## ABS_TRIANGLE",
      "",
      "### What it rests on",
      "",
      "```",
      "# a comment, inside a fence",
      """sbt "tactics/runMain ... Ask x = x"""",
      "```",
      "",
      "### How to get it"
    )
  }

  it should "leave a line that is not a heading where it is" in {
    Theorems.demoted("plain prose\n$$x \\le y$$") shouldBe "plain prose\n$$x \\le y$$"
  }

  /* -------------------------------------------------------------------- the document */

  "docs/theorems.md" should "be what the command produces, not something that resembles it" in {
    // The clue is the command, because this test fails at the moment somebody adds a lemma the
    // showcase rests on or changes how the theory prints, and what they need then is what to run.
    val generated = Theorems.generatedPartOf(document()).fold(why => fail(why), identity)
    val expected = Theorems.listing().fold(why => fail(why), identity)

    withClue(Theorems.Section.clue) {
      generated shouldBe expected.trim
    }
  }

  it should "hold a page for every theorem in the showcase, with the sections a page has" in {
    // Asserted by name as well as whole, and the two are not the same test: the comparison above
    // fails on any difference at all, and this names what a reader of the failure can act on. The
    // sections are asserted because a page that had degenerated to a statement and nothing else
    // would still match the generator, and the whole claim of this document is that each result
    // arrives with the program that proves it.
    val text = document()

    Theorems.Showcase.foreach { case (name, why) =>
      withClue(s"$name: ") {
        text should include(s"## $name")
        text should include(why)
      }
    }

    // `How to get it` is the section this card exists for and the one Angelo asked for by name.
    // One occurrence per page, counted rather than found once, so a single page carrying it cannot
    // stand in for the rest.
    val reproductions = "### How to get it".r.findAllMatchIn(text).size
    withClue(s"pages carrying the reproduction section: $reproductions\n") {
      reproductions shouldBe Theorems.Showcase.size
    }

    // And every page's command is a real one rather than a sentence about running something.
    val asks = java.util.regex.Pattern.quote(Essay.AskCommand)
    asks.r.findAllMatchIn(text).size should be >= Theorems.Showcase.size
  }

  it should "be refused rather than guessed at when the markers are not there" in {
    // This writes over somebody's document and the one thing it must not do is decide for itself
    // where the generated part begins. The same three refusals `LibrarySpec` asserts for the
    // listing, because they are the same mechanism and a second spelling of it would be a second
    // implementation of the same check.
    Theorems.spliced("no markers here", "x").left.map(_.contains("no `")) shouldBe Left(true)
    Theorems.spliced(s"${Theorems.Start}\nbody", "x").left.map(_.contains(Theorems.End)) shouldBe
      Left(true)
    Theorems.spliced(s"${Theorems.End}\nbody\n${Theorems.Start}", "x").left.map(
      _.contains("wrong way round")
    ) shouldBe Left(true)

    Theorems.spliced(s"head\n${Theorems.Start}\nold\n${Theorems.End}\ntail", "new") shouldBe
      Right(s"head\n${Theorems.Start}\n\nnew\n\n${Theorems.End}\ntail")
  }

  it should "send a reader to the listing, which is the other half of the pair" in {
    // The showcase answers "what can this system do" and the listing answers "is there already a
    // lemma about this". A reader who arrives at one and cannot reach the other has half of it.
    document() should include("lemmas.md")
  }
}
