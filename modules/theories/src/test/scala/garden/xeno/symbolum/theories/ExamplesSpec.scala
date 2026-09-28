package garden.xeno.symbolum.theories

import java.nio.file.{Files, Path}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The showcase document, and the two ways a showcase rots.
 *
 * **It goes stale**, which is the ordinary one and is what the generated region is for: the pages
 * are rendered from the theorems rather than transcribed, so the only way they can disagree with
 * the code is if somebody edits the file instead of running the command, and the comparison below
 * catches exactly that.
 *
 * **It shrinks quietly**, which is the one a generator does not prevent by itself. A curated list
 * of names is a hand-maintained list, and the failure mode of every hand-maintained list of
 * examples is that an entry stops resolving and the document goes on looking complete. So the
 * generator refuses by name rather than skipping, and the test below asserts the refusal happens
 * rather than trusting that it would.
 *
 * The prose above the marker is not checked for being true, and could not be: it is an argument
 * about what the system cannot do. What **is** checked is that the documents it points a reader at
 * exist, because a reference to a missing record is the one part of an argument a test can settle.
 */
class ExamplesSpec extends AnyFlatSpec with Matchers {

  private def document(): String =
    Files.readString(Path.of(Examples.Document))

  "The examples document" should "show a theorem the library actually holds, for every name chosen" in {
    // Checked before the comparison below and separately from it, because the two failures want
    // different repairs: a name that no longer resolves is a rename to follow, and a page that
    // differs is a command to run.
    val library = Library.of(Chain.standard)

    Examples.Chosen.foreach { case (heading, names) =>
      withClue(s"$heading: ") {
        names should not be empty
        names.foreach { name =>
          withClue(s"$name is chosen and the library does not hold it: ") {
            library.named(name) should not be empty
          }
        }
      }
    }
  }

  it should "show the textbook's form of a theorem wherever the library holds one" in {
    // Card `fd256345`, from its verification of 2026-09-27: five pages showed a theorem with its
    // continuity two-sided at the ends of `[a, b]`, stronger than the textbook's hypothesis, while the
    // library held the textbook's form under the same name with `_WITHIN`, and no page said which it
    // was. A reader of a showcase compares a page with the statement they know, so the form shown is
    // the one that asks no more. Seen red at `2df36b66` before the names moved: INTERMEDIATE_VALUE,
    // CONTINUOUS_ATTAINS_MAX, ROLLE, MEAN_VALUE and DERIVATIVE_INTEGRAL.
    val library = Library.of(Chain.standard)
    val stronger = Examples.Chosen.flatMap(_._2).filter(name => library.named(s"${name}_WITHIN").nonEmpty)
    withClue(s"chosen where the library holds the form relative to [a, b]: ${stronger.mkString(", ")}\n") {
      stronger shouldBe empty
    }
    // Non-vacuity: the suffix is one the library does use, so an empty result above is a finding.
    library.named("ROLLE_WITHIN") should not be empty
  }

  it should "refuse rather than skip when a chosen name stops resolving" in {
    // The assertion that the paragraph above is true rather than intended. A generator that dropped
    // an unresolvable name would leave a document that is smaller and still looks finished, and
    // nothing else in this file would notice.
    Essay.of(Chain.standard, "NOT_A_LEMMA_ANYBODY_HOLDS").isLeft shouldBe true
  }

  it should "be what the command produces, not something that resembles it" in {
    val generated = Examples.generatedPartOf(document()).fold(why => fail(why), identity)
    val expected = Examples.pages().fold(why => fail(why), identity)

    withClue(s"${Examples.Document} is not what the code says; run:\n  ${Examples.Command}\n") {
      generated shouldBe expected.trim
    }
  }

  it should "point a reader only at records that exist" in {
    // A reference that stops resolving is removed in the change that removes the thing, and this
    // is what makes that checkable here: the table above the marker argues from two decisions, and an
    // argument that cites a record nobody can open is worse than one that cites none. The paths are
    // read out of the document rather than listed here, so a citation added later is covered.
    val cited = "docs/adr/\\d{4}[a-z0-9-]*".r.findAllIn(document()).toVector.distinct
    cited should not be empty

    cited.foreach { reference =>
      val held = Option(Path.of("docs/adr").toFile.list())
        .map(_.toVector)
        .getOrElse(Vector.empty[String])
      val matching = held.filter(_.startsWith(reference.stripPrefix("docs/adr/")))

      withClue(s"$reference is cited and no such record exists: ") {
        matching should not be empty
      }
    }
  }
}
