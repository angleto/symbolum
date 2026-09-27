package garden.xeno.symbolum.theories

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The generated table of `README.md`, compared with the code it is a function of.
 *
 * The same arrangement `LibrarySpec` and `GuideSpec` have, after the failure that arrived first on
 * the front page: the first table a reader meets said the naturals cost two axioms and a development
 * holding both eighteen, while `NaturalSpec` asserted three and nineteen and `ChainSpec` asserted
 * nineteen in four places. Nothing was looking at the document, so the two figures were wrong from
 * 2026-09-10 to 2026-09-14 in the one table this system asks a reader to take on trust.
 *
 * **The mechanism itself is not retested here.** `GuideSpec` covers `Generated`: the splice, the
 * refusals, the second run that writes nothing, and the named markers. A second copy of those would
 * be a second implementation site of the same check.
 *
 * What this adds is the front page. The counts are pinned in `NaturalSpec` and `ChainSpec`, which is
 * where a regression in the theory should be found; this fails when the document stops agreeing with
 * them, and it says which command to run rather than what to type.
 */
class FoundationSpec extends AnyFlatSpec with Matchers {

  private def read(relative: String): String =
    new String(Files.readAllBytes(Paths.get(relative)), StandardCharsets.UTF_8)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private val naturals = Natural.standard
  private val reals = Real.standard
  private val both = Chain.standard.widest

  private val generated = Foundation.trustedBaseTable(naturals, reals, both)

  "The trusted-base table in README.md" should "be what the command produces, not something that resembles it" in {
    // The half that goes red the day an axiom is added or removed. A hand-pasted row carries the
    // count it had on the day it was pasted, which is exactly how the row for the naturals came to
    // say two. The clue is the command, because this fails at the moment somebody changes what the
    // system asks a reader to believe, and the thing they need then is what to run.
    withClue(Foundation.TrustedBase.clue) {
      force(Foundation.TrustedBase.partOf(read(Foundation.Document))) shouldBe generated.trim
    }
  }

  it should "carry the figures the developments measure rather than a rounding of them" in {
    // Each column asserted against its own source, so that a generator quietly printing something
    // else — a bound, the size of the wrong theory, the count of named axioms instead of held ones —
    // is caught here and not by a reader. The comparison above would pass on any consistent lie.
    // One `drop`, not two: the alignment row `Generated.table` writes is `|---|---|---|`, which does
    // not start with a space and never reaches this filter. Dropping two here silently discarded the
    // row for the reals and left the assertion below comparing two rows against three expectations,
    // which is how this test failed the first time it ran.
    val counts = generated.linesIterator
      .filter(_.startsWith("| "))
      .drop(1)
      .map(_.split('|').map(_.trim).toVector)
      .toVector

    counts.size shouldBe 3
    counts.map(_(2)) shouldBe Vector(
      naturals.theory.axioms.size.toString,
      reals.theory.axioms.size.toString,
      both.theory.axioms.size.toString
    )
  }

  "The rows for the reals and for everything" should "hold the claim their labels make, that they are built on the naturals" in {
    // The labels say the reals are built from the naturals and the chain holds everything, which is a
    // sentence about the theories and not a rendering of a number. It is true because `Real.standard`
    // is the construction over `Natural.standard` since `docs/adr/0053`: every axiom of the naturals
    // is one of the reals', and the reals add none. Until then the reals sat over `Logic.standard`
    // and this file asserted the opposite, that the two shared none and the chain held their sum.
    reals.theory.axioms.toSet shouldBe naturals.theory.axioms.toSet
    naturals.theory.axioms.toSet.subsetOf(both.theory.axioms.toSet) shouldBe true
  }

  "Every row" should "name as many axioms as it counts, and leave none unnamed" in {
    // The guard against the assertions above being vacuous. The names are resolved by matching each
    // axiom's conclusion against the maps of the logic and the naturals, and a term nothing matched
    // would come back as "an unnamed axiom": the count and the list would then disagree, and a reader
    // shown three and told two names has no way to tell which is the mistake.
    val rows = generated.linesIterator.filter(_.startsWith("| ")).drop(1).map(_.split('|').map(_.trim).toVector).toVector
    rows.size shouldBe 3
    rows.foreach { cells =>
      withClue(s"${cells(1)}: ") {
        val listed = cells(3).split(",").map(_.trim).toVector
        listed should not contain "an unnamed axiom"
        listed.size shouldBe cells(2).toInt
        listed.foreach(name => name should startWith("`"))
      }
    }
  }
}
