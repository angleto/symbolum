package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.theories.{Essay, Theorems}

/**
 * The commands `docs/theorems.md` publishes, run rather than counted.
 *
 * The showcase is the document that answers "what can this system do", and its title says each
 * result arrives with the program that proves it. Every page carries a line a reader pastes. Until
 * 2026-09-15 nothing put one of those lines to the prover: `TheoremsSpec` counts occurrences of the
 * command string, which says a page has a command and nothing about what the command does, and
 * `EssayCommandSpec` checks the literal against `Ask.Command`, which says the command names the
 * right entry point and nothing about the claim after it.
 *
 * What running them found, measured that day: **six of the twelve were settled and six were
 * refused**, under a sentence reading "Put the claim to the prover, which settles it from the whole
 * tactic surface". That sentence is gone and [[Essay.RefusalNotice]] is in its place. The partition
 * is asserted by name below, so it fails in both directions: when the surface reaches something it
 * could not, and when it stops reaching something it could.
 *
 * This spec is in `modules/tactics` for the reason `EssayCommandSpec` is: `Essay` renders the page
 * from `modules/theories`, which is below the prover and cannot run it. The generator structurally
 * cannot know whether the command it prints works, so the check belongs in the one module that
 * sees both halves.
 */
class ShowcaseSpec extends AnyFlatSpec with Matchers {

  private val document: String =
    new String(
      java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(Theorems.Document)),
      "UTF-8"
    )

  /** Each page of the generated region, with the claim a reader can paste off it. */
  private lazy val published: Vector[(String, Option[String])] = {
    val region = Theorems.generatedPartOf(document).fold(why => fail(why), identity)

    ("\n" + region).split("\n## ").toVector.drop(1).map { page =>
      val name = page.linesIterator.next().trim
      val claim = page.linesIterator
        .find(_.startsWith(Essay.AskCommand))
        .map(_.stripPrefix(Essay.AskCommand).trim.stripSuffix("\""))
      (name, claim)
    }
  }

  /** The first line of the report, which is `s"${report.outcome}: $claim"` or a refusal to read. */
  private def verdictOf(claim: String): String = Ask.of(claim).linesIterator.next()

  private def settles(claim: String): Boolean =
    verdictOf(claim).startsWith(s"${Cost.Outcome.Proved}:")

  /* ----------------------------------------------------------------- what is published */

  "Every page of the showcase" should "publish a claim, and be the page the selection names" in {
    // The extraction below reads pages out of the document by their heading, so what it found has
    // to be checked against what the generator was told to write before anything is concluded from
    // it. A page that lost its heading would otherwise silently shrink the population and every
    // assertion after this one would pass over what was left.
    published.map(_._1) shouldBe Theorems.Showcase.map(_._1)

    val silent = published.collect { case (name, None) => name }
    withClue(s"pages with no line a reader can paste: ${silent.mkString(", ")}\n") {
      silent shouldBe empty
    }
  }

  it should "carry the notice that says what a refusal from the prover means" in {
    // The sentence this replaced promised the prover settles the claim, which is false for half
    // the pages. Asserted per page rather than once, because the notice is only worth anything on
    // the page whose command comes back refused, and which page that is changes as the surface
    // does.
    val occurrences = java.util.regex.Pattern.quote(Essay.RefusalNotice).r
      .findAllMatchIn(document)
      .size

    occurrences shouldBe Theorems.Showcase.size
  }

  /* ------------------------------------------------------------------- what they do */

  "Every claim the showcase publishes" should "read back through the prover" in {
    // The half `Signature.legible` already guarantees inside the generator, asserted here through
    // the entry point a reader actually uses: `Ask` takes text, not a term, and a claim that did
    // not read would print `unreadable` where the page promised a proof. This has never failed and
    // is the cheaper half of the pair below; it is here because the expensive half cannot
    // distinguish "the prover could not read it" from "the prover could not settle it", and those
    // are the two answers this repository spends `Refutation`'s seven cases keeping apart.
    val unreadable = published.flatMap { case (name, claim) =>
      claim.filter(text => verdictOf(text).startsWith("unreadable")).map(_ => name)
    }

    withClue(s"published and not readable: ${unreadable.mkString(", ")}\n") {
      unreadable shouldBe empty
    }
  }

  it should "be settled by the surface, or refused by it, in the proportion measured" in {
    // A figure meant to fail. It moves when the tactic surface reaches something it could not,
    // which is the work `docs/evaluation.md` tracks, and it moves the other way on a regression.
    // Both are worth a red build, and a range would report neither.
    //
    // Measured 2026-09-15 by putting all twelve through `Ask` in one JVM. The six that are refused
    // are refused because they were obtained by hand derivations: the surface decides a few
    // fragments and chains library lemmas for the rest, and none of those routes reaches a proof
    // of Euclid's lemma.
    //
    // Read it as a reading with a date rather than as a property. `Chaining` and `Propositional`
    // both reach goals they did not a week ago, so the expected direction of travel is that this
    // list goes red because something moved from the second vector to the first, and the repair is
    // to move it here rather than to loosen the assertion.
    val (settled, refused) = published.collect { case (name, Some(claim)) => (name, claim) }
      .partition { case (_, claim) => settles(claim) }

    withClue(s"settled: ${settled.map(_._1).mkString(", ")}\n") {
      settled.map(_._1) shouldBe Vector(
        "EXCLUDED_MIDDLE",
        "NUM_ARCHIMEDES",
        "ABS_TRIANGLE",
        "SUM_TELESCOPES",
        "SUM_BY_PARTS",
        "NUM_PRIME_UNBOUNDED"
      )
    }

    withClue(s"refused: ${refused.map(_._1).mkString(", ")}\n") {
      refused.map(_._1) shouldBe Vector(
        "NUM_INDUCTION",
        "NUM_BEZOUT",
        "NUM_EUCLID",
        "NUM_CRT",
        "NUM_SQUARE_NOT_DOUBLE",
        "NUM_PROV_DEDUCTION"
      )
    }

    // And neither side is empty, which is what makes the two assertions above say something about
    // this document rather than about an empty population. A showcase of only settled claims would
    // make the notice above look like caution nobody needed; one of only refused claims would mean
    // the first route on every page is decoration.
    settled should not be empty
    refused should not be empty
  }
}
