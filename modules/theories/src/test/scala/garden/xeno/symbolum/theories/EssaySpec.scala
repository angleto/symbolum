package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.logic.*
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

/**
 * What a generated page says, and what it must not be able to say.
 *
 * The page is the most persuasive artifact this repository produces: it sets a theorem the way a
 * book sets it, walks its derivation, and lists what it is believed on. So the assertions worth
 * making are not that it is pretty. They are that **every claim on it is one the code can make**,
 * and the failure modes are specific enough to be named:
 *
 *  - a formula that cannot be read back, published without the form that can;
 *  - a derivation that is missing, reported as a derivation that is short;
 *  - a theorem listed among the things it rests on, which reads as circular and is what the first
 *    page this produced actually said;
 *  - a citation to a name a reader cannot look up.
 *
 * The two fixed pages here are compared against properties rather than against text. A golden page
 * would pin the prose and fail on every spelling improved, which is the opposite of what should be
 * expensive to change: the wording is meant to move, the guarantees are not.
 */
class EssaySpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val library = Library.of(chain)
  private val signature = chain.widest

  private def page(name: String): String = Essay.of(chain, name).toOption.get

  "The page for a recorded theorem" should "carry both forms of the statement" in {
    val text = page(Magnitude.Triangle)
    val pair = signature.readable(library.named(Magnitude.Triangle).head.theorem.conclusion).get

    text should include(s"$$$$${pair.printed}$$$$")
    text should include(pair.legible)
    text should include(Essay.PrintedNotice)
  }

  it should "have one line for each recorded step, and say how many" in {
    val account = chain.magnitude.scripts(Magnitude.Triangle)
    val text = page(Magnitude.Triangle)

    text should include(s"${account.size} steps, recorded as the derivation was written")

    // Every step numbered, which is the property that would break if the page ever summarised the
    // account instead of carrying it. The heads themselves are checked below rather than here: the
    // first version of this assertion rebuilt them with an empty table of names, so it expected
    // "from step 1" where the page correctly says "from LT_TOTAL", and it was the expectation that
    // was wrong. A test that rebuilds what it is checking has to rebuild it the same way.
    (1 to account.size).foreach { number =>
      withClue(s"step $number is not on the page: ") { text should include(s"\n$number. ") }
    }
  }

  it should "name a premise by the lemma a reader can look up" in {
    val text = page(Magnitude.Triangle)

    // A lemma is cited by its name even where it is also the result of an earlier step, which is
    // the order `Script.lines` resolves in: `LT_TOTAL` is step 1 of this account and is still
    // referred to by name, because a name is what a reader can look up.
    text should include("specialise at x, y from LT_TOTAL")
    text should include("from ABS_ABOVE")

    // And a step whose result no library names is referred to by its number.
    text should include("from step ")
  }

  it should "not list the theorem among the things it rests on" in {
    // The first page this produced listed ABS_TRIANGLE under "what it rests on", because the walk
    // that finds the named facts finds the theorem's own conclusion. True, useless, and it reads as
    // a proof that leans on itself.
    val text = page(Magnitude.Triangle)
    val restsOn = text.split("## The derivation").head

    restsOn should not include s"`${Magnitude.Triangle}`"
    restsOn should include("`ADD_LE`")
    restsOn should include("`LT_TOTAL`")
  }

  it should "name the axioms it reaches and count the ones it cannot name" in {
    val text = page(Magnitude.Triangle)
    val axioms = garden.xeno.symbolum.kernel.Derivation.axiomsOf(library.named(Magnitude.Triangle).head.theorem)

    text should include(s"${axioms.size} axioms reached")
  }

  it should "report the kernel's own count, and the share of it that is bookkeeping" in {
    val theorem = library.named(Magnitude.Triangle).head.theorem
    val text = page(Magnitude.Triangle)

    text should include(s"${garden.xeno.symbolum.kernel.Derivation.size(theorem)} inferences")
    text should include("| rule | inferences | share |")
    text should include("Congruence")
  }

  // The counts on this page are what a reader is told a theorem costs, and until 2026-09-18 two of
  // the three were written as a bare interpolation followed by a plural: the page said "1 steps"
  // and "1 inferences". `Essay.count` already existed and already conditioned the plural; three of
  // its four call sites simply did not use it.
  //
  // BOTH DIRECTIONS IN ONE TEST, which is the whole of why this is not two. A test written only on
  // the singular passes on an `Essay` that has stopped saying the plural at all, and the repair
  // being a shared helper makes exactly that mistake cheap: one wrong comparison turns every count
  // on the page singular and a one-sided test calls it fixed.
  it should "write the singular where the count is one and the plural where it is not" in {
    // A definition is what the kernel holds in a single inference. The sixteen of the reals were the
    // subject here while they were asserted, an axiom being one inference too; they are proved since
    // `docs/adr/0053`, and `BIT0`'s defining equation is the library's entry that stays one step.
    val single = page(Real.Bit0)
    val singleSize = garden.xeno.symbolum.kernel.Derivation.size(library.named(Real.Bit0).head.theorem)

    withClue("BIT0 is no longer held in one inference, so it cannot exercise the singular: ") {
      singleSize shouldBe 1
    }
    single should include("1 inference of its own")
    single should not include "1 inferences"

    // The plural, on the same page and the same noun, so a helper that went singular everywhere
    // fails here rather than passing.
    val theorem = library.named(Magnitude.Triangle).head.theorem
    val many = page(Magnitude.Triangle)
    val manySize = garden.xeno.symbolum.kernel.Derivation.size(theorem)

    withClue(s"$$Magnitude.Triangle is held in $manySize inference(s), so it cannot exercise the plural: ") {
      manySize should be > 1
    }
    many should include(s"$manySize inferences of its own")
  }

  it should "condition the step count the same way, on both sides" in {
    val scripts = chain.magnitude.scripts
    val recorded = scripts(Magnitude.Triangle)

    // The plural, from a real account.
    withClue(s"$Magnitude.Triangle is ${recorded.size} step(s), so it cannot exercise the plural: ") {
      recorded.size should be > 1
    }
    page(Magnitude.Triangle) should include(s"${recorded.size} steps, recorded")

    // The singular, built rather than looked for, and that is the point rather than a convenience.
    // Measured on 2026-09-18: of the 17 accounts this chain records, ZERO are one step long, so a
    // test that went looking for one in the library would find nothing and quietly assert nothing.
    // The page the card was opened against was a notebook's, where a session's own `derive` makes
    // an account of exactly one step, and `Script` is a plain case class, so that shape is one
    // `take` away.
    val single = Script(recorded.steps.take(1))
    val theorem = library.named(Magnitude.Triangle).head.theorem
    val page_ = Essay.of(signature, library, Magnitude.Triangle, theorem, Some(single))

    single.size shouldBe 1
    page_ should include("1 step, recorded")
    page_ should not include "1 steps"
  }

  "The page for a theorem nobody recorded" should "say that, rather than showing nothing" in {
    // `ADD_SYM` is an axiom of the reals: it has a statement, a foundation and a cost, and no
    // account, and the page has to be readable as exactly that. A page that simply omitted the
    // section would read as a theorem proved in no steps.
    val text = page("ADD_SYM")

    text should include("Not recorded")
    text should include("## What it rests on")
    text should include("## The proof the kernel holds")
  }

  "Every page" should "say which of its claims are checked" in {
    Vector(Magnitude.Triangle, "ADD_SYM", "NUM_EUCLID").foreach { name =>
      page(name) should include("## What on this page is checked")
    }
  }

  "A name the library does not hold" should "be refused, and the refusal names the command" in {
    Essay.of(chain, "NO_SUCH_LEMMA") match {
      case Left(reason) => reason should include("NO_SUCH_LEMMA")
      case Right(_) => fail("a page was produced for a lemma that does not exist")
    }
  }

  /* ------------------------------------ what a change to the rendering has to regenerate */

  /**
   * Every site that renders a page, and what it does with the result.
   *
   * The distinction is the one nothing stated until 2026-09-15: `Session` consumes the
   * **renderer** and leaves nothing behind, while `Theorems` and `Examples` consume the
   * **rendering** into a committed document. A change to the prose in `Essay.reproduce` moves
   * exactly the second kind, and that day one of the two was regenerated and the other was not.
   * `ExamplesSpec` went red on the shared branch, and the repair was swept into an unrelated
   * commit by the next session to regenerate its documents, so the account of why that file moved
   * is in a commit message about operator overloading.
   *
   * Nothing in `Essay.scala` named the set. Its docstring named `Session` and `Notebook`, which
   * are the consumers a reader meets and the two that do **not** have to be regenerated, so the
   * one fact a caller needed was the one absent.
   */
  private val Renderers: Map[String, String] = Map(
    "Theorems.scala" ->
      "writes docs/theorems.md, and regenerating it is part of any change to the rendering",
    "Examples.scala" ->
      "writes docs/examples.md, on the same terms and by a command of its own",
    "Session.scala" ->
      "renders on demand for the `show` cell, into a reply, and leaves nothing behind"
  )

  /** Every `.scala` under a module's `src/main`, which is the population the census reads. */
  private def mainSources: Vector[Path] = {
    val modules = {
      val stream = Files.list(Paths.get("modules"))
      try stream.iterator().asScala.toVector
      finally stream.close()
    }

    modules.flatMap { module =>
      val root = module.resolve("src/main")
      if (!Files.exists(root)) Vector.empty
      else {
        val stream = Files.walk(root)
        try stream.iterator().asScala.toVector.filter(_.toString.endsWith(".scala"))
        finally stream.close()
      }
    }
  }

  private def renderingSites: Vector[String] =
    mainSources
      .filterNot(_.getFileName.toString == "Essay.scala")
      .filter(path => Files.readString(path).contains("Essay.of("))
      .map(_.getFileName.toString)
      .distinct
      .sorted

  "The sites that render a page" should "be the ones named here, and no others" in {
    // Both directions, because each catches a different thing. A site that appears and is not in
    // the map is a consumer nobody classified, and if it writes a document it has joined the
    // regeneration set silently. An entry in the map that matches nothing is a sentence describing
    // a file that has stopped rendering, which is how a census turns into decoration.
    val found = renderingSites

    withClue(s"rendering and not classified: ${found.filterNot(Renderers.contains).mkString(", ")}\n") {
      found.filterNot(Renderers.contains) shouldBe empty
    }

    val stale = Renderers.keys.toVector.sorted.filterNot(found.contains)
    withClue(s"classified and no longer rendering: ${stale.mkString(", ")}\n") {
      stale shouldBe empty
    }
  }

  it should "be read off a scan that found something, which is how this passes for free" in {
    // The failure a census like this has is finding nothing: a wrong working directory, a build
    // that moved the sources, a walk that returns an empty stream. Then every assertion above is
    // green about a population of zero. A floor rather than a count, since files are added daily;
    // measured at 154 on 2026-09-15, by this walk and by `find` independently. The figure written
    // here first was 124 and was not measured at all, which is the defect this file spent the
    // evening on, one level down.
    mainSources.size should be >= 80
    renderingSites should not be empty
  }
}
