package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.theories.Linarith

/**
 * The trail from a conclusion back to the measurements it rests on.
 *
 * Every assertion here is about which of three groups a thing lands in, because that is the whole
 * content of the file: a premise with a source, a premise with none, and a source no premise used.
 * A test that checked only that sources came back would pass against a register that quietly
 * dropped the premises it could not attribute, which is the failure this is against.
 */
class ProvenanceSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val linarith = Linarith.standard
  private val reals = linarith.reals

  private def register(citations: (String, String)*): Provenance =
    force(Provenance.of(reals, citations.toVector))

  /* ----------------------------------------------------------------- the three groups */

  "A proof of a claim about named quantities" should "come back with its measurements named" in {
    // The shape a corpus of measurements is written in: two premises from two sources, and a
    // conclusion an article states. What a reader wants back is the two sources, not the two
    // formulas, and the formulas are what a sequent carries.
    val sources = register(
      "deaths:real = 53 * beds:real" -> "ARS 2022, table 4",
      "0 < beds:real" -> "ISPRA Tab. 3.1, 2026 edition"
    )

    val trail = force(
      sources.trail(linarith, "deaths:real = 53 * beds:real /\\ 0 < beds:real ==> deaths <= 60 * beds")
    )

    trail.premises.map {
      case Provenance.Premise.Cited(_, source, _) => source
      case Provenance.Premise.Uncited(_, _) => Provenance.Uncited
      case Provenance.Premise.Unnameable(_, _) => Provenance.Unnameable
    } shouldBe Vector("ARS 2022, table 4", "ISPRA Tab. 3.1, 2026 edition")

    trail.idle shouldBe empty
    trail.stale shouldBe empty
  }

  it should "keep a premise nobody cited as its own case, not as an absence" in {
    // The distinction the file exists for. A register that reported only what it could attribute
    // would print a tidy list of sources under a proof that also rests on something nobody said
    // where they got, and a reader would have no way to notice.
    val sources = register("deaths:real = 53 * beds:real" -> "ARS 2022, table 4")

    val trail = force(
      sources.trail(linarith, "deaths:real = 53 * beds:real /\\ 0 < beds:real ==> deaths <= 60 * beds")
    )

    trail.premises.count {
      case _: Provenance.Premise.Cited => true
      case _ => false
    } shouldBe 1

    trail.premises.count {
      case _: Provenance.Premise.Uncited => true
      case _ => false
    } shouldBe 1
  }

  it should "report a source no premise used, rather than letting it go stale in silence" in {
    // The discipline an exception list has, for the same reason. A citation usually stops matching
    // because the proposition beside it was reworded, and a register that never says so
    // accumulates sources for assumptions nobody makes any more.
    val sources = register(
      "deaths:real = 53 * beds:real" -> "ARS 2022, table 4",
      "0 < beds:real" -> "ISPRA Tab. 3.1, 2026 edition",
      "beds:real < 900" -> "a bound nothing here needs"
    )

    val trail = force(
      sources.trail(linarith, "deaths:real = 53 * beds:real /\\ 0 < beds:real ==> deaths <= 60 * beds")
    )

    // Cited for a proposition this goal never assumes, so the register is what is out of date.
    trail.stale.map(_.source) shouldBe Vector("a bound nothing here needs")
    trail.idle shouldBe empty
  }

  /* ---------------------------------------------------- why it reads the support, not the sequent */

  "A premise the proof did not need" should "not be credited with holding the conclusion up" in {
    // The reason this reads `Linarith.support` and not a theorem's hypotheses. All three premises
    // are assumed and the sequent carries all three; the certificate weighs two of them, and `z < w`
    // took no part. Attributing the sequent would credit a measurement that did nothing, which is
    // the opposite of a trail back to the data.
    val sources = register(
      "x:real < y:real" -> "first",
      "y:real < z:real" -> "second",
      "z:real < w:real" -> "third, and not needed"
    )

    val trail = force(
      sources.trail(linarith, "x:real < y:real /\\ z:real < w:real /\\ y:real < z:real ==> x < z")
    )

    trail.premises.collect { case Provenance.Premise.Cited(_, source, _) => source } shouldBe
      Vector("first", "second")

    // The other kind, and the reason the two are not one list. `z < w` **is** assumed by this goal,
    // and the certificate weighed it zero, so what is out of date is the argument rather than the
    // register: the assumption can go. Told together with the case above, a reader would have to
    // work out which of the two every line was.
    trail.idle.map(_.source) shouldBe Vector("third, and not needed")
    trail.stale shouldBe empty
  }

  /* ------------------------------------------------------------------- what it refuses */

  "A goal that quantifies over the very quantities cited" should "say so, not blame the register" in {
    // The trap the refusal existed for, and it is real: this goal quantifies over `d` and `b`, so
    // the premises come back naming variables the procedure opened, and no citation written about
    // `deaths` and `beds` could ever have named them.
    //
    // What changed on 2026-09-10 is the answer, not the analysis. Refusing the whole goal was one
    // way to avoid reporting those premises as `Uncited`; a third case is the other, and it keeps
    // the goals whose premises DO survive the stripping, which the refusal threw away with them.
    val sources = register("deaths:real = 53 * beds:real" -> "ARS 2022, table 4")

    val trail = force(sources.trail(linarith, "!d:real b:real. d = 53 * b /\\ 0 < b ==> d <= 60 * b"))

    // Every premise names an opened variable, so none is citable and none is reported uncited.
    trail.premises.collect { case p: Provenance.Premise.Uncited => p } shouldBe empty
    trail.premises.collect { case p: Provenance.Premise.Unnameable => p } should not be empty

    // And the citation is reported stale, which is the right reading: the register is about named
    // quantities and the claim is not about them.
    trail.stale.map(_.source) should contain("ARS 2022, table 4")
  }

  "A register citing one assumption twice" should "be refused, because which one is a person's question" in {
    Provenance
      .of(reals, Vector("0 < x:real" -> "one source", "0 < x:real" -> "another"))
      .isLeft shouldBe true
  }

  "A citation whose proposition does not read" should "be a repair of the text" in {
    // Rather than an entry that will never match anything, which is how a register goes quietly
    // wrong: nothing fails, and the source simply never appears in a trail.
    Provenance.of(reals, Vector("0 < " -> "a source")) match {
      case Left(error) => Remedy.of(reals, error) shouldBe a[RepairTheText]
      case Right(register) => fail(s"expected a refusal, got ${register.entries}")
    }
  }

  "A goal that does not follow" should "get the refusal, not a list of sources" in {
    val sources = register("0 < x:real" -> "a source")

    sources.trail(linarith, "0 < x:real ==> 1 < x").isLeft shouldBe true
  }

  /* ------------------------------------------------------------------------ the report */

  "The report" should "name the source first and read every proposition back" in {
    // The source first because that is what the file is for, and through `Readback` because a
    // reader comparing an article against a premise is comparing text: text that does not read back
    // as the term is text about a different premise, and a trail is read exactly when somebody is
    // checking.
    val sources = register(
      "deaths:real = 53 * beds:real" -> "ARS 2022, table 4",
      "beds:real < 900" -> "a bound nothing here needs"
    )

    val trail = force(
      sources.trail(linarith, "deaths:real = 53 * beds:real /\\ 0 < beds:real ==> deaths <= 60 * beds")
    )
    val report = force(sources.report(trail))

    report should include("rests on:")
    report should include("ARS 2022, table 4: deaths = 53 * beds")
    report should include(s"${Provenance.Uncited}: 0 < beds")
    report should include("cited and not assumed:")
    report should include("a bound nothing here needs: beds < 900")
  }

  it should "head the two kinds of unused citation differently, since they are fixed in different places" in {
    // One register, one goal, and both kinds at once. `beds < 900` is cited for a proposition this
    // goal never assumes, so the register is stale; `0 < staff` is assumed by the goal and weighed
    // zero, so the argument carries an assumption it does not need. A reader shown one heading for
    // both has to work out which of the two every line is, which is the work this split does once.
    val sources = register(
      "deaths:real = 53 * beds:real" -> "ARS 2022, table 4",
      "0 < staff:real" -> "a staffing figure the conclusion does not need",
      "beds:real < 900" -> "a bound nothing here needs"
    )

    val trail = force(
      sources.trail(
        linarith,
        "deaths:real = 53 * beds:real /\\ 0 < staff:real /\\ 0 < beds:real ==> deaths <= 60 * beds"
      )
    )
    val report = force(sources.report(trail))

    trail.idle.map(_.source) shouldBe Vector("a staffing figure the conclusion does not need")
    trail.stale.map(_.source) shouldBe Vector("a bound nothing here needs")

    report should include("assumed and not needed:\n  a staffing figure the conclusion does not need: 0 < staff")
    report should include("cited and not assumed:\n  a bound nothing here needs: beds < 900")
  }

  it should "say what a weight above one was, since a premise may be used more than once" in {
    val sources = register("0 < beds:real" -> "ISPRA Tab. 3.1, 2026 edition")
    val trail = force(
      sources.trail(linarith, "deaths:real = 53 * beds:real /\\ 0 < beds:real ==> deaths <= 60 * beds")
    )

    force(sources.report(trail)) should include("weighed 7")
  }

  /* --------------------------------------- the quantified goal, which used to be refused */

  "A goal with leading quantifiers" should "be attributed, not refused outright" in {
    // It was refused by name until 2026-09-10, and the argument for the refusal was right about the
    // danger and wrong about its extent: only the premises that MENTION a variable the quantifier
    // opened cannot be cited, and a goal whose register cites facts about a function has premises
    // that survive the stripping untouched. Refusing the whole goal threw those away with the rest.
    val register = force(
      Provenance.of(
        reals,
        Vector("0 < scale:real" -> "the calibration note, 2026")
      )
    )

    val trail = force(
      register.trail(linarith, "!t:real. 0 < scale:real /\\ 0 < t ==> 0 < scale + t")
    )

    trail.premises should not be empty
  }

  it should "keep 'no citation could name this' apart from 'nobody cited it'" in {
    // The merge the refusal was protecting against, now avoided by a third case rather than by
    // refusing everything. A reader who acts on `Uncited` when the truth is `Unnameable` goes
    // looking for a source that cannot exist.
    val register = force(Provenance.of(reals, Vector("0 < scale:real" -> "the calibration note")))

    val trail = force(
      register.trail(linarith, "!t:real. 0 < scale:real /\\ 0 < t ==> 0 < scale + t")
    )

    val unnameable = trail.premises.collect { case p: Provenance.Premise.Unnameable => p }
    val uncited = trail.premises.collect { case p: Provenance.Premise.Uncited => p }

    withClue(s"premises: ${trail.premises}\n") {
      unnameable should not be empty
      uncited shouldBe empty
    }
  }

  it should "still cite what the register named, through the quantifier" in {
    val register = force(Provenance.of(reals, Vector("0 < scale:real" -> "the calibration note")))

    val trail = force(
      register.trail(linarith, "!t:real. 0 < scale:real /\\ 0 < t ==> 0 < scale + t")
    )

    trail.premises.collect { case Provenance.Premise.Cited(_, source, _) => source } should
      contain("the calibration note")
  }
}
