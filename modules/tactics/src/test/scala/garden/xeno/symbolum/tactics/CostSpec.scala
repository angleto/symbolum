package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.{Term, Type}
import garden.xeno.symbolum.logic.Intuitionistic
import garden.xeno.symbolum.theories.Real

/**
 * What one report says, and the reason each field is its own.
 *
 * The interesting assertions here are the ones about what the report does **not** merge. Every
 * answer this file gathers already existed and each was already tested where it lives, so a spec
 * that only re-checked them would say nothing; what is new is that the answers `Cost`'s docstring
 * lists arrive together and that a reader can tell which question each one answered.
 */
class CostSpec extends AnyFlatSpec with Matchers {

  private val cost = Cost.standard
  private val reals = cost.reals

  private def report(text: String): Cost.Report =
    cost.of(text).fold(error => fail(error.message), identity)

  private def page(text: String): String =
    cost.render(report(text)).fold(error => fail(error.message), identity)

  /**
   * A variable whose name the lexer cannot read, which is what cannot be read back now.
   *
   * The choice axiom was the example until 2026-09-12: it quantifies over a type variable, the
   * printer wrote one without its quote, and the reader refused it. That is repaired at the
   * printer, so the branch below needs a term that is genuinely unreadable rather than one that was
   * printed wrongly. `%` starts no name the lexer accepts, which is why `Matching` opens binders
   * with variables named that way, and printing one produces text nothing can read.
   */
  private val unreadable: Term = Term.variable("%0", Real.realType)

  "An axiom that does not read back" should "be shown and named, not withhold the page" in {
    // The rule, and it is a rule about what a reader is shown rather than about axioms. Everything
    // on this page except the axioms is the caller's own text and is read back strictly: text that
    // does not come back as the term is text about a different claim. An axiom is the theory's, the
    // caller cannot have got it wrong, and withholding the rest of the page over it helps nobody.
    val shown = cost
      .page(
        Cost.Report(
          claim = reals.proposition("!x:real. x + 0 = x").fold(error => fail(error.message), identity),
          outcome = Cost.Outcome.Proved,
          axioms = Set(unreadable)
        ),
        believed = true
      )
      .fold(error => fail(error.message), identity)

    shown.mkString("\n") should include("believed on, and it does not read back: %0")
    shown.mkString("\n") should include("Proved")
  }

  /* ------------------------------------------------------------ what it charges */

  "An identity that needs no denominator" should "be proved outright, with nothing owed" in {
    val settled = report("!x:real y:real. (x + y) * (x + y) = x * x + 2 * (x * y) + y * y")

    settled.outcome shouldBe Cost.Outcome.Proved
    settled.conditions shouldBe empty
  }

  "An identity that cancels a denominator" should "be a theorem with its price on the left" in {
    // The claim this whole file exists to make legible: `(x * y) / y = x` is not true and is not
    // false, it is true away from zero, and the report says which. `Prove` alone answers this with
    // a refusal, because a procedure returning a theorem or nothing has nowhere to put a price.
    val priced = report("!x:real y:real. (x * y) / y = x")

    priced.outcome shouldBe Cost.Outcome.Conditional
    priced.conditions.map(reals.show) shouldBe Vector("~(y = 0)")
  }

  it should "not be filed with the claims nothing is known about" in {
    // The merge this design is most at risk of. A priced theorem and an unsettled goal are both
    // "Prove said no", and a report that put them together would tell an author to go and look for
    // an argument that is already written down.
    report("!x:real y:real. (x * y) / y = x").outcome should not be Cost.Outcome.Unsettled
  }

  /* --------------------------------------------------------- what it is believed on */

  "A proved claim" should "carry the axioms its own derivation reaches, not the theory's" in {
    // Sixteen are asserted and eight are reached. The ones absent are the point: nothing about the
    // order and nothing about completeness is used to multiply two sums out, and before a theorem
    // recorded its derivation there was no way to say so.
    val settled = report("!x:real y:real. (x + y) * (x + y) = x * x + 2 * (x * y) + y * y")

    settled.axioms.size shouldBe 8
    settled.axioms.map(reals.show) should contain("!x:real. !y:real. x * y = y * x")
    settled.axioms.map(reals.show) should not contain "!x:real. ~(x = 0) ==> x * inv x = 1"
    settled.inferences should be > 1000
  }

  it should "reach the inverse axiom exactly when a denominator was cancelled" in {
    val priced = report("!x:real y:real. (x * y) / y = x")

    priced.axioms.map(reals.show) should contain("!x:real. ~(x = 0) ==> x * inv x = 1")
  }

  /* ------------------------------------------- whether the quantifiers are the right way round */

  "A claim whose quantifiers alternate" should "be decided, and said to be decided rather than proved" in {
    // The two differ by the order of two quantifiers and by nothing else, which is the mistake
    // autoformalisation is known for. Neither is certified, and the report says that in the same
    // breath as the answer rather than leaving it to be assumed.
    report("!x:real. ?y:real. x < y").outcome shouldBe Cost.Outcome.Holds
    report("?y:real. !x:real. x < y").outcome shouldBe Cost.Outcome.Fails
  }

  it should "say what would have to change for a certificate, not that the claim needs rewriting" in {
    page("!x:real. ?y:real. x < y") should include("decided, not certified")
    page("!x:real. ?y:real. x < y") should not include "no proof"
  }

  /* ------------------------------------------------------------ what is missing */

  "A claim that is false" should "still come back with the point it fails at and what would repair it" in {
    // Deciding it false is not the end of the answer, it is where the useful part starts. Stopping
    // at `Fails` would throw away both halves of what an author asks next: where, and what to add.
    val broken = report("!x:real. 0 < x ==> 1 < x")

    broken.outcome shouldBe Cost.Outcome.Fails
    broken.point.getOrElse(fail("no point")) should include("x = 1")
    broken.vacuous.map(reals.show) should contain("x < 0")
    broken.circular.map(reals.show) should contain("1 < x")
  }

  it should "keep the kinds of candidate apart" in {
    // `Abduce`'s own discipline, carried through rather than flattened: a premise that closes the
    // goal, one that makes the premises impossible, and one that is the conclusion handed back are
    // three different things to be told, and only the first is an answer.
    val broken = report("!x:real. 0 < x ==> 1 < x")

    broken.missing should not contain theSameElementsAs(broken.vacuous)
    broken.missing.map(reals.show) should not contain "x < 0"
    broken.missing.map(reals.show) should not contain "1 < x"
  }

  "A claim nothing in the candidate language repairs" should "come back with the point and no guess" in {
    // `x <= y ==> x < y` wants `~(x = y)` and the candidates are bounds. An empty list is the right
    // answer and the point is what makes it usable.
    val broken = report("!x:real y:real. x <= y ==> x < y")

    broken.missing shouldBe empty
    broken.point should not be empty
  }

  /* ------------------------------------------------------------ the page */

  "The rendered report" should "print every proposition in the theory's notation" in {
    // Through `Readback`, for the reason that file exists: a reader compares text against the claim
    // they meant, and text in the kernel's notation is text about a claim they did not write.
    val printed = page("!x:real y:real. (x * y) / y = x")

    printed should startWith("Conditional: !x:real. !y:real. x * y / y = x")
    printed should include("charges: ~(y = 0)")
    printed should include("inferences over 8 axioms")
    printed should not include "(div "
  }

  it should "count the inferences of a conditional theorem too, since there is one" in {
    report("!x:real y:real. (x * y) / y = x").inferences should be > 0
  }

  it should "say nothing about a proof where there is none" in {
    page("!x:real. ?y:real. x < y") should not include "inferences"
  }

  // Until 2026-09-18 this line was a bare interpolation followed by a plural, so the page said
  // "1 axioms" on any claim resting on a single axiom — which is not a corner: at the tip the card
  // was opened against, `Ask` on `!x:real. !y:real. x + y = y + x` printed
  // "77 inferences over 1 axioms". This is the surface on which this repository tells a reader what
  // it costs to believe something, so the number and its noun have to agree there if anywhere.
  //
  // BOTH DIRECTIONS IN ONE TEST, for the reason `EssaySpec` gives for the same shape: the repair is
  // a shared helper, so one wrong comparison in it turns every count on every page singular, and a
  // test written only on the singular calls that fixed. The report is built here rather than proved
  // for, because the singular at the inference count needs a proof exactly one inference long and
  // what is under test is the rendering, not which claims are that cheap.
  "The two counts on the proof line" should "take the singular at one and the plural elsewhere" in {
    val claim = reals.proposition("!x:real. x + 0 = x").fold(error => fail(error.message), identity)

    def proofLine(inferences: Int, axioms: Int): String = {
      val distinct: Set[Term] = (0 until axioms).map(i => Term.variable(s"a$i", Real.realType)).toSet
      withClue(s"the fixture asked for $axioms axioms and built ${distinct.size}: ") {
        distinct.size shouldBe axioms
      }
      cost
        .page(
          Cost.Report(
            claim = claim,
            outcome = Cost.Outcome.Proved,
            inferences = inferences,
            axioms = distinct
          ),
          believed = false
        )
        .fold(error => fail(error.message), identity)
        .find(_.contains(" over "))
        .getOrElse(fail(s"no proof line at $inferences inference(s) over $axioms axiom(s)"))
    }

    proofLine(1, 1).trim shouldBe "1 inference over 1 axiom"
    proofLine(77, 1).trim shouldBe "77 inferences over 1 axiom"
    proofLine(1, 2).trim shouldBe "1 inference over 2 axioms"
    // Zero takes the plural, which is the case a reader of the condition does not picture, and it
    // is the ordinary reading of a claim the kernel settled without reaching an axiom at all.
    proofLine(4, 0).trim shouldBe "4 inferences over 0 axioms"
  }

  /* ------------------------------------------- what it rests on, read as mathematics */

  "A report over a chain" should "say what the proof rests on, by name, beside the axioms" in {
    // The two lines answer different questions and one of them is about to stop being interesting.
    // "Believed on" lists the axioms a derivation reached, and `docs/adr/0007` turns the sixteen
    // into theorems: after that it answers "choice, eta, infinity" for everything, which is
    // precisely the uninformative answer Lean's `#print axioms` gives. "Rests on" counts **named
    // facts**, and a fact keeps its name when it stops being an axiom.
    val overChain = Cost.construct(garden.xeno.symbolum.theories.Chain.standard).fold(error => fail(error.message), identity)
    val found = overChain.of("!x:real. x * 1 = x").fold(error => fail(error.message), identity)

    found.reach should not be empty
    found.reach.get.domain should not be empty

    val printed = overChain.render(found).fold(error => fail(error.message), identity)

    printed should include("rests on:")
    printed should include("named facts")
    printed should include("assumed about the subject:")
  }

  it should "say nothing about the reach when the caller had no library, rather than nothing at all" in {
    // `Cost.standard` is over the theory of the reals alone and has no chain to read a reach
    // against. An empty reach and an absent one are different answers, and the page shows the
    // difference by leaving the line out.
    report("!x:real. x * 1 = x").reach shouldBe None
    page("!x:real. x * 1 = x") should not include "rests on:"
  }

  /* ------------------------------------- a price a bound chose rather than the claim */

  /**
   * The chain of implications `PropositionalRouteSpec` uses, built here for the same reason it is
   * built there: it is the one family whose consumption of the intuitionistic net grows with a
   * parameter, so one link apart is the whole difference between a free route that finishes and
   * one that is cut short.
   */
  private def chainOf(links: Int): Term = {
    val logic = garden.xeno.symbolum.theories.Chain.standard.widest.logic
    def force[E, T](result: Either[E, T]): T =
      result.fold(error => fail(s"expected success, got $error"), identity)
    def atom(i: Int): Term = Term.variable(s"p$i", Type.Bool)
    val steps = (1 to links).map(i => force(logic.mkImp(atom(i), atom(i + 1))))
    force(
      logic.mkImp(
        steps.reduceLeft((a, b) => force(logic.mkConj(a, b))),
        force(logic.mkImp(atom(1), atom(links + 1)))
      )
    )
  }

  // The defect card 011218be exists for, on the surface a person reads. `Prove` has reported the
  // case in its own type since 2026-09-18 and `Cost.Report` has carried it since the same day, and
  // until 2026-09-19 **nothing read the field**: the page of a 128-link chain and the page of
  // Peirce's law differed by the claim and by the inference count and by nothing else, both
  // resting on the same `select`. So no surface could reconstruct the caveat from the price, and
  // `docs/adr/0031` said each surface says it while one of the two did not.
  //
  // BOTH DIRECTIONS IN ONE TEST, and here that is not a rendering convention but the measurement
  // itself: a page that printed the caveat always would be as wrong as one that never did, and
  // only the pair separates them. The two goals are one link apart, so what differs between the
  // pages is the bound and not the mathematics.
  "The page of a goal the free route was cut short on" should "name which search stopped and at what, where the page of a goal it finished names nothing" in {
    val overChain =
      Cost.construct(garden.xeno.symbolum.theories.Chain.standard).fold(error => fail(error.message), identity)

    def printed(links: Int): String = {
      val found = overChain.of(chainOf(links)).fold(error => fail(error.message), identity)
      overChain.render(found).fold(error => fail(error.message), identity)
    }

    // 128 links: the net runs out and the classical procedure answers, at the choice axiom.
    val short = printed(128)
    short should include(Intuitionistic.SearchName)
    short should include(s"stopped at ${Intuitionistic.Fuel}")
    short should include("this price is a bound's rather than this claim's")

    // 127 links: the same theorem one link shorter, decided inside the net, and the page says
    // nothing of the sort. This is the positive control, and without it the assertion above is
    // satisfied by a renderer that has started saying it about everything.
    val whole = printed(127)
    whole should not include Intuitionistic.SearchName
    whole should not include "cut short"
  }
}
