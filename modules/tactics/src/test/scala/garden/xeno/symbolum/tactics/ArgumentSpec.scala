package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.{TyApp, Type}
import garden.xeno.symbolum.logic.LogicError
import garden.xeno.symbolum.theories.*

/**
 * A document rather than a claim, and the question that only exists at that size.
 *
 * `Cost` answers the questions its own docstring lists about one claim and `Provenance` names the
 * sources behind one proof. Run `n` times over a register of `m` citations, the second one gives an
 * answer that is wrong in a specific and misleading way: nearly every citation looks stale on
 * nearly every line, because a measurement used by the second conclusion was not used by the first.
 * A reader handed that page has to work out for themselves which of the twelve "stale" lines are
 * real.
 *
 * So the three buckets are computed over the argument, and the test that matters here is the
 * contrast: the same citation, stale to `Provenance.trail` on one claim and used by the document.
 *
 * The worked example is a small environmental argument, because that is the shape the declared
 * purpose names: measurements with sources, a threshold from a regulation, and a conclusion that a
 * limit is not exceeded.
 */
class ArgumentSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def forced[T](result: Either[TacticError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val real: Type = TyApp(Real.TypeName, Nil)

  /** The reals with three constants of a domain, which cost nothing to believe. */
  private val extended = force(
    Real.standard.extended(
      Vector.empty,
      Vector("load" -> real, "rate" -> real, "cap" -> real)
    )
  )

  private val order = force(
    for {
      arithmetic <- Arithmetic.construct(extended)
      ring <- Ring.construct(arithmetic)
      built <- Order.construct(ring)
    } yield built
  )

  private val linarith = force(Linarith.construct(order))

  private val cost = Cost(
    force(Prove.construct(order)),
    force(Field.construct(order.ring.arithmetic)),
    Abduce(linarith, Refutation(Evaluate.over(extended, Model.Numbers))),
    Quantified(linarith)
  )

  /**
   * The register: the argument below weighs most of it, states one citation and never weighs
   * it, and never states another at all. The two tests after the first pin which one is which.
   */
  private val register = forced(
    Provenance.of(
      extended,
      Vector(
        "0 < rate" -> "ISPRA Tab. 3.1",
        "load <= 60 * rate" -> "ARS 2022, table 4",
        "cap = 100 * rate" -> "Decreto 152/2006 art. 101",
        "0 < load" -> "ARS 2022, table 7",
        "load < cap" -> "Decreto 152/2006 art. 99"
      )
    )
  )

  private val argument = Argument(cost, linarith, register, Real.standard.theory.axioms.toSet)

  private val claims = Vector(
    "0 < rate /\\ load <= 60 * rate /\\ cap = 100 * rate ==> load < cap",
    "0 < rate /\\ cap = 100 * rate ==> 0 < cap",
    "0 < rate /\\ 0 < load ==> 0 < rate + rate"
  )

  private lazy val reading = forced(argument.read(claims))

  /* ------------------------------------------------------- the register, over the whole */

  "A citation one claim does not use" should "not be stale when another claim uses it" in {
    // The reason this file exists, as a contrast rather than an assertion about one side.
    //
    // `load <= 60 * rate` is weighed by the first conclusion and by neither of the others. Asked of
    // the third claim alone, `Provenance.trail` calls it stale, and it is right to: that claim does
    // not state it. Asked of the argument, it is used, and a page that called it stale would send a
    // reader to fix a register that is correct.
    val alone = forced(register.trail(linarith, forced(TacticError.lift(extended.proposition(claims(2))))))
    alone.stale.map(_.source) should contain("ARS 2022, table 4")

    reading.stale.map(_.source) should not contain "ARS 2022, table 4"
    reading.idle.map(_.source) should not contain "ARS 2022, table 4"
  }

  it should "still be idle when every claim that states it weighs it at nothing" in {
    // `0 < load` is stated by the third conclusion and weighed by nothing. The argument assumes
    // something it does not need: the thing to fix is the argument, and the register is right.
    reading.idle.map(_.source) shouldBe Vector("ARS 2022, table 7")
  }

  it should "be stale when no claim states it at all" in {
    // `load < cap` is the conclusion of the first claim and a premise of none of them. A citation
    // for a proposition the document never assumes is a register out of date, usually because the
    // proposition beside it was reworded: the thing to fix is the register, and the argument is
    // right.
    reading.stale.map(_.source) shouldBe Vector("Decreto 152/2006 art. 99")
  }

  /* ------------------------------------------------------------- what each line reports */

  "Every conclusion" should "carry its price, its premises and where each one came from" in {
    reading.lines should have size 3
    all(reading.lines.map(_.proved)) shouldBe true

    val first = reading.lines.head
    first.premises should have size 3
    first.premises.collect { case Provenance.Premise.Cited(_, source, _) => source } shouldBe
      Vector("ISPRA Tab. 3.1", "ARS 2022, table 4", "Decreto 152/2006 art. 101")

    // Every weight is the certificate's own and not a count of premises: the ones below are what
    // the Farkas multipliers came out as, and a reader checking the argument by hand checks these.
    first.premises.collect { case Provenance.Premise.Cited(_, _, weight) => weight } should
      not contain BigInt(0)

    first.report.inferences should be > 1000
  }

  it should "separate the axioms this document asked for from the ones it was built over" in {
    // The column a reader of the **document** can argue with, and it is empty here, which is the
    // outcome to aim for: three declared constants cost nothing to believe, and every assumption
    // sits on the left of a turnstile where somebody can disagree with it.
    reading.domainAxioms shouldBe empty
    reading.foundational should have size 13

    info(
      s"${reading.lines.length} claims, ${reading.inferences} inferences, " +
        s"${reading.domainAxioms.size} axioms of the domain, ${reading.foundational.size} foundational"
    )
  }

  "A conclusion with no linear certificate" should "still be costed, and say why it has no premises" in {
    // A ring identity is proved and has no Farkas multipliers to report. Leaving such a line off the
    // page, or leaving it blank, would hide the half of it the tactics can still answer for: the
    // outcome, the price and the axioms are all there.
    val ringed = forced(argument.read(Vector("!x:real. (x + 1) * (x + 1) = x * x + 2 * x + 1")))
    val line = ringed.lines.head

    line.proved shouldBe true
    line.premises shouldBe empty
    line.whyNoPremises should not be empty
    line.report.inferences should be > 0
  }

  "A premise nobody cited" should "be labelled as uncited and not left out" in {
    // The reason `Provenance.Premise` is two cases and not an `Option`: a page that listed only the
    // premises it could attribute would print a tidy set of sources under a proof that also rests
    // on something nobody said where they got.
    val mixed = forced(argument.read(Vector("0 < cap /\\ 0 < rate ==> 0 < cap + rate")))
    val labels = forced(argument.render(mixed))

    mixed.lines.head.premises.collect { case Provenance.Premise.Uncited(_, _) => true } should
      have size 1
    labels should include(s"${Provenance.Uncited}: 0 < cap")
  }

  "A premise no citation could have named" should "say so, rather than read as uncited" in {
    // The third case, and the distinction `Provenance` drew on 2026-09-10: a universal goal's
    // premises come back naming the variable the procedure opened the quantifier into, that
    // variable did not exist when the register was written, and "nobody said where this came from"
    // would send a reader looking for a source that cannot exist.
    val quantified = forced(argument.read(Vector("!t:real. 0 < t /\\ load <= t ==> load <= t + 1")))
    val page = forced(argument.render(quantified))

    quantified.lines.head.premises.collect { case Provenance.Premise.Unnameable(_, _) => true } should
      not be empty
    page should include(Provenance.Unnameable)
  }

  "A claim whose binder the caller named" should "come back beside the caller's own text" in {
    // `docs/adr/0002` says a bound name is not part of a term, and it names this page as covered by
    // the same cheap move `Ask` makes. It was not: `read` parsed each text and dropped it, so an
    // argument written about `spend` was answered about `x` and the ADR asserted a repair that did
    // not exist. What makes it matter here rather than only in `Ask` is that this is the page a
    // reader checks a formal document against the informal one with, which is the whole obligation.
    val named = forced(argument.read(Vector("!spend:real. 0 < spend /\\ load <= spend ==> load <= spend + 1")))
    val page = forced(argument.render(named))

    named.lines.head.asked shouldBe
      Some("!spend:real. 0 < spend /\\ load <= spend ==> load <= spend + 1")
    page should include("as asked: !spend:real. 0 < spend /\\ load <= spend ==> load <= spend + 1")
    page should include(Argument.NameNote)
  }

  it should "say nothing where the page already prints the claim as it was written" in {
    // The control, and the reason the assertion above is worth having: a line printed on every
    // claim would pass that test while telling a reader nothing, since it would carry no
    // information about which claims actually came back renamed. A claim with no binder at all
    // cannot be renamed, so this is the case that must stay silent.
    val plain = forced(argument.read(Vector("0 < cap /\\ 0 < rate ==> 0 < cap + rate")))
    val page = forced(argument.render(plain))

    plain.lines.head.asked should not be empty
    page should not include "as asked:"
    page should not include Argument.NameNote
  }

  it should "explain itself once for the page rather than once for every line" in {
    // Measured rather than asserted, because the cheap implementation is one note per line and it
    // reads as noise by the third claim. Two renamed claims, one explanation.
    val two = forced(
      argument.read(
        Vector(
          "!spend:real. 0 < spend ==> spend <= spend + 1",
          "!budget:real. 0 < budget ==> budget <= budget + 1"
        )
      )
    )
    val page = forced(argument.render(two))

    page.linesIterator.count(_.contains("as asked:")) shouldBe 2
    page.linesIterator.count(_ == Argument.NameNote) shouldBe 1
  }

  "A conclusion decided false" should "count as settled and not as proved" in {
    // The two are different columns of the summary on purpose. A claim the elimination decides
    // false is finished, and it is not a theorem: an argument whose conclusions are half decided and
    // half proved is a different document from one whose conclusions are all proved.
    // Quantified, because that is what the elimination decides: `0 < rate ==> rate < 0` over a
    // declared constant comes back `Unsettled`, since `rate` is a constant of the domain and not
    // something to eliminate.
    val refuted = forced(argument.read(Vector("!x:real. 0 < x ==> x < 0")))
    val line = refuted.lines.head

    line.settled shouldBe true
    line.proved shouldBe false
    refuted.summary should include("0 proved, 1 decided")
  }

  "A conclusion nothing settles" should "be counted as open rather than quietly dropped" in {
    val open = forced(argument.read(Vector("0 < rate ==> 0 < load")))
    val line = open.lines.head

    line.settled shouldBe false
    line.proved shouldBe false
    open.summary should include("1 open")
  }

  /* ---------------------------------------------------------------------- the page */

  "The page" should "put the claims first and the register's own verdict last" in {
    val page = forced(argument.render(reading))
    val lines = page.linesIterator.toVector

    lines.head shouldBe reading.summary
    lines.head should include("3 claims, 3 proved")
    // Two counts and one noun until 2026-09-18, which no rule over the pair renders as English.
    // Each number governs a noun of its own now, so this reads "1 idle citation and 1 stale
    // citation" rather than "1 idle and 1 stale citations".
    lines.head should include("1 idle citation and 1 stale citation")

    // The axioms are listed once for the document and not once per claim. Thirteen of them on each
    // of a dozen lines is a hundred and fifty lines saying one thing, and the count stays on every
    // line because a claim that reached three and a claim that reached thirteen are not the same
    // claim.
    lines.count(_.contains("believed on")) shouldBe 13
    lines.count(_.contains("inferences over 13 axioms")) shouldBe 3

    page should include("weighed 1, from ARS 2022, table 4: load <= 60 * rate")
    page should include("assumed and never weighed: 0 < load (ARS 2022, table 7)")
    page should include("cited and never assumed: load < cap (Decreto 152/2006 art. 99)")
  }

  // Three of this line's counts carry a noun and none of them conditioned it until 2026-09-18, so
  // a document of one claim said "1 claims" and one that reached a single axiom of its own said
  // "1 axioms of the domain". The citations were the case with no repair available at the last
  // letter: two counts shared one noun, and neither "1 idle and 1 stale citations" nor "1 idle and
  // 0 stale citation" is English, so each number governs a noun of its own now.
  //
  // BOTH DIRECTIONS IN ONE TEST, for the reason `EssaySpec` gives at the same shape: the repair is
  // one shared helper and one wrong comparison in it turns every count on every page singular,
  // which a test written on the singular alone reports as fixed. The reading is BUILT here rather
  // than read from the fixture above: `summary` is a function of four fields and nothing else, and
  // a document costing one claim and one domain axiom is a fixture rather than a proof to find.
  "The counts on the summary line" should "take the singular at one and the plural elsewhere" in {
    val claim = force(extended.proposition("0 < load"))
    val axiom = force(extended.proposition("0 < cap"))

    def line(claims: Int, domain: Int, idle: Int, stale: Int): String = {
      val report = Cost.Report(
        claim = claim,
        outcome = Cost.Outcome.Proved,
        axioms = if (domain == 0) Set.empty else Set(axiom)
      )
      withClue(s"this fixture can build 0 or 1 domain axioms and was asked for $domain: ") {
        domain should be <= 1
      }
      Argument
        .Reading(
          lines = Vector.fill(claims)(Argument.Line(claim, report, Vector.empty, None)),
          idle = Vector.fill(idle)(Provenance.Entry(claim, "a source")),
          stale = Vector.fill(stale)(Provenance.Entry(claim, "another source")),
          foundation = Set.empty
        )
        .summary
    }

    line(1, 1, 1, 1) should
      startWith("1 claim, 1 proved, 0 decided, 0 open; 1 axiom of the domain")
    line(1, 1, 1, 1) should include("1 idle citation and 1 stale citation")

    // The plural on every one of the three, on a reading of the same shape, so a helper that has
    // gone singular everywhere fails here rather than passing.
    line(2, 0, 0, 3) should
      startWith("2 claims, 2 proved, 0 decided, 0 open; 0 axioms of the domain")
    line(2, 0, 0, 3) should include("0 idle citations and 3 stale citations")
  }
}
