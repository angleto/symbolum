package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Chain, Field, Library, Linarith, Order, Prose, Reach, RealTheory, Signature}

/**
 * Everything this system can say about one claim, gathered in one place.
 *
 * The parts have existed separately for a while and nobody had put them together, which is why the
 * thing they add up to was easy to describe and impossible to show. Each answers a question a
 * reader of a formal development asks and a prover normally does not:
 *
 *  - **what it charges.** `Field` proves an identity that needs a denominator to be non-zero and
 *    hands the condition back in the sequent, so `(x * y) / y = x` costs `~(y = 0)` and says so.
 *  - **what it is believed on.** A theorem records its derivation, so the axioms its proof reaches
 *    are a set that can be printed: `12 * 12 = 144` reaches five of the sixteen and touches neither
 *    the order nor completeness.
 *  - **where it fails.** `Refutation` names a point at which the premises hold and the conclusion
 *    does not, which a reader can check without trusting anything here.
 *  - **what is missing.** `Abduce` proposes what would have to be assumed, keeps apart a premise
 *    that would make the premises impossible and one that is the conclusion asked for back, and
 *    proves the goal with each before reporting it.
 *  - **whether the quantifiers are the right way round.** `Quantified` decides a claim whose
 *    quantifiers alternate, which is the failure autoformalisation is most known for.
 *
 * == It gathers and does not decide ==
 *
 * Every field below is one of those answers with its own meaning kept. Nothing here merges two of
 * them into a verdict, and the outcome names which question was actually answered rather than
 * flattening "not proved" and "shown false" into one. That is the same discipline `Refutation`
 * keeps seven outcomes for, one level up: a report that said less than its parts would be worse
 * than the parts.
 *
 * A field that is empty means the question did not arise, not that the answer was no.
 */
final class Cost private (
  val prove: Prove,
  val field: Field,
  val abduce: Abduce,
  val quantified: Quantified,
  /**
   * The library a proof's reach is read against, when the caller has a chain to build one from.
   *
   * `axioms` answers "which unproved things did this use" and stops answering the day the reals
   * are constructed, which `docs/adr/0007` decides they will be: the sixteen become theorems and
   * the count says "choice, eta, infinity" for everything, which is exactly Lean's uninformative
   * answer. `Reach` asks "which **named facts** did this use" instead, and a fact keeps its name
   * when it stops being an axiom.
   *
   * `None` is a caller with no chain, and then the report carries the axioms and says nothing
   * about the reach rather than pretending the question did not arise. `Cost.standard` is over the
   * theory of the reals alone and is one of those.
   */
  val held: Option[Library]
) {

  import Cost.*

  val reals: Signature = prove.reals

  /** The one `Abduce` searches with, which is where a point at which the claim fails comes from. */
  val refutation: Refutation = abduce.refutation

  /** The report for a claim in the theory's notation. */
  def of(text: String): Either[TacticError, Report] =
    TacticError.lift(reals.proposition(text)).flatMap(of)

  /**
   * The report for a claim already read.
   *
   * The order the questions are asked in is the order of what an answer is worth. A proof settles
   * it and the rest is about the proof. A decision without a proof settles it and says so. Only
   * after both fail is it worth asking what is missing, which is the expensive question.
   */
  def of(claim: Term): Either[TacticError, Report] = prove(claim) match {
    case Right(outcome) =>
      val theorem = outcome.theorem
      Right(
        Report(
          claim,
          Outcome.Proved,
          conditions = theorem.hypotheses.toVector,
          axioms = Derivation.axiomsOf(theorem),
          inferences = Derivation.size(theorem),
          census = Derivation.census(theorem),
          reach = reachOf(theorem),
          // The one thing this report cannot compute from the theorem, and the reason it is carried
          // rather than derived: `axioms` says the choice axiom is there and cannot say whether the
          // claim needed it or a bound chose it. `Prove` is the only place that knows, and until
          // 2026-09-18 it threw the answer away. `docs/adr/0031`.
          cutShort = outcome match {
            case Prove.Outcome.CutShort(_, search, depth) => Some(search -> depth)
            case Prove.Outcome.Settled(_) => None
          }
        )
      )

    case Left(refusal) =>
      priced(claim) match {
        // The refusal is dropped here and only here. `Prove` refuses a priced claim by naming the
        // price, so keeping it would print "no proof" above the theorem and its conditions, which
        // is the same fact twice and the second time as its own contradiction.
        case Some(report) => Right(report)

        case None =>
          quantified.decide(claim) match {
            case Right(Quantified.Holds) =>
              Right(Report(claim, Outcome.Holds, refusal = Some(refusal)))

            // A claim decided false is the case abduction is *for*, so the outcome and the gap are
            // both reported. Stopping at "it fails" would throw away the point it fails at and the
            // premise that would repair it, which is what an author asks for next.
            case Right(Quantified.Fails) =>
              Right(withGap(Report(claim, Outcome.Fails, refusal = Some(refusal))))

            case _ =>
              Right(withGap(Report(claim, Outcome.Unsettled, refusal = Some(refusal))))
          }
      }
  }

  /** What a theorem rests on, when this was built over something that can say. */
  private def reachOf(theorem: Kernel.Thm): Option[Reach] =
    held.map(library => Reach.of(library, theorem))

  /**
   * What `Abduce` knows about a claim there is no theorem for, folded into the report.
   *
   * It can also change the outcome, and that is the one thing this does beyond copying fields. A
   * point found among values the model computes exactly is a refutation rather than evidence, so a
   * claim about the naturals that fails at `x = 3, y = 5` is [[Outcome.Fails]] and not
   * [[Outcome.Unsettled]]. Before 2026-09-11 it was `Unsettled` and, worse, `Novelty` read it as
   * `Unreadable`, which says no procedure could take the shape: three proposals of this
   * repository's own audit were labelled that way while carrying the number they fail at.
   *
   * Only exactness buys this. `Abduce.Gap.decisive` says which points qualify and why the exact
   * rational solver is not among them.
   */
  private def withGap(report: Report): Report = abduce.missing(report.claim).toOption match {
    case None => report
    case Some(gap) =>
      report.copy(
        outcome = if (gap.decisive) Outcome.Fails else report.outcome,
        point = gap.point,
        missing = gap.found,
        circular = gap.circular,
        vacuous = gap.vacuous,
        unchecked = gap.unchecked
      )
  }

  /**
   * The report for a claim `Field` settles at a price, or nothing when there is no price.
   *
   * `Prove` already asked `Field` and turned its answer into a refusal naming the conditions, which
   * is the right thing for something that returns a theorem or nothing. Here there is somewhere for
   * the theorem to go, so it is asked again and kept: what comes back is a real theorem with the
   * price on its left, and its derivation answers the axiom question like any other.
   *
   * **An empty condition list is not this case**, for the reason `Prove.priceOf` gives: `Field`
   * proving something with nothing assumed did no more than the ring normalisation did, and that
   * has already refused. Reporting a price of zero would announce a charge that was never made.
   */
  private def priced(claim: Term): Option[Report] =
    field.prove(claim).toOption.filter(theorem => field.conditions(theorem).nonEmpty).map {
      theorem =>
        Report(
          claim,
          Outcome.Conditional,
          conditions = theorem.hypotheses.toVector,
          axioms = Derivation.axiomsOf(theorem),
          inferences = Derivation.size(theorem),
          census = Derivation.census(theorem),
          reach = reachOf(theorem)
        )
    }

  /**
   * The report as a page, which is the form a person reads it in.
   *
   * Through `Readback` for every proposition, and for the reason that file exists: a reader
   * comparing a claim against what is printed is comparing text, and text that does not read back
   * as the term is text about a different claim.
   */
  def render(report: Report): Either[TacticError, String] =
    page(report, believed = true).map(_.mkString("\n"))

  /**
   * The same page, as its lines, with the axiom list optional.
   *
   * `Argument` is the caller that wants it without: a document is a dozen claims over one theory,
   * every one of them believed on the same thirteen axioms, and printing that list once per line
   * is a hundred and fifty lines saying one thing. The **count** stays on every line, because a
   * claim that reached three axioms and one that reached thirteen are not the same claim; the list
   * moves to the end of the document, where it belongs to the document.
   *
   * One renderer with a parameter rather than two renderers, because the alternative is a second
   * copy of this that drifts.
   */
  def page(report: Report, believed: Boolean): Either[TacticError, Vector[String]] = {
    def believedLine(axiom: Term): String =
      Readback.of(reals, axiom) match {
        case Right(text) => s"  believed on: $text"
        // Shown in the theory's own printing and named as what it is. `Remedy` reads `NotLegible`
        // as a defect of this repository rather than of the caller, and that reading is right and
        // is not a reason to withhold the other twelve lines.
        case Left(_) => s"  believed on, and it does not read back: ${reals.show(axiom)}"
      }

    def lines(label: String, terms: Vector[Term]): Either[TacticError, Vector[String]] =
      terms.foldLeft[Either[TacticError, Vector[String]]](Right(Vector.empty)) { (acc, term) =>
        for {
          done <- acc
          text <- Readback.of(reals, term)
        } yield done :+ s"  $label: $text"
      }

    for {
      claim <- Readback.of(reals, report.claim)
      charged <- lines("charges", report.conditions)
      missing <- lines("assume", report.missing)
      circular <- lines("asks for the claim back", report.circular)
      vacuous <- lines("would make the premises impossible", report.vacuous)
      unchecked <- lines("would close it, and was not checked against the premises", report.unchecked)
      // The axioms are read back **leniently** and everything else strictly, and the asymmetry is
      // the point. A claim and the premises around it are the caller's own text and have to come
      // back as text the caller can compare; an axiom is the theory's, and one of them does not
      // read back at all. The choice axiom prints as a proposition about `select` at a type
      // variable that the reader will not take, so a page over any development holding it — which
      // is every development with the naturals in it — refused entirely, and a claim about `num`
      // could not be shown at all. A line marked as not reading back is worth more than no page.
      axioms <-
        if (believed) Right(report.axioms.toVector.sortBy(reals.show).map(believedLine))
        else Right(Vector.empty)
      // Beside the axioms and not instead of them, and printed as names rather than as terms: the
      // point of the reading is that a name survives a fact ceasing to be an axiom, so the line is
      // about the mathematics and the one above it is about the trusted base.
      resting = report.reach.map(found => s"  rests on: ${found.summary}").toVector
      named = report.reach
        .filter(_.domain.nonEmpty)
        .map(found => s"  assumed about the subject: ${found.domain.mkString(", ")}")
        .toVector
    } yield {
      val head = s"${report.outcome}: $claim"
      // Both counts go through `Prose.count`, and both reach one. The page this line is the whole
      // point of said "1 axioms" until 2026-09-18 on any claim resting on a single axiom, which is
      // the ordinary case rather than a corner: `!x:real. !y:real. x + y = y + x` reads that way.
      // The inference count is guarded above zero here and so only ever reads the singular at one.
      val proof =
        if (report.inferences > 0)
          Vector(
            s"  ${Prose.count(report.inferences, "inference")} over " +
              s"${Prose.count(report.axioms.size, "axiom")}"
          )
        else Vector.empty
      val where = report.point.map(point => s"  fails at: $point").toVector
      // Through `Remedy` rather than the refusal's own text, which names the shape it wanted and
      // prints the term it got in the kernel's notation. The claim is already at the top of this
      // page in the theory's, so printing it again in another one says nothing and reads as a
      // second, different claim. What is left is what a reader can do about it.
      //
      // The label changes with the outcome because the same advice means two things. Under
      // `Unsettled` nothing is known and restating is how to find out; under `Holds` or `Fails` the
      // question is answered and restating is how to get a certificate for an answer one already
      // has. A single label would make the first reading the only one, and would read as the tool
      // asking for a true statement to be rewritten.
      val label = report.outcome match {
        case Outcome.Holds | Outcome.Fails => "decided, not certified"
        case _ => "no proof"
      }
      val why = report.refusal.map(refusal => s"  $label: ${Remedy.of(reals, refusal).message}").toVector

      Vector(head) ++ proof ++ charged ++ axioms ++ resting ++ named ++ why ++ where ++ missing ++
        circular ++ vacuous ++ unchecked
    }
  }
}

object Cost {

  /** Which question the report answers, kept apart rather than merged into a verdict. */
  enum Outcome {

    /** A theorem with nothing on its left, and the rest of the report is about that proof. */
    case Proved

    /**
     * A theorem, and `conditions` is what it assumes.
     *
     * Kept apart from [[Proved]] because the difference is the whole of what this report exists to
     * show, and kept apart from [[Unsettled]] because a price is an answer: `(x * y) / y = x` is
     * settled everywhere `y` is not zero, and a report that filed it with the things nothing is
     * known about would be describing a different situation.
     */
    case Conditional

    /** No theorem, and the claim holds over the reals by elimination. Decided, never certified. */
    case Holds

    /** No theorem, and the claim does not hold. Also decided rather than certified. */
    case Fails

    /** Neither. The rest of the report is what is known about why. */
    case Unsettled
  }

  /**
   * What a claim costs, and what is known about it.
   *
   * An empty field means the question did not arise. `conditions` is what the theorem assumes and
   * is empty exactly when [[Outcome.Proved]] says it is: the outcome and the field agree, rather
   * than one of them carrying the news.
   */
  final case class Report(
    claim: Term,
    outcome: Outcome,
    conditions: Vector[Term] = Vector.empty,
    axioms: Set[Term] = Set.empty,
    inferences: Int = 0,
    /**
     * What the proof is **made of**, which is `inferences` taken apart by rule.
     *
     * Beside the length rather than instead of it, and the reason is that a cost anybody can be
     * held to has to be a function of the proof. A wall clock measures the afternoon it was read
     * in; this suite has run in 41 seconds and in 6 minutes 39 on one tree in one day. A census
     * does not move unless the proof does.
     */
    census: Map[String, Int] = Map.empty,
    /**
     * Which bound stopped the free route, and at what depth, where one did.
     *
     * Empty is the ordinary answer and says the price above is the claim's own. Where it is set,
     * `axioms` carries an axiom a larger bound might not have charged, and the pair names **which**
     * search stopped and **at what**, because what a reader needs to know is that an arbitrary
     * constant rather than the mathematics decided this price.
     */
    cutShort: Option[(String, Int)] = None,
    refusal: Option[TacticError] = None,
    point: Option[String] = None,
    missing: Vector[Term] = Vector.empty,
    circular: Vector[Term] = Vector.empty,
    vacuous: Vector[Term] = Vector.empty,
    /**
     * What would close the goal, and whether it does so for nothing was not decided.
     *
     * Carried rather than folded into `missing`, because the two are the difference between "assume
     * this" and "assume this, and nobody checked whether assuming it makes your premises
     * impossible". `Abduce.Gap.unchecked` has the measurement of how often the second is the case.
     */
    unchecked: Vector[Term] = Vector.empty,
    /**
     * What the proof rests on read as mathematics, when a library was there to read it against.
     *
     * Beside `axioms` rather than instead of it, because the two answer different questions and one
     * of them is about to stop being interesting: `axioms` says which unproved things a proof used,
     * and `docs/adr/0007` turns the sixteen into theorems. `Reach` says which **named facts** it
     * used, which survives that.
     */
    reach: Option[Reach] = None
  )

  /** Over the standard theory. */
  lazy val standard: Cost =
    new Cost(Prove.standard, Field.standard, Abduce.standard, Quantified.standard, None)

  /**
   * The accounting over a chain, which is what [[Prove.construct]] is for proving.
   *
   * [[standard]] reads in `Real.standard`, a signature with no `num` in it, so a claim mentioning a
   * natural number could not be **stated** to it, let alone accounted for. Every part below is
   * rebuilt over the chain's own order rather than over the standard one, because the two are
   * different objects: the chain builds the naturals first and the reals over them, so its `Order`
   * reads in a theory that has both types and `Order.standard` reads in one that has neither.
   *
   * The procedures still decide the fragments of the reals they always did. What changes is what
   * can be put to them, which is the difference between a refusal that names a fragment and a
   * refusal that says the statement does not parse.
   */
  def construct(chain: Chain): Either[LogicError, Cost] =
    for {
      prove <- Prove.construct(chain)
      field <- Field.construct(chain.arithmetic)
      linarith <- Linarith.construct(chain.order)
    } yield new Cost(
      prove,
      field,
      Abduce(linarith, Refutation(Evaluate.over(chain.reals, Model.Numbers))),
      Quantified(linarith),
      Some(Reach.library(chain))
    )

  /** Over a development of one's own. */
  def apply(prove: Prove, field: Field, abduce: Abduce, quantified: Quantified): Cost =
    new Cost(prove, field, abduce, quantified, None)

  /** The same, for a caller that has a library to read a proof's reach against. */
  def apply(
    prove: Prove,
    field: Field,
    abduce: Abduce,
    quantified: Quantified,
    held: Library
  ): Cost = new Cost(prove, field, abduce, quantified, Some(held))
}
