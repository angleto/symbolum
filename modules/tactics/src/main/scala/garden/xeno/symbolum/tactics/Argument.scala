package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.{Kernel, Term}
import garden.xeno.symbolum.theories.Linarith

/**
 * A whole argument on one page: what each conclusion cost, what it rests on, and where it came from.
 *
 * `Cost` answers five questions about **one** claim and `Provenance` names the sources behind
 * **one** proof. A document is neither: it is a dozen claims that lean on each other and on one
 * register of measurements, and the questions a reader of a document asks are about the set.
 *
 * == The question that only exists at this level ==
 *
 * Whether a citation is stale. Asked of one claim, the answer is nearly always yes and nearly
 * always wrong: a register that cites eight measurements and a claim that uses two leaves six
 * looking unused, when five of them are used by the next claim. So the three buckets are computed
 * over the argument and not over the line:
 *
 *   - **used** somewhere: it carries a source and a weight, on whichever lines weighed it;
 *   - **idle**: some claim states it as a premise and no certificate weighed it anywhere. The
 *     argument assumes something it does not need, and the register is right;
 *   - **stale**: no claim states it at all. The register is out of date, usually because the
 *     proposition beside it was reworded, and the argument is right.
 *
 * That is [[Provenance.Trail]]'s distinction taken up one level, and taking it up is the whole
 * reason this file exists rather than a loop over `Provenance.trail`.
 *
 * == The other one: which axioms are the domain's ==
 *
 * A theorem's axioms are a set of terms and a reader wants them in two heaps: what this repository
 * asks everybody to believe, and what **this document** asked for on top. The second is the part a
 * reader of the document can argue with, and it is the part a reader of the trusted base cannot
 * see. So an argument is built over the foundation it extends, and every line reports the
 * difference.
 *
 * An argument that adds no axiom of its own reports an empty domain column, which is the outcome to
 * aim for: `docs/proving.md` shows a tiering rule proved over a declared domain at zero axioms,
 * with every assumption on the left of the turnstile where a reader can disagree with it.
 *
 * == What it does not do ==
 *
 * Decide anything about the claims. Each line is `Cost`'s report, unchanged, and `Cost` is careful
 * about the difference between proved, decided and neither. A line that says `Unsettled` says it on
 * the page.
 *
 * Nor does it check that the premises can all hold at once. `h1..hn |- c` is vacuously true when the
 * premises contradict each other, and an argument whose assumptions are inconsistent proves
 * everything: `Refutation.satisfying` is the untrusted answer and it is a separate question asked of
 * the assumptions rather than of the conclusions. Nothing here calls it, and a page that looked
 * complete without it would be the more dangerous artifact.
 */
final class Argument private (
  val cost: Cost,
  val linarith: Linarith,
  val register: Provenance,
  /**
   * The axioms that are not this argument's own.
   *
   * Everything a line believes that is **not** in here was asserted by the development the argument
   * is written over, which is what a reader of the document is entitled to see separately.
   */
  val foundation: Set[Term]
) {

  import Argument.*

  /**
   * The page for a list of claims written in the theory's notation.
   *
   * The text each claim was written as is kept beside the term it parsed to, and the renderer
   * prints it back wherever the two differ. That costs a string this method already held, and
   * `docs/adr/0002` is why it is needed at all: a bound name is not part of a term, so a reader who
   * asked about `budget` is otherwise answered about `x` and cannot check the answer against the
   * claim it translates. [[of]] is the same page for claims nobody wrote as text, and it prints no
   * such line because there is no author's name to lose.
   */
  def read(texts: Vector[String]): Either[TacticError, Reading] =
    texts
      .foldLeft[Either[TacticError, Vector[(Term, Option[String])]]](Right(Vector.empty)) {
        (acc, text) =>
          for {
            claims <- acc
            claim <- TacticError.lift(register.reals.proposition(text))
          } yield claims :+ (claim, Some(text))
      }
      .map(asWritten)

  /**
   * The page for claims already read.
   *
   * Every claim is costed, whether or not it has a certificate: a conclusion outside the linear
   * fragment still has an outcome, a price and a list of axioms, and only its premises go missing.
   * Saying nothing about such a line would hide the half of the argument that the tactics can still
   * answer for.
   */
  def of(claims: Vector[Term]): Reading = asWritten(claims.map(claim => (claim, None)))

  /** [[of]], with the text each claim was written as where a caller wrote one. */
  private def asWritten(claims: Vector[(Term, Option[String])]): Reading = {
    val lines = claims.map { case (claim, asked) =>
      val report = cost.of(claim) match {
        case Right(found) => found
        case Left(refusal) => Cost.Report(claim, Cost.Outcome.Unsettled, refusal = Some(refusal))
      }

      register.trail(linarith, claim) match {
        case Right(trail) => Line(claim, report, trail.premises, None, asked)
        case Left(refusal) => Line(claim, report, Vector.empty, Some(refusal), asked)
      }
    }

    val weighed = lines.flatMap(_.premises).map(propositionOf).toSet
    val stated = claims.flatMap { case (claim, _) => register.stated(strip(claim)) }.toSet
    val unused = register.entries.filterNot(entry => weighed.contains(entry.proposition))

    Reading(
      lines,
      idle = unused.filter(entry => stated.contains(entry.proposition)),
      stale = unused.filterNot(entry => stated.contains(entry.proposition)),
      foundation = foundation
    )
  }

  /**
   * The page as text.
   *
   * Each claim through `Cost.page`, which is the one renderer for what a claim costs and is not
   * copied here, then the premises with their sources, then what the whole document believed and
   * what its register did with itself. The last three sections belong to the argument rather than
   * to any line, and that is the whole difference between this page and `n` copies of `Cost`'s.
   */
  def render(reading: Reading): Either[TacticError, String] = {
    def readAll(label: String, terms: Vector[Term]): Either[TacticError, Vector[String]] =
      terms.foldLeft[Either[TacticError, Vector[String]]](Right(Vector.empty)) { (acc, term) =>
        for {
          done <- acc
          text <- Readback.of(register.reals, term)
        } yield done :+ s"  $label: $text"
      }

    def entries(label: String, listed: Vector[Provenance.Entry]): Either[TacticError, Vector[String]] =
      listed.foldLeft[Either[TacticError, Vector[String]]](Right(Vector.empty)) { (acc, entry) =>
        for {
          done <- acc
          text <- Readback.of(register.reals, entry.proposition)
        } yield done :+ s"  $label: $text (${entry.source})"
      }

    for {
      blocks <- reading.lines.foldLeft[Either[TacticError, Vector[String]]](Right(Vector.empty)) {
        (acc, line) =>
          for {
            done <- acc
            block <- renderLine(line, reading)
          } yield done :+ block
      }
      domain <- readAll("asked of the domain", ordered(reading.domainAxioms))
      believed <- readAll("believed on", ordered(reading.foundational))
      idle <- entries("assumed and never weighed", reading.idle)
      stale <- entries("cited and never assumed", reading.stale)
      note = if (blocks.exists(_.contains("\n  as asked: "))) Vector(NameNote) else Vector.empty
    } yield (Vector(reading.summary) ++ blocks ++ domain ++ believed ++ idle ++ stale ++ note)
      .mkString("\n")
  }

  private def ordered(axioms: Set[Term]): Vector[Term] =
    axioms.toVector.sortBy(register.reals.show)

  private def renderLine(line: Line, reading: Reading): Either[TacticError, String] =
    for {
      costed <- cost.page(line.report, believed = false)
      premises <- line.premises.foldLeft[Either[TacticError, Vector[String]]](Right(Vector.empty)) {
        (acc, premise) =>
          for {
            done <- acc
            text <- Readback.of(register.reals, propositionOf(premise))
          } yield done :+ s"  ${labelOf(premise)}: $text"
      }
      unnamed = line.whyNoPremises.map(refusal => s"  no certificate: ${refusal.message}").toVector
      asked <- asAsked(line)
    } yield (costed ++ premises ++ unnamed ++ asked).mkString("\n")

  /**
   * The claim as its author wrote it, printed only where the page prints it differently.
   *
   * Silent when the two agree, which is the common case and the one that must stay quiet: a note
   * on every line would be noise, and a reader who sees this line is being told something true
   * about the line it sits under. The explanation of WHY they differ is printed once for the page
   * rather than once per line; [[Argument.NameNote]] carries it.
   */
  private def asAsked(line: Line): Either[TacticError, Vector[String]] =
    line.asked match {
      case None => Right(Vector.empty)
      case Some(text) =>
        Readback.of(register.reals, line.claim).map { printed =>
          if (printed == text) Vector.empty else Vector(s"  as asked: $text")
        }
    }

  private def labelOf(premise: Provenance.Premise): String = premise match {
    case Provenance.Premise.Cited(_, source, weight) => s"weighed $weight, from $source"
    case Provenance.Premise.Uncited(_, weight) => s"weighed $weight, ${Provenance.Uncited}"
    case Provenance.Premise.Unnameable(_, weight) => s"weighed $weight, ${Provenance.Unnameable}"
  }

  /** A claim with its leading quantifiers off, which is the shape a register's citations match. */
  private def strip(claim: Term): Term =
    garden.xeno.symbolum.logic.Logic.stripForall(claim).map(_._2).getOrElse(claim)
}

object Argument {

  /**
   * Why a claim can come back under names its author did not write.
   *
   * Printed once per page rather than once per line, and only when a line differs. `docs/adr/0002`
   * is the decision: a bound name is not part of a term, so the printer invents one, and `x, y, z`
   * survive as often as they do only because they are the first three it reaches for.
   */
  val NameNote: String =
    "  (a bound name is not part of a term; the names above are the printer's, see docs/adr/0002)"

  private def propositionOf(premise: Provenance.Premise): Term = premise match {
    case Provenance.Premise.Cited(proposition, _, _) => proposition
    case Provenance.Premise.Uncited(proposition, _) => proposition
    case Provenance.Premise.Unnameable(proposition, _) => proposition
  }

  /**
   * One conclusion, everything known about it.
   *
   * `premises` is empty and `whyNoPremises` is set when the claim has no linear certificate, which
   * is not a failure of the claim: a conclusion proved by the ring normalisation or by the
   * propositional fragment has no weights to report and still has a price and a list of axioms.
   * Two fields rather than an `Option[Vector]`, because "no premises" and "no certificate" are
   * different facts and a reader acts on them differently.
   */
  final case class Line(
    claim: Term,
    report: Cost.Report,
    premises: Vector[Provenance.Premise],
    whyNoPremises: Option[TacticError],
    /**
     * The text this claim was written as, where a caller wrote one.
     *
     * Empty for a claim a generator built, which is most of them: `Propose` and `Sweep` hand over
     * terms assembled out of theorems and there is no author's name in them to lose. Defaulted so
     * that a caller constructing a line by hand is not asked for something it does not have.
     */
    asked: Option[String] = None
  ) {

    /** Whether this conclusion is settled, which is proved or decided and never "not refuted". */
    def settled: Boolean = report.outcome match {
      case Cost.Outcome.Proved | Cost.Outcome.Conditional => true
      case Cost.Outcome.Holds | Cost.Outcome.Fails => true
      case Cost.Outcome.Unsettled => false
    }

    /** Whether a proof of it exists, as against a decision about it. */
    def proved: Boolean = report.outcome match {
      case Cost.Outcome.Proved | Cost.Outcome.Conditional => true
      case _ => false
    }
  }

  /** The whole argument, with the register's verdict on itself. */
  final case class Reading(
    lines: Vector[Line],
    idle: Vector[Provenance.Entry],
    stale: Vector[Provenance.Entry],
    foundation: Set[Term]
  ) {

    /** The axioms this argument asked for beyond the ones it was built over. */
    def domainAxioms: Set[Term] = lines.flatMap(_.report.axioms).toSet.diff(foundation)

    /** The foundational axioms it reached, which is the part a reader cannot argue with. */
    def foundational: Set[Term] = lines.flatMap(_.report.axioms).toSet.intersect(foundation)

    /** What the whole run cost, in the inferences the kernel actually took. */
    def inferences: Int = lines.map(_.report.inferences).sum

    /** The first line of the page. */
    def summary: String =
      s"${lines.length} claims, ${lines.count(_.proved)} proved, " +
        s"${lines.count(line => line.settled && !line.proved)} decided, " +
        s"${lines.count(line => !line.settled)} open; " +
        s"${domainAxioms.size} axioms of the domain, ${foundational.size} foundational; " +
        s"${idle.length} idle and ${stale.length} stale citations"
  }

  /** Over a development, a register, and the axioms that are not this argument's own. */
  def apply(
    cost: Cost,
    linarith: Linarith,
    register: Provenance,
    foundation: Set[Term]
  ): Argument = new Argument(cost, linarith, register, foundation)
}
