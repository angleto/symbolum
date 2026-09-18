package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path, StandardOpenOption}
import java.time.Instant
import scala.jdk.CollectionConverters.*
import scala.util.control.NonFatal
import garden.xeno.symbolum.Expr
import garden.xeno.symbolum.theories.Prose

/**
 * What has already been asked of this system, and what came of it.
 *
 * `Discovery` screens and certifies and then forgets. Its own comment calls the unsettled bucket
 * the output worth a person's attention, and that output lives until the process exits. Run the
 * loop twice and it does the same work twice; run it over a generator and it produces repetition
 * rather than knowledge. This is the part that makes the second run cheaper than the first.
 *
 * == Why this comes before a generator ==
 *
 * A generator without a memory is a machine for re-deriving what it derived yesterday. The order
 * is not a preference: with the ledger, a generator's value is what it adds to it, and without one
 * there is nothing to add to and no way to see whether a strategy is producing anything. So the
 * ledger is first and the generator is next.
 *
 * == What a verdict is for ==
 *
 * Not a record of the past. Each one answers a question about the future, which is whether asking
 * again could give a different answer, and after what.
 *
 * | Verdict | Ask again? |
 * |---|---|
 * | `Proved`, `Disproved` | never; the answer does not depend on the system's strength |
 * | `DecidedNotCertified` | never for the truth of it; **yes** for a certificate, and see below |
 * | `Outside` | when the theory has the constant it lacked |
 * | `TooLarge` | when the numeral arithmetic gets cheaper, or with a higher budget |
 * | `Unfinished` | now, with a higher step limit |
 * | `Open` | this is the lead: a person looks, and nothing here settles it |
 * | `Unasked` | when the model can say something about the question at all |
 *
 * == The eighth verdict, and why it is not `Proved` ==
 *
 * `DecidedNotCertified` is a claim that **holds**, settled by a procedure that produced no theorem:
 * quantifier elimination over the reals, or a set of rules decided contradictory. `docs/adr/0005` is
 * the argument and it is the one this whole repository turns on: a decision is not a proof, and the
 * two must never share a word. Recording such a claim as `Proved` would put a sentence in a file a
 * person greps, saying the kernel had blessed something it never saw.
 *
 * `Open` is equally wrong and in the other direction: it says nobody settled the question, and
 * somebody did. That is the reason a seventh verdict could not be stretched to cover it, and the
 * reason the word is long. Anything shorter reads as a proof.
 *
 * == What a reader that does not know a verdict does ==
 *
 * Drops the line, which means the question reads as never asked and the work is done again. That is
 * the safe direction and it is the one this file wants: an old reader meeting a file a newer writer
 * produced repeats a certification rather than trusting a word it cannot interpret. It is also why
 * adding a verdict is a change to a **format** and not a change to an enum, and why this one was
 * left out of a commit it would have been convenient to slip into.
 *
 * == The file ==
 *
 * One entry per line, four tab-separated fields, and a header naming them, so that the thing is
 * readable with `less` and searchable with `grep` by whoever is wondering what the machine has been
 * doing. No dependency, because this repository has none and a ledger is not the place to acquire
 * the first one.
 *
 * Appending rather than rewriting, so a crash costs the last line rather than the file, and so two
 * runs against one ledger interleave instead of overwriting each other. What that does not give is
 * atomicity across processes: two writers appending at the same instant can interleave a line, and
 * a ledger that mattered that much would want a real store rather than a file.
 *
 * == What it does not do ==
 *
 * It matches statements by their exact printed form. `x + 1 = 1 + x` and `1 + x = x + 1` are two
 * entries for one question, and a run that reorders its candidates gets no benefit from yesterday's
 * work. Keying by a canonical form would fix that and would put the untrusted simplifier in charge
 * of deciding what counts as already answered, where a wrong answer silently hides a question
 * rather than producing a wrong theorem. That is a worse failure than the repetition, so this keeps
 * the dumb key until something checks the canonical one.
 *
 * **What the checked key would cost, measured on 2026-09-10** rather than left as the reason to
 * avoid the unchecked one. A key that carries its own proof is the pair of `Ring` normal forms,
 * since `Ring.normalise` returns the theorem that the term equals its form. On three products of
 * binomials, warm, single runs: normalising both sides took 3.1, 5.4 and 3.5 ms where settling the
 * pair outright took 2.8, 1.7 and 4.8 ms. Read them as one number: **the checked key costs about
 * what the answer costs.**
 *
 * That decides when it would pay rather than whether it is possible. Every question asked would pay
 * one normalisation, and every question re-asked in different words would save one certification,
 * so the key is worth having once re-spellings are more than about half of what a run asks. Nothing
 * measured here says they are, and a generator that produced them would be the thing that made it
 * worth building. Until then the repetition is cheaper than the cure.
 *
 * The lookup itself is not the cost anywhere near this. Warm, mean of a hundred: 0.33 ms against a
 * three-line ledger and 1.1 ms against a thousand-line one, since [[entries]] reads the file whole.
 * It grows with the file and not with the question, and at any size this file has been it is under
 * what it saves. A first call is far slower, about 15 ms, and that is the file machinery loading
 * rather than the ledger.
 */
final class Ledger private (val file: Path, private val now: () => Instant) {

  import Ledger.*

  /** Every entry, oldest first, or nothing at all when the file does not exist yet. */
  def entries: Vector[Entry] =
    if (!Files.exists(file)) Vector.empty
    else
      Files
        .readAllLines(file)
        .asScala
        .toVector
        .filterNot(line => line.isEmpty || line.startsWith(HeaderMark))
        .flatMap(parse)

  /** What the ledger already says about this statement, if anything. */
  def settled(statement: String): Option[Entry] =
    entries.reverse.find(_.statement == statement)

  /**
   * Write down what was found.
   *
   * Returns the entry as recorded, which carries the time, because a caller that wants to report
   * what it did should report what was written rather than what it meant to write.
   */
  def record(statement: String, verdict: Verdict, evidence: String): Entry = {
    val entry = Entry(statement, verdict, evidence, now())

    if (!Files.exists(file)) {
      Option(file.getParent).foreach(Files.createDirectories(_))
      Files.write(file, (Header + "\n").getBytes("UTF-8"))
    }

    Files.write(
      file,
      (render(entry) + "\n").getBytes("UTF-8"),
      StandardOpenOption.APPEND
    )
    entry
  }

  /** The same, from an outcome the loop produced. */
  def record(outcome: Discovery.Outcome): Entry =
    record(statementOf(outcome), verdictOf(outcome), evidenceOf(outcome))

  /**
   * The same, from a reading of a claim the generator proposed.
   *
   * The other way in. [[Discovery.Outcome]] is what the screening loop makes of a *pair* of
   * expressions; a reading is what the whole tactic surface makes of a *proposition*, which is what
   * `Propose` emits. Both end up as one line, because a ledger that kept two shapes of entry would
   * be two ledgers.
   *
   * The statement arrives printed rather than as a term, and the signature is the caller's: the key
   * has to be the same string going in and coming back, and a ledger that printed it with a
   * signature of its own would write entries the caller could never find again.
   */
  def record(statement: String, reading: Novelty.Reading): Entry =
    record(statement, Ledger.verdictOf(reading.standing), Ledger.evidenceOf(reading))

  /**
   * Settle a pair, unless the ledger already knows.
   *
   * This is the whole point of the file: the second run of a candidate costs a lookup instead of a
   * certification, and the entry it returns is the one written the first time, timestamp and all.
   * A caller that wants the work done again despite the ledger has [[Discovery.settle]] and should
   * say so at the call site.
   */
  def settle(
    discovery: Discovery,
    left: Expr,
    right: Expr,
    samples: Vector[Map[String, Double]]
  ): Entry =
    settled(statementFor(left, right)).getOrElse(record(discovery.settle(left, right, samples)))
}

object Ledger {

  /** How an entry answers the only question a ledger is asked. See the table above. */
  enum Verdict:
    case Proved, Disproved, DecidedNotCertified, Outside, TooLarge, Unfinished, Open, Unasked

  /** One question, its answer, what the answer rested on, and when. */
  final case class Entry(statement: String, verdict: Verdict, evidence: String, at: Instant)

  /** A ledger over a file, which need not exist yet. */
  def at(file: Path): Ledger = new Ledger(file, () => Instant.now())

  /** The same with the clock supplied, so that a test is not a race against the wall. */
  def at(file: Path, now: () => Instant): Ledger = new Ledger(file, now)

  /** How a pair of candidates is written down, and therefore how it is looked up again. */
  def statementFor(left: Expr, right: Expr): String = s"$left = $right"

  private val Separator: String = "\t"
  private val HeaderMark: String = "#"
  private val Header: String = s"${HeaderMark}statement${Separator}verdict${Separator}evidence${Separator}at"

  private def statementOf(outcome: Discovery.Outcome): String =
    statementFor(outcome.left, outcome.right)

  private def verdictOf(outcome: Discovery.Outcome): Verdict = outcome match {
    case _: Discovery.Proved => Verdict.Proved

    // Both stages of the screen land on the same verdict, and the evidence line is where they stay
    // apart. What a verdict answers is whether asking again could give a different answer, and for
    // a pair told apart at sixteen digits and one told apart at fifty it could not. Which stage did
    // it is a fact about the candidate rather than about the question, and `evidenceOf` carries it.
    case _: Discovery.Disproved => Verdict.Disproved
    case _: Discovery.Separated => Verdict.Disproved

    case unsettled: Discovery.Unsettled =>
      unsettled.why match {
        case Discovery.Why.OutsideTheFragment => Verdict.Outside
        case Discovery.Why.BeyondTheBudget => Verdict.TooLarge
        case Discovery.Why.RewriterRanOut => Verdict.Unfinished
        case Discovery.Why.NotProvableHere => Verdict.Open
      }
  }

  /**
   * What the answer rested on, which is a different thing for each answer.
   *
   * A disproof rests on its witness and is worth nothing without it; an open question rests on how
   * many points it survived, because agreement at three points is not a lead and agreement at three
   * hundred is. A proof rests on a theorem, which the file cannot hold, so it says so.
   */
  /**
   * Which verdict a novelty standing is, which is where the eighth one is produced.
   *
   * Five of the seven standings map without argument. [[Novelty.Standing.Decided]] is the one that
   * had no verdict until 2026-09-11: it is "holds over the reals, by elimination, with no
   * certificate", and both of the obvious answers are wrong. See the table at the top of this file.
   *
   * `Earned`, `Known` and `Immediate` are one verdict here and three standings there, and that is
   * not a loss. The scale ranks by **how much a claim cost against the minimum**, which is a
   * question about whether a result is news; the ledger answers whether asking again could give a
   * different answer, and for all three of those it cannot.
   */
  def verdictOf(standing: Novelty.Standing): Verdict = standing match {
    case Novelty.Standing.Earned => Verdict.Proved
    case Novelty.Standing.Known => Verdict.Proved
    case Novelty.Standing.Immediate => Verdict.Proved
    case Novelty.Standing.Decided => Verdict.DecidedNotCertified
    case Novelty.Standing.False => Verdict.Disproved
    case Novelty.Standing.Open => Verdict.Open
    case Novelty.Standing.Unreadable => Verdict.Outside
  }

  /**
   * What a reading rested on, in the one line the file holds.
   *
   * The standing is already the verdict, so what is worth the second field is the **size**: a claim
   * certified in 300 inferences and one certified in 30000 are the same verdict and not the same
   * event, and a reader grepping the file for what the machine has been doing wants the difference.
   */
  private def evidenceOf(reading: Novelty.Reading): String =
    s"${reading.standing}: ${Prose.count(reading.inferences, "inference")} over " +
      s"${Prose.count(reading.axioms, "axiom")}"

  private def evidenceOf(outcome: Discovery.Outcome): String = outcome match {
    case _: Discovery.Proved => "certified by the kernel"
    case disproved: Discovery.Disproved =>
      val point = disproved.witness.toVector.sortBy(_._1).map { case (name, value) =>
        s"$name=$value"
      }
      s"differs by ${disproved.difference} at ${point.mkString(", ")}"
    case separated: Discovery.Separated =>
      val point = separated.witness.toVector.sortBy(_._1).map { case (name, value) =>
        s"$name=$value"
      }
      s"agreed to ${separated.agreement} digits at ${point.mkString(", ")}"
    case unsettled: Discovery.Unsettled =>
      s"${Prose.count(unsettled.pointsTried, "point")} tried: ${unsettled.reason.message}"
  }

  private def render(entry: Entry): String =
    Vector(entry.statement, entry.verdict.toString, entry.evidence, entry.at.toString)
      .map(oneLine)
      .mkString(Separator)

  /**
   * A field is one line.
   *
   * An error message could in principle carry a newline, and an entry that spans lines is one the
   * next reader cannot parse. The message is evidence for a person rather than data anybody
   * computes with, so folding it is a fair trade; the statement and the verdict cannot contain
   * either character to begin with.
   */
  private def oneLine(field: String): String =
    field.replace("\t", " ").replace("\n", " ").replace("\r", " ")

  private def parse(line: String): Option[Entry] =
    line.split(Separator, -1) match {
      case Array(statement, verdict, evidence, at) =>
        try Some(Entry(statement, Verdict.valueOf(verdict), evidence, Instant.parse(at)))
        catch { case NonFatal(_) => None }
      case _ => None
    }
}
