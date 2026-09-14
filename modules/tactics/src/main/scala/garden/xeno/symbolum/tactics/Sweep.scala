package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.theories.Signature

/**
 * One pass of the generator against the ledger, and what it added.
 *
 * `Propose` makes candidates and `Novelty` says what each one cost; `Ledger` remembers. Each of the
 * three worked and none of them knew about the others, so running the generator twice did the work
 * twice, and the question the ledger was built to make askable — **is this source worth running
 * again** — had no answer because nobody was writing what a source produced into the file.
 *
 * This is the composition, and it is small on purpose: look up, settle what is not there, write it
 * down, count.
 *
 * == The two things it is for ==
 *
 * **A pass that does not repeat.** The second run of a sweep against the same ledger settles
 * nothing: every proposal is found and the cost is a lookup. That is the property `Ledger`'s own
 * comment says is the reason it comes before a generator, and until this file nothing exercised it
 * over a generator's output.
 *
 * **A figure per source.** `Propose` has two sources, weakening a hypothesis and substituting an
 * operator, and they are not equally worth running. What decides that is how many `Open` entries a
 * source adds per proposal it settles: an `Open` entry is a claim that survived every procedure
 * here and is the only kind a person has to look at, which is `Discovery`'s `NotProvableHere` seen
 * from the other end. Everything else is the machine agreeing with itself.
 *
 * == What it deliberately does not claim ==
 *
 * A high rate of `Open` entries is **not** evidence that a source is discovering anything.
 * `docs/evaluation.md` makes the argument and it is not answered by anything here: a claim nothing
 * certified is a claim nothing certified, and it is a lead exactly as often as a person looking at
 * it finds something. What the figure measures is where a person's attention would go per unit of
 * machine time, which is a question about how to spend an afternoon rather than about mathematics.
 *
 * And a sweep proposes nothing of its own. Everything it puts to the prover came from a lemma the
 * library already holds, so the space is bounded by what is there. `Propose` says so at more
 * length and it is the reason both of these are still the second source of four.
 */
final class Sweep private (val propose: Propose, val ledger: Ledger) {

  import Sweep.*

  private val reals: Signature = propose.reals

  /**
   * Every proposal put to the ledger, settling only what the file does not already answer.
   *
   * The lookup is by the printed statement, which is `Ledger`'s key and its stated limit: a
   * proposal printed differently is a second entry for one question. Nothing here works around
   * that, for the reason that file gives.
   */
  def run(): Report = {
    val tallies = propose.proposals
      .groupBy(_.source)
      .toVector
      .sortBy(_._1.toString)
      .map { case (source, proposals) =>
        val started = System.nanoTime()

        val outcomes = proposals.map { proposal =>
          val statement = reals.show(proposal.claim)

          ledger.settled(statement) match {
            case Some(entry) => (true, Some(entry.verdict))
            case None =>
              propose.novelty.of(proposal.claim).toOption match {
                case Some(reading) => (false, Some(ledger.record(statement, reading).verdict))
                // A claim the novelty scale refused to *read*, which is not the same as one it
                // read and no procedure could take: that second one is a reading, its standing is
                // `Unreadable`, and it lands in the file as `Outside`. This is the reading itself
                // failing, so there is nothing to write down: the ledger answers "could asking
                // again give a different answer", and about a claim that never became a question
                // this pass produced no answer. Counted so that a source producing nothing but
                // these is visible as such.
                case None => (false, None)
              }
          }
        }

        Tally(
          source = source,
          offered = proposals.size,
          remembered = outcomes.count(_._1),
          refused = outcomes.count { case (remembered, verdict) => !remembered && verdict.isEmpty },
          verdicts = outcomes
            .collect { case (false, Some(verdict)) => verdict }
            .groupBy(identity)
            .map { case (verdict, held) => (verdict, held.size) },
          milliseconds = (System.nanoTime() - started) / 1000000L
        )
      }

    Report(tallies)
  }
}

object Sweep {

  /**
   * What one source produced in one pass.
   *
   * `offered` is what the source made, `remembered` is what the file already answered — including a
   * claim this same pass proposed twice, which the generator does — and the verdicts are what was
   * settled now. Those three and `refused` add up to `offered`, and they are kept apart rather than
   * folded into "done": a pass whose proposals were all remembered did no work, and a pass whose
   * proposals were all refused did no work either, and those are opposite news about the source.
   *
   * **`refused` is not `Ledger.Verdict.Outside`.** A claim the surface read and no procedure could
   * take is a reading, and it lands in the file. This is the reading failing before there was a
   * question, and it lands nowhere.
   */
  final case class Tally(
    source: Propose.Source,
    offered: Int,
    remembered: Int,
    refused: Int,
    verdicts: Map[Ledger.Verdict, Int],
    milliseconds: Long
  ) {

    /** How many claims were put to the whole tactic surface, which is the unit of work. */
    def settled: Int = verdicts.values.sum

    /** The entries a person has to look at: survived everything, certified by nothing. */
    def opened: Int = verdicts.getOrElse(Ledger.Verdict.Open, 0)

    /**
     * Leads per claim settled, which is the figure the ledger was supposed to make askable.
     *
     * `None` where nothing was settled, because zero out of zero is not zero: a source whose
     * proposals the file already answered has no rate this pass, and reporting it as the worst
     * possible one would say the opposite of what happened.
     */
    def yieldRate: Option[Double] = if (settled == 0) None else Some(opened.toDouble / settled)
  }

  /** One pass, per source. */
  final case class Report(tallies: Vector[Tally]) {

    /** Every proposal the pass made, across sources. */
    def offered: Int = tallies.map(_.offered).sum

    /** Every claim it put to the surface, which is what the pass cost. */
    def settled: Int = tallies.map(_.settled).sum

    /** Every proposal the file already answered. */
    def remembered: Int = tallies.map(_.remembered).sum

    /** A line per source, for a caller printing the pass. */
    def lines: Vector[String] =
      tallies.map { tally =>
        val rate = tally.yieldRate.fold("no work this pass")(value => f"$value%.2f open per settled")
        val verdicts = tally.verdicts.toVector
          .sortBy(entry => -entry._2)
          .map { case (verdict, howMany) => s"$verdict $howMany" }
          .mkString(", ")

        s"${tally.source}: ${tally.offered} offered, ${tally.remembered} remembered, " +
          s"${tally.settled} settled in ${tally.milliseconds} ms, ${tally.refused} refused" +
          (if (verdicts.isEmpty) "" else s" [$verdicts]") + s"; $rate"
      }
  }

  /** A sweep of a generator against a ledger. */
  def apply(propose: Propose, ledger: Ledger): Sweep = new Sweep(propose, ledger)
}
