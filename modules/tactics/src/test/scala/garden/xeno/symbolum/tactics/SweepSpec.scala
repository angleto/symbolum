package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path}
import java.time.Instant
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The generator and the ledger, composed, which is the arrangement each of them was built for.
 *
 * `Ledger`'s own comment says why it comes before a generator: *"a generator without a memory is a
 * machine for re-deriving what it derived yesterday"*. Both existed and nothing joined them, so the
 * claim was an argument rather than a measurement and the figure it promised — how much a source
 * adds to the file per unit of work — had nobody to compute it.
 *
 * The assertion that carries the file is the second pass. Everything else printed here is a
 * measurement of this repository's own library, which moves when the library moves, and is
 * therefore reported rather than pinned.
 */
class SweepSpec extends AnyFlatSpec with Matchers {

  /** A ledger on a fresh file, with a clock that does not race the wall. */
  private def freshLedger(): (Ledger, Path) = {
    val directory = Files.createTempDirectory("symbolum-sweep")
    val file = directory.resolve("run.tsv")
    var ticks = 0
    val ledger = Ledger.at(
      file,
      () => {
        ticks += 1
        Instant.ofEpochSecond(1000L + ticks)
      }
    )
    (ledger, file)
  }

  private val propose = Propose.standard

  "A second pass over the same ledger" should "settle nothing, which is the whole reason the file exists" in {
    // The property the ledger was built for and that nothing exercised over a generator's output
    // until this file. It is asserted as an identity rather than as a ratio: one claim re-settled
    // is one certification paid for twice, and there is no threshold at which that is acceptable.
    val (ledger, _) = freshLedger()
    val sweep = Sweep(propose, ledger)

    val first = sweep.run()
    first.lines.foreach(info(_))
    first.settled should be > 0

    val second = sweep.run()

    withClue(s"the second pass settled ${second.settled} of ${second.offered}:\n${second.lines.mkString("\n")}\n") {
      second.settled shouldBe 0
      second.remembered + second.tallies.map(_.refused).sum shouldBe second.offered
    }
  }

  it should "have written one entry per proposal it settled, and no more" in {
    // The file and the tally have to agree, or one of the two is describing a different run. The
    // generator can propose the same claim twice from two lemmas, so the comparison is against the
    // distinct statements rather than against the count.
    val (ledger, _) = freshLedger()
    val report = Sweep(propose, ledger).run()

    ledger.entries.map(_.statement).distinct.size shouldBe ledger.entries.size
    ledger.entries.size shouldBe report.settled
  }

  "Each source" should "report what it adds to the file per claim it settles" in {
    // The figure the ledger was supposed to make askable, and the reason `Propose` keeps its two
    // sources apart. It is printed and not asserted: it measures this repository's library and
    // moves when the library does. What IS asserted is that both sources answered, because a
    // report with one source in it would make the comparison vacuous.
    val (ledger, _) = freshLedger()
    val report = Sweep(propose, ledger).run()

    report.lines.foreach(info(_))
    report.tallies.map(_.source).toSet shouldBe Propose.Source.values.toSet
    every(report.tallies.map(_.offered)) should be > 0
  }

  "A claim decided and never certified" should "be written down as neither proved nor open" in {
    // The eighth verdict, and the reason it had to exist before this file could be written. A claim
    // `Quantified` decides holds is settled — so `Open`, which says nobody settled it, is false —
    // and nothing certified it — so `Proved`, which `docs/adr/0005` says a decision is not, is
    // worse than false. Both of the seven verdicts that existed were wrong answers.
    // The order is unbounded above, which `Quantified` decides by elimination and no procedure here
    // certifies: the statement has an existential in it, so there is no theorem to hand back.
    val claim = "!x:real. ?y:real. x < y"

    val reading = Novelty.standard
      .of(claim)
      .fold(error => fail(s"expected a reading, got ${error.message}"), identity)

    reading.standing shouldBe Novelty.Standing.Decided

    val (ledger, _) = freshLedger()
    val entry = ledger.record(claim, reading)

    entry.verdict shouldBe Ledger.Verdict.DecidedNotCertified
    entry.evidence should include("Decided")
  }

  "Every novelty standing" should "have a verdict, since the two vocabularies have to meet" in {
    // The map is total by the compiler, and what this adds is that no two standings that mean
    // different things collapse into one verdict by accident. Three of them do collapse, onto
    // `Proved`, and that is a decision with an argument on `Ledger.verdictOf`: the scale ranks how
    // much a claim cost, the ledger answers whether asking again could change the answer, and for
    // all three of those it cannot.
    val mapped = Novelty.Standing.values.toVector.map(standing => (standing, Ledger.verdictOf(standing)))

    mapped.collect { case (standing, Ledger.Verdict.Proved) => standing }.toSet shouldBe
      Set(Novelty.Standing.Earned, Novelty.Standing.Known, Novelty.Standing.Immediate)

    mapped.map(_._2).distinct.size shouldBe 5
    mapped.toMap.apply(Novelty.Standing.Decided) shouldBe Ledger.Verdict.DecidedNotCertified
  }
}
