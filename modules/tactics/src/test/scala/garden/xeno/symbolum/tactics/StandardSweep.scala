package garden.xeno.symbolum.tactics

import java.nio.file.Files
import java.time.Instant

/**
 * One first pass of `Sweep` over `Propose.standard`, on a fresh ledger in a temporary directory,
 * shared by every suite of this module that wants one.
 *
 * A pass puts every proposal of the library to the prover and answers the same over a fixed
 * library, so a suite that ran its own was asking a question already answered in the same JVM.
 * Four did, three in `SweepSpec` and one in `DocumentationSpec`: measured on 2026-10-03, about a
 * minute each in a plain `tools/sbt test` and eight under coverage, both on this laptop and on a CI
 * runner, where the coverage job was cancelled at its sixty-minute limit inside the third of them.
 *
 * What it does not cover: a suite that needs a pass over a different `Propose` (a library with
 * lemmas hidden, a different model) still runs its own, and must, since the answer is different.
 * And the ledger is shared, so a suite writing to it changes what a later one finds there: `entries`
 * is copied out when the pass ends, and that copy is what a suite counting the entries reads.
 */
object StandardSweep {

  /** The ledger, with a clock that does not race the wall. */
  lazy val ledger: Ledger = {
    val file = Files.createTempDirectory("symbolum-sweep").resolve("run.tsv")
    var ticks = 0
    Ledger.at(
      file,
      () => {
        ticks += 1
        Instant.ofEpochSecond(1000L + ticks)
      }
    )
  }

  /**
   * The report of the first pass and the ledger's entries as that pass left them, taken together
   * so that no later write to the ledger can come between the two.
   */
  private lazy val firstPass: (Sweep.Report, Vector[Ledger.Entry]) = {
    val report = Sweep(Propose.standard, ledger).run()
    (report, ledger.entries)
  }

  def report: Sweep.Report = firstPass._1

  def entries: Vector[Ledger.Entry] = firstPass._2
}
