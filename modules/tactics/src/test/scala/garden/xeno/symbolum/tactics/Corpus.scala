package garden.xeno.symbolum.tactics

import org.scalatest.Tag

/**
 * The tests that put a whole vendored corpus to the prover, marked so the coverage run can skip them.
 *
 * They are **not** skipped by `sbt test`, which is the point: a corpus that runs only when somebody
 * remembers to ask for it has stopped being a measurement, and the numbers in `docs/evaluation.md`
 * are meant to fail here rather than go quietly stale.
 *
 * What they are skipped by is `sbt coverage test`, and the reason is that the two are asking
 * different questions. Coverage asks which lines the suite exercises; `ReachSpec` exercises the same
 * lines as `RingCorpusSpec` and `LinarithCorpusSpec` and adds almost nothing to that answer, while
 * costing more than the rest of the build put together — measured, on 2026-09-11: the instrumented
 * run was still inside it after seventeen minutes, where the whole suite without it takes about two.
 *
 * The exclusion is in `build.sbt` and is conditional on `coverageEnabled`, so it cannot leak into an
 * ordinary run by accident.
 *
 * == The library is a corpus too, since 2026-11-12 ==
 *
 * `ProposeSpec`'s audit and the first pass `StandardSweep` takes put every proposal the library
 * yields, about a thousand, to the prover, and the tests reading either are marked here for the
 * same reason (card `de662da8`). They were the whole of why CI's coverage job had been cancelled at
 * its ninety-minute limit on every push since 2026-11-06. On the last two, CI runs 43198316508 and
 * 43014126746, the sweep's suite took 38.5 and 56.5 minutes under coverage and the audit's was
 * still running when the job was cancelled, against 16.1 and 22.3 minutes for the 117 and 114 other
 * suites together, each measured between the timestamps of consecutive suite headers.
 * Uninstrumented, on the test job at `8d627e29`, the two cost 862 and 887 seconds and nothing else
 * in those three suites took a second. Those are figures of one day; what is not of one day is the
 * shape: a pass over the library costs as much as the library is large and the prover slow, and
 * both grow.
 *
 * What the mark does not do is take their lines out of coverage, and that is the condition on it
 * rather than a hope. `audit` and `Sweep.run` were reached by nothing else, so a pass over a
 * handful of lemmas, unmarked, sits beside each and reaches the branches the population pass
 * reaches; and the coverage run that decided this was compared with the one before it, module by
 * module.
 */
object Corpus extends Tag("garden.xeno.symbolum.Corpus")
