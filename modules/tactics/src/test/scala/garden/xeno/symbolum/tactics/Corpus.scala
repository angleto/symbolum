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
 */
object Corpus extends Tag("garden.xeno.symbolum.Corpus")
