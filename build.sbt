// Module layout and the direction of dependencies.
//
// `core` is the computer algebra system. It answers "what does this expression become", and it
// answers with a value, not with evidence. Under the proof-assistant work it keeps that role and
// becomes an untrusted oracle: a tactic may ask it for a candidate result and must then prove
// that result through the kernel, so a wrong answer from `core` costs a failed tactic and can
// never produce a theorem.
//
// `kernel` is the trusted base: the term representation and the inference rules, and the only
// place a theorem can be constructed. The remaining modules are added as they gain content. The
// constraint on all of them is fixed because it is the reason for the split: the trusted base
// MUST NOT be able to see `core`. Expressed as a build dependency rather than as a convention,
// no tactic code can drift into the trusted base by an import nobody reviewed.
//
//     kernel   -> (nothing)
//     logic    -> kernel
//     theories -> logic
//     tactics  -> theories, core
//     examples -> tactics
//
// Every module in that graph now exists. `mark` is beside it rather than in it: it depends on
// nothing, it is not depended on, and what it does is write `docs/logo.svg` from the character art
// in `docs/logo.md` and assert the three things that document asks of a copy. It is a module rather
// than a file in `examples` for one reason, which is that `examples` depends on `tactics`: a check
// over two files under `docs/` that could only run after the prover compiled would stop running on
// exactly the days the prover is broken.
//
// `examples` depended on `core` alone until 2026-09-13, which made it the algebra half's
// demonstration directory and nothing else: a demonstration of the proof half had nowhere to
// live, and the one that now does could not be compiled there. It depends on `tactics` instead,
// which is above the boundary and therefore cannot weaken it. The constraint the split exists for
// is about what is *below* `tactics`, and that is unchanged: `kernel`, `logic` and `theories`
// still cannot see `core`, and `modules/kernel/src/test` still asserts it.

ThisBuild / version := "7.0.0"

ThisBuild / scalaVersion := "3.3.5"

ThisBuild / organization := "garden.xeno"

lazy val commonSettings = Seq(
  libraryDependencies ++= Seq(
    "org.scalatest" %% "scalatest" % "3.2.18" % Test,
    "org.scalatestplus" %% "scalacheck-1-17" % "3.2.18.0" % Test,
    "org.scalacheck" %% "scalacheck" % "1.17.0" % Test
  ),

  scalacOptions ++= Seq(
    "-deprecation",
    "-feature",
    "-unchecked",
    "-Xfatal-warnings"
  ),

  Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),

  /*
   * The corpus measurements run on every `sbt test` and are skipped when measuring coverage.
   *
   * Not a convenience. The two commands ask different questions: coverage asks which lines the suite
   * exercises, and `ReachSpec` exercises the same lines as the other two corpus suites while costing
   * more than the rest of the build put together. Measured on 2026-09-11: the instrumented run was
   * still inside it after seventeen minutes, where the whole suite without it takes about two.
   *
   * What must NOT happen is the corpus being skipped by an ordinary run, because the figures in
   * `docs/evaluation.md` are meant to fail here rather than go quietly stale. Hence the condition on
   * `coverageEnabled` rather than a tag excluded by default. `garden.xeno.symbolum.tactics.Corpus` carries the
   * same argument at the tests it marks.
   */
  Test / testOptions ++= {
    if (coverageEnabled.value)
      Seq(Tests.Argument(TestFrameworks.ScalaTest, "-l", "garden.xeno.symbolum.Corpus"))
    else Seq.empty
  },

  Test / parallelExecution := false
)

/**
 * The coverage floor, per module, set to the value measured rather than to a target.
 *
 * Measured on 2026-09-05: core 88.30, kernel 82.67, logic 92.05, theories 97.42, tactics 94.06, and
 * again an hour later, with nothing changed in between: core 88.24, kernel 82.82, logic 92.05,
 * theories 97.35, tactics 94.06. That pair is the margin below, measured rather than asserted.
 *
 * **Measured again at the end of 2026-09-11**, by the same full run, and the figures below are what
 * it read: kernel 94.84, checker 90.20, logic 95.59, theories 97.71, core 91.79, tactics 92.65. The
 * floors have NOT been moved to meet them, and that is a decision to put to somebody rather than
 * one to take while passing, because raising a floor is irreversible by the rule at the end of this
 * note.
 *
 * Two things in that row are worth reading rather than skipping. **Kernel has moved twelve points**,
 * from 82.67 to 94.84 against a floor of 81.0, so what the floor catches there is nothing that could
 * plausibly happen. And **tactics has gone down**, 94.06 to 92.65 against a floor of 92.5, which
 * leaves fifteen hundredths of a point: that is the one module where the next change is likelier to
 * fail this gate than to be caught by it, and the reason is that the module has grown faster than
 * its suite. Two readings an hour apart on the same evening were 92.84 and 92.65, which is the
 * property-test spread this note describes below, and it is now wider than the margin.
 *
 * Measured by the full run, `sbt coverage test coverageReport`, which is the command the gates are
 * written for: the tests of an upper module exercise the modules below it, so a lower module's
 * number is higher in the full run than under its own tests alone (core measures about five points
 * less under `core/test` by itself). A floor is therefore a statement about the full run, and a
 * module run on its own under coverage can fall below it without anything being wrong.
 *
 * A point below the measurement rather than at it, and the reason is the property tests: their
 * generators choose different inputs on every run, so which statements execute varies a little
 * between runs and a floor set exactly at the measurement would fail on a different sample rather
 * than on a real regression. Fixing the ScalaCheck seed would remove the variation and also the
 * reason to run the properties more than once, which is the wrong trade for this project.
 *
 * The floor only rises. When a change raises the measurement, raise the number with it.
 *
 * == The run has to be a clean one, and the gate does not say so ==
 *
 * Found on 2026-09-13 by running it twice in the same tree, a commit apart. The second report
 * covered **two files**: the report is built from what the instrumented compiler saw, and an
 * incremental build only recompiles what changed. `theories` came back as 172 statements at
 * 100.00%, against 22663 at 97.56% from the clean run an hour earlier, and the gate **passed**,
 * because 100.00 is above 96.0.
 *
 * That is the failure this project refuses everywhere else, arriving here: an assertion that
 * passes because it is empty rather than because it holds. Nothing in the number says which of the
 * two it is, and the shape of a vacuous pass is a rate that is suspiciously round over a statement
 * count nobody looked at.
 *
 * So a measurement is `sbt clean coverage test coverageReport`, or a worktree that has never been
 * built, and the statement count is read alongside the rate rather than the rate alone. There is no
 * check for this: a gate that could tell a partial report from a whole one would have to know how
 * many statements the module has, which is the thing being measured.
 */
lazy val coverageSettings = Seq(
  coverageFailOnMinimum := true
)

/**
 * Publishable to this machine, and not to anywhere else.
 *
 * `publish / skip := true` is deliberate on the prover modules and stays: a published artifact is a
 * promise, the surface is still moving, and pushing one to a registry is not a decision to take
 * while passing. But sbt delegates `publishLocal / skip` up to `publish / skip`, so that one line
 * was also switching off the local publish, and the consequence was larger than intended:
 * **nothing outside this checkout could depend on the prover at all**, including another checkout
 * on this same machine. The only artifact that shipped was `modules/core`, which is the half the
 * documentation says nothing may believe.
 *
 * Setting the more specific scope wins, which was worth measuring rather than believing: an audit
 * on 2026-09-10 recorded that it does not work because the publish task does not read that key.
 * It does. `kernel/publishLocal` writes the jar, the sources, the docs and the POM to
 * `~/.ivy2/local` with the flag set this way, which is how a development in another repository
 * gets to `libraryDependencies += "garden.xeno" %% "symbolum-theories" % version`.
 */
lazy val localOnlyPublishing = Seq(
  publishLocal / skip := false
)

lazy val publishSettings = Seq(
  publishMavenStyle := true,

  publishTo := Some(
    "GitHub Package Registry" at "https://maven.pkg.github.com/angleto/symbolum"
  ),

  credentials += Credentials(
    "GitHub Package Registry",
    "maven.pkg.github.com",
    "angleto",
    sys.env.getOrElse("GITHUB_TOKEN", "")
  ),

  licenses := Seq("GPL-3.0-or-later" -> url("https://www.gnu.org/licenses/gpl-3.0.html")),
  homepage := Some(url("https://symbolum.xeno.garden")),
  scmInfo := Some(
    ScmInfo(
      url("https://github.com/angleto/symbolum"),
      "scm:git:git@github.com:angleto/symbolum.git"
    )
  ),
  developers := List(
    Developer(
      id = "angleto",
      name = "angleto",
      email = "",
      url = url("https://github.com/angleto")
    )
  ),
  pomIncludeRepository := { _ => false }
)

lazy val root = (project in file("."))
  .aggregate(core, kernel, checker, logic, theories, tactics, examples, mark)
  .settings(
    name := "symbolum-root",
    publish / skip := true
  )

// The one published module, and until 2026-09-14 the only one of the eight whose artifact was not
// `<project>-<module>`. It was the bare project name, under a comment saying that was "the
// coordinates the library already has": nothing had ever been published, `gh api
// user/packages?package_type=maven` answers `[]`, so there were no such coordinates and nobody
// depending on them. What the bare name did instead was hand the whole project's name to the half
// that is trusted by nothing, while `symbolum-kernel` meant the kernel of the whole. The bare
// name is now unused, and is where an aggregate would go if one is ever published.
lazy val core = (project in file("modules/core"))
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-core",
    /*
     * Breeze, and only here.
     *
     * Two numeric capabilities were named as blocking work that wants to move into this repository:
     * a discrete Fourier transform at N = 2^22, and the dominant eigenvalue of a non-negative
     * matrix. Both are dense numerical linear algebra and that is not something to write here: a
     * hand-rolled eigensolver is a decade of edge cases, and a hand-rolled transform at four
     * million points is a cache-blocking exercise. `garden.xeno.symbolum.Spectrum` and `garden.xeno.symbolum.Perron`
     * are the two files that use it and they are thin on purpose.
     *
     * **The artifact is `breeze`, not `breeze-natives` and not `breeze-viz`**, and that is the
     * choice that keeps the consequence smallest. `breeze-natives` adds the netlib-java native
     * binary bundles, tens of megabytes of platform-specific payload, to buy a faster BLAS that no
     * measurement here asks for. `breeze` alone resolves to `dev.ludovic.netlib`, which uses a
     * native BLAS when the machine already has one and otherwise runs a pure-JVM translation, so
     * **nothing here requires a native library to be installed**. `breeze-viz` is plotting and has
     * no consumer.
     *
     * **This module is published** as `garden.xeno:symbolum-core`, so the dependency is what a
     * consumer downloads, and that cost is the reason it is declared in exactly one module.
     * `docs/numerics.md` carries the measured closure rather than an estimate of it.
     *
     * **No module on the proof side may gain this**, which is what `NumericIsolationSpec` asserts:
     * no library produces `|- det (A * B) = det A * det B`, so a number out of Breeze is evidence
     * and never a theorem. `kernel`, `logic` and `theories` cannot reach this module at all by the
     * graph above. `tactics` depends on `core` and therefore does have Breeze on its classpath
     * transitively, which the build cannot prevent while `tactics` is the module that sees both
     * halves; a source scan is what keeps it out of the code there.
     *
     * Pinned at 2.1.0, which is the last release and the only line cross-published for Scala 3. It
     * is compiled against 3.1.3 and read by 3.3.5 here, which is the direction TASTy compatibility
     * runs in. There is nothing to float to.
     */
    libraryDependencies += "org.scalanlp" %% "breeze" % "2.1.0",
    // Measured 88.21% in the full run on 2026-09-04 (78.09% on 2026-09-03; 83.04% under its own
    // tests alone, see the note above), and 88.30% on 2026-09-05 with nothing in this module
    // changed, and 88.24% an hour after that. The floor is just under a point below the lower of
    // the two, which is the sampling variation the note describes.
    coverageMinimumStmtTotal := 87.3
  )

// The trusted base. It depends on nothing, which is the enforcement mechanism: a theorem cannot
// be built by code that this module cannot see, and this module can see no other module.
// Not published yet: the surface is still moving, and a published artifact is a promise.
lazy val kernel = (project in file("modules/kernel"))
  .settings(localOnlyPublishing)
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-kernel",
    publish / skip := true,
    // Measured 79.64%. The uncovered part is mostly the printer and the text of the refusals,
    // which is worth knowing: it means the rules themselves are exercised and their messages are
    // not.
    // Raised to 82.09% measured on 2026-09-04, with the boundary and open-term tests.
    // 82.67% on 2026-09-05, which is the top of the spread this module has already shown across
    // three runs with no code change (81.94, 82.09, 82.67). The floor stays: a rise inside the
    // known variation is not a rise, and setting the number from the best of three samples is how
    // a gate starts failing on the sample rather than on the code. The rerun an hour later read
    // 82.82%, a fourth value, which is the argument rather than an exception to it.
    coverageMinimumStmtTotal := 81.0
  )

// The connectives and the rules derived from the kernel's ten. Untrusted: everything here is a
// function that puts primitive rules together, so a mistake costs a failed derivation.
lazy val logic = (project in file("modules/logic"))
  .settings(localOnlyPublishing)
  .dependsOn(kernel)
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-logic",
    publish / skip := true,
    // Measured 89.96%, raised with it: the notation and the reader that walks it are exercised
    // by the round-trip property.
    // Raised to 92.00% measured on 2026-09-04, with the schema rules and the new connectives, and
    // 91.83% later that day when the rewriter gained its limit diagnostic. The floor stays: it only
    // rises, and this went down. 92.05% on 2026-09-05, which is back where it was and not above it.
    coverageMinimumStmtTotal := 91.0
  )

// The mathematics: the theory of the reals and, later, the numerals. This is where the trusted
// base grows, so its axiom list is asserted by a test rather than described.
lazy val theories = (project in file("modules/theories"))
  .settings(localOnlyPublishing)
  .dependsOn(logic)
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-theories",
    publish / skip := true,
    // Measured 96.77% on 2026-09-03 and 96.28% on 2026-09-04; the floor stayed a point below.
    // 97.42% on 2026-09-05, and this one is a real rise rather than a sample: the order facts, the
    // certificate search and the exact satisfiability search all arrived with their own suites, and
    // the module grew by about a thousand lines without the uncovered part growing with it. Raised
    // to a point and a half below the measurement, which is also more than a point below the lowest
    // reading this module has ever given. The rerun an hour later read 97.35%, so the margin is
    // doing its job on the day it was set.
    coverageMinimumStmtTotal := 96.0
  )

// Where the two halves meet: the computer algebra system proposes and the kernel checks. The only
// module that depends on both, and the reason the boundary was drawn where it was.
// A second reader of a proof, and the one module whose value is that it duplicates another.
//
// It depends on the kernel for the data a theorem carries and reaches for none of its rules: a test
// scans the sources to say so. Everything it needs in order to check an inference, the typing, the
// closedness, the substitution and the beta step, it implements again over a term representation of
// its own, because a checker that called the kernel's would agree with the kernel about exactly the
// things a second implementation exists to disagree about.
lazy val checker = (project in file("modules/checker"))
  .settings(localOnlyPublishing)
  // The theories only at test scope, and the direction is the point: the checker is a consumer of
  // the kernel's data and knows nothing about the mathematics, while its tests need real proofs to
  // check and the only place real proofs come from is a real development.
  .dependsOn(kernel, theories % "test->compile")
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-checker",
    publish / skip := true,
    // Measured 90.60% on the first run, 2026-09-10. The floor is set below it and only rises.
    coverageMinimumStmtTotal := 88.0
  )

lazy val tactics = (project in file("modules/tactics"))
  .settings(localOnlyPublishing)
  // The checker's TESTS on this module's test classpath, which is a narrower edge than it looks and
  // is there for one reason: `garden.xeno.symbolum.tactics.Evaluation` regenerates the figures of
  // `docs/evaluation.md`, and two of its three tables are the second reader's own counts over the
  // proofs `ReplaySpec` replays. A document is regenerated by ONE named command, so the alternatives
  // were a second command writing into the middle of the same file, or a second copy of the list of
  // proofs — which is the defect that document's own card is about. The main scopes are untouched:
  // nothing published from here can see the checker, and the checker still depends on the kernel
  // alone.
  .dependsOn(theories, core, checker % "test->test")
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-tactics",
    publish / skip := true,
    // Measured 94.07% on 2026-09-04 with the ledger, having climbed through 91.85, 92.44 and 92.76
    // that same day as the evaluator, the model search and the four cases of `Unsettled` arrived
    // (86.89% under its own tests alone on 2026-09-03). The evaluator arrived below the floor at
    // 90.06%, and what closed the gap was two tests worth having rather than a lower number: the
    // polarity rule on a compound premise, and an assignment of the wrong type, which is the only
    // thing between a mis-keyed value and an answer.
    // The margin is about a point and a half on purpose. Measurements move without the code
    // moving, because the property tests draw their samples fresh: `kernel` read 82.09%, 81.94%
    // and 82.67% across three runs while nothing in it changed.
    // It was 0.0 for one commit, which is a floor that cannot fail; an audit pointed out that
    // this is the module where the oracle's answers head for the kernel.
    // 94.06% on 2026-09-05, against 94.08% the day before: unchanged, so the floor is too.
    coverageMinimumStmtTotal := 92.5
  )

// Runnable demonstrations, of both halves. Separate from `core` so they stay out of the published
// artifact: while they lived in `core`'s default package they were part of what a consumer
// downloaded. On `tactics` rather than on `core`, which reaches `core` transitively and reaches
// the proof side too; see the graph at the top of this file for why that costs the trust argument
// nothing.
lazy val examples = (project in file("modules/examples"))
  .dependsOn(tactics)
  .settings(commonSettings)
  .settings(
    name := "symbolum-examples",
    publish / skip := true,
    // No floor, stated rather than set to zero: these are demonstrations that print expressions,
    // every function they call is covered by `core`'s suite, and a threshold here would be
    // satisfied by asserting that printing does not throw.
    coverageFailOnMinimum := false
  )

// The mark, and the checks `docs/logo.md` describes. Depends on nothing, is depended on by nothing,
// and is not published: it is a documentation tool that happens to be written in the language the
// repository already builds.
lazy val mark = (project in file("modules/mark"))
  .settings(commonSettings)
  .settings(
    name := "symbolum-mark",
    publish / skip := true,
    // No floor, stated rather than set to zero, for the reason `examples` gives and one of its own:
    // everything here is exercised by `MarkSpec` against the committed files, so the number this
    // would gate is a property of two documents rather than of the code.
    coverageFailOnMinimum := false
  )
