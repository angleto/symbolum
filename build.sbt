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
// `scan` is beside that graph too and is reached only at test scope: it holds the one decision
// about what in a source of this repository is a comment, for the gates in `theories`, `tactics`
// and `dist` that read the repository's own text before checking it. It depends on nothing, so it
// cannot weaken the boundary, and it is a module for the same reason `mark` is one.
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

// The version comes from the git tag, through sbt-dynver: exactly the tag on a clean tree at a
// tagged commit, and the tag with the distance, the hash and a dirty marker anywhere else.
//
// What it removes is one fact written twice. This line held `7.0.0` while `git describe` answered
// `7.0.0-16-g27dd486`, and the publishing workflow reconciled them by rewriting this line with a
// value typed into a form, so what a published artifact called itself was whatever the person who
// dispatched the run had typed. The release convention already reads `git describe`; the build now
// reads the same answer.
//
// Tags here are `7.0.1` and never `v7.0.1`, and dynver expects the prefix, so it is switched off.
ThisBuild / dynverVTagPrefix := false

// And the dirty marker's timestamp is pinned rather than read off the clock, which is a measurement
// rather than a preference: dynver writes the current minute into the version of any tree that is
// not exactly a tag, so a second `sbt dist/Universal/packageZipTarball` a minute after the first
// regenerated every jar, every pom and the API documentation of every module, because every
// artifact had a new name. What the marker is for is saying that nobody else can reproduce this
// build, and a fixed date says that as well as a moving one.
ThisBuild / dynverCurrentDate := new java.util.Date(0)

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
 * **And raising it to the measurement makes the NEXT change in that module tight, which is a
 * sequencing hazard rather than a mistake in either half.** Measured on 2026-09-16, in one
 * session and by one author, which is why it is written here rather than left to be met: the
 * `theories` floor went 96.0 -> 97.4 in the morning, taking the margin from 734 statements to
 * 39.7; two commits later a 404-statement development landed in that same module carrying 10
 * uncovered statements, and the margin fell to 30.4. Nothing broke. A quarter of the headroom
 * went in one commit, and neither half was wrong: the floor was raised to what the rule sets, and
 * the development was covered to 97.5% of itself.
 *
 * The order is what did it, and the next person will work in the same order because that is the
 * order the work arrives in: you measure, you raise, and then you land the thing you were
 * measuring for. What follows is not "raise it less" -- a ratchet set below the rule is the defect
 * this note spent four sections arguing against. It is that a floor raised in the same session as
 * a landing into that module should be **re-measured after the landing**, and that a module about
 * to receive a large file is one to raise last rather than first.
 *
 * == Measured again on 2026-09-16, and only three of the seven moved ==
 *
 * At `f9e0672`, by `clean coverage test coverageReport` in a worktree that had never been built,
 * 2129 tests green, with `HEAD` and the dirty count recorded before and after the run and unchanged
 * across it. The statement count is beside every rate because the rate alone is what lets a partial
 * report pass, which the section below this one is about:
 *
 * {{{
 *   module     statements   rate     floor      moved
 *   kernel           1126   95.65    81.0 -> 93.4   yes
 *   checker           831   91.82    88.0 -> 88.8   yes
 *   core             2901   92.18    87.3 -> 91.3   yes
 *   sat               428   92.99    92.0           no
 *   logic            4589   95.10    91.0           no
 *   theories        43676   97.42    96.0           no
 *   tactics          4951   92.83    92.5           no
 *   mark              434   84.56    none           no
 * }}}
 *
 * **The margin is 25 statements, not a point, and the arithmetic is why.** A point is 4.3 statements
 * on `sat` and 436.8 on `theories`, so one sentence repeated in seven comments is two different
 * gates: the tightest would land on the module with no property draws at all and the loosest on the
 * one carrying the only unbounded generator in the build. The mechanism the margin exists for is
 * property-test variation, which is an absolute effect rather than one proportional to module size.
 * 25 is about two and a half times the largest spread this note has ever recorded, which is the
 * 0.88 points across four readings of `kernel` — ten statements.
 *
 * **Four of the seven were left alone because three other sessions had unlanded work in them**, and
 * that is a decision rather than caution. A floor that only rises is a ratchet, and a ratchet set
 * from a tree somebody is mid-change in is not conservative: it is a claim about a commit nobody has
 * made. The asymmetry decides it. A floor set too low costs one more pass later and nothing else; a
 * floor set from a statement count that moves under it turns somebody's green branch red for a
 * reason that is not in their diff, and they spend their first hour looking for a defect they did
 * not write. `theories` and `logic` were about to take a 2100-line development; `sat` and `mark` a
 * rewrite of seven constructs; `tactics` a new spec of about 380 lines.
 *
 * So the honest form of that measurement was **three now and four when the tree settles**, and the
 * four were not a gap in the work but the part of it that a single morning could not establish.
 *
 * == And "four when the tree settles" was wrong: it was one, 2026-09-16 ==
 *
 * Measured at `fb3f45a` by a second full clean run, 2163 tests green, 79 minutes. The four left
 * standing are not four pieces of work waiting on a quiet tree. Two of them **can never rise**,
 * because the floor each already carries is tighter than the 25-statement rule above would set:
 *
 * {{{
 *   module     statements   rate     floor    the rule would set   outcome
 *   sat               437   92.68    92.0     86.96                cannot rise, 3 stmts of margin
 *   tactics          4951   92.83    92.5     92.33                cannot rise, 16 stmts of margin
 *   logic            4635   95.02    91.0     94.48                91.0 -> 94.4
 *   theories        47506   97.47    96.0     97.42                not raised, see below
 * }}}
 *
 * So one floor moved. `theories` did not, and the reason is the tip check rather than the tree
 * being busy: `git diff --numstat fb3f45a..7.0 -- modules/theories` is **not** empty, and what it
 * holds is 36 added lines under `src/main`, so the statement count itself moved and the rate
 * measured here is for a different population than the floor would name. The same check over
 * `modules/logic` is empty, which is the whole difference between the two. That floor wants one run
 * on a rebased tree and nothing else.
 *
 * Two things this says that the earlier note could not. The ratchet has produced **two gates the
 * rule above would never have set**, and the tighter of the two got tighter still across the two
 * runs. Both were put to a person on 2026-09-16 and both **stay**: loosening either means lowering
 * a floor against the rule at the end of this note, and that trade was declined rather than
 * overlooked. The record is beside each of the two numbers as well as here, because a decision
 * written only in a summary is one a reader of the setting never meets. And the red gate that started all of this is gone: `tactics` failed this file at 89.92 and
 * 90.13, and passes at 92.83.
 *
 * One caution that belongs beside a raised floor rather than in the partial-report section below,
 * because raising a floor makes it worse rather than better. A partial report passes any floor by
 * being nearly empty, and the gate behaves identically whether the number is 96.0 or 97.4. What
 * changes is the reader: a high rate that passes is more convincing than a low one that passes, so
 * the higher these numbers go the more a vacuous pass looks like a result. The count of compiled
 * sources against `find` is the check that separates them, it costs one line, and the run above was
 * verified that way: ten modules, each compiling exactly the number of `.scala` files on disk.
 *
 * **And the three that moved are still measured, five commits later.** `f9e0672..aaad597` is five
 * commits by three sessions, and `git diff --numstat f9e0672..aaad597 -- modules/kernel
 * modules/checker modules/core` is **empty**: not one line of the three modules whose floors rose
 * changed in them. So these numbers are of `f9e0672` and are equally numbers about the tip, which
 * is the check worth running before raising a floor off a hash that is no longer the tip rather
 * than assuming the reading has gone stale because the branch moved.
 *
 * Two things in the table that nobody had written down before. **`sat` has four statements of
 * margin**, 92.99 against 92.0, which makes it the tightest gate in the build and the one most
 * likely to fail on a change that is not a regression. And **`mark` is the lowest-covered module in
 * the repository at 84.56%**, which its own note anticipates and argues for: what a floor there
 * would gate is a property of two documents rather than of the code.
 *
 * == The rebased run the section above asked for, 2026-09-16 ==
 *
 * At `748f1f5`, `clean coverage test coverageReport` in a worktree created at the tip and never
 * built, **2225 tests green**, exit 0, the measured tree clean before and after. Twelve minutes on
 * a machine carrying no other sbt, which is worth writing beside the 79 of the previous run
 * because the difference is the neighbours and not the build:
 *
 * {{{
 *   module     statements   rate     floor         margin    the rule sets   outcome
 *   kernel           1122   95.72    93.4            26.0    93.4            stays
 *   checker           831   91.82    88.8            25.1    88.8            stays
 *   core             2901   92.18    91.3            25.5    91.3            stays
 *   sat               437   92.68    92.0             3.0    86.9            stays, tightest
 *   logic            4644   95.24    94.4 -> 94.7    39.0    94.7            yes
 *   theories        49594   97.48    96.0 -> 97.4   734.0    97.4            yes
 *   tactics          4952   93.05    92.5            27.2    92.5            stays
 *   mark              432   84.03    none               -    -               no gate
 *   examples          240   11.67    none               -    -               no gate
 *   dist                8   62.50    none               -    -               no gate
 * }}}
 *
 * **`theories` is the one this run existed for**, and the section above named the condition it was
 * waiting on rather than leaving it to be rediscovered. The population check passes this time:
 * `git diff --numstat 748f1f5..7.0 -- modules/theories modules/logic` is empty, so the rate and
 * the floor name the same population. Nothing under any module's `src/main` moved across those
 * commits at all; what did move is two documents and one test source.
 *
 * **The gap the ratchet had left at `theories` was 734 statements**, which is the number worth
 * carrying out of this run. The rule fixes the margin at 25, so that gate was twenty-nine times
 * looser than intended, on the module that carries four fifths of the statements in the build. The
 * three floors raised in the morning of 2026-09-16 were between 0.8 and 12 points low; this one was
 * low by 1.48 points and by far the most statements, because a point is 496 statements here. **A
 * floor's looseness is not readable from the points between it and the measurement**, which is the
 * same arithmetic the 25-statement rule was introduced for, seen from the side of a floor that was
 * never revisited rather than from the side of one being set.
 *
 * And the two sentences in this note that are now spent rather than true: "four when the tree
 * settles" resolved to one on 2026-09-16 and then to two here, and `theories` did not need a quiet
 * tree, it needed a rebased one. Both are left above as they were written, because what they got
 * wrong is the part worth reading.
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
 *
 * == And a runner checkout has never been built, which is where these floors are enforced now ==
 *
 * The section above is a discipline on one laptop, and on 2026-09-16 it became a property of the
 * machine instead: `.github/workflows/ci.yml` runs the same command on a runner, where the checkout
 * is fresh by construction and the memory is not the 85 to 207 MB this note's gate passed on. The
 * first run was 24 minutes, exit 0, every floor held. Read off the uploaded `scoverage.xml` rather
 * than off the console, and that is not fastidiousness: the console prints a rate with no statement
 * count and no module name, and the projects report in parallel, so reading the rates in the order
 * they appear against the order the modules were instrumented in sent **five of the eleven to the
 * wrong module** and left `kernel` with none at all, while `dist` received two. Every row of it
 * looked like a reading.
 *
 * {{{
 *   module     statements   rate     floor    margin (statements)
 *   kernel           1122   95.72    93.4      26.0
 *   checker           831   91.82    88.8      25.1
 *   core             2913   92.24    91.3      27.4
 *   sat               437   92.68    92.0       3.0
 *   scan              185  100.00    99.0       1.9
 *   logic            4644   95.63    94.7      43.2
 *   theories        50792   97.45    97.4      25.4
 *   tactics          5143   93.12    92.5      31.9
 *   mark              432   84.03    none         -
 *   examples          240   11.67    none         -
 *   dist                8   62.50    none         -
 * }}}
 *
 * **`scan` is the tightest gate in the build and `sat` is no longer it.** 185 statements at 99.0
 * leaves 1.9, which is one statement: lose one and it still passes at 99.46, lose two and the line
 * goes red. That is tighter than the 25-statement rule would ever set and it was never measured
 * against it, the floor having been read off a run of that module alone.
 *
 * **What this says about the platform is narrower than "the figures hold", and the narrower reading
 * is the one worth having.** Five modules had no line changed under `src/main` *or* `src/test`
 * between `748f1f5` and this run — kernel, checker, sat, mark, examples — so for those the
 * population is provably the same and the comparison is clean. All five read the **same statement
 * count and the same rate to the hundredth** as they did on the laptop, which runs macOS on Apple
 * silicon under Temurin 23 against the runner's Linux, x86 and Temurin 17. Not one of the three
 * differences moved a figure, and the property-test spread this note sets the margin for did not
 * appear on them either.
 *
 * `logic` is the case that looks like a platform difference and is not, which is why it is written
 * out: same 4644 statements, 95.24 there against 95.63 here, an 18-statement gap. Its `src/main` did
 * not move, but `RewriteSpec` gained 18 lines in the same interval. The tests explain it and the
 * platform is not needed to, so the platform is not established as a cause by this run.
 *
 * **And the check that separates a whole report from a partial one has exactly one false positive,
 * measured here rather than guessed.** Counting the distinct sources in each `scoverage.xml` against
 * `find` agrees on ten of the eleven modules; `core` reads 32 against 33 on disk, and the file that
 * is absent is `NumericConstants.scala`, an object of `val` literals that carries no instrumented
 * statement at all. So the check is "every source that holds a statement", not "every source", and
 * anybody turning it into a gate writes that difference down or it goes red on the first constants
 * file that lands.
 */
lazy val coverageSettings = Seq(
  coverageFailOnMinimum := true
)

/**
 * What ships, and as what.
 *
 * Two kinds of artifact, because a library and an environment are not reached the same way. The
 * six library modules take these settings and go to the registry under their own coordinates, so a
 * development elsewhere writes `libraryDependencies += "garden.xeno" %% "symbolum-theories" % ...`
 * and has the prover; `symbolum` is the aggregate for a consumer who wants all six at one
 * coordinate. What a person runs is none of those. `dist` builds a tarball carrying the jars, the
 * runtime classpath and a launcher per entry point, and that is the second kind: a maven
 * coordinate is consumed by a build tool, never executed by somebody who wants to ask the prover a
 * question.
 *
 * Until 2026-09-15 only `core` had these settings and the five prover modules carried
 * `publish / skip := true`, on the argument that a published artifact is a promise and that the
 * prover's surface is still moving. The argument is sound; what it justified was not. The promise
 * an artifact makes is the one its version number makes, and the convention here already numbers a
 * moving surface, a new line for every minor. What `skip` produced instead was a README telling a
 * reader to depend on `garden.xeno %% symbolum-core % 7.0.0` while
 * `gh api user/packages?package_type=maven` answered `[]`, which it still did on 2026-09-15:
 * nothing had ever been published anywhere, so the one module allowed to ship had not shipped
 * either, and the documented installation could not work for anybody.
 *
 * `examples` and `mark` stay unpublished, which is a different decision rather than the old one
 * left standing. Neither is a library. `examples` exists to be read and run, and `mark` regenerates
 * two files under `docs/`, so a consumer who called it would have it write into whatever directory
 * they were standing in. Both reach a person through the distribution instead, which is where a
 * runnable thing belongs.
 */
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
  // `sat` has to be named here or its suite does not run. It landed on 2026-09-15 without this line
  // and `sbt test` passed for an hour over a module whose sixteen tests nobody executed, which is
  // the failure "a suite that is configured but not executed does not exist" names exactly.
  // `DocumentationSpec` asserts the list against the directories now, so the next module is a
  // decision rather than an omission.
  .aggregate(core, kernel, checker, logic, theories, tactics, examples, mark, sat, scan, symbolum, dist)
  .settings(
    name := "symbolum-root",
    publish / skip := true
  )

// Published, and until 2026-09-15 the only module that was. Until 2026-09-14 it was also the only
// one of the eight whose artifact was not
// `<project>-<module>`. It was the bare project name, under a comment saying that was "the
// coordinates the library already has": nothing had ever been published, `gh api
// user/packages?package_type=maven` answers `[]`, so there were no such coordinates and nobody
// depending on them. What the bare name did instead was hand the whole project's name to the half
// that is trusted by nothing, while `symbolum-kernel` meant the kernel of the whole. The bare
// bare name is the aggregate at the end of this file.
lazy val core = (project in file("modules/core"))
  .settings(commonSettings)
  .settings(publishSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-core",
    /*
     * The two numeric libraries, and only here.
     *
     * Two numeric capabilities were named as blocking work that wants to move into this repository:
     * a discrete Fourier transform at N = 2^22, and the dominant eigenvalue of a non-negative
     * matrix. Both are dense numerical work and that is not something to write here: a hand-rolled
     * eigensolver is a decade of edge cases, and a hand-rolled transform at four million points is
     * a cache-blocking exercise. `garden.xeno.symbolum.Spectrum` and `garden.xeno.symbolum.Perron`
     * are the two files that use them and they are thin on purpose.
     *
     * **It was `org.scalanlp:breeze:2.1.0` for both until 2026-09-16, and what removed it is
     * weight.** Measured off `core/fullClasspath` with the same command before and after: **20 jars
     * and 30.96 MB** became **5 jars and 10.12 MB**, so what a consumer of this module downloads is
     * 20.84 MB lighter. Both libraries underneath Breeze were already on that classpath as its own
     * dependencies, and this module calls two functions: `breeze.signal.fourierTr` was
     * `org.jtransforms.fft.DoubleFFT_1D` and `breeze.linalg.eig` was LAPACK's `dgeev` through
     * `dev.ludovic.netlib`.
     *
     * **What is left is not what the card that asked for this predicted, and the difference is one
     * jar.** It counted `scala-library` 2.13 at 5.65 MB among what Breeze drags in because it is
     * cross-built. It is still here with Breeze gone: `scala3-library_3` depends on it, so it is
     * Scala 3's own tail rather than Breeze's, and it is 56% of what remains. Nothing in this
     * module can remove it.
     *
     * **What the swap had to be measured against was the numbers, not the compilation.** The risk
     * of moving off a numeric library is a different answer rather than a build error, so the
     * existing corpus is the judge and it was run against both. The transform is
     * **bit-identical** at fourteen lengths from 1 to 4096, power-of-two and not, because
     * `fourierTr` called the routine this now calls; it is also 897 ms against 2017 ms at
     * `n = 2^22`. The eigenvalue is a different implementation of the same algorithm and agrees to
     * `2.3e-13` at worst over `PerronSpec`'s matrices and over 200 random ones, with no refusal.
     *
     * **`commons-math3` cannot do the transform**, which is the measurement that decided the shape
     * of this rather than a preference: `FastFourierTransformer` refuses any length that is not a
     * power of two, naming it, and `SpectrumSpec` pins `n = 15` because numpy's rule at an odd
     * length is what `Spectrum.ofReal` promises. One library for both was the obvious answer and it
     * is not available.
     *
     * **This module is published** as `garden.xeno:symbolum-core`, so these dependencies are what a
     * consumer downloads, and that cost is the reason they are declared in exactly one module.
     * `docs/numerics.md` carries the measured closure rather than an estimate of it.
     *
     * **No module on the proof side may gain these**, which is what `NumericIsolationSpec` asserts:
     * no library produces `|- det (A * B) = det A * det B`, so a number out of either is evidence
     * and never a theorem. `kernel`, `logic` and `theories` cannot reach this module at all by the
     * graph above. `tactics` depends on `core` and therefore does have both on its classpath
     * transitively, which the build cannot prevent while `tactics` is the module that sees both
     * halves; a source scan is what keeps them out of the code there.
     *
     * Pinned at the versions the measurements above were made at. JTransforms 3.1 is the last
     * release, from 2016, and brings `pl.edu.icm:JLargeArrays` with it; commons-math3 3.5 is what
     * breeze resolved and 3.6.1 is the end of that line, floated to only when something measures a
     * reason. Neither library has a Scala version, so both are `%` and neither drags a second
     * standard library in.
     */
    libraryDependencies += "com.github.wendykierp" % "JTransforms" % "3.1",
    libraryDependencies += "org.apache.commons" % "commons-math3" % "3.5",
    // Measured 88.21% in the full run on 2026-09-04 (78.09% on 2026-09-03; 83.04% under its own
    // tests alone, see the note above), and 88.30% on 2026-09-05 with nothing in this module
    // changed, and 88.24% an hour after that.
    //
    // **92.18% over 2901 statements on 2026-09-16, at `f9e0672`**, and the floor rises to 91.3,
    // which is 25 statements under the measurement. See the note above this project list for why
    // the margin is counted in statements rather than in points, and why only three of the seven
    // floors moved that day.
    coverageMinimumStmtTotal := 91.3
  )

// The trusted base. It depends on nothing, which is the enforcement mechanism: a theorem cannot
// be built by code that this module cannot see, and this module can see no other module.
// Not published yet: the surface is still moving, and a published artifact is a promise.
lazy val kernel = (project in file("modules/kernel"))
  .settings(publishSettings)
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-kernel",
    // Measured 79.64%. The uncovered part is mostly the printer and the text of the refusals,
    // which is worth knowing: it means the rules themselves are exercised and their messages are
    // not.
    // Raised to 82.09% measured on 2026-09-04, with the boundary and open-term tests.
    // 82.67% on 2026-09-05, which is the top of the spread this module has already shown across
    // three runs with no code change (81.94, 82.09, 82.67). The floor stays: a rise inside the
    // known variation is not a rise, and setting the number from the best of three samples is how
    // a gate starts failing on the sample rather than on the code. The rerun an hour later read
    // 82.82%, a fourth value, which is the argument rather than an exception to it.
    //
    // **95.65% over 1126 statements on 2026-09-16, at `f9e0672`**, and the floor rises to 93.4,
    // which is 25 statements under the measurement. Thirteen points in one move, from a number that
    // caught nothing that could plausibly happen: the note above recorded 94.84 here in September
    // and declined to act on it, which was right then and is what made this jump the size it is.
    coverageMinimumStmtTotal := 93.4
  )

// What in a source of this repository is a comment, for the gates that read the repository's own
// text. Depends on nothing, publishes nothing, and is reached only at `test->compile`.
//
// It is a module rather than a file in one of the test scopes that ask, and the argument is the one
// `mark` carries further down rather than a taste for small modules. Six gates decided what a
// comment is separately, in two shapes that did not agree on three inputs, and three of the six sit
// in three different modules' test scopes: `theories`, `tactics` and `dist`. Sharing along the
// edges that already exist means `theories % "test->test"` on `tactics`, which puts 75 test files
// and 21 097 lines into the compile graph of every `tactics/testOnly` in order to remove two copies
// of one function. Measured on 2026-09-16. The inner loop is not where that is spent, and a check
// over this repository's own text should not wait for the prover to compile: the days the prover is
// broken are exactly the days such a check is worth running.
//
lazy val scan = (project in file("modules/scan"))
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-scan",
    publish / skip := true,

    // **Measured 100.00% of statements and 100.00% of branches over 185 statements on 2026-09-16**,
    // by `sbt clean coverage scan/test scan/coverageReport`, seventeen tests.
    //
    // A hundred is the reading this repository distrusts on sight, and `CLAUDE.md` says why: an
    // incremental report covers only the files that were recompiled, and `theories` once read
    // 100.00% over 172 statements while the real figure was 97.56% over 22 663. So the denominator
    // is quoted beside the rate, and it is the whole module rather than a fragment of it: the first
    // run of the same command read 91.89% over the same 185, and the six tests that closed the gap
    // are named below.
    //
    // The floor is a point under, which on 185 statements is **two statements of margin**, and the
    // usual reason for a margin does not apply here: there is no property test in this module, so
    // the reading does not move between runs. What it is for is the next statement somebody adds
    // without a test, and two is deliberately not many. That those six tests exist is the argument
    // that it is affordable: each covers a branch a docstring in `Comments` already claimed (an
    // interpolation holding a quote, an escape, a quote that opens no character literal, and the
    // two guards that keep the reader total on a malformed line), and every one of those claims was
    // unchecked until the report named the lines.
    coverageMinimumStmtTotal := 99.0
  )

// The propositional solver. Depends on **nothing**, and that is the correctness argument rather
// than a property it happens to have: a search is untrusted here, and a module that cannot see
// `kernel` cannot construct a theorem whatever it does. `docs/adr/0003` makes the module graph the
// trust boundary and this is that decision applied one level down, where `tactics.Consistency` has
// to make the same promise with a test that scans its own source.
lazy val sat = (project in file("modules/sat"))
  .settings(publishSettings)
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-sat",
    // Measured 92.99% over 428 statements on the first landing, 2026-09-15, with `sat/clean` in
    // front of it for the reason `CLAUDE.md` gives about incremental reports. `Solver` is 98.29%
    // of 292; what is uncovered is mostly the arms that report a defect in this module to its
    // caller, which is the shape of gap to expect and not one to close with a test that asserts a
    // message. The floor is a point under the measurement, which is where the two modules measured
    // across several runs put theirs, and it only rises.
    //
    // **This floor cannot rise, and that is arithmetic rather than caution.** Measured 92.68% over
    // 437 statements on 2026-09-16 at `fb3f45a`: 25 statements is 5.72 points here, so the rule the
    // section above fixes would set 86.96, which is below 92.0. The floor was set by the older
    // rule, a point under the measurement, and a point is 4.4 statements on this module. So what
    // stands here is the **tightest gate in the build, at three statements of margin**, and it got
    // tighter rather than looser: 92.99 over 428 on 2026-09-15 to 92.68 over 437 today. Leaving it
    // is the ratchet working as written; changing it means lowering a floor, which is a decision
    // for a person and not one to take while passing. **Put and decided on 2026-09-16: it stays.**
    // So this module runs on three statements of margin deliberately, and the next reading that
    // finds the gate tight here is looking at a decision rather than at an oversight. What would
    // reopen it is the gate failing on a change that is not a regression, which is the thing the
    // margin exists to prevent and which has not happened here yet.
    coverageMinimumStmtTotal := 92.0
  )

// The connectives and the rules derived from the kernel's ten. Untrusted: everything here is a
// function that puts primitive rules together, so a mistake costs a failed derivation.
lazy val logic = (project in file("modules/logic"))
  .settings(publishSettings)
  // `sat` and not just `kernel` since `Propositional` landed: the solver proposes a refutation and
  // the rules here re-derive it. The dependency points at a module that depends on nothing, so the
  // trusted base is untouched and the graph still says which half is believed.
  .dependsOn(kernel, sat)
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-logic",
    // Measured 89.96%, raised with it: the notation and the reader that walks it are exercised
    // by the round-trip property.
    // Raised to 92.00% measured on 2026-09-04, with the schema rules and the new connectives, and
    // 91.83% later that day when the rewriter gained its limit diagnostic. The floor stays: it only
    // rises, and this went down. 92.05% on 2026-09-05, which is back where it was and not above it.
    //
    // **95.02% over 4635 statements on 2026-09-16, at `fb3f45a`, and the floor rises to 94.4**,
    // which is 25 statements under the measurement by the rule the section above fixes. This is
    // the fourth of the seven the note above left standing as "three now and four when the tree
    // settles", and it is the only one of those four that moved, for reasons written there rather
    // than here.
    //
    // The check that makes this a number about the tip and not only about the commit it was taken
    // at, which is the one the section above describes and the one worth repeating before raising
    // any floor: `git diff --numstat fb3f45a..7.0 -- modules/logic` is **empty**, so not one line
    // of this module changed between the measured tree and the branch. How many commits that is
    // goes stale within the hour and is deliberately not written here: it was three when the
    // measurement was taken and five when it landed, and the check is the diff rather than the
    // count. The
    // same check over `modules/theories` is not empty, which is why that floor did not move with
    // this one although the measurement was in the same report. That sentence is now spent:
    // `modules/theories` was measured on a rebased tree on 2026-09-16 and its floor moved, which
    // is recorded beside it.
    //
    // **95.24% over 4644 statements on 2026-09-16, at `748f1f5`, and the floor rises to 94.7.**
    // Nine statements more than the module carried at `fb3f45a` and the rate up 0.22, so this is a
    // rise of the measurement rather than of the sample. The same tip check passes:
    // `git diff --numstat 748f1f5..7.0 -- modules/logic` is empty. Margin at the old 94.4 was 39
    // statements, which is above the 25 the rule fixes, so the raise is the ratchet doing what it
    // says rather than a tightening argued for separately.
    coverageMinimumStmtTotal := 94.7
  )

// The mathematics: the theory of the reals and, later, the numerals. This is where the trusted
// base grows, so its axiom list is asserted by a test rather than described.
lazy val theories = (project in file("modules/theories"))
  .settings(publishSettings)
  // `scan` at test scope only, and it is the narrowest edge in this file: `Sources.code` decides
  // what a comment is before a census reads a source, and that decision is shared with two other
  // modules' test scopes. The main scope is untouched, and `scan` depends on nothing, so nothing
  // published from here can reach it and the direction of the graph is unchanged.
  .dependsOn(logic, scan % "test->compile")
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-theories",
    // Measured 96.77% on 2026-09-03 and 96.28% on 2026-09-04; the floor stayed a point below.
    // 97.42% on 2026-09-05, and this one is a real rise rather than a sample: the order facts, the
    // certificate search and the exact satisfiability search all arrived with their own suites, and
    // the module grew by about a thousand lines without the uncovered part growing with it. Raised
    // to a point and a half below the measurement, which is also more than a point below the lowest
    // reading this module has ever given. The rerun an hour later read 97.35%, so the margin is
    // doing its job on the day it was set.
    //
    // **97.48% over 49594 statements on 2026-09-16, at `748f1f5`, and the floor rises to 97.4.**
    // This is the run the note above asked for in as many words: it left this floor standing not
    // because the tree was busy but because `modules/theories` had moved between the reading and
    // the branch, so the rate was for a different population than the floor would have named, and
    // it said the floor "wants one run on a rebased tree and nothing else". This is that run, in a
    // worktree created at the tip and never built, and the check it exists for passes:
    // `git diff --numstat 748f1f5..7.0 -- modules/theories` is **empty**, so the population
    // measured and the population gated are the same one.
    //
    // What the ratchet had left here is worth a line, because it is the widest gap in the build
    // and the opposite of the two tight ones below. At 96.0 this floor sat **734 statements**
    // under the measurement, against the 25 the rule fixes: a gate twenty-nine times looser than
    // intended, on the largest module in the repository by a factor of ten. What it would have
    // caught is nothing that could plausibly happen, which is the sentence the note above already
    // wrote about `kernel` at twelve points. The rule sets 97.4 and that is what stands.
    coverageMinimumStmtTotal := 97.4
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
  .settings(publishSettings)
  // The theories only at test scope, and the direction is the point: the checker is a consumer of
  // the kernel's data and knows nothing about the mathematics, while its tests need real proofs to
  // check and the only place real proofs come from is a real development.
  .dependsOn(kernel, theories % "test->compile")
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-checker",
    // Measured 90.60% on the first run, 2026-09-10. The floor is set below it and only rises.
    //
    // **91.82% over 831 statements on 2026-09-16, at `f9e0672`**, and the floor rises to 88.8,
    // which is 25 statements under the measurement. The smallest module of the three that moved
    // that day, so the same 25 statements buy it three points of margin where they buy `core`
    // under one: that asymmetry is the reason the margin is counted in statements at all.
    coverageMinimumStmtTotal := 88.8
  )

lazy val tactics = (project in file("modules/tactics"))
  .settings(publishSettings)
  // The checker's TESTS on this module's test classpath, which is a narrower edge than it looks and
  // is there for one reason: `garden.xeno.symbolum.tactics.Evaluation` regenerates the figures of
  // `docs/evaluation.md`, and two of its three tables are the second reader's own counts over the
  // proofs `ReplaySpec` replays. A document is regenerated by ONE named command, so the alternatives
  // were a second command writing into the middle of the same file, or a second copy of the list of
  // proofs — which is the defect that document's own card is about. The main scopes are untouched:
  // nothing published from here can see the checker, and the checker still depends on the kernel
  // alone.
  //
  // `scan` beside it, at test scope and compile-only: four of this module's specs decide what a
  // comment is before they read a source, and until 2026-09-16 they decided it three ways that did
  // not agree with each other or with the two other modules asking. The edge is to a module that
  // depends on nothing, so it costs the compile graph one file.
  .dependsOn(theories, core, checker % "test->test", scan % "test->compile")
  .settings(commonSettings)
  .settings(coverageSettings)
  .settings(
    name := "symbolum-tactics",
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
    //
    // **The red gate this module carried is gone, and this floor still cannot rise.** It read
    // 89.92% on 2026-09-14 and 90.13% on 2026-09-15 against this 92.5, which is the only time a
    // floor here has actually failed; the suites that closed it were `Chaining`'s and the one that
    // reaches this module's web surface over a socket. Measured **92.83% over 4951 statements on
    // 2026-09-16 at `fb3f45a`**, so the gate passes. It does not rise because 25 statements is
    // 0.505 points here and 92.83 less that is 92.33, under the floor already standing. Sixteen
    // statements of margin, which is the second tightest in the build after `sat`, and the note
    // above recorded in September that this is the module where the next change is likelier to
    // fail this gate than to be caught by it. That is still true, and **it was put and decided on
    // 2026-09-16: this floor stays where it is.** Sixteen statements of margin on the module that
    // carries the only unseeded property draws in the build is the tightest thing here after
    // `sat`, and it is held on purpose rather than by nobody having looked.
    coverageMinimumStmtTotal := 92.5,

    // A compiler at test time, for `ReadmeSpec` and for nothing else.
    //
    // Until 2026-09-16 the front page's examples were certified by a test that RE-TYPED them, and
    // the two spellings drifted: `val expr = 2 * n + 3 * n - 1` was the first example a reader met
    // and did not compile anywhere, while the guard beside it evaluated `Num(2) * Var("n") + ...`
    // and was green. A test that rewrites what it certifies does not certify it, so the block is
    // now read from `README.md` and compiled as it stands.
    //
    // `Test` scope only: nothing published from here gains a dependency, which is the whole reason
    // it is not in `commonSettings`. `modules/dist` carries the same artifact at `Compile` scope
    // because the distribution's REPL is one, and that module publishes nothing either.
    libraryDependencies += "org.scala-lang" %% "scala3-compiler" % scalaVersion.value % Test,

    // The classpath those blocks compile against, written where a test can read it.
    //
    // Read from `dependencyClasspath` plus the two class directories rather than from
    // `fullClasspath`, which would be a cycle: `fullClasspath` contains `Test / products`, which
    // contains the resources this generator produces. The two directories are what
    // `fullClasspath` adds on top of the dependencies, so the file holds the same entries.
    //
    // A generated file and not `java.class.path`, because sbt runs tests in a classloader of its
    // own and that property holds the launcher, not the suite's classpath. A harness reading it
    // would compile every block against almost nothing and report an error about `Var`.
    Test / resourceGenerators += Def.task {
      val file = (Test / resourceManaged).value / "test-classpath.txt"
      val entries = (Test / dependencyClasspath).value.map(_.data) ++
        Seq((Compile / classDirectory).value, (Test / classDirectory).value)
      IO.write(file, entries.map(_.getAbsolutePath).mkString("\n"))
      Seq(file)
    }.taskValue
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

// One coordinate for all six library modules, for a consumer who wants the system rather than a
// link in its chain. It holds no source: what it publishes is a pom naming the six as dependencies,
// and the empty jar sbt writes beside that pom is left alone rather than switched off, because a
// pom that declares a jar and ships none fails to resolve under some resolvers and an empty jar is
// a download nobody notices.
//
// `dependsOn` and not `aggregate`: aggregation decides which projects a task runs over and puts
// nothing in the pom, and the pom is the whole content of this module.
lazy val symbolum = (project in file("modules/aggregate"))
  .dependsOn(kernel, checker, logic, theories, core, tactics, sat)
  .settings(publishSettings)
  .settings(
    name := "symbolum"
  )

// The distribution: what a person installs, as against what a build tool resolves.
//
// `Ask`, `Find` and `Notebook` were reachable only as `sbt "tactics/runMain ..."` inside a checkout
// of this repository, so the half of the project that is an environment rather than a library did
// not ship in any form. This module produces `target/universal/symbolum-<version>.tgz`: every
// module's jar, the full runtime classpath, and one launcher script per entry point.
//
// It is not published to the registry. A tarball is not a maven artifact, and the place for it is
// a release asset; `publish / skip` says so here rather than leaving it to the workflow.
lazy val dist = (project in file("modules/dist"))
  .enablePlugins(JavaAppPackaging)
  // `scan` at test scope: `LauncherSpec` compares the text of the launchers with the comments off,
  // and what a comment is is decided one place for the three modules that ask.
  .dependsOn(tactics, examples, scan % "test->compile")
  .settings(commonSettings)
  .settings(
    name := "symbolum-dist",
    publish / skip := true,

    // The REPL of the distribution needs a compiler to be a REPL, and this is the only place one is
    // wanted: nothing that ships as a library depends on it. It costs the tarball the compiler's
    // own jars, which is the trade the alternative avoids -- `scala-cli repl --dep
    // garden.xeno::symbolum-tactics:<version>` needs no compiler here and no tarball at all, and
    // needs a network and scala-cli instead. Both are documented in the README; this is the one
    // that works on a machine with neither.
    libraryDependencies += "org.scala-lang" %% "scala3-compiler" % scalaVersion.value,

    // The launchers, by allowlist rather than by discovery: name what ships, never take whatever is
    // there. Discovery reaches every main class below this module, and five of them -- `Lemmas`,
    // `Register`, `Guide`, `Examples` and `Foundation`, all in `theories` -- regenerate documents
    // of this repository through `Generated`, which resolves `docs/...` against the working
    // directory. A consumer who ran one from an unpacked tarball would have it write into whatever
    // directory they were standing in, and the failure would look like a bug in the prover.
    //
    // `WhatAClaimCosts` is here because it is the demonstration of the proof half and only prints.
    // The other three demonstrations print too and are on the classpath, which is part of what a
    // distribution is; they are not launchers because nobody installs a system to run its tests.
    //
    // `mark` is not a dependency of this module and so is in no tarball. It regenerates two files
    // under `docs/` and is of no use to anybody who did not clone the repository, which is the same
    // reason it sits beside the module graph rather than in it.
    Compile / discoveredMainClasses := Seq(
      "garden.xeno.symbolum.tactics.Ask",
      "garden.xeno.symbolum.tactics.Find",
      "garden.xeno.symbolum.tactics.Notebook",
      "garden.xeno.symbolum.examples.WhatAClaimCosts",
      "garden.xeno.symbolum.dist.Repl"
    ),

    // No default main class, which is what makes the script written under the project's own name a
    // general one: it refuses to start anything until it is given `-main <class>`. That script is
    // how the three demonstrations and the five document generators stay reachable without a
    // launcher each, and it is why picking one of the five arbitrarily would have been worse.
    Compile / mainClass := None,

    // The launcher names. Packaging derives a script name from the main class's simple name, which
    // gives `bin/ask` and `bin/find`: a distribution whose `bin` somebody puts on their PATH would
    // shadow `find(1)`. Renaming the mapping renames the command and breaks nothing, because each
    // script is standalone -- it holds its own main class and the whole classpath as literals, and
    // finds the distribution by resolving its own path -- so no script names another.
    Universal / mappings := (Universal / mappings).value.map {
      case (file, path) if path.startsWith("bin/") && path != "bin/" =>
        val name = path.stripPrefix("bin/")
        val renamed =
          if (name.startsWith("symbolum-dist")) name.replace("symbolum-dist", "symbolum")
          else s"symbolum-$name"
        (file, s"bin/$renamed")
      case entry => entry
    },

    Universal / packageName := s"symbolum-${version.value}",

    // Demonstrations and a documentation tool, so nothing here is measured against a floor. The
    // reason `examples` and `mark` give for having none is the reason this module has none.
    coverageFailOnMinimum := false
  )
