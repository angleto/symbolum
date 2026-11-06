# The fatal-warnings probe, and where each half was seen failing

A source that must not compile, and a control that compiles the same source with one flag removed.
Together they are the positive control for `-Xfatal-warnings`: the instrument that says the flag
reaches the compiler, rather than that the string is in `build.sbt`. The gate over them is the
`fatalWarnings` task in `build.sbt`, which `Test / test` on the root depends on, so it runs under
`tools/sbt test` and in CI without a step of its own. Run it alone with `tools/sbt fatalWarnings`.

Two projects, neither aggregated by the root:

- `warningProbe`, base `tools/fatal-warnings-probe`, holding the one source. Its compilation MUST
  fail.
- `warningProbeControl`, base `tools/fatal-warnings-probe/control`, holding no source of its own
  and reading the same directory, with the flag removed from its options by derivation rather than
  by a second list. Its compilation MUST succeed.

## Why a compilation and not an assertion

`LogicErrorSpec` asserts the flag is WRITTEN in `build.sbt`. That is a different claim from the
flag ARRIVING, and the two have already come apart here: `sbt doc` takes none of these options, its
log says `Skipping unused scalacOptions: -Werror`, and 57 unresolved scaladoc links were reported
as warnings under an exit 0 while the textual assertion stayed green. Nothing a compiled program
reads at runtime says which diagnostics were emitted when it was compiled, so a test in the suite
cannot be this check. A compilation that has to fail can.

## What a healthy run prints: one line, or one line and the probe's eight

Both compilations log into a stream nobody reads. That is not cosmetic. The gate rides `Test /
test`, so its expected error would otherwise land in every full suite log, and three sessions here
were reading a run by counting `[error]` lines against zero, after a run reporting `827 succeeded,
0 failed` turned out to be a module that had not compiled with the modules under it never started.
Measured before the silencing, under sbt 1: nine `[error]` lines on a GREEN run, of which one named
the probe's path and eight were echoed source, carets and `one error found`. After: zero.

Under sbt 2 the silencing holds for a compilation that runs, and a green gate then contributes one
`[info]` line and no compiler output. But sbt 2 caches a compile's outcome, a failed one included,
and when it serves the probe's failure from that cache it replays the stored diagnostics into the
build's own log rather than the compile's, so neither the quiet logger nor a compiler reporter
reaches them: eight `[error]` lines, all E029 on `NonExhaustiveMatch.scala`, naming the path of
whichever checkout first compiled the probe, above the gate's line. Counted in five whole runs on
2026-09-26 and again on 2026-09-28. The count to read a run against is therefore zero where the
probe was compiled and eight where it was served, and `AGENTS.md` has the measurement that a served
failure is still evidence.

What the silencing costs is that debugging the probe needs `tools/sbt warningProbe/compile` or
`tools/sbt warningProbeControl/compile`, which restores the log, and every red message from the
gate says so.

## Seen failing, 2026-09-18, against `c10d61c` plus this change

macOS, Apple silicon, Temurin 23, sbt 1.10.10, Scala 3.3.5, each perturbation applied alone and
reverted before the next. The first two rows were taken twice: once when they were written, and
again after the messages changed, so what is quoted is what the gate says today rather than what
it said when the perturbation was run.

| perturbation | what the gate did |
|---|---|
| none (the tree as committed) | green, one line: `-Xfatal-warnings reaches 12 projects, and the compilation that had to fail did, quietly.` (the wording of sbt 1; under sbt 2 the line ends `did.`, and a failure served from sbt 2's cache prints the probe's diagnostics above it) |
| `-Xfatal-warnings` deleted from `commonSettings` | red, exit 1: `-Werror or -Xfatal-warnings is not in the effective scalacOptions of: mark (Compile and Test), examples, sat, core, scan, warningProbe, theories, logic, checker, dist, tactics, kernel` -- all twelve, each with both configurations |
| `theories / Compile / scalacOptions -= "-Xfatal-warnings"`, string left in `build.sbt` | red, exit 1: `-Werror or -Xfatal-warnings is not in the effective scalacOptions of: theories (Compile and Test)`, while `logic/testOnly ...LogicErrorSpec` stayed green at 5 tests. This is the defect class the card is about, reproduced: written and not arriving |
| a project added to the build that never took `commonSettings` | red, exit 1, `forgot (Compile and Test)`: the check is over `inAnyProject` and a question to the disk, so a project nobody named is inside it |
| the probe source made ill-formed (an undefined name) | red at the CONTROL, with the message that the probe is broken rather than warning, so a failing probe is never read as a working flag |
| `tools/sbt coverage fatalWarnings` | green, and `find tools/fatal-warnings-probe -name 'scoverage*'` returns nothing afterwards, so no coverage data about this source enters any module's measurement. What kept it out was `coverageEnabled := false` on both projects, and not the filter this row used to credit: that stripped `-Xplugin` and `-P:`, which are Scala 2's, from `Compile / scalacOptions`, where scoverage adds nothing, and measured on 2026-10-22 with the first layer removed the probe received Scala 3's `-coverage-out:` through it. The filter is a second layer since that day, at the task's scope and naming that option, and `build.sbt` carries the measurement beside it. That is the interaction the full `clean coverage test coverageReport` would exercise as well; what was run is the cheap half of it |
| `rm -rf tools/fatal-warnings-probe/control`, which is what a fresh clone looks like | green: git cannot track a directory holding no file, the control's base exists only as a target, and sbt creates it. The gate does not need a placeholder committed to stand it up |

One more measurement, taken directly rather than through sbt, because it decides what the first
half is allowed to accept. Run against the 3.3.5 compiler on a three-case enum matched at two
cases: `-Xfatal-warnings` and `-Werror` both give `[E029] Pattern Match Exhaustivity Error`, exit 1
and zero class files, and neither of them gives the same diagnostic as a warning, exit 0 and seven
class files. They are one option with two spellings, so the check accepts either: a gate that went
red on a rename would be repaired by loosening it, and what it is asked to notice is the option not
arriving.

Two readings from that table are worth keeping. The second row names twelve projects where this
build has eleven modules: `warningProbe` is one of the twelve, because the probe must carry the
flag and is therefore inside the same check as everything else. And the third row reports `Compile
and Test` for a perturbation that touched `Compile` alone, because a configuration delegates to its
parent and `Test` extends `Runtime` extends `Compile`.

## What is NOT covered, and one of them is a hole rather than a boundary

- **The flag lost between the setting and the compiler was not reproduced.** The probe covers it by
  construction, since it compiles through sbt's own `compile` task rather than through a compiler
  invoked from the gate, but no perturbation here exhibits it: the ways of losing options that can
  be written in `build.sbt` are all visible to the first half of the check, which reads
  `Compile / compile / scalacOptions`. So that half of the argument is structural and is the one
  thing in this file that has not been seen failing.
- **A probe that stopped warning is caught but misdiagnosed on its own.** If somebody completes
  the match, both compilations succeed, and what the gate sees is the probe compiling, which is
  also what a dead option looks like. It goes red either way, so nothing passes quietly, and the
  message names both causes and the one command that separates them. Telling them apart inside the
  gate would want the compiler's diagnostics back, and no supported key hands them over:
  `compilerReporter` was absent on sbt 1.10.10 and is `private[sbt]` on 2.0.9, where a build
  setting it fails to load (measured on 2026-10-03; `build.sbt` has the two refusals).
- **This directory is outside every scan that reads `modules/`**: the style scan, the language scan
  and the comment census do not read it. What stands in for them is that it is one short source and
  that the gate reads it twice, once expecting failure and once expecting success.
- **The hook is the weak link and is guarded by text.** It is two settings on the root since sbt 2,
  `(LocalRootProject / Test / test).dependsOn(LocalRootProject / fatalWarnings).evaluated` and the
  same on `Test / testFull` with `.value`, and if either is deleted from `build.sbt` the run that
  goes through it reaches nothing here and nothing here can notice. `LogicErrorSpec` asserts both
  lines are present, which is a textual guard again, and deliberately:
  what it guards is a line rather than a value reaching a tool, so the failure mode that defeated
  the assertion it sits beside has no counterpart.

## Under sbt 2, measured on 2026-09-25

| perturbation | result |
|---|---|
| `-Wconf:any:s` on the probe's `Compile` options only | red: the probe and its control differ by more than the flag, before anything compiles |
| `-Wconf:any:s` on the probe's project options, which the control derives from, so the two still differ by the flag alone | red: sbt 2 did not serve the probe from its cache, recompiled, and the gate said the probe COMPILED under this build's options |
