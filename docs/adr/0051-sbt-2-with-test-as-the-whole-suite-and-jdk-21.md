# 0051. The build moves to sbt 2, `test` stays the whole suite, and the library asks for JDK 21

- **Status:** accepted
- **Date:** 2026-09-25

## Context

The build ran on sbt 1.10.10 until this record. Angelo asked for sbt 2.0.9 on 2026-09-25, and the
move changes three things this repository leans on, each of which had to be decided rather than
inherited.

**What `test` means.** sbt 2 made `test` incremental: it runs the suites a change touched and
answers the rest from what it remembers, and the whole suite became `testFull`. Every figure,
gate, handover and card here reads `tools/sbt test` as the whole suite, and `CLAUDE.md` says so in
its first command.

**Which JDK.** sbt 2 runs on JDK 17 or later. Until this record CI tested the library on 11 and 17
and published it from 11, so a consumer on 11 was supported.

**How sbt runs.** Unless told otherwise, sbt 2's runner starts a server in the background, talks to
it through a native client, and joins every argument into one command line. On a machine that caps
concurrent builds, a server outliving its command is a JVM nobody queued for, and the joined line
broke every multi-command invocation this repository uses, the coverage gate's included.

## Decision

**`tools/sbt test` runs every suite of every module.** Decided by Angelo, choosing it over sbt 2's
default. `Test / test` is `testFull`, uncached, in every module; the incremental run keeps its own
name, `testQuick`. A green read off part of the suite and taken for a green over all of it is a
mistake this repository has recorded more than once, and a default that produces it silently is
not a default worth keeping.

**The library asks for JDK 21.** Decided by Angelo: support for 11 is dropped, and the baseline is
21 rather than the 17 sbt itself would need. The compiler is given `-java-output-version 21`, so
the class files are for 21 and the JDK's API is 21's whatever JDK runs sbt; CI tests and publishes
on 21, and the scaladoc mapping points at 21's javadoc.

**sbt runs in the foreground**, through `--server` in `.sbtopts` at the build's root, which the
runner reads for every invocation that starts there: people, tools and CI.

## Consequences

**For a consumer of `garden.xeno:symbolum-core`, JDK 21 is now required.** The release that carries
this record is the first that does not run on 11 or 17, which is the one change here a reader
outside the repository meets. `-java-output-version 21` is what makes it a property of the artifact
rather than of the machine that built it: without it a build on the JDK 23 the laptop runs would
accept a call that exists only after 21.

**What sbt 2 changed beside these three, and where each is written.** Output moved from each
module's `target/` to the build's `target/out/jvm/scala-3.3.5/symbolum-<module>/`, which the
coverage scripts, their harnesses and CI now read. Settings written bare in `build.sbt` apply to
every subproject, so the fatal-warnings gate is scoped to the root by name. sbt 2 caches task
results, failed compiles included, and replays a cached failure's diagnostics; a probe failure
served from that cache was measured to still be evidence, and `CLAUDE.md` says why its replayed
lines are expected. Tests stay forked one module at a time, as `build.sbt` explains; nothing in this
move changed that.

**What was measured before this record, on the branch that carries it.** The whole suite on sbt 2
passed but for one textual pin, since moved; scoverage 2.4.4 wrote `scan`'s report where the
scripts now look, 185 statements at 100.00%, the figure sbt 1 read; `.sbtopts` ran four commands as
four and left no server behind.

## Alternatives rejected

**sbt 2's own `test`, with `testFull` written wherever the whole suite is meant.** Faithful to the
tool, and every session typing `tools/sbt test` from habit would get a partial run reading green.

**Keeping JDK 11**, with sbt on a newer JDK and the tests forked onto 11. It keeps the widest set of
consumers and costs a second JDK in CI and a build setting per job; not chosen.

**Staying on sbt 1.10.10.** Nothing here needed sbt 2; the move was asked for.
