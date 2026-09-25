# Symbolum

## What this is

A computer algebra system that is also a proof assistant, in one repository, and the relationship
between the two is the whole design. The algebra side is fast and knows a lot; several of its
rewrites are valid only under hypotheses it does not record. The proof side is slow and knows
almost nothing; what it produces is certain. They are joined so that the first proposes and the
second checks, which is the arrangement `docs/adr/0003` describes.

**The thing a newcomer gets wrong:** assuming `modules/core` is trusted because it is the oldest and
largest part. It is not trusted at all. Nothing it says is believed anywhere in the proof side, and
that is deliberate: it is what lets it stay fast and heuristic.

## Running it

**Every command below starts with `tools/sbt` and not `sbt`, and that is the whole of what this
paragraph asks.** This machine caps how many builds run at once, because eight concurrent sbt JVMs
out of eight worktrees is not a slower measurement, it is a different one: two coverage runs were
killed by the operating system on 2026-09-16 and a two-minute run took twelve. The cap lives outside
every checkout, so nothing in here can enforce it and this file used to name it nowhere; measured
that evening, five of the seven builds running had never asked it for anything, and every one of
them was a session doing what the commands below told it to. `tools/sbt` hands the build to
whatever the machine names in `SYMBOLUM_BUILD_WRAPPER`, and where nothing is named it says so on
stderr and runs `sbt` anyway, so a checkout with no such arrangement around it loses nothing.

**The variable is in no profile, so whether a session has it is a coin toss, and the announcement
alone did not cover that.** The clause that used to end the paragraph above said nobody is left
believing they are in a queue they are not in; on 2026-09-18 a session read that stderr line sixteen
times, concluded the cap had been removed from the machine, and ran a whole suite in thirty-six
minutes against the four it costs quiet. The line was true and said *this build*; it was read as
*this machine*. So since that day the fall-through also says **which of the two it is**: a build on
this machine is capped and this session is not in it, and then it prints what to put in front of the
command; or nothing here is capped either; or nothing else is running and nothing has left a cap
behind, and then whether there is a queue at all is not something this session can see. Three
answers rather than two, which is the distinction `Refutation` keeps seven of one floor down.

**How it knows, without this file knowing where the cap lives.** A build that HAS a wrapper leaves
the path in a file under `$TMPDIR`, and a build that has none reads it; the environment of the sbt
processes already running is read as well, and second, because it is the one thing a file cannot
say — that a build is capped **now** rather than that one was once. What is written down here is the
rendezvous, which is a name this repository chooses; the wrapper's own path never is. `$TMPDIR` and
not `/tmp` because on this machine it is `drwx------` and the user's own, where `/tmp` is
world-writable. `tools/sbt-test.sh` holds all of it against stubs and CI runs it.

What it is **not** is a cap of its own: it holds nothing, waits for nothing, and **never runs what
it found** — a path from another process's environment or from a file in the temporary directory is
printed as the thing to do and is not executed, because a build that ran a program nobody in this
session named would be a different tool with the same name.

- **Tests:** `tools/sbt test`. Most of the wall clock is one suite: `ReachSpec` puts miniF2F's 244
  statements to the whole tactic surface and most of **that** is the ones it attempts and cannot
  settle. That cost is the prover's rather than the test's, and it is tracked. **How many they are
  is not written here**, for the reason the paragraph below gives about the wall clock: it was
  eighteen from `docs/adr/0029` until the completed square landed on 2026-09-18 and it is sixteen
  now, and a figure that moves whenever the prover gets stronger is a figure this file cannot
  hold. `ReachSpec` prints every one of them by name and `docs/adr/0029` classifies them.

  **The number that used to be here is gone rather than corrected.** It said forty seconds, against
  eleven before the corpus landed, and by 2026-09-14 a run was taking a hundred and ten on a quiet
  machine and twelve minutes on a busy one. A wall clock depends on the machine and on what else is
  running, so unlike every other figure in this repository it cannot be generated from the code
  either: there is no source of truth for it to be read off. What the sentence was for survives
  without it, which is that the cost is concentrated in one suite and why that suite is not
  excluded. This is the third of the three repairs `Generated.scala` lists, and it records that this
  one is met most often and chosen least. It is **not** excluded here, on purpose: a corpus that runs only when
  somebody remembers to ask for it has stopped being a measurement, and the figures in
  `docs/evaluation.md` are meant to fail rather than go quietly stale.

  It was two minutes for most of 2026-09-11, and the minute and a half that went is worth a line:
  `Abduce` was running a quadratic comparison over candidates it should never have compared, which
  it reached by misreading "the satisfiability question was not settled" as "the premises hold up".
  A suite that got slower is how that was found.
- **One module:** `tools/sbt kernel/test`, `tools/sbt theories/test`, and so on
- **One suite:** `tools/sbt "core/testOnly garden.xeno.symbolum.CanonicalFormSpec"`
- **The check that `-Xfatal-warnings` arrives:** `tools/sbt fatalWarnings`, and it is **not a
  command anybody has to remember**: `Test / test` on the root depends on it, so every
  `tools/sbt test` and every CI run of it pays for the check, at no step of its own. It reads the
  effective `Compile / compile / scalacOptions` and `Test / compile / scalacOptions` of every
  project of this build that holds sources, which it finds by asking the disk rather than from a
  list, so a project that never took `commonSettings` is inside the check; and then it compiles
  `tools/fatal-warnings-probe`, a source with an inexhaustive match that **must** fail, against a
  control compiling the same source with the one flag removed, which must succeed. The pair is
  what makes a red probe attributable to the flag rather than to a broken probe.

  **The question it answers is not the one the old guard answered.** `LogicErrorSpec` asserts the
  flag is *written* in `build.sbt`, and this repository holds a case of written and not arriving:
  the documentation build, `tools/sbt doc`, takes none of these options, says `Skipping unused
  scalacOptions: -Werror` in its own log, and read green over 57 unresolved links. That spec keeps its textual assertion and now says
  what it does not cover and names this task; what it adds is that the task is still wired to
  `Test / test`, since a gate can report a dead flag and cannot report that nobody runs it.

  **A green run of it prints one line and no compiler output**, because both probe compilations
  log into a stream nobody reads: a gate that rides `tools/sbt test` would otherwise put nine
  `[error]` lines into every suite log, and a healthy log that looks unhealthy is how a reader
  stops reading it. To see the probe's diagnostics, `tools/sbt warningProbe/compile` restores
  them, and every refusal the gate prints says so.

  The two probe projects are outside `modules/` and the root aggregates neither, which is what
  keeps `tools/sbt compile` green over a project that is supposed to fail. It also puts them
  outside every scan that reads `modules/`, which is the cost of the arrangement and is written
  where the probe is. `tools/fatal-warnings-probe/README.md` has the perturbations each half was
  seen failing under.
- **Coverage, with the floors enforced:** `tools/coverage-gate.sh`. This one
  **skips the corpus measurements**, which `tools/sbt test` does not: the two ask different questions, and
  `ReachSpec` exercises the same lines as the other corpus suites while costing more than the rest
  of the build put together. `build.sbt` and `garden.xeno.symbolum.tactics.Corpus` carry the argument.

  **It is a script and not the four sbt commands, because the four are a sequence and sbt stops at
  the first one that fails.** So `coverageReport` does not run when `test` is red, and until
  2026-09-19 nothing said so: sixteen minutes and forty-six seconds of a run that did not measure
  the thing it was launched for, with a log that reads as a test failure. The same silence in a
  second shape, measured that night on a run killed at `sbt-exit = 143` with nine modules of ten
  reported: `grep -icE "coveragereport|coverage minimum|scoverage"` over its 4068 lines returned
  **0**, against 11 for the run that finished twenty minutes later. **The absence of
  `Coverage is below` is not a pass, it is an instrument that did not read**, and a reader who
  greps for that line and does not find it concludes the floors held. The script ends on a verdict
  saying which of three things happened: the floors were asked and held, they were asked and one
  fell, or **they were never asked**; and it prints the third one from a signal handler too, so a
  run the supervising harness takes away says it as well. What decides which is not the exit code
  but whether a report of this run's own vintage exists per module, since a run killed before
  `coverageReport` and a run whose floor fell are both non-zero.
  `tools/coverage-gate-test.sh` holds every branch of that against stubs and CI runs it.

  **And what a change adds is a second figure, which is `tools/coverage-delta.sh`.** The floors
  above are on a module's **average**, and an average is a property of the pair (module, set of
  suites that ran) rather than of the module: measured at `30a1452`, `clean coverage
  theories/test theories/coverageReport` read 54027/55521 and `clean coverage test
  coverageReport` read 54113/55521 on the same code, **86 statements apart**, because `tactics`,
  `checker` and `dist` execute `theories`. The slack a floor leaves is about 25. What a change
  adds barely moves that way, and the pair was measured again on 2026-09-19 over one window:
  the two commands read **98.32% and 98.26%** on the same 3164 statements, two apart, while the
  module average read 97.52% and 97.32% and **crossed its floor**. Same mechanism, a lever short
  enough that no difference of that origin can decide a floor of 90. It reads the
  reports already on disk and runs no build, it compares no two reports — the added lines come
  out of `git diff` in the current file's coordinates and the report is in those same
  coordinates, so the line-shift problem every coverage-diff tool has does not arise — and its
  floor is 90% with changes under ten statements reported rather than judged. **And it refuses
  where a module carrying a changed line has no report**, which is what a narrow run leaves
  behind and which it answered until 2026-09-20 with a rate over the modules that did report: 9
  of 9 statements at 100.00% on a change of 176 lines across eight modules, the tool's own
  defect inside the tool written for it. The criterion is the change and not the build, so a
  module with no changed line and no report is not a shortfall. `docs/adr/0035` is
  the decision, including why the average floors stay. `tools/coverage-delta-test.sh` is the
  gate over it.

  **`clean` is not optional and the gate will not tell you.** The report is built from what the
  instrumented compiler saw, so on an incremental build it covers only the files that were
  recompiled. Run twice a commit apart on 2026-09-13, the second report held **two files**:
  `theories` read 172 statements at 100.00% against 22663 at 97.56%, and the gate **passed**,
  because 100 is above the floor. Read the statement count beside the rate, and run it in a
  worktree that has never been built or after `clean`. There is no check for this, and `build.sbt`
  says why there cannot easily be one.

  **Never pass `-J-Xmx` to it, and the reason is measured rather than cautious.** Since
  2026-09-25 each module's tests run in a JVM of their own, one module at a time, at `-Xmx1024m
  -Xss4M`, which is what `Test / javaOptions` in `build.sbt` says and what the launcher's own
  default is; before that day nothing forked and the whole suite shared the launcher's 1g, which
  is the heap **every floor in `build.sbt` was measured at**. So `-J-Xmx` now reaches only the
  launcher, which compiles and no longer runs a test. Why the tests left it is in the comment on
  `Test / fork`: `tools/sbt test` died of `OutOfMemoryError` in every aggregated run on 2026-09-24
  and 25, because sbt 1.10.10 keeps a finished module's test state for the whole session and
  because the aggregated run holds several modules' chains at once. The price is a second JVM:
  2924 MB of physical footprint at the peak of one `tools/sbt test`, launcher and fork together,
  measured with `footprint`, since `ps` leaves out the pages this machine compresses.

  Before that change, granting more made the run likelier to die, which is the opposite of what it looked like. Measured
  on 2026-09-16 against `4b96fe1`, same command, same tree, quiet machine, the two runs minutes
  apart: at the default the gate **landed in 10m15s with a peak resident set of 1922 MB**; at
  `-J-Xmx2g` it **died after about 8.5 minutes having written no report**, with a peak of 2380 MB.
  **Read those two figures as absolutes, not as a ratio that grows.** The resident set is 1.88x the
  heap at 1g and **1.16x at 2g**, so doubling the heap bought a quarter more footprint rather than
  double: the ratio falls. What makes the flag a bad idea is the plain 458 MB on a run whose free
  memory sits between 85 and 207 MB for its whole ten minutes, and not any runaway. Anyone
  extrapolating the 1.8x forward predicts about 3.7 GB at 2g and is over by 1.3 GB.

  What that death does **not** establish: the run was stopped by the harness supervising it and not
  demonstrably by the kernel, with no `hs_err`, heap dump or `OutOfMemoryError` produced. That is
  also true of the earlier kills, so it is the same kind of event rather than a different one. "The
  machine cannot carry it" and "the harness will not let it run" are different claims and only the
  second is established, for this run and for those.

  **The gate does run on this machine.** It ran twice on the evening of 2026-09-16, by two sessions,
  both landing, after an evening on which four attempts had died and a card had been opened saying
  it could not be run. Three of those four carried `-J-Xmx2g`. It wants a quiet machine and about
  ten minutes, and it is about four times the wall clock of `tools/sbt test` at a comparable resident set,
  so what it spends is exposure rather than size.

  **And since 2026-09-16 it does not only run here: `.github/workflows/ci.yml` runs the same command
  on every push to a release line**, which is where the memory is and where a checkout has never been
  built, so the `clean` hazard two paragraphs up cannot arise there at all. The first run was 24
  minutes and every floor held. What it settled, and it is narrower than "the figures travel": the
  five modules whose `src/main` and `src/test` had not moved since the laptop's last full run read
  the **same statement count and the same rate to the hundredth** on Linux, x86 and Temurin 17
  against macOS, Apple silicon and Temurin 23. `build.sbt` carries that table, the one module that
  looks like a platform difference and is not, and the tightest gate in the build, which is now
  `scan` at one statement of slack rather than `sat`.
- **The API documentation, and the check that reads it:** `tools/sbt doc`. Scaladoc reports a
  `[[link]]` it cannot resolve as a warning and **exits 0**, so the step that runs this in
  `.github/workflows/ci.yml` read green over 57 unresolved queries. Since 2026-09-18 that step
  greps its own output and fails when it names `No DRI found`; it costs no runner minutes of its
  own, because the `build` job already ran this command on every push to a release line and every
  pull request. Neither `-Xfatal-warnings` nor `-Wconf` reaches these: the log says `Skipping unused
  scalacOptions: -Werror`, the doc tool not being the compiler.

  **A query resolves inside the module being documented and nowhere else**, which is what decides
  how a reference is written here rather than taste. Within a file the path is qualified from the
  top-level entity: `[[Verdict.Countermodel]]` does not resolve and
  `[[Propositional.Verdict.Countermodel]]` does. Across a module boundary nothing resolves at all,
  since scaladoc runs once per module, so those go in backticks. That is not a demotion invented for
  the gate: counting, on 2026-09-18 and before this change, every mention of a name that is the file
  stem of a main source in **another** module, 636 were already in backticks and 31 in `[[ ]]`. The
  criterion over-counts the backticks, since a name written in prose that happens to be a file stem
  is counted, and it is quoted here because the ratio is what the decision rested on and a ratio of
  20 to 1 survives that slack.

  **The warning is one per documented symbol and query, not one per occurrence**, and that is why
  clearing the 57 took **thirteen** runs of this command: two `[[Foo]]` in one comment are one
  warning, and the next broken query in that same comment is invisible until the first is repaired.
  123 warnings and 138 occurrences over 48 files in all, 116 qualified and 22 put in backticks. So a
  red build here says at least one link is broken and never how many.

  **A link that resolves to the wrong thing is a second question, and since 2026-09-18 it has an
  answer rather than a watcher.** `[[Undecided]]` written in a file where some other `Undecided` is
  in scope is a working link to the wrong page, and this repository has four entities by that name;
  the grep above emits nothing, because the link resolved. `tools/scaladoc-scope.sh` reads the
  generated HTML instead of the log, where the `href` **is** the address scaladoc chose, and it
  runs in the same `build` job on documentation already on disk, so it costs no runner minutes of
  its own. `tools/scaladoc-scope-test.sh` checks the classification against pages built for the
  purpose, in the `shell-tools` job.

  **What it found is that the class is empty because scaladoc cannot produce it.** At `d247b58`:
  912 unqualified queries on 551 pages, 656 into the writer's own entity, 25 into a member it
  inherits, 231 into a top-level entity of the module, **none** anywhere else. A query resolves in
  the lexical and inheritance scope of the entity writing it and consults **no import**, measured
  twice on `sat/Resolution.scala`, whose `Cnf.Problem` is in scope for the compiler: `[[Problem]]`
  came back `No DRI found` under `import Cnf.*` and again under an explicit `import Cnf.Problem`.
  So an unqualified query lands in its writer's scope or fails loudly, and the failure is the gate
  above. What the script is therefore **for** is pinning that argument: it goes red if a scaladoc
  resolves differently or a module grows a second package repeating a top-level name.

  Two things it does not reach, and the first is where the defect that is left lives. **Intent**: a
  query whose writer's own scope holds the name, meant by its author as another entity's, is
  correct by every rule here and lands on the wrong page, and so is a **qualified** query naming
  the wrong path. And scaladoc publishes neither private members nor links into them, so 912 of
  this repository's 1528 unqualified sites are all it reads. The census over the sources was the
  alternative and is not what landed: it calls 217 sites suspect, on the criterion that their own
  module declares the name more than once, and reading them shows what that counts, since
  `[[normalisation]]` in `Arithmetic` resolves to `Arithmetic.normalisation` and is flagged because
  `Polynomial` and `Semiring` have one too.

- **A console with the algebra loaded:** `tools/sbt core/console`
- **Asking the prover one thing, without writing Scala:**
  `tools/sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:real. x + 0 = x"`. It puts the claim to the whole
  tactic surface over the widest signature the chain assembles, so a claim about `num` is one it can
  take, and prints what `Cost` reports: the outcome, the price, the axioms, what it rests on, and
  where it fails if it fails. `|` separates two claims; the claim is **not** quoted, because `sbt`
  hands the arguments over already split and the shell's quotes are gone by then.
- **Looking for a lemma, by name or by shape:**
  `tools/sbt "tactics/runMain garden.xeno.symbolum.tactics.Find SUM"`, or
  `tools/sbt "tactics/runMain garden.xeno.symbolum.tactics.Find x:real + y:real = y + x"`. It puts the query to all
  three of the library's questions, the name, the constant and the shape, and prints each answer
  under its own heading including the empty ones, because a reader shown two answers to three
  questions cannot tell which was empty and which was never asked. A bare identifier reads as a
  boolean **variable** and a variable pattern matches every lemma there is, so that one is refused
  by shape rather than answered with the whole library.
- **Working on a theory interactively, in a browser:**
  `tools/sbt "tactics/runMain garden.xeno.symbolum.tactics.Notebook"`, then open `http://127.0.0.1:8642`. A column
  of cells over one `Session`: `declare`, `define`, `assume`, `prove`, `derive`, `ask`, `find`,
  `show`. The chain is built once when it starts, a few seconds, and each question after that is
  milliseconds. `DocumentationSpec` compares that list with `Session.Command.Keywords` in both
  directions, and it does so because the list stood at seven for the day after `derive` became the
  eighth: a sentence with no figure in it has nothing watching it, and the paragraph below was
  rewritten in that time to repair another false sentence about `derive` without anybody rereading
  this line.

  **A session holds exactly one theory, and that is the whole safety argument rather than a
  convenience.** The falsity `SoundnessAttackSpec` derives needs *two* theories that each declare
  one name, and a notebook whose cells re-run in any order is that caller by construction. So the
  transcript is append-only: going back to a cell discards everything after it, and a second
  `declare p` is refused by the kernel's own `AlreadyDeclared` because there is one theory to
  declare into. `assume` is in the language, because the promise here is accounting rather than
  purity: every theorem downstream of an assumption carries it, printed on the page, through
  `Derivation.foreignTo` against the chain.

  What it cannot do, named rather than left to be discovered: **no tactic spends an assumption.**
  No procedure searches over an assumed constant, and the reason is the surface's rather than the
  domain's: the tactic surface is built over the base chain, so a claim in a vocabulary the session
  added is one no procedure has a reading of. The domain-theory paragraph below is what says a
  procedure is not barred from a domain's constants in principle. So a session's own axiom reaches
  a conclusion through a hand derivation, and since `c0830ce` the command for that **is** written:
  `derive NAME : <step>`, over the `Recorder` in `modules/logic`. This said it was not written for
  the hours between that commit and 2026-09-16, which is the shape of stale reference nothing goes
  red on. What it offers is the five inferences whose arguments are names of facts the session
  already holds; the three of `DomainTheorySpec`'s that take a term or a free variable as a premise
  are absent and named absent in `Session.Surface.Inferences`, because offering one is a decision
  about elaborating a term in the middle of an inference and not this one.

  **A paste of several lines is one submission and its lines run in the order they were pasted**,
  which is how a development is replayed, and a submission names the transcript it was written
  against, so anything else driving the port is refused rather than interleaved into it. Both
  landed on 2026-09-16: until then the page fired one request per line and waited for none of them,
  so the order of a transcript was the network's rather than the writer's.

  **A refusal is somewhere to carry on from rather than the end of the load**, which is what the
  message on it has always said and what the page did not do for the hours after the refusal
  landed: a flag that stopped the sending never came back down, so every command written next was
  swallowed and the box emptied as though it had gone. What the page holds now is the transcript it
  was written against, as a number that moves when the server refuses one, so what was queued
  behind the refusal is dropped and what is written after the new cells are rendered is sent.
  Nothing that did not land disappears: the message names each one, and the box gets it back when
  what it would get is a single line. It is listening on loopback with no authentication: a
  single-user tool, not a service.
- **Regenerating `docs/lemmas.md`:** `tools/sbt "theories/runMain garden.xeno.symbolum.theories.Lemmas"`. It
  replaces what lies between the two markers and leaves the prose above them alone. `LibrarySpec`
  compares the file against the code and fails naming this command, which is the point: the document
  breaks exactly when somebody adds a lemma.
- **Regenerating the mark:** `tools/sbt "mark/runMain garden.xeno.symbolum.mark.Mark"`. It writes **both**
  the character art in `docs/logo.md` and `docs/logo.svg`, from the description in
  `garden.xeno.symbolum.mark.Figure`, which is in radii rather than in cells. It **refuses** rather
  than writing when what it draws fails one of the three checks that document describes: that the
  operator stream covers every filled cell in reading order, that the mark is one connected region,
  and that it encloses exactly one empty one. `MarkSpec` runs the same three and compares both
  committed files against the description, failing and naming this command.

  **With a size in rows it prints instead of writing**, which is the point of the description:
  `tools/sbt "mark/runMain garden.xeno.symbolum.mark.Mark 33"`. Not every size holds, and the ones nobody
  has measured are a question rather than a gap: twenty, twenty-three and thirty-three hold,
  twenty-six leaks its counter and forty-six seals a pocket, and `MarkSpec` asserts all five.
- **Regenerating `docs/reading-register.md`:**
  `tools/sbt "theories/runMain garden.xeno.symbolum.theories.Register"`. The same arrangement as the lemmas, for the
  three things nothing but a reader checks: every axiom, every defined constant and every row of the
  precedence table, each with whether somebody has read it, when, and against which source.
  Everything says **NOT READ**, because nothing has been. The attestations are written by hand in
  `docs/reading-register-attestations.txt` and are folded in by the generator, so a reading survives
  the regeneration and nothing is ever recorded by editing the generated block. `RegisterSpec` fails
  when a statement has no row and names this command. It checks nothing about whether a statement is
  **right**, and the document says why a test that appeared to would be worse than none.

## Layout

Dependencies point one way, and the direction is the correctness argument rather than tidiness:

```
kernel    -> (nothing)      the trusted base
checker   -> kernel         a second reading of a proof, as text or in this process
sat       -> (nothing)      a conflict-driven solver and the refutations it produces
logic     -> kernel, sat    connectives, derived rules, rewriting, parser, printer
theories  -> logic          the naturals, the reals, numerals, arithmetic, RING, LINARITH
core      -> (nothing)      the computer algebra system, published as garden.xeno:symbolum-core
tactics   -> theories, core the lowest module that sees both halves
examples  -> tactics        runnable demonstrations of either half, not published
mark      -> (nothing)      the figure, the art and the drawing written from it, and its checks
scan      -> (nothing)      what in a source of this repository is a comment, for the gates that ask
```

`sat` depending on nothing is the same kind of statement as `kernel` depending on nothing, read from
the other end. A search is untrusted here, and a module that cannot see `kernel` cannot construct a
theorem whatever it does, which `modules/sat/src/test/.../IsolationSpec` asserts. It is worth having
as a module rather than as a file under `tactics` because that is the difference between a property
and a convention: `tactics.Consistency` makes the same promise about itself with a test that scans
its own source for the name of an inference rule, and its comment says why a runtime check was not
available to it.

`mark` is beside that graph rather than in it: nothing depends on it and it depends on nothing. It
is a module and not a file in `examples` for one reason, which is that `examples` depends on
`tactics`, and a check over two files under `docs/` that could only run after the prover compiled
would stop running on exactly the days the prover is broken.

`scan` is beside it for the same argument and is reached only at **test** scope, by `theories`,
`tactics` and `dist`. It holds the one decision about what in a source of this repository is a
comment. Six gates decided that separately until 2026-09-16, in two shapes that disagreed on three
inputs: a trailing `// note` after a call, a doc comment closed in the middle of a line, and a `//`
inside a string literal, where the text-cleaning shape deleted real code. What makes it a module
rather than a file in one of the three test scopes is the measurement: sharing along the edges that
already exist means `theories % "test->test"` on `tactics`, which on 2026-09-16 put 75 test files
and 21 097 lines into the compile graph of every `tactics/testOnly` to remove two copies of one
function. The main scopes are untouched, so nothing published can see it and the trust boundary is
unchanged.

`kernel` declaring no dependency is what makes the trusted base something you can point at rather
than describe, and a test in `modules/kernel/src/test` asserts it cannot see the algebra side.

`tactics` was **the only** module seeing both halves until 2026-09-13, and that sentence was worth
correcting rather than preserving: what the split enforces is that nothing **below** `tactics` sees
`core`, and `examples` is above it. It depended on `core` alone, which made it the algebra's
demonstration directory by accident of the graph, and a demonstration of the proof half had nowhere
to live. `WhatAClaimCosts` is the first one that does.

## The trusted base, exactly

Everything this system asks anyone to believe, and no one development is asked for all of it:

1. **`Kernel`, `Term`, `Type` and `Theory` in `modules/kernel/src/main`**, under 1220 lines. The
   directory also holds a printer, the refusal surface, the proof record and the reader of which
   commit the classes were built from, which are not counted and cannot construct a theorem, which
   a test checks rather than claims. `Kernel.Thm` is a class
   with a private constructor rather than an opaque type, which erases to what it wraps:
   `TrustBoundaryTwinSpec` casts the underlying pair and gets a `ClassCastException` where it used
   to get a theorem out of nothing. Ten primitive inference rules construct a theorem, and three
   theory extensions also do: defining a constant, defining a type, and asserting an axiom. Only
   the last of those adds to what has to be believed. `Kernel.cite` builds one too and infers
   nothing: it restates a published fact's sequent under the fact's name, which is where a report
   on a proof stops walking, and `docs/adr/0047` is why. Term constructors are `private[kernel]`, so a
   term exists only because a checking constructor built it and is well-typed by construction. Type
   constructors are not private, because naming a type proves nothing: a type entering the system
   from outside is checked by `Theory.checkType`.
2. **The sixteen axioms in `modules/theories/.../Real.scala`**, which state a complete ordered
   field. `RealSpec` asserts the theory holds exactly those and in that order.
3. **Three axioms added on 2026-09-10**: a choice operator and eta in
   `modules/logic/.../Classical.scala`, and infinity in `modules/theories/.../Natural.scala`. The
   first two are asked of the formalism rather than of a domain, and the third of a type nothing
   else interprets. `docs/adr/0007` is the record of choice and of infinity, `docs/adr/0009` of
   eta. They are what the naturals are built from, and the naturals are **defined**: the type `num`
   costs no axiom of its own. **The excluded middle is not among them**: it is derived from choice
   alone, in 841 steps, and three places in the repository said the opposite until `docs/adr/0009`
   measured it.

   **That figure is written by hand in this sentence, in `docs/proving.md` and in `Logic.scala`,
   and `ClassicalSpec` spells all three from `Derivation.size` rather than comparing them with a
   literal.** Two further readings are generated and compared with the same measurement, the
   classical table of `docs/proving.md` by `GuideSpec` and the showcase page by `TheoremsSpec`,
   and one more is the pin, which is the only place the digits are written as a literal against
   the code. **Everywhere else the derivation is named and the count is not repeated**, and
   `ClassicalSpec` walks the repository to say so, because a list of guarded sentences covers
   what somebody put on it and nothing else. It reads every Scala source of every module and, since
   2026-09-24, every document on disk outside the directories git ignores; in a file that carries
   the figure it exempts the sentences named there and not the file. From 2026-09-22 until then it
   read a list of three documents and exempted carriers whole, and this sentence said "every other
   document": a copy in `docs/adr/0009` stayed green, and so did a second live sentence here. A
   list of documents covers what somebody put on it, too.

   **This paragraph said until then that the figure was "written by hand in four documents and
   asserted in all four by `ClassicalSpec`, which is what makes writing it by hand safe here", and
   the interesting part is which half was wrong.** Not the coverage: that gate is real and has
   been since 2026-09-11. What was wrong is that it read as covering **every** copy, and it
   covered the sentences on its list; six others were live, present tense, and watched by nothing,
   including one inside a generated page sitting twenty-eight lines from the same count printed
   from the measurement. A reader met the promise, concluded that writing the number out was safe
   here, and wrote it out again.

   **The card that repaired this was opened on a reading that was itself false, and that is the
   part worth carrying.** It was written from `git grep 841` and concluded nothing guarded the
   figure. The gate that did guard it **spells** the number instead of writing it, so it has no
   digits in it and a grep for the digits cannot see it. An absence an instrument reports is not
   an absence until that instrument has been seen finding something.

   **And the copies were three kinds of thing, which is why a count of them decides nothing.**
   Some sat inside generated regions. Two were dated statements about a past move, like the
   sentence below this one, and what happened on a day does not go stale when the figure moves
   again. The rest were live, and those are the ones that are gone.

   It has moved twice, 983 to 829 when `Conv.refl` began sharing an atom's reflexivity, and 829 to
   841 on 2026-09-16 when `Rules.mp` stopped accepting an antecedent differing from the
   implication's by a beta redex. Which of the axioms a session pays for depends on what it builds on, and
   `NaturalSpec` measures each case: sixteen over the reals alone, three over the naturals alone,
   nineteen for a development holding both, which is what `Chain.standard` assembles and `ChainSpec`
   asserts. `docs/adr/0007` decides that the reals will be constructed rather than axiomatised, so
   this count goes up before it comes down: the sixteen become theorems at the end of that work and
   what is left is the foundation. A session in the middle sees a larger trusted base than the one
   before it, and that is the decision rather than a defect.

Everything else is proved. The connectives are definitional extensions, the numerals are
definitions, and every arithmetic lemma is derived. If a change makes the axiom count move, it is
either deliberate and needs a record in `docs/adr/`, or it is a defect.

## Conventions here

**Add a lemma by proving it, not by asserting it.** `Kernel.assertAxiom` exists and is named so that
it reads as what it is at the call site. Reach for `Arithmetic`, `Ring`, or a hand derivation
first; the file already contains a dozen worked examples of what a hand derivation looks like.

**A case split about a proposition is `Classical.cases`, not `LT_TOTAL`.** Until 2026-09-10 the
theory of the reals was the only supplier of a disjunction here, so a proof by cases could only be
about an order. `Classical.standard` now has the excluded middle, `cases`, `contradiction` and
`ext`, and a development that wants them takes the extension rather than the bare `Logic.standard`.

**A function defined by cases is written with `COND`, which `Classical` defines.** Until 2026-09-12
there was no conditional constant anywhere in the chain, so a definition by cases had nothing at all
to write its cases with. `COND p a b` is `select (\x. (p ==> x = a) /\ (~p ==> x = b))` and costs no
axiom, which is why the count of nineteen above did not move when it landed; what it costs is a
constant in the signature and a row in `docs/reading-register.md`. It lives in
`modules/logic/.../Classical.scala` rather than in a development, because a constant defined in a
development is unreachable from every link below it. It has **no spelling of its own**: it is
written `COND p a b`, and `if p then a else b` would be a change to the parser and the printer
rather than a row in the precedence table. Its first use outside the file that defines it is
`Rotation`, where it is what lets a caller hand `WORD_MAKE` a function that is already padded.

**A numeral belongs to the type its context forces, and there are two.** Until 2026-09-12 a digit
string was always a `real`, because `Parser` decided from the declared type of `1`; `Power 2 3`
could not be written, since `Power : real -> num -> real` wants a real base and a natural exponent.
`Peano` now declares a second encoding (`NUM_ONE`, `NUM_BIT0`, `NUM_BIT1`, all defined, no axiom)
and the elaborator decides: a numeral takes a metavariable and is expanded once unification has
said what its surroundings required. Three consequences a reader meets immediately:

- **`ZERO` prints as `0`**, because `ZERO` is the encoding's zero rather than a fourth constant
  beside it. `0:num` and `ZERO` are the same term, which is what keeps every lemma about `ZERO`
  reachable from a statement written with `0`. `SUC ZERO` and `NUM_ONE` are still different terms
  with the same value; `NUM_ONE_SUC` is the bridge, and `Successor` is what walks it.
- **A numeral nothing determines is refused** where the theory reads two, and taken where it reads
  one. The escape is `2:num` or `2:real`, which the parser did not read before.
- **A caller that knows the type says so in the call, not in the text**: `Signature.term(text,
  expected)` rather than an annotation inside the string. The measurement is in `Parser.term`'s
  docstring: of seven refusals across a consumer's 630 hand-written texts, all seven were
  unambiguous to the caller, and the text is the thing a reader compares against the informal claim.

**An operator symbol stands for more than one constant, and the elaborator picks which.** The
numerals' rule one level out, landed 2026-09-15 as `docs/adr/0018`. `+`, `*`, `<` and `<=` are
`num`'s as well as the reals', so `!n:num. n + 0 = n` reads and is proved where until that day it
was refused with "real and num cannot be the same type". `Notation` gains no types: it hands back
every candidate for a symbol and the parser, which has the theory, elaborates against the shape the
candidates share and reads the answer back after unification. Overloaded only where the operation
is the **same** one: `-` and `/` are truncated and floor over `num`, so they keep the prefix form
and a reader who writes them is told which constant to reach for.

Four things a reader meets immediately, and the last two are what the change cost rather than what
it bought:

- **Nothing printed moves for the reals, and 135 statements move for `num`.** The criterion is
  the one the measurement used, and it is written down because without it the figure cannot be
  reproduced: of the statements whose text changed between 7.0.2 and 7.0.3, compared by **name**
  rather than by line, 135 carried a `:num` binder beforehand. The 136th changed without one and
  is `le` becoming `real_le`. This sentence read "135 of the library's 436" until 2026-09-16,
  and the denominator was the library's size on the afternoon it was written: a count of what
  moved at one past event does not drift, and the size of the library does, so the ratio was
  true for a day and nothing failed when it stopped being. The card that asked for the work
  predicted 172 of 427 and no criterion on the population reproduces that pair, so a 172 found
  anywhere is the prediction rather than a measurement.
  `NUM_DIVISION_UNIQUE` is the one to look at: it was `NUM_ADD (NUM_MUL x y) z = ...` and is
  `x * y + z = x * u + v /\ z < x /\ v < x ==> y = u /\ z = v`, which is the uniqueness of quotient
  and remainder as anybody would write it. `docs/reading-register.md` gained more than
  `docs/lemmas.md` did, and those are the rows nobody has read.
- **A text whose type nothing determines is refused, and that now includes a text made only of
  digits.** `0 < 1` at the widest signature is ambiguous in two ways at once and is refused naming
  both; `(0:real) < 1` reads. The escape `Signature.term(text, expected)` does **not** reach this
  case when the text is a proposition, because the type a caller can pass is then `bool` and `bool`
  says nothing about the operands. A caller whose ambiguity is inside an equation annotates in the
  text, which is what `Algebraic` does when it builds a polynomial out of variable names.
- **A constant's name is never a symbol any more, and three were.** `Real.Addition` was literally
  `"+"`. It is `real_add`, with `real_mul` and `real_lt` beside it, and `le` became `real_le` so the
  four read alike. This paragraph went on to say that `Real.Zero` was still `"0"` and `Real.One`
  still `"1"`, left alone on purpose for `docs/adr/0012`; they are `real_zero` and `real_one` and
  have been since some change that did not come back here, so the sentence describing the exception
  outlived the exception. Nothing goes red on it, which is why it is worth saying where it is found
  rather than only fixing it: the six constants are named in `Real.scala` and nowhere else, and a
  reader wanting the name asks that file.
- **`Arithmetic.ringOrder` needed the product to sort before the sum, and got that from ASCII.**
  `*` precedes `+` in ASCII and `real_mul` does not precede `real_add`, so the rename reversed a
  comparison the canonical form depends on, and associativity stopped flattening. **One corpus entry
  in `PolynomialSpec` caught it and **no other test in the repository** did.** The ranking is written down in
  that file now. Read it before touching any order a normal form depends on: the general lesson is
  the one the file already carried about `num`, which is that such an order must not be a property
  of how two constants happen to be spelled.

**A numeral reaches a recurrence only through `Successor`, and until 2026-09-13 it did not reach
one at all.** Every recurrence over `num` is stated at `SUC n`, and `2:num` is `NUM_BIT0 NUM_ONE`,
so nothing written as a numeral hooked anything: `Power x 2 = x * x` was not provable, and
`Bounded.prove` still takes a bound spelled `SUC (SUC ZERO)` and refuses one spelled `2`. The
driver is `chain.successor`; `spell` puts a numeral into the successor form and `expand` opens a
power at a written exponent. It is **aimed** rather than a rule set turned loose, because the five
rules over a whole goal would open every numeral of `num` in it and a modulus of ten thousand
becomes a term with ten thousand nodes, and it derives each expansion over a **variable** base
because otherwise a numeral inside the base is opened too. A caller whose claim is not about a
power does the same thing in two lines with `spell` and `Kernel.eqMp`, which is what `Bounded`
needs and why the spelling is published as an equation rather than as a term.

**The algebra side has known conditionally-valid rewrites**, and they are not defects there: a
simplifier that carried every side condition would be unusable. `ValuePreservationSpec` pins them
by example, with the value each one changes. Do not build anything that trusts them.

**An assertion is only as good as the thought somebody gave to what would make it empty.** Half the
guards here rest on that and none of them used to say it. `RestsOnSpec` asserts that the reach
report's library holds names the searchable one does not, and on 2026-09-12 that is what refused a
change which would have made the assertion **vacuous rather than false**: adding the classical
axioms to `Library.of` would have emptied the difference it checks, and an empty difference passes.
`ProposeSpec`'s buckets are the same discipline from the other side, since a bucket that quietly
stopped receiving anything would read as a clean result. When writing a guard, ask what input makes
it trivially true, and assert against that too.

**A search may add a theorem and must never take a refusal away.** `Prove` asks `Chaining` and then
the hypothesis route after everything else, and neither failing changes the refusal the shape rule
chose. The rule that class is about is that the procedure whose fragment recognises the goal's
shape is the one whose refusal is reported, and a
search recognises no shape: it either reaches the goal or does not, so it has no claim on the
message. The one place the order is reversed is the propositional address, where `Intuitionistic`
runs before `Propositional` and the **second** refusal survives, because the first names a fragment
that is no longer the only one. **This sentence named `Minimal` until 2026-09-18**, when
`docs/adr/0023` moved the address off the gate and onto the calculus under it; the argument it
makes is unchanged, and what was wrong was the procedure it named, in the one document every
session reads first. `PropositionalRouteSpec` reads this sentence against `Prove.Search` now, so a
third procedure at that address goes red here rather than being noticed by a reader.

**A goal's own hypotheses are facts, and until 2026-09-18 they were not.** `H ==> C` went to the
library and to the search **whole**, so a lemma had to conclude the implication itself and the
premise was syntax on the road to the conclusion rather than something known. `Context` assumes the
antecedents, splits a conjunction into its halves and keeps the whole beside them, and
`Prove.underHypotheses` puts the conclusion alone to the scan, to the procedures and to the chaining
search before `Context.discharge` puts the antecedents back with the deduction theorem. Nothing in
the matching step learned what a hypothesis is: `Kernel.assume` gives `A |- A`, which `Apply` reads
as a lemma, and an assumption that is itself an implication is one owing its own antecedent.

What it cost is **one** relaxation, and it is in two places: `Prove.held` and `Chaining` refused a
candidate carrying any hypothesis and now refuse one carrying a hypothesis this goal did not assume,
so the promise that what comes back rests on nothing is a check at the end rather than an invariant
at every step. `docs/adr/0025` is the decision. The half a reader should not skip is that
`Linarith.split` had always assumed a linear goal's antecedents, which is why **no goal already
proved changes route or price**.

**Where it moved the measurement is not where the card predicted.** miniF2F did not move at all
across **that** change, 21 proved and 18 unsettled before and after it, because what stopped those
eighteen is nonlinear arithmetic rather than a premise nobody could see. Those are the figures of
one past event and they do not drift; what they are not is the corpus today, which the completed
square moved later the same day. What moved is the showcase, from six of its
fourteen claims settled by the tactic surface to **twelve**, and the six that moved are lemmas this
library **holds**: a lemma that is the goal was refused, because `Apply` specialises it and then
reads the instance's own antecedents as obligations, and `Prove.held` takes only a candidate owing
nothing. The system was refusing claims it had written down. What it costs is that `ReachSpec`'s
corpus pass roughly doubles, which is measured three ways in the record.

**And the order candidates are tried in is the whole of whether a bounded search works.** Sorting by
fewest obligations is the obvious order and it is wrong here, measured on 2026-09-15: `DOUBLE_NEGATION`
matches every goal at all and owes `~~goal`, `LT_FROM_ZERO` owes `0 < goal - 0`, and each owes one
obligation, so each sorts ahead of the lemma that settles the goal. The lemma that works ranked 4, 5
and 3 by count and 1, 2 and 0 by the total size of what is owed. At forty expansions the miniF2F
corpus cost 2.45 times its own baseline and proved nothing new; at ten under the right order it is
back at baseline and keeps every goal. A candidate whose obligations are smaller than the target is
making progress and one whose obligations are larger is not.

**`Linarith`'s fragment is named rather than measured by a degree, and since 2026-09-18 it holds
one fact nobody wrote.** Linear inequalities over the atoms, where a product of unknowns is an
atom; the hypotheses multiplied by each other and then by the hypotheses again, which reaches
degree three; and one square completed over an atom that is one unknown times itself, justified by
`Order.SQUARE_NONNEG` and so checked by the kernel like every other fact. `docs/adr/0032` is the
decision and the measurement that chose it is the one to carry: **the fact pool is generated from
the goal's hypotheses and nothing else**, so a goal with none has an empty pool, and an empty pool
has no products at any degree. Widening the schedule to a parametric degree therefore settles
nothing for such a goal, whatever the degree, which is arithmetic about an empty set rather than a
judgement about cost, and it is why that road was rejected for the two miniF2F statements that
asked for the work. Both are proved now.

Three things it costs a reader, and the last is the one that bites. The **refusal splits**: a goal
past the degree still hears about the degree, and a goal with no hypotheses hears that its pool is
empty, because the sentence about the degree is true of an empty set and sends nobody anywhere.
`Linarith.support` returns a **`Support` with two fields**, the hypotheses a proof rested on and
beside them the squares it was given, since a square is a premise nobody wrote and a report that
dropped it would make such a proof look like one needing no premise at all. And a procedure that
gets stronger **breaks the tests whose subject is the shape of a proof**: `ChainingSpec`'s witness
was `0 < inv (x * x + 1)`, whose lower rung the square now settles, so six assertions there went
red and the line was red with them from `73dc859` until the witness was replaced by
`0 < (x * x) * (y * y) + 1`, whose rung is a product of four factors and out of reach of both the
schedule and the completion. The repair is a new witness and never a loosened assertion, and that
file is where the argument is written.

**A tactic that cannot settle a goal must refuse.** `Ring` and `Linarith` are decision procedures
for small fragments and they say so by failing on the rest; `Translate` refuses what the theory has
no constant for, by name. A tactic that guessed would be worse than one that stops.

**Specialise a library lemma by the instance you want, not by position.** The order a lemma's
quantifiers are written in is not part of any contract: it follows from how the lemma was derived,
and on 2026-09-13 a derivation rewritten for an unrelated reason reversed the binders of `SUM_SUC`,
`POWER_SUC` and `PROD_SUC`. A consumer specialising those positionally stopped building, and it
stopped only because the two arguments had different types. Where two leading quantifiers share a
type the reversal is invisible and what comes out is a theorem that is true and is not the one the
caller meant: of the library's 743 lemmas, 498 have two or more leading quantifiers and **433 of
those have two that share a type**. `Rules.specTo` takes the body to be obtained and finds the
instantiation by matching, so the order is nowhere in the call; `Rules.specToReduced` is the same
where the caller's argument is a lambda and the instance carries a redex, which is a **different
theorem** and therefore a different operation. Neither protects the positional call sites that
remain.

That count is of binders sharing a type anywhere in the prefix, and the obvious next thought, that
only adjacent ones are realistically swapped and so the real number is smaller, is wrong and was
measured on 2026-09-13: of the sites a whole suite run reaches, 204 specialise a lemma with two
alike binders and 202 of those have two alike and adjacent (measured before `Magnitude` joined the
chain, which added nine alike-binder lemmas and no call sites, and before `Concatenation` joined it
on 2026-09-16, which added both: that file specialises `WORD_EXTENSIONALITY` by position at two
arguments of one type. The pair of numbers is a reading with a date rather than a property, and what
it was for is the ratio between them, which nothing since has moved). A lemma with three binders of one type
has adjacency anyway. The narrow reading and the broad one are the same number.

**The order the rewriting sorts by is not the kernel's.** `Arithmetic.ringOrder` compares by the
term under any negations first, so that a term ends up next to its own negation and the two cancel.
Changing it to the obvious structural order breaks cancellation silently.

**A model answers at a point, and `None` is not `false`.** `Evaluate` returns nothing where the
model has nothing to say: a constant nobody interpreted, `inv 0`, a quantifier over the reals.
Every caller skips such a point rather than counting it. `Refutation` keeps seven answers apart for
the same reason: a point found by sampling, a point found by solving, no witness at the points that
answered, no point that answered at all, a decision that the premises cannot all hold, a decision
that the claim cannot be refuted, and a refusal because sampling cannot settle a question of that
shape. Collapsing any two of them turns "I could
not ask" into "I asked and it was fine", which is the one way this machinery can mislead.
`docs/adr/0005` has the rest, including what changed on 2026-09-05 and what it did not change.

**A probe goes in `scratch/`, never under `modules/`.** That directory is ignored by git and is in
no sbt source set, and it exists because the alternative happened: a session left a throwaway spec
under `modules/` and the next run of the suite on this shared checkout failed for somebody else
with an error about a file they had never seen. If you are delegating to an agent, repeat this in
the briefing: a rule in this file does not reach an agent the project did not write.

**A perturbation harness is not a probe, and it is the one verification instrument that is kept.**
`docs/adr/0034` is the decision. What separates them is what the instrument can become: a
measurement that counts what a theorem rests on, or prints what a surface says, **can** be an
assertion in a spec, and a probe that finds something is telling you that no assertion carries it,
so what it earns is the assertion rather than a home. A perturbation edits a source, runs the suite
and puts the bytes back, which no spec can do from inside the run it is part of, so it is the only
one that is lost by not being kept — and it was rewritten twice for one card on 2026-09-18. Those
live in `tools/verify/`, one file per card and named in the file's first line. Nothing runs them,
because a harness can only pass by first making the tree wrong. Everything else stays in `scratch/`
and dies with the checkout, which is what should happen to it.

**They are kept because they survive, and that is a measurement rather than a hope.** At `ba3a60d`
the eight harnesses there named twelve perturbation targets between them, written across two days
against files that moved a great deal in that window, and **eleven of the twelve still applied
exactly once**. The twelfth refused because the card whose harness sits beside it had rewritten that
line, which is the refusal working: the perturbation tool refuses a substitution that did not apply
rather than running against unperturbed code, so a harness that has gone stale says so and names
the string. Repairing it belongs to the change that moved the string, as any other reference here
does.

**Property tests carry their sample count and the measurement that chose it.** They exist to probe
the design, not only to guard against regressions, so a new invariant belongs in one of them rather
than in another example.

**A figure in prose is one of three things, and which one decides what it costs.** It is **alive
and recomputable** if the code knows it, and then it is spelled from the measurement rather than
written: `FiguresSpec` searches `docs/evaluation.md` for the sentence with the measured number
already substituted in, so it goes red when the code moves and when somebody edits the sentence.
It is **alive and not recomputable** if it came from an instrumented run nobody can repeat, and
then it gets one declaration and every copy is spelled from that: `Rewrite.WidestMeasured` and
`Rewrite.WidestFromGoal` are the pair, and `docs/adr/0037` is the record whose copies `RewriteSpec`
compiles. Or it is a **photograph**, a dated past event that stays true when the code moves, and
then it wants nothing at all.

**The third is the one to get right, because calling it a defect deletes the record of how a guard
came to exist.** `docs/adr/0037` and `docs/numerics.md` each carry a section saying which of
their own figures are which, the first under its measurement and the second at its end, and those are the two worked examples; `docs/numerics.md` is the one
to read first, being almost entirely photographs with four live figures in it. **A decision record
is a photograph by default** — it says what was measured when the decision was taken, and
`docs/adr/0004` is superseded rather than edited for the same reason — and a figure in one crosses
into the second class exactly when something live starts resting on it, which is what happened to
that pair and is written where it happened.

Two traps, both paid for here. **A count of copies is itself a copy**: the sentence that counted
the sites of `841` counted the repair rather than the population, and this file carries that
account. And **a figure spelled out in words has no digits in it**, so a grep for the digits
reports an absence that is not one: `ClassicalSpec` guards `841` by spelling it, and the card that
was opened on `git grep 841` concluded nothing guarded it.

## Where this is going

The goal is exploration: proposing identities quickly and having each one certified, so that a long
symbolic development does not rest on a step that was only conditionally true. `modules/tactics`
is where that loop lives.

What the proof side reaches today, development by development, and what is not written between
them, is [docs/where-it-stands.md](docs/where-it-stands.md): read it when the work touches the
mathematics, not at every start. What comes next is in Mycelium, under the project tag `symbolum`
and indexed by card `e3eb75b1`. Neither goes back into this file, which every session reads whole
before its first question: a paragraph of progress written here is paid for by all of them, and
this section reached 113 000 characters that way.

## Working agreements

**Verify before recording as done.** A tactic is built when it has proved something end to end, not
when it compiles and its unit tests pass.

**Stale references are worse than missing ones.** When something moves, the references move in the
same change: a document naming a file that is gone gets consulted and believed.

**Ask before anything irreversible or outward-facing.** Approval for one action is not approval for
the next.
