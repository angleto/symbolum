# 0035. A change is judged by what it covers, and the module average stays beside it

- **Status:** accepted
- **Date:** 2026-09-19

## Context

Every coverage floor in `build.sbt` is on a module's **average**, and an average is not a
property of the module. It is a property of the pair (module, set of suites that ran). Measured
on 2026-09-18 at `30a1452` by `symbolum-4a`, on one tree, with two commands minutes apart:

    clean coverage theories/test theories/coverageReport   54027/55521 = 97.309%   FAILS
    clean coverage test coverageReport                     54113/55521 = 97.464%   passes

**86 statements of difference on identical code.** scoverage attributes every execution of an
instrumented class to the module that owns the source, and `tactics`, `checker` and `dist`
execute `theories`, so a run that does not include them reads a lower rate for `theories` than a
run that does. The gate is the second command. The slack the floors leave is about 25 statements;
the number one tree moves by changing the command is three times that.

Two consequences follow and only the first is obvious. A session measuring one module gets a
figure the gate would not agree with, which costs an afternoon each time somebody meets it. And
the figure the gate does read cannot be reproduced except by running the whole build, so
"is this change covered" is a question nobody can answer in under twenty minutes.

There is a second thing wrong with an average, older and not measured here: it answers a question
nobody asks. A floor at 97.4% over 55521 statements permits about 1400 uncovered ones, and says
nothing about whether the twenty a change just added are among them. `2cc13929` measured that a
module never breaks its own floor for code covered at that floor or better, whatever its size:
the average floor is already a threshold on the quality of what enters, expressed in a form
nobody can read without redoing the arithmetic.

## Decision

**A second gate, on the coverage of what a change adds**, in `tools/coverage-delta.sh`, with the
module floors left exactly as they are.

The figure is the fraction of statements on added or changed lines under `modules/*/src/main`
that some test executed. It barely moves with the command, because who else runs a file enters
it only through the added statements that another module's suite alone reaches; the table under
Consequences measures that at two statements of 3164. **Corrected in place on 2026-09-24**: this
sentence said "it does not move with the command" when it was written, and the measurement of
2026-09-19 below it had already shown a difference of 0.06 points.

**It compares no two reports, and that is the whole of the construction.** The obvious tool diffs
two `scoverage.xml` files, and it is wrong: one line inserted moves the line number of every
statement below it, so the naive comparison reports the rest of the file as new. This reads the
added lines out of `git diff` in the coordinates of the **current** file and reads the current
report, which is in those same coordinates. The current file is the one in the working tree,
since 2026-09-24; see "What it read" below for why it was not before and what that cost. There is no baseline, so there is nothing to shift.
That also means no baseline file to commit, no artifact of a previous push to fetch, and nothing
that can go stale except the report itself, whose date is printed beside the figure.

**The floor is 90%, and the number is measured rather than chosen.** Cumulative windows of the
last thirty commits of `7.0`, measured on 2026-09-19 against the report of
`tools/coverage-gate.sh` at that tip, read between 95.83% and 98.98%: the narrowest window is 24
statements at 95.83% and the widest 13136 at 96.65%. The lowest average floor in `build.sbt` is
88.8, so 90 is not weaker than the weakest thing already enforced, and the gap to the observed
95.83 is the room a genuinely hard-to-cover addition needs. A change under 90 is materially worse
than anything this line has landed in thirty commits.

**Below ten statements the figure is reported and not judged**, and the ten is computed from the
floor rather than chosen beside it: a change of *n* statements with one miss reads (n-1)/n, so it
takes ten before a single miss survives a floor of 90. At five statements one miss is 80% and
would fail, which would make the gate a rule about the size of a change. Raise the floor and the
number rises with it.

**The average floors stay, and stay as gates.** They are not superseded by this and this record
does not lower one; `build.sbt` says a floor rises and never falls, and lowering one remains an
explicit decision rather than a side effect of this.

## Consequences

**What is covered.** A change that adds poorly covered code is red at the push that adds it,
naming the statements nobody executed.

**And the figure barely moves between the two commands, which is less than "is the same" and is
what was measured.** Both run on 2026-09-19 over one window, base `7cb7d148`, restricted to
`theories`:

| | statements on changed lines | executed | delta | module average |
|---|---|---|---|---|
| `clean coverage test coverageReport` | 3164 | 3111 | **98.32%** | 97.52%, passes |
| `clean coverage theories/test theories/coverageReport` | 3164 | 3109 | **98.26%** | 97.32%, FAILS |

The denominator is identical, two statements differ, and the delta figure moves 0.06 points
while the average moves 0.20 and crosses its floor. So the mechanism is not absent from the
delta figure — it is the same mechanism with a much shorter lever. **The two statements are on
one line and the line is known**: `Linarith.scala:1743`, the head of `Linarith.constant`, which
this window changed and which only a suite outside `theories` calls. A statement that a change
adds and that only another module's tests reach is counted as uncovered by the narrow command
and as covered by the wide one, exactly as before; what changed is that the population it is
measured against is the change rather than the module, so one such line is 0.06 points instead
of 86 statements being 0.20.

Written the other way round, which is the way a reader should carry it: the delta gate's floor
is 90 and the two readings are 98.32 and 98.26, so no command-dependence of that size can
decide this gate, where a difference of that origin already decides the average one.

**What is not, and it is the reason the floors stay.** A module can drift down slowly with every
individual change well covered: old code deleted, new code added at 90 where the module sits at
97. The delta gate cannot see that and the average floor is exactly what does. So the two answer
different questions and the repository carries both. A reader who concludes from this record that
the floors have become advisory has read it backwards.

**What it read, and it had to be told how much to expect.** As delivered the tool took the
reports it found and had no notion of how many there should be, so after a narrow run it printed a
rate for the whole change computed over the one module that reported: 9 of 9 statements at 100.00%
on a change of 176 lines across eight modules, with no line of the output naming the second
element. That is this record's own defect -- a figure that is a property of the pair (subject, set
of reports that exist) -- inside the tool written to remove it, and the verification of card
`32c9a285` found it on 2026-09-20. Since that day the tool asks which modules carry a changed line,
compares that set against the modules with a report, and **refuses** when one is missing rather
than rating the change over the rest. The criterion is the change and not the build, which is
sharper than the neighbouring gate's and is what keeps a narrow local run of the one module a
change touches measurable: a module with no changed line hides nothing by not reporting.

**And what it read was still part of the change, one level down, until 2026-09-24.** The
verification of card `2cc13929` measured four more ways for the figure to be about something other
than the change, and each is a refusal now rather than a rate:

- **A changed file no report lists** left the denominator in silence: a fixture of 42 changed
  lines of code read 20 of 20. The tool now refuses and names the file. What that costs is a
  source with no statement at all, which no report can list either; none of the 183 sources under
  `modules/*/src/main` was free of `def`, `val` and `var` that day, so nothing here is expected to
  meet it.
- **The diff was to `HEAD` and the report of the working tree.** With anything uncommitted the two
  are in different coordinates, and on a real report of `scan` the tool answered "none of those
  lines carries a statement" for a change of six statements, two never run. **Decided: the diff is
  to the working tree, and a source git does not track yet is added whole**, because that is the
  tree the report was built from. Refusing a dirty tree is the alternative and is correct as well;
  it is rejected because measuring an uncommitted change is the local use this tool has, and on a
  runner the two are the same since the checkout is clean.
- **A report no build wrote**, a fourteen-byte `<statements/>` dated 2020 that the shared checkout
  held in every module, passed a change of 199 lines. A report without scoverage's `timestamp` is
  refused, and so is a report older than a changed file of its module: that report is of a tree
  without the change. The file's modification time is what is compared, since the report is of
  the working tree, and a checkout rewrites the times of what it changes.
- **The date printed was the wrong one**: `ls -l` columns sorted as text print the 3rd of a month
  before the 22nd. It is read from the reports' own stamps now, as a number.

**The report's date was the wrong date to compare, found on 2026-09-25.** The verification of card
`61cdee9d`, on a real report of `scan`: an uncommitted line inserted above the change, then
`coverage scan/coverageReport` alone. That command recompiles nothing and rewrites `scoverage.xml`
from the `scoverage-data/scoverage.coverage` the last instrumented compile left, so the report was
newer than the edit and in the coordinates before it, and the tool answered "none of those lines
carries a statement", exit 0, on six statements of which two were never run. It is not an exotic
route: `tools/coverage-gate.sh` recommends that command when its sequence stops. A report's date
says when it was written and not what it was written from, so the tool now also compares each
changed file with the instrumentation's date, and refuses a report with no instrumentation beside
it, since then nothing says which tree it is of.

And the base a runner measured from was decided by an expression in `ci.yml` that no test could
reach: empty on a manual run, so red on every one, and on a pull request's later pushes the
previous push rather than the base. The script takes the event and decides, and its test holds
all three.

**What it still cannot distinguish**, said here because it is the shape of failure this
repository cares about: changed lines carrying no statement in a file the report does list. A
comment, a blank line and a signature produce that reading, and so would a report whose compile
is dated after the change and did not read it. The checks above leave two ways to that, both
about modification times rather than content: a file saved while the instrumented compile was
running, after the compiler read it and before it wrote its instrumentation, and a file whose
time was set back, by `touch -t`, `cp -p` or an archive. On that reading the tool **exits 0**,
which on a runner is a green step, and says in its output that a stale report looks the same and
which date to check; until 2026-09-25 this paragraph said it refused to call it a pass, which the
exit code did not bear out.

**What it costs.** No runner minutes of its own: the `coverage` job already builds the reports
and this reads them. `fetch-depth: 0` on that job's checkout, because a shallow clone has no
base to diff against.

## Alternatives rejected

**Diff two `scoverage.xml` files, one from the previous push's artifact.** This is what every
coverage-diff tool does and it buys the line-shift problem, a baseline to fetch or commit, and a
failure mode where the baseline is missing and the tool has to decide what to do. The
construction above has none of them, and the thing the baseline would have bought — knowing
whether an *existing* statement stopped being covered — is what the average floors already
answer.

**Replace the average floors with the delta gate.** This is the attractive one, because the
average is the figure with the defect. It is refused: the drift the paragraph above describes is
real, invisible to a delta gate, and the only thing watching for it. A gate with a known blind
spot is not improved by removing the thing that covers the spot.

**Make the delta figure per module with its own floor per module.** More arithmetic, a second
table to keep in step with `build.sbt`, and no measurement asking for it: the observed spread
across thirty commits is between 95.8 and 99, which does not separate by module in any way this
data can see. One number until something measured wants two.

**Report the figure without failing on it.** A step that cannot go red is a step nobody reads,
which is the defect `tools/coverage-gate.sh` was written for one record ago.
