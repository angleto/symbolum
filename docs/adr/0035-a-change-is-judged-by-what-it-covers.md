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
that some test executed. It does not move with the command, because who else runs a file does
not enter it: a new statement is executed by somebody or it is not.

**It compares no two reports, and that is the whole of the construction.** The obvious tool diffs
two `scoverage.xml` files, and it is wrong: one line inserted moves the line number of every
statement below it, so the naive comparison reports the rest of the file as new. This reads the
added lines out of `git diff` in the coordinates of the **current** file and reads the current
report, which is in those same coordinates. There is no baseline, so there is nothing to shift.
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
naming the statements nobody executed, and the figure is the same under
`clean coverage test coverageReport` and under `clean coverage theories/test
theories/coverageReport` — measured both ways on 2026-09-19 over the same thirty-commit window
restricted to `theories`, which is the defect this record exists to close.

**What is not, and it is the reason the floors stay.** A module can drift down slowly with every
individual change well covered: old code deleted, new code added at 90 where the module sits at
97. The delta gate cannot see that and the average floor is exactly what does. So the two answer
different questions and the repository carries both. A reader who concludes from this record that
the floors have become advisory has read it backwards.

**What it cannot distinguish**, said here because it is the shape of failure this repository
cares about: changed lines carrying no statement at all. A comment, a blank line and a signature
produce that reading, and so does a report written before the change. The tool refuses to call
it a pass and prints the report's date beside it, which puts the judgement on a reader rather
than on a silence.

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
