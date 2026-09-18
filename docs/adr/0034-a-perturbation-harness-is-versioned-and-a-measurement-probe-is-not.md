# 0034. A perturbation harness is versioned and a measurement probe is not

- **Status:** accepted
- **Date:** 2026-09-18

## Context

Two written instructions governing this repository appeared to contradict each other, and on
2026-09-18 a session resolved the contradiction by violating one of them.

`CLAUDE.md` says a probe goes in `scratch/`, which is ignored by git and in no sbt source set. The
workflow station a unit of work passes through before it closes says the opposite about the same
artefacts: *"the tests written for the verification stay in the repository, not in the session that
wrote them, and they are what the next round re-runs."*

A session verifying `011218be` wrote three instruments, obeyed the second instruction, and had to
force-add them past `.gitignore` to do it. Its checkout was then abandoned with that commit
reachable from no other ref. On the same evening two sessions independently built the same probe
for that same card within three hours of each other, because the first one's copy was not anywhere
the second could find it.

**The contradiction is not real, and the measurement that shows it is a census of what the
instruments actually are.** Counting `scratch/verify` on the shared checkout on 2026-09-18:
fourteen entries, of which **eight are perturbation harnesses**, four are measurement or
exploration files carrying three instruments between them, one is a README and one is an ignored
output directory. The two kinds of instrument have opposite properties, and calling both of them a
probe is what made the two instructions look incompatible.

A **perturbation** puts a delivered guard back at the defect it was written for by editing a source,
running the suite and restoring the bytes. It cannot be a spec: no test can do that from inside the
run it is part of. It is therefore the only kind of verification instrument that is lost when it is
not kept, and it was rewritten twice for one card that evening.

A **measurement** — what a theorem rests on, what a surface prints — can be a spec, and when it
finds something it is telling you that nothing asserts it. Both measurements that mattered that
evening were of exactly this shape: a probe counting the axioms under the `Collatz` part-C facts,
and a probe printing the page `Ask` renders. In both cases the finding was *no test asserts this*,
and in both cases the repair is an assertion, not a parked probe.

## Decision

**A perturbation harness is a versioned tool. It lives in `tools/verify/`, one file per card, and
names its card in its first line.**

**A measurement probe and an exploration are not kept.** They stay in `scratch/` and die with the
checkout, which is the intended outcome. A measurement worth keeping is written as an assertion in
the spec that should have carried it; an exploration's result belongs in the card, with the
criterion it counted by.

`CLAUDE.md`'s rule is unchanged in substance and gains the distinction. The workflow station's
sentence is satisfied without weakening it: what it asks to stay in the repository is a test, and a
test is a spec — the harness is the one instrument that cannot be one, so it gets a home of its
own rather than an exemption.

Three consequences of the move, each of which is a change and not a copy:

- **The private paths are gone.** The harnesses invoked a perturbation tool and a build wrapper by
  absolute path under a directory that is not part of this repository and is not delivered with it.
  The build wrapper is replaced by `tools/sbt`, which is this repository's own entry point and
  already decides whether a build goes under the machine's cap. The perturbation tool is supplied in
  `PERTURB` with no default, and a harness run without it refuses by name. That is the arrangement
  `tools/sbt` already uses for `SYMBOLUM_BUILD_WRAPPER`, decided for the same reason.
- **The stale defaults are gone.** Five of the eight defaulted `WT` to a worktree that no longer
  exists. They now derive the checkout they sit in. Versioning them without this would have
  committed five references to directories nobody can open.
- **Nothing runs them.** Not CI and not the suite. A harness can only pass by first making the tree
  wrong, and a gate that did that on every push would be editing the sources of a shared machine.

## Consequences

**The directory is kept from becoming a graveyard by the instruments themselves rather than by a
sweep.** The perturbation tool refuses a substitution that did not apply rather than running against
unperturbed code, so a harness whose string has moved fails loudly and names the string. Repairing
it belongs to the change that moved the string, which is the discipline any other reference in this
repository is already under.

**What justifies keeping them at all is a measurement and it is written down so it can be retaken.**
At `ba3a60d` the eight harnesses named twelve perturbation targets between them, written across two
days against files that changed heavily in the same window, and **eleven of the twelve still applied
exactly once**. The twelfth refused, and it refused because the card whose harness sits beside it
had rewritten that line — the refusal working rather than the harness rotting. If that ratio ever
falls far, the decision to version them is the thing to reconsider, and the count is how.

**The cheap reading of this record is the one to avoid.** It does not say "keep what a verification
produced". Of the twelve instruments in the census, the eight harnesses are kept and the three
measurements and explorations are not, and the three are the ones a session is likelier to reach
for next. Parking a probe is easier than writing the assertion it proves is missing, so a rule that
allowed the parking would get the parking, and the repository would accumulate instruments where it
wanted guards.

**One thing a reader should not conclude.** A green harness is not evidence a guard is good. It says
the guard fires at the one defect the harness reconstructs, and the perturbation tool says of itself
that it does not decide whether a failure is the right failure.

## Alternatives rejected

**Leave it as it stands.** This is what had been running and its cost is measured rather than
predicted: one abandoned checkout holding a force-added commit against `.gitignore`, one probe built
twice for one card in three hours, and a session that could not obey both written instructions at
once. The instructions would also stay in contradiction, which is the part that does not decay on
its own.

**Rewrite the workflow station to say a verification instrument is throwaway.** It would remove the
contradiction in one line, and it is a decision against the data: eleven of twelve targets survived
two days of churn on the files they name. It would also keep paying the rewriting cost that the
census already shows being paid.

**Version all of `scratch/verify` under `tools/`.** The comfortable version of this record, and it
is wrong for the reason the third consequence above gives. It would keep five probes whose findings
belong in specs, and it would let a session satisfy the verification station by parking an
instrument instead of writing the assertion.

**Vendor the perturbation tool into this repository so the harnesses are self-contained.** It is a
tool that belongs to the machine rather than to the checkout, the same as the build wrapper, and
`docs/adr` has no record turning that arrangement around for `tools/sbt`. Doing it here for one
directory would create a second convention for the same kind of dependency.
