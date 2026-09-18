# The perturbation harnesses, one per card, and the one kind of instrument kept here

Each file beside this one puts a delivered guard back at the defect it was written for: it
substitutes a literal string in a source, runs the suite that should go red, and restores the
bytes. A harness is the executable half of a verification recorded on a Mycelium card, and every
one of them names its card in its first line.

**What belongs here is a perturbation and nothing else.** The rule that decides it is not about
tidiness and is worth stating in one sentence, because the alternative is a directory that fills
with everything a verification touched:

- a **perturbation** cannot be a test. It edits a source, runs the suite, and puts the source
  back; no spec can do that from inside the run it is part of. So if it is not kept, it is
  rewritten from scratch next time, and it was rewritten twice for one card on 2026-09-18.
- a **measurement** can be a test, and if it is worth keeping it is an assertion in a spec. A probe
  that counts what a theorem rests on, or prints what a surface says, is telling you that nothing
  asserts it. Write the assertion. A probe parked here instead is the easier of the two and would
  be chosen, which is how a repository ends up with instruments where it wanted guards.
- an **exploration** — sizing a population, finding where a bound bites — is thrown away when it
  has answered. Its result belongs in the card, with the criterion it counted by.

The second and third go in `scratch/`, which is ignored by git and in no sbt source set, and they
die with the checkout. That is the intended outcome for both.

## Why these are versioned when `scratch/` says a probe is not

Because they survive, and that was measured rather than assumed. On 2026-09-18 at `ba3a60d`, the
eight harnesses collected here named **twelve** perturbation targets between them, written across
two days against files that changed heavily in the same window. **Eleven of the twelve still
applied exactly once.** The one that refused is `chained(goal).orElse(underHypotheses(goal))` in
`Prove.scala`, and it refused because that line was rewritten by the card whose harness sits next
to it — which is the refusal working, not the harness rotting.

That number is what separates this directory from a graveyard. A harness that stops applying is
not silently wrong: the perturbation tool refuses a substitution that did not apply rather than
running the suite against unperturbed code, so a stale harness fails loudly and says which string
moved.

## How a harness leaves

Three ways, and the first is the common one:

1. **The string it names moves.** Repair it in the change that moved the string, the way any other
   reference is repaired, or delete the harness with the card it belongs to.
2. **Its card is closed and its guard became a spec.** Then the harness has nothing left to prove
   and goes.
3. **The code it perturbs is gone.** So is the harness.

Nothing here is pruned on a schedule, and nothing should be: a directory that gets swept by age
loses exactly the harnesses that have been stable longest.

## Running one

    PERTURB=/path/to/perturbation-tool sh tools/verify/perturb-derive.sh

`PERTURB` is a tool that captures the bytes of a file, substitutes one literal string for another,
runs a command, restores the bytes and verifies the restore. **Its path is not written down in this
repository**, which is the same arrangement `tools/sbt` uses for the build wrapper and for the same
reason: the instrument belongs to the machine the work happens on, not to the checkout. A harness
run without it refuses by name rather than starting.

`WT` defaults to the checkout the script sits in and is overridden to point a harness at another
one. Give it a tree of its own: a perturbation edits a tracked file, and a peer reading that file
during the window sees a broken source. Two of these edit `CLAUDE.md`.

Output goes to `$WT/scratch/verify/out`, which is ignored.

## What runs these, which is nobody

Not CI, and not the suite. A harness asserts that a guard fires at a defect that is **not** in the
tree, so it can only pass by first making the tree wrong; a gate that did that on every push would
be editing the sources of a shared machine. They are run by hand, when a card is verified, by
somebody who is not the author. `.github/workflows/ci.yml` names the shell tools it runs one at a
time and says why it names them rather than the directory; these are not among them.

## The control comes first, and it is not a formality

A red under a perturbation proves nothing unless the same command is green without it. Every
harness here runs the unperturbed suite first and logs it under `0-control`. The perturbation tool
says of itself that it does not decide whether a failure is the **right** failure: that judgement
is the reader's, and it is made by checking that the test which went red is the one the card
names and that its neighbours stayed green.
