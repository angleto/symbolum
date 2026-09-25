# 0047. A report stops at a cited fact, and a checker does not

- **Status:** accepted
- **Date:** 2026-09-25
- **Decides:** the choice `0016` measured and left open

This record decides where a report on a proof stops walking: at a fact another development
published, which the proof now records as a citation. The checker still replays everything. It
names what that bought on the first quotient, what it cost in the trusted base, and what it does
not reach.

## Context

`docs/adr/0016` measured, on 2026-09-20, what a proof record costs once the reals are built rather
than assumed. An asserted axiom has `Derivation.size` 1. The median published fact of `Integer`, the
first quotient, was 11107 nodes, and the nine facts of `Inclusion`, which are what a claim about a
real will carry, ran from 12827 to 24362. The construction stacks three quotients, each carrying
the ones below it by identity, so 10^5 to 10^6 nodes per theorem about a real was the extrapolation.

It named two mitigations and measured which one answers the growth. `Cost` walks a report's graph
three times, in `axiomsOf`, `size` and `census`, and `Check` and `foreignTo` walk it again where a
caller asks. A memoised walk is a constant factor of about three and leaves the walk where it is.
A boundary at a cited fact bounds the graph a report reads. The choice was left to Angelo because
the second is near the kernel. On 2026-09-25 he chose the boundary.

## Decision

**A published fact is cited, and a citation is a node of the proof.** `Kernel.cite(name, theorem)`
returns the same sequent with `Derivation.Citation(name, theorem)` as its record. It infers nothing:
the sequent is the one given, so nothing is believed that was not already. `Published.cite` in
`modules/logic` applies it to a development's `facts` where the development is built, and every
class holding a `facts` map does so. `LibrarySpec` asserts it twice, over the library at run time
and over every such field in the sources, because two developments merged the same morning had
left the line out and nothing else would have said so. A
consumer reads the fact through `fact(name)` and gets the citation, so a proof that uses a lemma
of the development below holds one node for it.

It is applied where a fact is published and not where it is read, because a citation has to be one
object for the sharing to hold. Two readers who each built their own citation of one fact would put
two nodes into a proof that used both, and each would work out the axioms under it again. A fact
re-exported by another development under the same name, which `Order` does for `Positivity`, is
left as it is rather than cited twice.

**The walks of a report stop at a citation, and answer for the whole proof all the same.**

| walk | what it does at a citation | why |
|---|---|---|
| `axiomsOf` | adds the axioms the citation keeps, worked out once on first asking | the answer is about the whole proof and is one set per fact |
| `size`, `census` | counts it as one inference, `Citation` in the census | what a report is about is the proof's own work |
| `foreignTo` | goes through `axiomsOf` | the same answer, from the same summary |
| `restingOn` | walks through it, paying the whole graph | the facts it is asked about are any named collection, which no summary kept on the citation could answer for |

A theorem that is itself a citation is walked from what it cites. Asking a published fact for its
size asks about its proof, and stopping at the root would answer one for every fact in the library.

**A checker replays through it.** `Derivation.premises` of a citation is the fact, so `Proof.write`
writes the cited proof once, before the citation, and `Check.proof` walks into it. The text gains a
rule, `cite NAME` with one premise, and the format is `proof 2`. The checker's own rule is that the
citation's sequent is its premise's, hypotheses included, which `SideConditionSpec` exercises.

**The trusted base bound goes from 1200 lines to 1220, for the first time.** The four files were
1197 lines with the bound at `< 1200`, and `cite` is eleven lines with its comment, because a `Thm`
can only be built inside `Kernel`. `0006` and `0008` spent headroom and did not raise the bound;
this one had three lines of headroom and needed eleven, and on the day it landed the new bound
leaves thirteen.

## Measured

On 2026-09-25, from `IntegerSpec`, which asserts the readings rather than keeping them here. "Read"
is `Derivation.size`, what a report walks. "Replayed" is the number of step records in
`Proof.write`, what a checker walks.

| | before, 2026-09-20 | read | replayed |
|---|---|---|---|
| `INT_SAME_REFL` | 38 | 38 | 39 |
| `INT_EQUAL` | 7687 | 1443 | 7696 |
| the 44 facts of `Integer`, by quartile | 9784 / 11107 / 12775 | 952 / 1445 / 2163 | 9945 / 11620 / 12857 |
| the 9 facts of `Inclusion` | 12827 to 24362 | 3925 to 5975 | 12837 to 24386 |

The replayed column is the old one plus the citations, which is the control: the graph did not
change, only where a report stops reading it.

**Over the whole library.** Every published fact of
`Chain.standard`, 716 on the day, read by the three walks `Cost` makes, against the same three
walked through every citation, which is what they were before. In one JVM, interleaved over three
rounds after a warm-up that also filled every citation's summary: **12.4 seconds against 47.8**, a
factor of 3.9, and 5548170 nodes read against 15370388 replayed. The wall clock is of that
afternoon and the ratio is the reading, since both sides ran beside each other on one machine.

It is not uniform, and the spread is the part to carry. Where a development builds on facts, the
read median falls far below the replayed one: `Deduction` 1466 against 97294, `Integer` 1445
against 11620, `Primes` 3169 against 28004. Where its proofs are mostly its own work the two stay
close: `Root` 44850 against 48961, `Derivative` 36047 against 46903. Those are the analysis
developments, whose inferences come out of `Linarith` and `Ring` run inside each proof, and no
boundary at a published fact makes a proof's own work smaller. This was a probe and is not kept:
the node counts it could assert are asserted at the first quotient by `IntegerSpec`, and a wall
clock is asserted nowhere in this repository, deliberately.

**Inside `ReachSpec`, which is where a report is actually paid for, the saving is small.** This
record called the library measurement "where the report is paid" until the verification of the
card said it was not, and card 2a48d6d0 measured it there on 2026-09-25: the 23 statements of
miniF2F the prover settles, re-proved and read the same two ways. Nodes: **199912 read against
251374 replayed**, with 119 citations among them, a factor of 1.26 where the library's was 2.8,
because a proof the tactics produce is almost all its own work. Time, in one JVM over three
alternated rounds: the three accounting walks **872 ms against 1082**, and `Reach.of` **3177 ms**
on both sides, so a report's walks as a whole are **4049 ms against 4259**, about five per cent.
`ReachSpec` asserts the node half; the time is printed.

**The walk that dominates is `Reach.of`, and the boundary does not reach it.** It is
`Library.restingOn`, which the decision above leaves walking through every citation because the
facts it asks about are any named collection. On these statements it costs three times the three
accounting walks together. Bounding it would take a summary per citation of the named facts under
it, which is a different decision about memory and about what `Reach` means, and it is card `0c00cac9`
rather than a sentence here.

**What moved elsewhere in the repository, read off the suite rather than predicted.** The figures
that count a report are smaller wherever a proof uses a fact another development published: the
ring corpus census in `docs/evaluation.md` from 122862 to 105271, with 51 citations in it; `Family`'s
quartic from 29456 to 22869; the six facts of `Word` from 1214–3452 to 173–831, which is `Product`
no longer counted under them. The figures that count a replay rose by the citations and nothing
else: induction over the naturals 625 to 626. The generated pages, `docs/theorems.md` and
`docs/examples.md`, print the report's count and now say that a cited fact is one of it.

**What did not move is as informative.** The size of the excluded middle's derivation, which
`ClassicalSpec` spells from the measurement, held, because `Classical` proves it from rules of the
logic rather than from another development's facts; so did every figure pinned in `modules/logic`,
`modules/kernel` and `modules/checker`.

## What it does not reach

**A theorem handed across in a field other than `facts`.** A procedure holding a rule set, or a
development holding a law as a field, hands those theorems up uncited, and a report walks them down
to the nearest citation. That is why a fact of `Inclusion` still reads four to six thousand nodes
with two to eight citations in it: its own proof and the lemmas of the procedures it ran, which
were proved from facts that are cited. The growth is per stage now rather than the sum of the
stages below, and a stage that hands most of its work across in fields reads more than one that
publishes it.

**The checker.** It replays the whole graph, as before, because a checker that trusted a citation
by name would be trusting whatever produced the name. Checking a library once and resolving a
citation against that record is possible, and it would make the record a second thing to believe.
That is a decision about the trusted base, and it is not taken here.

**The memoised walk.** A constant factor on what a report reads, and it is not built: what is left
to read is the proof's own part.

## Rejected

- **A table beside the proof naming which theorems are boundaries**, which would have kept the
  kernel untouched. It is global state keyed by object identity, it has to hold its keys weakly or
  retain every theorem ever cited, and a proof written out or walked by a reader that did not
  consult it would be read differently. A boundary should be in the proof it bounds.
- **An empty instantiation as the marker**, which the kernel already builds and records with the
  same sequent. It cannot carry a name, and a walk could not tell it from a real one.
- **Citing where a fact is read.** Every read would build its own node, which undoes the sharing.
