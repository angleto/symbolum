# 0031. A price a bound chose is not a price the claim asked for

- **Status:** accepted
- **Date:** 2026-09-18

## Context

`Prove` serves its propositional address with `Intuitionistic`, which costs no axiom, and falls to
`Propositional`, which costs `SELECT`, when the free calculus refuses. The free calculus refuses for
two reasons that are not the same thing: the goal is not intuitionistically valid, or the search ran
out of `Intuitionistic.Fuel`. Until this record, both fell the same way and the answer was the same
in both cases: a theorem, with the choice axiom under it, and nothing saying which of the two
happened.

`docs/adr/0023` wrote the defect down when it made the calculus serve the address, and declined to
repair it there, on the ground that it "would mean a report with two outcomes where `Prove` returns
one theorem, which is a change to what every caller reads". It also read the case as unobserved:
over the enumerated population of `PropositionalRouteSpec` — every propositional formula of at most
six nodes on two atoms — the deepest goal uses 7 of 256.

**Both halves of that reasoning were measured on 2026-09-18 and neither survived.**

The population was the wrong one. The enumerated formulas are small by construction; the address
takes any statement whose atoms are all bare propositions, and those can be as long as a caller
writes. On a family that grows — a chain of implications, intuitionistically valid at every length,
where only the size changes — consumption grows as `2n + 2` and the net is reached:

| links | the free route | what `Prove` returned |
|---|---|---|
| 126 | uses 254 of 256 | the theorem, at no axiom |
| **127** | uses **256 of 256** | the theorem, at no axiom |
| **128** | **cut short** | the theorem, at **one** axiom |

The edge is one link wide, and the two goals are the same claim written one link apart. So the case
is exhibited rather than possible.

And the cost was overstated. The callers of a `Prove` instance in `src/main` are **two**:
`Session.scala` and `Cost.scala`, plus twelve test files that construct one. "Every caller" is what
a type change sounds like, not what this one costs.

What the measurement does **not** say: that anything this repository holds reaches the net. Of the
library's 505 statements, 184 take this address and the deepest uses **9** of 256, and the corpora
cannot take this address at all, because `Minimal.reads` and `Minimal.declines` both want every atom
to be a bare proposition and a corpus statement names `real_of_num`, `+` and `<`. The net is reached
by what a caller can write, not by what is here.

## Decision

**`Prove.apply` answers `Prove.Outcome`, which has two cases**: `Settled(theorem)` and
`CutShort(theorem, search, depth)`. The theorem is the same object in both; what differs is why
`Derivation.axiomsOf` of it reads as it does.

**A case and not a field**, which is the shape `docs/adr/0026` chose at the twin site in
`Domain.close` four hours earlier, and for the same reason: a caller that reads only the settled case
stops compiling rather than believing a price. A field with a default would have let every existing
caller keep the old answer, which is the defect this type exists to end.

**The depth is reported, not only the fact.** `CutShort` names which search stopped and at what
depth, because what a reader has to know is that an arbitrary constant rather than the mathematics
decided this price. The depth is read off the refusal rather than written as `Intuitionistic.Fuel`:
`Intuitionistic.atDepth` rewrites the bound with the depth the run was actually given, so the
refusal is the only thing that knows it, and a figure copied from the constant would be the copy
that goes stale.

**The fall to the classical procedure stays.** Refusing instead would take away a theorem the system
can produce, and no rule here asks for that: the rule this repository writes is that a search may
add a theorem and must never take a refusal away. `Propositional` settles those goals correctly, and
the price is real — what was missing was the reason for it.

**Each surface says it**, and that sentence was a decision written as though it were a fact for a
day. `Cost.Report` carries `cutShort`; the notebook renders it beside the theorem, because
`Session.Entry.restsOn` computes a price from the theorem and cannot tell the two cases apart. What
did not follow from carrying the field is that anything read it: on 2026-09-18 the field had **no
reader at all** outside the notebook's own road, and `Cost.page`, which is what `Ask`, `Argument`
and `WhatAClaimCosts` print, did not mention it. The verification of card 011218be measured that by
putting the page of a 128-link chain beside the page of Peirce's law and finding them different in
the claim and in the inference count and in nothing else, both resting on the same `select`. So the
one surface a person reaches for from the command line still could not tell the two apart, which is
precisely what the fourth alternative below was rejected for.

The page carries the line since 2026-09-19, directly under the count it qualifies, and
`Cost.cutShortCaveat` is the one place the sentence is written: the notebook read a copy of it
until then, and two copies of one sentence on two surfaces is what this repository calls a fact
written twice. `CostSpec` asserts both directions at 128 links and at 127, which is the same pair
one floor up from the two `PropositionalRouteSpec` already had, and
`tools/verify/perturb-cut-short-prove.sh` fires each half at its own defect.

This is the part that is more work than the alternatives, and it is the work the alternatives avoid
by not saying the thing. It is also the part that looked finished while half of it was missing,
which is the argument for the pair of witnesses rather than for one.

## Consequences

**What is covered.** Any caller of `Prove` that settles a goal at the propositional address after the
free route was cut short now reads which bound stopped and at what depth.

**What is not, named rather than left to be found.** A cut-short *leaf* inside a chained proof is not
reported: `chained` takes the theorem alone through `Chaining`'s contract, so a chain whose obligation
was settled after the net bit reads as settled. Repairing that is a change to what `Chaining` hands
back, and it is not this one.

**What this record did not decide, and what answered it.** At 127 links the search uses the whole
net. The constant is doing real work at that edge and nobody had chosen 256 for that reason:
`Intuitionistic.Fuel` is "a net under a termination argument and not the argument", and the measure
in that class's comment falls on every rule, so the fragment terminates without it. Whether 256 was
the right number, or whether the net should exist at all now that the termination argument is
written down, was a question this measurement opened and did not answer.

**Card 87e74c7f answered it on 2026-09-22 and the answer is that it stays at 256**, with the
criterion it is chosen by written where the constant lives and asserted where the population is.
The criterion is a relation and not a number: **the fuel a goal needs never exceeds the goal's own
size**, one for each connective and one for each atom occurrence, measured exhaustively over every
formula on two atoms of at most seven nodes, 5618 of them, with the bound approached at 6 of 7. So
256 read forwards is the promise that a goal of at most 256 nodes is answered rather than stopped,
which is a sentence a reader can check a written claim against, and the edge above is the generous
reading of the same thing: the 127-link chain is 511 nodes and saturates the net at half that size.

That relation is also the thing the net exists to catch. A rule that stopped decreasing the measure
would show up as a goal needing more than its size, and `PropositionalRouteSpec` now goes red there
instead of the mistake arriving as an out-of-memory.

The two figures in this record and the one in that spec's older test are three different statistics
and all three are right: **7** is the least depth at which the whole population still answers as the
full net does, **9** is the deepest of the library's 184 addressed statements, and the per-goal
worst need over the enumerated population is **4** at six nodes and **6** at seven.

### Rejected

**Leaving it, with the measurement written beside the net.** That was the right answer while the case
was possible and unobserved, and `docs/adr/0023` took it on that basis. The witness removes the
ground for it, and the twin site had already decided the other way four hours earlier: two sites that
fall differently for the same reason are worse than two that fall the same way.

**Refusing when the free route is cut short.** It looks like the convention this repository already
writes down, that a tactic which cannot settle a goal must refuse, and it is not: the procedure
*does* settle. What did not settle is the cheaper route.
This would make the system weaker in order to make it honest, when it can be both.

**Carrying the caveat in `Cost.Report` alone, leaving `Prove` as it was.** Cheaper by one call site,
and it fails where a human reads: the notebook shows a price through `Session.Entry.restsOn`, computed
from the theorem and never passing through `Cost`. The defect would have survived exactly on the
surface a person looks at.

**A field on the theorem.** A `Kernel.Thm` is what the trusted base hands out and carries what the
kernel checked. A tactic's note about how a search went has no business on it, and putting it there
would make the trusted base carry something no kernel rule produced.
