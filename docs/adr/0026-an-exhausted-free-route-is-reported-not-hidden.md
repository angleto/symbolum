# 0026. A free route that ran out of net is reported, not hidden behind the price it fell to

- **Status:** accepted
- **Date:** 2026-09-18

## Context

`Domain.Built.settle` decides a claim about a domain that is not mathematics, and what it sells is
the accounting: `Domain.Spending` says which of the domain's own axioms the conclusion spent and
which axioms of the foundation underneath it. `docs/adr/0022` is why the logical half of that price
is normally nought — `Intuitionistic` decides the fragment an ordinary argument about a domain lives
in and certifies it out of the derived rules alone — and `docs/adr/0024` is why arithmetic, when a
claim reaches it, is visible rather than free.

`Domain.Built.close` asks that calculus first and the classical decision second. The classical one
closes with `DOUBLE_NEGATION` and therefore rests on `SELECT`, so the order is by price and the
report is what says which route answered.

The calculus refuses in two ways and only one of them is about the claim:

- a refusal because the claim is not intuitionistically valid, which is a fact about it;
- `BoundReached`, carrying `Standing.Exhausted`, because `Intuitionistic.Fuel` ran out. That is a
  fact about the search. The fuel is a net under a termination argument rather than the argument
  itself, so hitting it says nothing in either direction.

Both were read through `toOption`, so both were the same `None`, and both fell to the classical
route. A claim whose free route was cut short therefore came back **settled at one axiom, with
nothing in the answer saying the free route had been truncated rather than decided against**. It is
the same shape `docs/adr/0023` records at `Prove`'s propositional address, at a second site; the
card that measured the first named only that one.

### Whether anything reaches the net, which is what decides the shape of the change

`docs/adr/0023` left the first site alone on a measurement: over the 1114 propositional formulas
`PropositionalRouteSpec` enumerates, no goal reaches the net and the deepest needs **7** of the 256.
That population is formulas of at most six nodes on two atoms. **What `close` builds is not from
that population**: it is an implication chain carrying one specialised axiom per link, and the
number of links is bounded by `Domain.Instances`, which is 64. A figure taken on six-node formulas
says nothing about a chain of sixty-four, and this record's first act was to stop citing it as
though it did.

Measured on 2026-09-18 against `423c12f`, on the chains `close` itself builds, one axiom per link,
every member of every family a chain of modus ponens and so intuitionistically valid at every
length. The atoms are the width of each axiom's antecedent, the links are how many axioms the claim
walks, and the links are the quantity `Domain.Instances` bounds at 64:

| atoms in the antecedent | 24 links | 32 links | 40 links | 48 links | 64 links |
|---|---|---|---|---|---|
| 1 | free | free | free | free | free |
| 2 | free | free | free | free | **cut short** |
| 3 | free | free | free | — | — |
| 4 | free | **cut short** | **cut short** | — | — |
| 5 | free | **cut short** | **cut short** | — | — |

The criterion is the one the claim needs rather than the one that is convenient to count: a claim
**reaches the net** when the calculus refuses the bridge with `BoundReached` naming its own search,
which `Domain.Verdict.CutShort` is what reports. Reading it off the spending instead would count a
claim that genuinely needs classical logic as one that ran out of net, which is the collapse this
record is about.

So it is reachable, inside this method's own bound, on a claim whose only difference from a free one
is size. What costs the search is the weight of what it takes apart rather than the count of axioms,
which is the first row: sixty-four axioms are free when each has one atom in front of it.

**The two-atom row is why the measurement went on past its first answer.** It puts the edge at
sixty-four links, which is `Domain.Instances` to the link, and a reading at the boundary supports
"inside the bound" on one point: a small change in the calculus's rules moves it to the other side
and takes the finding with it. At four atoms the edge is between 24 and 32, half the bound, and
five agrees with four. That is the family the guard is built on, and the margin is why.

## Decision

**The fall stays and the answer says it happened.** `Domain.Verdict` gains a fourth case,
`CutShort(theorem, spending, why)`, returned exactly where `Settled` would have been returned when
the intuitionistic attempt on the full instance set refused with `Standing.Exhausted`.

The refusal is read once, on the full set, before the route is fixed: that is the call whose answer
decides the route, and every later call inside the cutting-down is the chosen route's own and
answers a question about a subset. `why` is the calculus's own message, verbatim, naming the search
and the depth it was given.

## Consequences

**A caller that matches `Settled` alone stops compiling.** That is the point of a case rather than a
field. `Domain.Verdict` is matched in four places, all of them tests, and each now says what it does
with a price that carries a caveat.

**Nothing loses a theorem.** The classical route still runs and the theorem still comes back, with
the same `SELECT` it always cost. What changes is that a reader of the accounting is told the axiom
may be the net's rather than the claim's — `Intuitionistic.Fuel` is not a knob, so neither this
method nor its caller can find out which by asking again.

**`DomainTheorySpec` finds the length where the free route is lost rather than pinning it.** It
bisects the four-atom family for that length, asserts it on both sides of the edge, and asserts that
it is **strictly** less than `Domain.Instances`, which is the claim; the number itself is a property
of the calculus's rules and would move for reasons that are not defects. Beside it, the one-atom
family at the same length is asserted still free, so the instrument is reading weight rather than
size, and the excluded middle over a domain atom is asserted `Settled` at choice rather than
`CutShort`, so "I stopped" and "it is not so" are still told apart where the classical route is
right. The bisection costs about ten seconds of the module's suite.

**Rejected: refusing instead of falling.** A claim whose free route was cut short is a claim the
classical decision really does settle, and refusing it would trade a theorem for a caveat. The
caller cannot act on such a refusal either: the fuel is not a knob and there is nothing to raise.

**Rejected: a field on `Settled`, or a note inside `Spending`.** The second is worse than it looks:
`Built.spends` builds a `Spending` from a theorem alone and knows nothing about routes, so the field
would be `None` there in the sense of "not asked" while meaning "not cut short" here, which is the
same collapse one level down. The first keeps the compiler's help and loses the reading: a price
that needs a caveat and a price that does not are two answers.

**Rejected: raising the net, or making it grow with the formula.** `Intuitionistic.Fuel` is
documented as not a knob and nothing in the repository passes anything but the default. A net
derived from the sequent's own weight is the interesting version and it is not available for free:
the termination argument is a multiset ordering, which bounds nothing linearly, so a fuel computed
from the formula would be a number with an argument nobody has made yet.

**What this does not cover.** The other site is unchanged: `Prove` at its propositional address still
hands an exhausted goal to the classical procedure and returns one theorem, which is
`docs/adr/0023`'s open consequence and a change to what every caller of `Prove` reads. And a
`Countermodel` or a `Refused` coming back after an exhausted free route does not carry the note:
both are the classical decision's own answers about the claim, where this case is about a price.
