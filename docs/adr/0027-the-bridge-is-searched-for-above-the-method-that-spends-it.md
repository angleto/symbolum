# 0027. The bridge is searched for above the method that spends it, one candidate at a time

- **Status:** accepted, extends 0024
- **Date:** 2026-09-18

## Context

`docs/adr/0024` decided how a claim about a domain that is not mathematics reaches the foundation's
arithmetic: the caller hands `Domain.Built.settle` a **theorem** — a library lemma, or a fact it
derived itself — and that theorem is specialised at the claim's own foundation-typed subterms and
joins the domain's axiom instances in the irredundant-core cut-down. `Attempts j` is never given a
value, so what is used about it has to hold for every number, and the arithmetic shows in the price
rather than being free.

That record names the search as the next piece of work and puts four conditions on it, which are
the constraints this one is decided under:

1. **Bounded.** The candidates are lemmas about the foundation constants the claim already names,
   not the library; the cut-down is `2n + 1` decisions, so every extra candidate is paid for twice.
2. **It reports what it used.** A conclusion reached by a route the reader cannot see defeats the
   one thing this tool is for.
3. **It refuses rather than guesses**, which is the rule every procedure in this repository follows.
4. **The accounting does not get worse.** A bridge found charges what a bridge named charges, and
   between two that both work the cheaper in axioms is worth choosing.

Three measurements on the standard chain, 2026-09-18, decide the shape:

1. **The search space of a real claim is not one constant.** The retry claim of `0024` is
   `!j:job. NUM_LT (Attempts j) 3 ==> ~(Abandoned j)`, and the foundation constants in it are
   **three**: `NUM_LT`, and `NUM_ONE` and `NUM_BIT1`, which are what the numeral `3` is built from.
   `Library.about` answers 64, 72 and 53 for those, so the union before any filtering is of the
   order of the whole library rather than of a handful.

2. **Most of that space cannot possibly carry anything, and the reason is exact.** A bridge is
   specialised at the maximal subterms of its binders' types that the claim names. A lemma binding
   a `num -> num`, of which the coding and the primes hold many, finds no such term in this claim,
   produces **no instance**, and therefore changes no decision `settle` makes. `BridgingSpec`
   measures the two counts against each other rather than writing either down.

   What that alone left was **128 candidates against a bound of 128**, and a peer's lemmas landing
   in `Peano` the same afternoon took it to 129 and turned the answer into a refusal for size. The
   lemmas about `NUM_ONE` and `NUM_BIT1` were most of it, which is a bound growing with every proof
   anybody writes about the number one: a bound on the wrong thing.

3. **A lemma that settles a claim is not always a lemma the claim needed.** A foundation constant
   can sit where the decision never reads it: `NUM_LT (Attempts j) 3 /\ Abandoned j ==> Abandoned j`
   is settled by every candidate in the library and by none of them, because the conjunction is
   discharged by its other half. A search reporting whichever candidate it tried first would be
   naming a lemma that did nothing, and condition 2 would be met in form and broken in substance.

## Decision

**The search lives in `Bridging`, above `Domain.Built.settle` and calling it, and it tries one
candidate at a time.** Concretely, five things and their limits.

**It is a file of its own rather than a mode of `settle`.** `Domain.scala` names no library, because
`0024` decided the bridge is a theorem and not a name: a caller whose bridge is a fact it never
published must be able to hand it over. Putting a search inside `settle` would put `Library`
underneath that file and take it away. What the arrangement buys beyond tidiness is that the
repository's rule about search — it may add a theorem and must never take a refusal away — holds
structurally here: every theorem `Bridging` returns was built by `settle`, and every refusal
`settle` gives is still what a caller naming its own bridge gets.

**The candidates are the lemmas about the constants the claim names, minus those that cannot
produce an instance and minus those about what a numeral is built from**, and the set is published
as `Bridging.candidates` so that a bound has a visible subject. The two exclusions differ in kind
and the file says so: the first is exact, and the second is a judgement that a claim naming `3` is
about the order rather than about the encoding, which loses a bridge that really is about the
encoding and names what it loses. `Domain.Structural` already draws that line for the connectives;
this is the same line one level down, at the literal. Above `Bridging.Candidates` the search is refused for its size rather than run,
and the refusal names the route `0024` built.

**Each candidate is tried on its own.** A claim needing two lemmas at once is refused, and the
refusal says so in those words, so that a reader is not left concluding the claim is out of reach:
naming both settles it.

**A bridge is reported only where the claim did not settle without it.** The control is `|- T` as
the bridge, which is a bridge that supplies no fact: a claim that settles carrying only truth had
inert arithmetic in it, and comes back with no bridge named at all.

**Between candidates that each carry the claim, the cheapest in foundational axioms is reported**,
then the one whose free route was not cut short, then the first by name; the others are reported
beside it as alternatives rather than dropped.

## Consequences

`docs/adr/0024`'s route is untouched. `settle` keeps its signature and its behaviour, every
existing call site is unchanged, and the search is a second entry point rather than a mode.

**The cost of an answer is now a population rather than a call.** One `Bridging.settle` is up to
`Bridging.Candidates` calls to `Domain.Built.settle`, each of them `2n + 1` decisions. The bound is
what keeps that finite and it is a bound on the **search**: a claim past it is refused here and
still settled by naming the bridge.

**A claim needing two bridges is refused where naming both would settle it**, which is a capability
this search does not have rather than one it removes. The combining search wants a measurement of
its own: the candidate sets here are large enough that handing the whole set to `settle` is over
`Domain.Instances` and a pairwise search is the square of a number in the hundreds.

**"Cheapest" is coarser than it sounds, and the measurement that says so is the one that nearly
went into this record the other way round.** The price is a **set** of axioms, so a bridge whose
extra step reaches only for something already in the column is free by this measure. The first
version of `BridgingSpec`'s expensive twin was the lemma detached against `p ==> p` proved by
`Propositional`, which spends `DOUBLE_NEGATION` and therefore choice — and an arithmetic lemma
already charges choice, so the two came back at **2 axioms against 2** and the search was choosing
between equals. The twin in the tree spends an axiom of the reals instead, which nothing about
`num` can already have. What this decides for a reader: an answer costing fewer axioms is really
cheaper, and two answers costing the same set may still have taken very different routes.

**`Domain.Instances` now counts the bridges, and it did not before.** `0024` says the cut-down
costs `2n + 1` decisions and that `n` counts the bridges too; the check in `instancesFor` counted
the domain's axioms alone, so a caller naming many bridges walked past the guard. It was found by
building this search's own rejected alternative as a test — the whole candidate set handed to
`settle` in one call — and watching it run for minutes instead of being refused in a step. The
count is computed the same way the instances are built, before any of them is built, which is what
the bound was for in the first place.

**`Found.bridges` is a second thing a reader has to read.** `Domain.Spending` reports axioms, and a
bridge is a theorem, so the price alone cannot say which fact carried the claim: the naturals' two
axioms are what every arithmetic lemma charges. A report that named the price and not the lemma
would be `0024`'s promise of visibility met halfway.

## Alternatives rejected

**Resolving a name inside `settle`, so that a caller passes `"NUM_LT_NOT_LE"`.** It is the smallest
change and it is the one `0024` already rejected, for a reason this record inherits rather than
re-argues: it puts `Library` under `Domain.scala`, and it shuts out the caller whose bridge is a
fact it derived by hand. A search above the method has neither cost.

**Handing the whole candidate set to `settle` at once and letting the cut-down find the needed
ones.** It is the obvious way to reach a claim needing two lemmas, it reuses machinery that already
exists, and it fails on both cost and reporting. On cost: the instances are a product, and the
candidate set of the retry claim is over `Domain.Instances` on its own, so `settle` refuses for size
before deciding anything — which is true **since** this work, because measuring this alternative is
what found the bound not counting bridges at all. On reporting: the cut-down does not publish which instances survived, so
the answer would name a price and no lemma, which is the condition this work was given.

**Reporting the first candidate that works.** Cheaper by the tail of the search and it breaks
condition 4: between two derivations of one statement, the one that costs an axiom more is as likely
to be tried first as the other, and nothing in the report would say a cheaper route existed.
`BridgingSpec` builds exactly that pair — the same statement proved a second time through
`Propositional`, which charges the choice axiom — and asserts the search passes it over.

**Reporting the bridge without the truth control.** It would have made the report a statement about
the order candidates are tried in rather than about need, in exactly the case where the claim's
arithmetic is decoration. Measurement 3 is that case, and it is not exotic: a claim carrying a
condition it does not use is the ordinary shape of a rule written by a person.

**Leaving it at `0024`, so that the bridge is always named.** Defensible, and it is what the code
did until today: a caller who knows their domain knows which lemma relates its constants. What it
costs is measured rather than theoretical, and it is the shape of every real criterion: the caller
has to know that `num` has two orders and that `NUM_LT_NOT_LE` is what relates them, which is
knowledge about this library rather than about their rule.
