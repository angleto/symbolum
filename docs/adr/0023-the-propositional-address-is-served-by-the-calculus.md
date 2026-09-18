# 0023. The propositional address is served by the calculus, and the gate is the address

- **Status:** accepted
- **Date:** 2026-09-18

## Context

`docs/adr/0022` built `Intuitionistic`, Dyckhoff's contraction-free calculus, and made `Minimal` a
gate in front of it: the fragment with no negation in it, published as a promise, with the search
delegated. It rejected "leaving `Minimal` and adding this beside it" on the ground that two searches
for one question is one too many, and that rejection stands.

What it did not decide is which of the two `Prove` asks at its propositional address, and what
`Prove` did was ask `Minimal`. The consequence is arithmetic on the two facts:

- `Minimal.prove` **is** `Intuitionistic.prove` behind a test for a negation. Anything the gate
  proves, the calculus under it proves, identically.
- A goal with a negation in it is refused by the gate, falls through to `Propositional`, and comes
  back resting on `SELECT`, because that procedure's last step is `DOUBLE_NEGATION`.

So a goal that intuitionistic logic settles for nothing was being settled for one axiom whenever it
had a negation in it, which is the shape a claim about the world is made of. The same trade `0022`
measured on `DomainTheorySpec` and repaired for `Domain.Built.settle` was still being made by every
caller that goes through `Prove`, which is `Ask`, `Cost`, `Notebook` and the corpus suites.

The front page had already been rewritten to call `Minimal` "a fragment gate rather than a search of
its own" while `Prove.Search` listed it as a search and `Prove` asked it as one. One fact in two
places, disagreeing.

### What it is worth, measured

Two populations, answering different questions, both run on 2026-09-18 against `6554615`.

Over the propositional formulas themselves, every one of at most six nodes on two atoms:

| | count |
|---|---|
| formulas | 1116 |
| at `Prove.Address.Propositional` | 1114 |
| carrying a negation or falsity | 958 |
| classically provable | 188 |
| classically provable **and** carrying a negation | 152 |
| of those, provable intuitionistically | **58** |
| of those, classical-only (`p \/ ~p` and relatives) | 98 |
| proved by `Minimal` and **not** by the calculus under it | **0** |

The last row is what decides the shape of the change and the 58 is what it is worth: those goals
move from one axiom to none, and the 98 are why the classical procedure keeps a job.

Over what this repository already holds and already measures, which is the population the card
asking for the work named: the library of `Chain.standard` is 505 statements, 184 at this address,
**two** of them carrying a negation, and both are `Classical`'s own — the excluded middle and double
negation, classical by construction. It read 503 when this record was written, hours earlier the
same day, and 505 is `Order` gaining two: the denominator is a property of the library and moves,
the 184 and the two are properties of the address and did not. The Mathlib ring corpus and the statable slice of miniF2F put
**nothing** at this address at all. That zero is a fact about those populations rather than about
the change: they are arithmetic, and a goal reaches this address carrying a negation only where
every atom is a bare proposition. Read as "the change buys nothing" it is an absence reported by an
instrument pointed at a subject that cannot contain the thing.

## Decision

**At the propositional address `Prove` asks `Intuitionistic`, then `Propositional`. `Minimal` stays,
as the address.**

`Prove.addressOf` is where the gate is spent: its `reads` and `declines` are what put a goal at this
address in the first place, and `declines` is the half that recognises a statement of bare
propositions with a negation in it. So the gate still decides which goals are propositional; what it
stopped deciding is the goal.

`Prove.Search.Minimal` becomes `Prove.Search.Intuitionistic`, which is the enumeration of what a
prover reaches catching up with what it reaches. `MinimalSpec` is unchanged and so is `Minimal`: its
published fragment, its refusal and its promise are what `0022` left them.

The order is by price and that is now written where the order is. On the goal both take,
`(p /\ q) ==> (q /\ p)`, the calculus costs 182 primitive inferences and no axiom and the classical
procedure costs 1236 and the choice axiom. The theorem is the same term either way; what differs is
`Derivation.axiomsOf`, and the cheapest procedure that settles the goal is the one whose theorem
comes back. `Cost` reports the price of what it was handed and names no procedure, which stays true
precisely because the order is by price: naming the procedure as well would be a second way of
saying the same thing, and the one that goes stale.

## Consequences

**A goal with a negation that intuitionistic logic settles comes out of `Prove` resting on
nothing.** `ProveSpec` carries `~(p /\ ~p)` with both prices beside each other, so the zero is read
as a price and not as an absence, and `RefusalSpec` proves the same goal through `Prove.standard`,
which has no classical extension at all.

**One refusal changed meaning and was rewritten rather than patched.** A prover with no classical
extension used to refuse `p \/ ~p` by naming the negation, and that was the actionable fact while
the negation really was the boundary. It is not: `~(p /\ ~p)` is proved here with two negations in
it. What stops `p \/ ~p` is the caller's configuration, so that is what the message names, and
`RefusalSpec` asserts the word "negation" is **absent** from it. A refusal that stopped short keeps
its own message verbatim: `Standing.Exhausted` and `Standing.Unread` are the distinction
`LogicError` exists to hold, and rewriting a bound that was reached into a statement about the goal
would collapse them.

**Nothing pinned moves.** No lemma of the library changes price, no corpus figure moves, and
`docs/evaluation.md` regenerates to exactly what it held. What moved is the two document rows that
described the routing, and they moved because they were describing it.

**The figures above are a test and not a probe somebody ran once.** `PropositionalRouteSpec` builds
the enumeration, asserts every count in the table, puts all 58 to the prover and reads
`Derivation.axiomsOf` empty on each, and asserts the same 58 cost one axiom on the route they used
to take. It runs in about five seconds, so it is in the ordinary suite rather than behind the
`Corpus` tag. Both directions are asserted non-empty: a calculus that proved nothing and a calculus
that proved everything would each satisfy one half of the argument and neither satisfies both.

**Rejected: inserting the calculus as a third step, which is what the card asked for.** `Minimal`
first, then `Intuitionistic`, then `Propositional` runs the same search twice on every negation-free
goal that fails, because the first step is the second behind a test. The measured 0 in the table
above is that duplication seen from the other side: there is no goal the first step contributes.
Avoiding the waste means re-deriving the gate to decide whether the second step is a new question,
which is machinery bought to preserve a distinction that costs nothing to drop.

**Rejected: leaving it and documenting the exception.** That was the live option, and a card was
open for it: the front page's exception sentence — "nothing routes a goal there" — was prose beside
a guarded enumeration, and deleting the word `Intuitionistic` from that row would have left the gate
green. Anchoring the sentence would have frozen a wording to defend a routing that was itself the
defect. The sentence is gone because what it described is gone.

**Rejected: making `Minimal` route to the calculus itself.** That is `Minimal` losing its published
fragment, which is the thing `0022` decided it keeps. A caller that wants "the fragment that costs
nothing and has no negation in it" is asking a real question and there has to be somewhere to ask
it; `Prove` is simply not that caller.

**What the net costs, which nothing else here says out loud.** `Intuitionistic.Fuel` is 256 and is
a net under a termination argument rather than the argument, so a goal that reaches it comes back
`BoundReached`, carrying `Standing.Exhausted`. Where there is a classical procedure to ask, such a
goal is handed to it and may come back proved, at one axiom, and **nothing in the answer says the
free route was cut short rather than decided against**. That is one axiom charged where a larger net
might have charged none, and it is the one place this routing can quietly overpay. It is not
repaired here: it would mean a report with two outcomes where `Prove` returns one theorem, which is
a change to what every caller reads. Where there is no classical procedure the distinction **is**
kept, because the branch that rewrites the refusal leaves an `Exhausted` one verbatim.

**What this does not buy.** Nothing here reaches a quantifier, an equation between numbers, or a
constant of the foundation, exactly as `0022` says. The 98 classical-only formulas still cost an
axiom and there is no cheaper closing step for them, which `0022` argues from Glivenko. And an atom
is still given no meaning, so a goal valid for a reason living inside an atom is refused here as
though it were not valid at all.
