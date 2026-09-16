# 0022. The intuitionistic propositional fragment gets its own decision procedure

- **Status:** accepted
- **Date:** 2026-09-16

## Context

A claim about a domain that is not mathematics is settled here by an argument that is
**propositional over that domain's own assumptions**, and `DomainTheorySpec` is the case everything
below was measured on: a release gate, four axioms, one conclusion, no arithmetic anywhere.

Until this record there were two procedures for such a claim and neither covered it at its cost.

`Minimal` searched the propositional fragment **with no negation in it** and reached zero axioms.
That is the fragment nobody's rule is in. A criterion about the world is made of negations — *a
change that has not been reviewed does not ship* — so the procedure that was free refused the
statements it was written for.

`Propositional` decides classical validity and certifies it, by putting the goal to the solver in
`modules/sat` and re-deriving the refutation one resolution step at a time. Every step of that
replay is intuitionistic **except the last**: the refutation concludes falsity from the negated
goal, which gives `~~goal`, and `Classical.DOUBLE_NEGATION` turns that into the goal. So it costs
`SELECT`, the choice axiom, on every theorem it produces.

The consequence was written down in `DomainTheorySpec` before it was repaired, and is the
measurement this record acts on:

| route | the theorem | domain axioms spent | foundational axioms spent |
|---|---|---|---|
| by hand, out of the derived rules | yes | 1 of 4 | **0** |
| through `Propositional` | the same | 1 of 4 | **1**, `SELECT` |

The hand derivation is intuitionistic throughout: assume the three denials, suppose the change
ships, take the disjunction the fourth axiom gives, contradict each case. Nothing in it is
classical. A tactic that reaches the same theorem and charges an axiom the argument does not need
has not automated the derivation, it has bought fewer lines in the currency this repository exists
to report.

## Decision

**Decide the intuitionistic propositional fragment, with negation and falsity included, in a
procedure of its own**, and let a domain claim go to it first.

`Intuitionistic` in `modules/logic` is Dyckhoff's contraction-free sequent calculus, G4ip. Its
left rule for an implication is four rules, one per shape of the antecedent, and **none of them
keeps the principal formula**:

    P ==> B      with P atomic and already on the left      becomes   B
    (C /\ D) ==> B                                          becomes   C ==> (D ==> B)
    (C \/ D) ==> B                                          becomes   C ==> B  and  D ==> B
    (C ==> D) ==> B    two premises:  D ==> B  proving  C ==> D,  and  B  proving the goal

Termination is then a measure rather than a bound. With an atom, `T` and `F` weighing one,
`w(A /\ B) = w(A \/ B) = w(A) + w(B) + 1` and **`w(A ==> B) = w(A) + w(B)`**, every rule strictly
decreases the multiset of weights of the sequent. The implication weighing nothing for itself is
what makes the conjunction rule decrease: under the reflex weight `w(A) + w(B) + 1` the two sides
come out exactly equal and the argument is not an argument.

`~A` is read as `A ==> F` on the left and built with `notIntro` on the right, so negation is one set
of rules rather than a second copy of them.

**Rejected: a classical procedure with a cheaper closing step.** There is no cheaper closing step.
Glivenko's theorem is why `Propositional`'s replay is intuitionistic up to the last rule, and the
last rule is exactly where classical logic is; taking the goal from `~~goal` is the choice axiom in
this foundation, by `docs/adr/0009`, and no arrangement of the same search avoids it.

**Rejected: an external solver, which is the fork the card carrying this work refused to settle in
advance.** The argument for one is that it brings arithmetic with it and returns a replayable
propositional refutation; the argument against is a binary dependency and proofs that are hard to
replay, and `docs/adr/0003` puts anything untrusted outside the module graph anyway. Neither is what
decides it here. What decides it is that **no such solver answers this question**: SMT solvers
decide classical satisfiability, and what was missing was an *intuitionistic* decision, for which
Z3 and its siblings have no procedure at all. An external solver would have bought back exactly the
answer this repository already had, at one axiom, plus a dependency. The fork is therefore settled
for this fragment and left open for the one it was really about, which is arithmetic inside a
domain claim.

**Rejected: leaving `Minimal` and adding this beside it.** Two searches for one question. `Minimal`
keeps its published fragment, its address and its refusal, and delegates the search, which is why
`MinimalSpec` passes unchanged: a negation is still refused **there**, and Peirce's law is still out
of reach, because it is out of reach of intuitionistic logic rather than of the rule set that used
to live in that file.

**Rejected: a depth bound instead of the measure.** A bound turns "not provable" into "not found
within a number somebody chose". This repository keeps `Standing.Decided` and `Standing.Exhausted`
apart on purpose, and a procedure whose negative answer is a budget cannot be read as either.
`Intuitionistic.Fuel` exists as a net under the measure, and a goal that reaches it is reported as
exhausted rather than as refused.

## Consequences

**A domain claim costs what the hand derivation costs.** `Domain.Built.settle` is one call and the
accounting is the same as the forty-line derivation's: same theorem, one domain axiom of four, no
foundational axiom. `DomainTheorySpec` asserts the pair, and runs the classical route beside it,
still paying `SELECT`, so that the agreement is a measurement rather than a remark about an empty
set.

**The accounting needed a second half nobody had asked for.** Detaching every specialised axiom
reaches the theorem and makes `Derivation.axiomsOf` report all four, which is what the first run of
`settle` did. The instances are therefore cut down to an irredundant set first, by dropping each in
turn and deciding again — an unsatisfiable core obtained by deletion, because `Propositional` does
not publish the clauses its refutation read and this calculus has no clauses at all. It costs
`2n + 1` decisions and it is minimal rather than minimum: a different deletion order can leave a
different irredundant set.

**The boundary is now visible instead of implicit.** Peirce's law, the excluded middle, `~~p ==> p`
and the fourth De Morgan law are refused here and proved by `Propositional` at one axiom.
`IntuitionisticSpec` holds all four, each paired with what the classical procedure does with it, so
that a refusal is read as a price rather than as an inability.

**What a refusal still does not say.** An atom is given no meaning, so a goal valid for a reason
living inside an atom is refused exactly as a goal that is not valid at all. The refusal carries
`Standing.Unread`, which is the same argument `SkeletonFailsAt` makes for the classical side, and
`~(x = y) ==> ~(y = x)` is the witness `IntuitionisticSpec` pins.

**It reaches no solver**, which is what makes its cost checkable by reading it: the theorem is the
search, built step by step out of `Rules`, and there is no replay to get wrong. A scan in
`IntuitionisticSpec` asserts the file imports nothing from `modules/sat`, in the form `Quantified`
uses to say the opposite thing about itself.

**What this does not buy.** Nothing here reaches a quantifier, an equation between numbers, or a
constant of the foundation. A domain claim mentioning arithmetic is refused by name rather than
approximated, and composing this with `Linarith` is a separate piece of work.
