# 0040. A representation is a formula whose truth is the predicate, and provability comes once

- **Status:** accepted
- **Date:** 2026-09-25
- **Extends:** 0013

## Context

Mycelium card `4102f131` measured what stands between the Goedel stack and the first statement
of D1: twenty-three constants of the ambient logic (`NUM_TRI`, `NUM_PAIR`, `NUM_CODE`, the four
projections, `NUM_BETA`, the syntactic recursions, the two axiom sets, `NUM_STEP`, `NUM_PROOF`,
`NUM_PROV`), each of which needs a formula of the object language standing for it. `NUM_PROV` is
a predicate of this logic about codes; D1, D2 and D3 are statements about a **formula** with one
free variable, and until the twenty-three have formulas that formula cannot be written.

The card said what each needs: "a formula of the object language, and the proof that the formula
represents the HOL predicate, that is that it holds at the numbers where the predicate holds and
its negation is provable where it does not". It did not say how that proof is to be had, and the
two readings of it cost very different amounts.

**Read per constant**, it is a derivation in PA for every constant and every direction: that PA
proves the formula at the numerals where the predicate holds and proves its negation where it
does not, and for a function that the value is unique. That is twenty-three families of object
derivations, each one built from `Deduction`'s schemes, and the uniqueness halves are
quantified statements inside PA, which is the costliest kind this repository builds.

**Read through truth**, it splits into two things of different kinds. First, what the formula
**says**: a definition of when a formula of the object language is true at an assignment of
numbers to its variables, and for each constant a theorem of this logic that its formula is true
exactly where the predicate holds. That is ordinary mathematics about numbers and costs no object
derivation at all. Second, when a true formula is a **provable** one: completeness for the bounded
formulas, proved once, by induction on the formula, which gives both directions of every
representation at once because the negation of a bounded formula is bounded.

## Decision

**A representation is a formula of the object language together with a theorem that its truth is
the predicate**, stated with `NUM_TRUE`, the truth of a formula at an environment, which
`Truth.scala` defines by recursion on the code beside `NUM_VALUE`, the value of a term.

**Provability comes from completeness for bounded formulas, proved once**, and not from a
derivation per constant. Until it is proved, a representation in this sense is the semantic half
and says nothing about PA; every sentence that describes one has to keep the two apart.

**Both recursions answer with a function of the environment**, `NUM_TRUE p e` and `NUM_VALUE t e`,
code first. For the truth this is forced: the quantifier's clause reads the body at the
environment that differs from `e` at the bound index, and a recursion with the environment as a
fixed parameter cannot say that.

**The convention for a function's graph**: variable `0` is the value and the arguments are
variables `1`, `2` and so on, in order. `NUM_TRI_GRAPH` is the first, and every one above follows
it.

**`Truth` is a link of the chain**, above `provability` and below `limit`, which now extends it.
It was written first as a development beside the chain, on the argument that nothing in the chain
consumed it yet. When the suite first ran, `ChainCoverageSpec` asked for the file to be
classified, and the classification it offers for a development outside the chain says what was
wrong with the argument: outside it `Find`, `Ask` and the library cannot reach the constants, and
that standing is for constants describing one object of one investigation, which a truth
predicate for arithmetic is not. Completeness, the next consumer, needs this signature and `provability`'s at once, which a
link gives it for nothing.

## Consequences

The trusted base does not move. `NUM_VALUE`, `NUM_TRUE` and `NUM_TRI_GRAPH` are definitions and
every fact about them is derived.

`Language`'s course-of-values recursion learned one thing to carry the truth: its admissibility
proof now has congruence under a binder, because the branches of these two steps are abstractions
over the environment and the quantifier's branch applies the recursion under `!n.`. Its guard
settling moved into `Language.settleGuards` so that the clauses of both developments are read off
their recursion equations the same way. Neither change alters a statement `Language` publishes.

The per-constant cost is now a formula and a theorem about numbers. For `NUM_TRI` the formula is
quantifier-free, `v0 + v0 = v1 * S v1`, because the triangle is the unique solution of
`2x = n(n+1)`; for `NUM_PAIR` and the projections it will need bounded quantifiers, which
`Language` already abbreviates (`NUM_EXISTS_BELOW`, `NUM_ALL_BELOW`) and which `NUM_TRUE` has no
clause for yet, since they are codes built from the four connectives.

What is now the largest single piece of the program is named rather than dispersed: completeness
for bounded formulas, `NUM_TRUE p e` for a closed bounded `p` giving `NUM_PROV p`. `docs/adr/0013`
already says that D3 is the same theorem formalised inside PA, so this is the meta-level version
of the proof D3 will have to internalise, and building it here first is the rehearsal of that one.

## Alternatives rejected

**A derivation in PA per constant**, the first reading above. Rejected on the count: each of the
twenty-three would need its uniqueness proved as a quantified object statement, and the
syntactic ones would need the course-of-values recursion unfolded inside PA, once per constant.
Completeness pays for the object side once, by induction on the formula, and the per-constant
work becomes arithmetic this logic already does well.

**A truth predicate for closed formulas only**, defined through substitution: `!v. p` true when
every numeral substituted for `v` gives a true formula. It avoids environments, and it is not a
recursion on the code: the numeral substituted can have a code larger than the formula's, so
`Descent` does not apply and the definition would need a rank of its own. Environments cost one
function type and nothing else.

**The environment as a parameter of the recursion**, which `Language.defineShaped` already
supports and which the substitutions use for their index and replacement. Rejected by the
quantifier clause, as above; kept for the value would have meant two argument orders for two
recursions that are read side by side.

## What was measured and what was not

Measured: that the course-of-values recursion carries a step whose branches are abstractions,
once the admissibility proof opens a binder, and that the clauses of both recursions come out of
the equations by the same settling `Language` uses for its own; `TruthSpec` asserts each clause
against its published text and the truth predicate against formulas whose truth is known, in both
directions, including one where only a correct update of the environment gives the right answer.

Not measured: that completeness for bounded formulas is within reach of `Deduction`'s schemes as
they stand. It needs, at least, PA proving `x < S n -> x < n \/ x = n` at a numeral and the
bounded quantifiers unfolded into finite conjunctions and disjunctions; neither exists. That is
the claim in this record a reader should doubt first, and it is the next piece of work.

## What the first attempt at it measured, 2026-11-10

The existential side holds. `NUM_PROV_EXISTS_INTRO` introduces `?i. p` from `p[t/i]` at a closed
`t`, as specialisation of `~p` contraposed, and `NUM_PROV_LESS_NUMERAL` proves `numeral m <
numeral n` for every `m < n` with it. Both cost the naturals' two axioms and nothing else.

The universal side is where the doubt was placed, and the doubt survived. Refuting
`numeral m < numeral n` for `m >= n` is proving `!z. ~(numeral m + S v_z = numeral n)`, and the
case split `x < S n ==> x < n \/ x = n` is a statement about a variable `x`. Every derivation of
either that was tried needs an axiom of PA at an **open** term: `numeral m + S v_z = S (numeral m
+ v_z)` is `NUM_PA_ADD_SUC` at `numeral m` and `v_z`, and `~(S (a + b) = 0)` is `S x != 0` at
`a + b`. `NUM_LOGIC_SPECIALISE` and `NUM_LOGIC_REPLACE` take closed terms only, and the induction
scheme substitutes `0` and `S i` for `i` and nothing else, so none of them reaches those instances.
The docstring of `Language.ClosedName` named this cost and judged that Goedel's argument does not
pay it, because it substitutes numerals; completeness for bounded formulas is the place where it
does pay it, since a bounded universal is a claim about a variable.

What this does not establish: that no derivation exists. No proof of underivability was attempted,
and the induction scheme's open instance `p[S i/i]` is the one place an open term enters. The
textbook repair is the scheme's own condition, a term **substitutable** for the index rather than
a closed one, which needs a recursion over the formula `Language` does not have, and changes what
`NUM_PROV` means for every fact above it. That is a decision about the object logic, and it is
taken before completeness for bounded formulas is attempted again, not inside it.

The decision was taken on 2026-11-12 and is `docs/adr/0078`: both schemes ask that the term be
substitutable.

## The two pieces named above, 2026-11-19

Both pieces the section on what was not measured names now exist, and so does the universal half
of the unfolding. PA splits the order below a successor for a variable (`NUM_PROV_LESS_SUC_CASES`)
and refutes it below zero (`NUM_PROV_NOT_LESS_ZERO`). From those two, `NUM_PROV_ALL_BELOW_NUMERAL`
proves a bounded universal below a numeral from a proof of each instance under the bound. The
finite conjunction is the meta level's `!k. k < n ==>`, which is the form the completeness
induction consumes one instance at a time. Each costs the naturals' two axioms.

What it needed below `Deduction` was not an order fact. The equality case replaces a numeral by the
variable in a formula nobody wrote down, so `Language` now proves that putting `v_i` for `v_i`
changes no term and no formula and is always allowed (`NUM_SUBST_TERM_SELF`,
`NUM_SUBST_FORM_SELF`, `NUM_FREE_FOR_SELF`). `tools/verify/perturb-all-below.sh` records that the
proof does not build without them.

The existential half is not here. A bounded existential refuted from a refutation of every
instance is the universal of the negation read through `NUM_AND` and `NUM_EXISTS`, and one proved
from one instance is `NUM_PROV_EXISTS_INTRO` at a closed witness. Neither is written, and neither
is completeness for bounded formulas, which is still the claim in this record to doubt first.

## The existential half, 2026-11-20

The section above ends by naming the existential half as not written. It is written now, as two
facts in `Deduction`, and it needed nothing new below `Deduction`. `NUM_PROV_EXISTS_BELOW_NUMERAL`
proves a bounded existential from one instance under the bound: `NUM_PROV_EXISTS_INTRO` at the
witness `numeral k`, whose body is the conjunction of `numeral k < numeral n`, from
`NUM_PROV_LESS_NUMERAL`, and the instance. `NUM_PROV_NOT_EXISTS_BELOW_NUMERAL` refutes one from a
refutation of every instance under the bound: `NUM_PROV_ALL_BELOW_NUMERAL` at `~p`, with a double
negation put under the quantifier, because `NUM_AND` is `~(a ==> ~b)`. Each costs the naturals' two
axioms. `tools/verify/perturb-exists-below.sh` records what each one depends on.

Completeness for bounded formulas asks four things of a quantifier below a numeral: a universal
that holds is proved, one that fails is refuted, and the same for an existential. Three were here
that day, and the fourth followed it, below.

## The fourth case, 2026-11-20

`NUM_PROV_NOT_ALL_BELOW_NUMERAL` refutes a bounded universal from one instance under the bound
that PA refutes, the dual of the witness half and, like it, without an induction: the logical
axiom of specialisation at the closed witness `numeral k` gives `(!v_x. B) ==> B[numeral k/x]`,
the order in `B[numeral k/x]` is `numeral k < numeral n` from `NUM_PROV_LESS_NUMERAL` and is
detached under the universal, and contraposition with the refuted instance refutes the universal.
It costs the naturals' two axioms, as the other three do, and `tools/verify/perturb-not-all-below.sh`
records what it depends on.

All four cases are here. Completeness for bounded formulas, the induction over a formula that
consumes them, is not written, and it is still the claim in this record to doubt first.

## The truth of an instance, 2026-11-21

The four cases speak of instances `p[numeral k/x]` and the truth of a bounded quantifier speaks of
`p` at every value of `x`, so the induction needs the two read as one thing. `Truth` now proves it:
`NUM_VALUE_SUBST_NUMERAL` for a term and `NUM_TRUE_SUBST_NUMERAL` for a formula, each by strong
induction on the code. The update at `x` survives a quantifier over another index and is overwritten
by one over `x`, where the substitution stops. The two environments under a quantifier are
abstractions on both sides, so they are equated by the kernel's abstraction rule over a case split
on the argument and not by extensionality; the first version used `FUNCTION_EXTENSIONALITY`, spent
`ETA`, and `TruthSpec`'s per-fact cost refused it. Both cost choice and infinity.

What is left of completeness for bounded formulas is a decision before it is a proof: the class of
bounded formulas as a predicate on codes, which an induction over it must be able to read through a
substitution, and a measure that a numeral put for a variable does not raise, since the code of
`p[numeral k/x]` can be larger than the code of `p` and so strong induction on the code does not
reach it.

## The class of bounded formulas, 2026-11-21

`NUM_BOUNDED` is the class, as a recursion on the code in `Truth` beside `NUM_GROUND`. It holds of
every equation, and of a negation, an implication and a universal below when it holds of their
parts. A universal below is `NUM_ALL_BELOW z i b p`. Its order's witness `z` must differ from `i`,
and its bound `b` is a variable other than `v_i` and `v_z`, or a numeral. Any other universal is
outside the class. An existential below is written as the negation of a universal below. Five facts
read it: one clause per connective, and `NUM_BOUNDED_ALL`, which reads a universal in the class back
as a `NUM_ALL_BELOW`. The induction will meet the universal as `NUM_CODE 8 (NUM_PAIR j q)`, so it
needs that inversion.

**The bound is a variable or a numeral, and that is the decision this section records.** The plan
written the same morning allowed any term not mentioning the index. That plan needed a step that
this one drops: in a closed instance, bringing the bound to a numeral inside PA, under the
quantifier, by replacing equals. With a variable or a numeral, putting a numeral for a variable
keeps the class, and a closed formula of the class already has numerals for bounds. That is the
form the four facts in `Deduction` consume. What is lost is a bound written as a term. It comes back
one level up, as `?y. y = t /\ !i. i < y ==> p`, which is Sigma-1 and is what completeness for
Sigma-1 formulas will read. The choice is reversible. Widening the class later is a new clause plus
the PA step this one avoids.

Two pieces of machinery moved with it. The first is in `Language`'s admissibility proof for a
recursion. It read a bound only for a payload or a component of the payload's pair. It now walks
any nest of codes and pairs in the guard's shape, because the universal's branch recurses on the
body of the order's implication, two codes down. The second is `settleGuards`. It leaves standing a
guard comparing two codes of one tag whose payloads differ, where it used to fail asking two equal
tags to be distinct. No guard that previously settled is read differently. `NUM_BOUNDED_ALL` splits
on the one guard left standing.

On 2026-11-22 the class was shown to survive a numeral put for a variable, as
`NUM_BOUNDED_SUBST_NUMERAL`, by strong induction on the code. The universal is the case where the
decision above is used: under the substitution a variable bound becomes the numeral when it is the
variable substituted and stays a variable otherwise, and a numeral bound is left alone because it is
closed. A bound allowed to be any term would come out of the substitution as any term. The proof
needed one fact about formulas that `Language` did not have, `NUM_FORM_IMP_PARTS`: the parts of a
formula built by the implication are formulas. Without it nothing follows about the body of a
universal below from the universal being a formula.

What remains: a measure on codes that numeral substitution leaves unchanged, and the induction on
that measure, which consumes the four cases and the facts above.
