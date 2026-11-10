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
