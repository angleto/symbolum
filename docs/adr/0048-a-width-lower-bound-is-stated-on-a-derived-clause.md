# 0048. A width lower bound is stated on a derived clause, and proved by critical assignments without a restriction

- **Status:** accepted, extends 0044; its sentence calling the constant better than asked is corrected by 0055
- **Date:** 2026-09-25

## Context

`docs/adr/0044` named a resolution refutation, its size and its width, so that a statement over
every refutation of a family can be written, and `ResolvingSpec` wrote Haken's theorem for the
pigeonhole principle over those names without proving it. Mycelium card `01520749` asked for
**one** proof of a lower bound on the width of a refutation of the principle for `n + 1` pigeons
and `n` holes, of the form "at least `n / c`", and for the limits of this repository the work met
to be written down where they were met.

Two facts decide the shape of what was proved.

**`RES_WIDTH` counts the inputs.** It is the largest clause below `m`, and a step below `inputs` is
an input. The clause of a pigeon has `n` literals, one per hole. So "every refutation has width at
least `n / c`" holds of every refutation that uses a pigeon clause, for a reason that has nothing
to do with resolution, and a theorem of that form would be one step from `RES_WIDTH_BOUND`.

**A refutation's inputs are not the family.** The hypothesis says every input is a clause of the
principle, not that every clause of the principle is an input, so the theorem covers refutations
of any subset, which is the stronger statement and the one a lower bound wants.

## Decision

**The bound is on a derived clause.** `Pigeonhole.RES_PHP_DERIVED_WIDTH`:

```
!n k v s inputs m.
  NUM_LT ZERO n ==>
  (!j. NUM_LT j inputs ==> <clause j is a clause of the principle>) ==>
  RES_REFUTATION k v s inputs m ==>
  ?j. NUM_LE inputs j /\ NUM_LT j m /\ NUM_LE n (SUC (k j))
```

that is, some step at or past the inputs has at least `n - 1` literals, written without a
subtraction. The constant is `c = 1` up to the one literal, which is better than the card asked.

**The argument is the critical-assignment one**, and it needs no restriction of the variables. A
critical assignment for pigeon `p` puts the other `n` pigeons in the `n` holes one each; a pigeon is
bad for a clause when some critical assignment for it falsifies the clause. An input has at most
one bad pigeon, the empty clause has all of them, and a resolvent's bad pigeons are among its
parents' because whatever satisfies both parents satisfies it, which is `RES_STEP_SOUND` read at a
critical assignment. So the first step with two bad pigeons is derived and has exactly two. Moving
any third pigeon's hole to the first bad one turns a falsifying critical assignment into one that
satisfies the clause, and the two differ on two variables only, so the clause holds a literal on
one of them; those literals are distinct for distinct pigeons, and there are `n - 1` pigeons.

**The counting is the pigeonhole principle on `num`, which is proved here** as
`Pigeonhole.NUM_INJECTION_LE`: an injection from the first `a` numbers into the first `b` gives
`a <= b`. It belongs in `Peano`; it is published beside the bound because moving a link's library
moves `docs/lemmas.md`, `LibrarySpec`'s pins and the reading register, which is a piece of its own.

**It is outside the chain and declares nothing**, `Conjugacy`'s standing in `ChainCoverageSpec`:
the principle as a family of clauses is one investigation's object, and `PigeonholeSpec` is what
builds it.

## The measurement

Measured on 2026-09-25 against the classes of `7.0` at `71bf8cdf`, with this development compiled
beside them: `NUM_INJECTION_LE` is 13 805 nodes of `Derivation.size`, `RES_PHP_DERIVED_WIDTH` is
50 162, both rest on choice and infinity and on none of the reals' sixteen, and the second rests on
both `RES_STEP_SOUND` and `RES_EMPTY_UNSATISFIABLE`. The derivation takes about a second once the
chain is built. These are photographs of that tree; `PigeonholeSpec` asserts the axiom sets and
the resting-on, and does not assert the sizes.

The hypotheses are met: `PigeonholeSpec` derives all three for a five-step refutation at `n = 1`,
the two pigeon clauses, the hole clause, the resolvent `~x1` and the empty clause, with nothing
assumed, and detaches the theorem there. And `0 < n` is load-bearing: at `n = 0` the one-step
refutation of the empty pigeon clause meets the other two hypotheses and the conclusion is refuted
at it.

## Consequences

The card's fifth criterion, the limits met, is written in `Pigeonhole.scala`'s own comment where a
reader of the theorem meets it: no finite set or cardinality, so "exactly two bad pigeons" is
uniqueness plus two witnesses; no pigeonhole principle on `num` and no `SUC a <= SUC b`; and the
two propositional procedures read an equation between booleans as an atom, so "two assignments
disagree here" is four cases by hand.

**`docs/adr/0044`'s prediction is refuted, and it stays as written.** It said the work would need
"the behaviour of the width under a restriction of the variables, which is the step every such
argument turns on". Restrictions are how Ben-Sasson and Wigderson's route and Haken's go; the
critical-assignment argument never restricts anything, and nothing about restrictions was needed.
It would be needed for a size bound, which is not here.

## Alternatives rejected

**A bound on `RES_WIDTH` itself.** Rejected by the first fact above: it is true for a reason about
the inputs, and a reader would take it for a statement about resolution.

**Ben-Sasson and Wigderson's route through the width of the graph pigeonhole principle.** It is
what turns a width bound into Haken's size bound, and it needs restrictions, expansion of a
bipartite graph and the size-width relation, none of which the card asked for. The ordinary
principle has wide inputs, which is exactly why that route replaces it with a graph version.

**Adding `NUM_INJECTION_LE` to `Peano` in the same change.** Correct in the end and not here: the
fact is spent by nothing in the chain yet, and a link's library is pinned in a dozen places.

## What is not here

Haken's size bound, which stays stated in `ResolvingSpec` and unproved. Any bound on refutations of
a family other than this one.
