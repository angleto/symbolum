# 0052. The reals are lower cuts on the rationals, with the sign handled at multiplication

- **Status:** accepted, settles the first open question of 0016
- **Date:** 2026-09-25

## Context

[`0016`](0016-what-the-construction-needs-in-front-of-it.md) left the route of the construction
open on purpose and named what would settle it. Two routes were correct and shared the whole of the
quotient builder: cuts on the rationals, with multiplication defined on the positive cone and
extended by sign; or the positive rationals first, cuts on those, and the reals as a completion of
that cone, which never meets a sign case and keeps the integers off the critical path. The record
called the first the one to beat, because under it the integers and the rationals arrive as a
by-product rather than afterwards, with one type of rational rather than two, and deferred the
choice until the builder's cost was measured.

What has happened since is that the by-product arrived first. `int` is `Integer`, a quotient, since
2026-09-18 ([`0033`](0033-the-integers-arrive-as-a-prerequisite-and-not-as-stage-four.md)); `rat`
is `Fraction`, a quotient over pairs of an integer and a successor
([`0036`](0036-a-rationals-denominator-is-a-successor.md)), and on 2026-09-25 it became an ordered
field, Archimedean and dense, with a ring decider over its classes
([`0046`](0046-identities-of-a-commutative-ring-are-decided-by-one-builder.md)). So the second route
would now build a second type of positive rational beside one that exists, which is the cost 0016
held against it, and it would save a sign case analysis in exactly one place.

## Decision

The reals are **lower Dedekind cuts on `rat`**. A cut is a set of rationals that holds something,
does not hold everything, is closed downwards under `RAT_LT` and has no greatest element; `IS_CUT`
states those four clauses and `cut` is carved out of `rat -> bool` by it with `defineType`, the
witness being the cut of zero, whose fourth clause is `RAT_DENSE`.

**The order is inclusion.** Reflexivity, transitivity and antisymmetry are one line each, the last
through `ext`, and totality is the one argument: a member of `x` missing from `y` is above every
member of `y`. `CUT_OF_RAT q` is the cut of the rationals below `q`, and it is an order embedding.

**Least upper bounds come first, before any arithmetic**, and they are the union. `CUT_COMPLETE` is
`COMPLETENESS` word for word over `cut` and `CUT_LE`, proved, and it is the fact the whole
construction exists for: the axiom that separates an ordered field from the reals, which until now
nothing in this repository could do without assuming.

**The arithmetic follows in two stages.** Addition, zero and negation first, and they landed with
the carrier: `CUT_ADD x y` holds `r` when some `p` in `x` leaves `r - p` in `y`, one existential
rather than two; `CUT_NEG x` holds `p` when some `r > 0` leaves `-p - r` outside `x`; and the
additive inverse is where Archimedes is spent, because below zero a member whose step leaves the cut
has to exist. Then multiplication on the positive cone, extended by sign, with the inverse and
`inv 0 = 0` as a convention written in a definition. Only when all of it is in
place do the sixteen of `Real.scala` become theorems under their own names, which is phase 5 and not
this record.

## Consequences

**The construction declares the type beside the chain, as `Fraction` is.** `Cut` sits beside the
chain rather than in it, because nothing in the chain can reach it yet and the reals it will replace
are the chain's own. The move into the chain is phase 5.

**`Fraction` publishes its ring.** `Fraction.ring` is the `rat` instance of `CommutativeRing`, built
once by `Fraction.ringOver` and used by `Density` inside the construction and by `Cut` outside it,
where each used to be able to build its own.

**The trusted base does not move.** `CUT_COMPLETE` costs choice, eta and infinity, which the chain
already holds, and `CutSpec` asserts that no fact of the development reaches any of the sixteen,
with the positive control that antisymmetry does reach eta.

## Alternatives rejected

**The positive cone first**, for the reason in the context: it would add a type of positive rational
beside `rat`, and what it saves is the sign case of one operation.

**Upper cuts, or cuts as pairs of a lower and an upper set.** A pair makes negation symmetric and
doubles every other obligation, since each clause is stated twice and related; a lower cut makes
negation the one awkward definition, `{p | ?r. 0 < r /\ ~(x (-p - r))}`, and everything else
single. Upper cuts are the same choice mirrored.

**Cauchy sequences**, which 0016 already rejected: completeness becomes the diagonal argument, and
it is the one of the sixteen worth the most as a theorem.
