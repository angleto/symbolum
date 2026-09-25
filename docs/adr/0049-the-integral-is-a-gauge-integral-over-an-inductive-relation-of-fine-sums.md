# 0049. The integral is a gauge integral, over an inductive relation of fine sums

- **Status:** accepted
- **Date:** 2026-09-25

## Context

Mycelium card `0b413726` climbs the showcase one rung at a time, and after the derivative, the mean
value theorem and the sign of a derivative on an interval, the differential half of a first course
in analysis is in `Derivative`. The other half is the integral and the theorem that joins the two,
and until this record there was no notion of an integral anywhere in the repository.

The textbook integral is Riemann's, and its tidiest development is Darboux's: an upper and a lower
sum over a partition, each built from the supremum and the infimum of the function on a piece, and
the integral where the least upper sum meets the greatest lower one. That was the plan first put to
Angelo, and it did not survive being measured against what the library holds.

**Darboux wants two things this repository does not have, and neither is the integral.** A
supremum as a constant: `Root`, `MONOTONE_CONVERGES`, `Continuity` and `ExtremeValue` each write the
least upper bound out inline, and no `sup` exists to take one per piece. And, more expensively, the
common refinement of two partitions, which is what shows every lower sum is below every upper sum.
With a partition written as a sequence `num -> real`, a common refinement is the merge of two sorted
sequences with its length and its order proved, which is work about finite sequences and says
nothing about integration. The fundamental theorem in Darboux's form also asks that the derivative
be integrable, which is a hypothesis a reader must then discharge by a second theorem.

## Decision

**The integral is the gauge integral of Henstock and Kurzweil**, and a tagged division is not a
sequence at all.

`fine_sum f g u v s` says that `s` is the Riemann sum of `f` over a division of `[u, v]` fine for the
gauge `g : real -> real`, and it is the least relation closed under two rules, written with
`Inductive.INDUCTIVE` over the triple `(u, (v, s))`:

- **a piece**: `u <= x`, `x <= v` and `v - u < g x` give `fine_sum f g u v (f x * (v - u))`;
- **a join**: `fine_sum f g u v s` and `fine_sum f g v w t` give `fine_sum f g u w (s + t)`.

Every finite division is reached by splitting, so these are exactly the sums of the divisions the
textbook quantifies over. The piece's condition, `v - u < g x`, puts `[u, v]` inside
`(x - g x, x + g x)` because `x` is in it, and is implied by that containment at the gauge `2 * g`;
the integral it defines is therefore the usual one.

`has_integral f a b i` is the epsilon-gauge statement written out, as `derivative` and `continuous`
are: for every positive `e` a gauge positive everywhere under which every fine sum over `[a, b]` is
within `e` of `i`. `integral f a b` is `select` applied to it, and is pinned by uniqueness wherever
an integral exists.

Three consequences decide the rest, and each is a reason for the choice rather than a by-product:

- **Cousin's lemma is already proved.** Every positive gauge has a fine division of `[a, b]`, and
  that is `Continuity.INTERVAL_GLUING` at the property "some fine sum exists": the join glues, and
  a piece covers every short interval around its tag. Without it the definition could hold of
  every number vacuously, so it is also the guard against the definition being empty.
- **Uniqueness is one division fine for two gauges**, at their pointwise minimum, and no two
  partitions are ever merged.
- **The fundamental theorem needs no integrability hypothesis.** If `F` has derivative `f x` at
  every point of `[a, b]`, then `f` has integral `F b - F a`. The gauge at `x` is the radius the
  derivative gives at a tolerance, chosen by `select`; the bound on one piece is the straddle
  inequality, the error of `F` from both ends to the tag; and the bound on a whole division is an
  induction over the relation. A derivative that is not Riemann integrable is gauge integrable, so
  the theorem is stronger than the Darboux one rather than a restatement.

## Alternatives rejected

- **Darboux**, for the two reasons in the context: a supremum per piece and the common refinement
  of two partitions, neither of which buys anything beyond the integral.
- **Riemann with a constant mesh**: the gauge is a function precisely so that the fundamental
  theorem needs no uniform continuity of the derivative; with a constant mesh it would need the
  derivative continuous and the continuity uniform, which this repository has not proved.
- **Partitions as sequences with a gauge**: the same integral, and the join of two divisions
  becomes a reindexing of two sequences where here it is a rule.

## Consequences

A reader who knows only Riemann meets a less familiar definition. What they are owed is that the two
agree: every Riemann integrable function is gauge integrable with the same integral. That is not
proved here, and it is recorded as not proved rather than implied.

The gauge integral is not absolute: a function can be integrable while its magnitude is not. No
statement here depends on the magnitude, and a consumer that needs one has to prove it.

The integral is a link above `Derivative`, because the fundamental theorem names `derivative`.

**Where the supremum is spent, measured on 2026-09-25 when the nine facts first ran.** The two rules
of a fine sum spend no axiom at all. Cousin's lemma spends what `INTERVAL_GLUING` spends, the
sixteen axioms of the reals and the choice, and uniqueness and `integral` inherit it through
Cousin. `HAS_INTEGRAL_DERIVATIVE`, the fundamental theorem stated with `has_integral`, spends
fifteen of the sixteen and the choice and **not** `COMPLETENESS`: every fine sum being close is a
statement about the sums there are and needs none to exist. `IntegralSpec` asserts both.
