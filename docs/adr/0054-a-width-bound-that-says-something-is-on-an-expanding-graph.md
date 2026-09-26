# 0054. A width bound that says something is on an expanding graph, and the one on the complete principle is a one-step argument

- **Status:** accepted, extends 0048 and corrects one sentence of it
- **Date:** 2026-09-26

## Context

`docs/adr/0048` proved `Pigeonhole.RES_PHP_DERIVED_WIDTH`: every refutation of the pigeonhole
principle for `n + 1` pigeons in `n` holes derives a step of at least `n - 1` literals. It called
the constant "`c = 1` up to the one literal, which is better than the card asked". The verification
of 2026-09-25 on Mycelium card `01520749` showed why that sentence overclaims: a pigeon clause has
`n` literals, a resolvent with one as a parent keeps all but the pivot, and a refutation in which no
derived step has a pigeon parent would descend from hole clauses alone, which the all-false
assignment satisfies. So the bound follows from one step and the definition of a justified step, and
it says nothing about proof complexity: the inputs are already as wide as the conclusion. That record
also rejected, as not asked for, the route that does say something.

Angelo chose on 2026-09-26, on the card, between three criteria: a width bound on an encoding with
short inputs, the one-step bound declared as such, or Haken's size bound. He chose the first.

## Decision

**The bound is Ben-Sasson and Wigderson's, on the pigeonhole principle over a bipartite graph.**
`ExpanderPigeonhole.RES_GPHP_WIDTH`, outside the chain, declaring nothing:

```
!np n adj r w k v s inputs m.
  NUM_LT 0 r ==> MATCHABLE ==> EXPANDING ==>
  (!j. NUM_LT j inputs ==> <clause j is a clause of the principle on adj>) ==>
  RES_REFUTATION k v s inputs m ==>
  ?j. NUM_LT j m /\ NUM_LE w (k j)
```

Pigeon `p` may go only to a hole `h` with `adj p h`, so a pigeon clause is as wide as the pigeon's
degree and the inputs are short. `EXPANDING` says that every set of exactly `t` pigeons with
`t <= r < 2t` has at least `w` holes with a single neighbour in it. For a bounded-degree expander `w`
is linear in the number of holes and larger than the degree, and then the conclusion is not a fact
about the inputs.

**`MATCHABLE` is a hypothesis, and it is Hall's theorem.** Every set of at most `r` pigeons has an
injective matching into the holes along `adj`. The source derives it from the expansion by Hall's
theorem. That theorem is not in this repository, so the statement carries its conclusion instead of
proving it. Both hypotheses are properties of the graph and neither mentions a refutation.

**The argument is the source's, with the least step taken by `NUM_LEAST`.** `mu(C)` is the least
number of pigeons whose clauses, with every hole clause, imply `C`. It is at most one on an input and
more than `r` on the empty clause, where the matching is a satisfying assignment. A resolvent is
bounded by the sum of its parents, which is `RES_STEP_SOUND`. So the first step no set of `r`
implies has a parent with `r < 2 mu <= 2r`. At that parent, each unique-neighbour hole of a least
implying set carries a literal of the clause, and `NUM_INJECTION_LE` counts them. The source descends
by strong induction; the least step is `Pigeonhole`'s own pattern and needs no induction hypothesis
to be stated.

**Sizes are injections.** There are no finite sets or cardinalities here, as `Pigeonhole.scala`
records, so "at most `t`" is an injection into `[0, t)` and "exactly `t`" is that and not "at most
`PRE t`".

**`RES_PHP_DERIVED_WIDTH` stays, and is described as what it is.** It is correct and proved, and it
is the one-step argument above in a longer proof. The sentence in 0048 about `c = 1` is the
overclaim, and this record is its correction: 0048 is a photograph of that day and is not edited.

## The measurement

**Both theorems now detach where their width conjunct is not free.** Both use the nineteen-step
refutation of three pigeons in two holes in `ResolutionFixture`, found by eliminating the third
pigeon's variables first. The refutation's three functions are written as conditionals, and every
value the derivation reads is proved by deciding one, so nothing is assumed.

- `PigeonholeSpec` detaches `RES_PHP_DERIVED_WIDTH` at `n = 2`. Its conjunct `2 <= SUC (k j)` fails
  at the empty clause. The detachment at `n = 1` that stood there until today did not read the
  conjunct: `1 <= SUC (k j)` holds of every step. That is the verification's second point.
- `ExpanderPigeonholeSpec` detaches `RES_GPHP_WIDTH` on the complete graph `K(3, 2)` at `r = 1` and
  `w = 2`. Four steps of the refutation have fewer than two literals.
- `EXPANDING` is load-bearing: at `w = 20` the other hypotheses still hold at the same refutation,
  and the conclusion is refuted there.

**What the guard does not show** is a graph whose `w` exceeds its degree. On `K(3, 2)` both are two.
The small expanders with that property are far past what a hand-written refutation reaches, so the
guard shows that the hypotheses can hold together, not that they hold where the theorem is strong.

## Alternatives rejected

**Proving Hall's theorem first.** It is the correct eventual shape, and it is its own piece of work:
a matching argument over finite sets in a repository without finite sets. Carrying it as a hypothesis
states exactly what is used, and a later proof of it discharges the hypothesis without changing the
theorem.

**Strong induction on the step index, as the source descends.** `NUM_STRONG_INDUCTION` is available.
The least step is shorter here because every other fact is already stated about a step, not about a
prefix of the refutation.

**Keeping the complete principle and declaring the bound trivial.** That was option 2 on the card,
and Angelo chose against it.

## What is not here

Hall's theorem; a bounded-degree expander family with `w` linear in the holes, which is what turns
this into a statement about complexity; the size-width relation that turns a width bound into
Haken's size bound. Haken's theorem stays stated in `ResolvingSpec` and unproved.
