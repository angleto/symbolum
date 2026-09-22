# 0009. The classical axioms, and a reason that was wrong

- **Status:** accepted
- **Date:** 2026-09-10

## Context

The owner decided on 2026-09-10 that this logic supports the excluded middle.

Until that day it did not, and the absence was not an oversight. `Logic` is a purely definitional
extension, eight connectives and no axiom, and `docs/adr/0007` set the rule that an axiom arrives in
the commit whose derivation needs one and never in advance. Earlier the same day a choice operator
was asserted in `Classical.scala`, `SELECT_AX` under another spelling, because `Kernel.defineType`
needs a closed predicate and therefore the naturals need a named witness.

**Three places in the repository then said the excluded middle was still out of reach, and gave the
same reason: Diaconescu's argument needs extensionality as well, and extensionality was asserted
nowhere.** `Classical.scala`'s own scaladoc said it, `Natural.scala`'s said it, and `docs/proving.md`
said it. So the decision looked like a decision about which axiom to spend.

**That reason was wrong, and this record exists as much for that as for the decision.** `docs/adr/0007`
had it right — "choice gives the excluded middle by Diaconescu's argument" — and the three source
comments contradicted the ADR. Nobody had tried.

## Decision

**Two axioms, and only one of them is what the excluded middle cost.**

    SELECT : !P x. P x ==> P (select P)        asserted 2026-09-10, for the naturals
    ETA    : !t:'a->'b. (\x. t x) = t          asserted 2026-09-10, this record

**The excluded middle is derived, and it costs no axiom of its own.** `EXCLUDED_MIDDLE` is a
theorem on `Classical.standard`: **829 inference steps by `Derivation.size` when this was
written**, reaching `SELECT` and nothing else. The figure is left at what it was on the day rather
than restated, because what this record decided is the axiom set and not the price, and a price
written into a decision record is a copy that goes stale without anything going red. It has moved
since, once: `Rules.mp` stopped accepting an antecedent differing from the implication's by a beta
redex and began converting it instead, and Diaconescu's argument reaches choice twice, so it pays
twice. **What it is now is not written here.** `ClassicalSpec` pins it against the code and the
generated table of `docs/proving.md` prints it, and those are the two places to read it off.

That sentence carried a second, present-tense figure until 2026-09-22 — the count as it stood on
2026-09-16 — which is the shape to avoid in a dated record: true when written, and one derivation
away from being false with nothing going red. Card `ad47e293` is where the copies were counted.
Nothing about which axioms are reached changed, which is the claim this paragraph is making. `ClassicalSpec` asserts that axiom set both ways round, as a set equality against
choice and as a `should not contain` against eta, so the claim fails the build if it stops being
true. It was reachable from the moment choice landed.

Why extensionality is not needed, which is the part the three comments got wrong. Diaconescu's
argument compares `U = \x. x = T \/ p` and `V = \x. x = F \/ p` and needs `U = V` under `p`. Both
are **literal abstractions**, and `Kernel.abs` takes `s = t` to `(\x. s) = (\x. t)`: that is
function extensionality already, restricted to functions written as lambdas, and it has been one of
the ten primitive rules from the beginning. What eta adds is the rest of the range, a function
arriving as a variable or a constant. Diaconescu never has one. Propositional extensionality, the
other half people count, is `Kernel.deductAntisym` and has also been in the trusted base from the
start.

The derivation needs no decision about whether the two chosen values are equal, which is the step
the argument is usually presented as needing: two nested disjunction eliminations do that work. Each
of `select U = T \/ p` and `select V = F \/ p` comes from the choice axiom, and the branch that has
both equations derives `~p`, because `p` would make the selections equal and hence `T = F`.

**`ETA` is a separate purchase and is asserted for a different reason: to end the congruence-lemma
tax.** `Series` carries `SUM_CONGRUENCE`, `!f g. (!i. f i = g i) ==> !n. Sum f n = Sum g n`, and its
own comment explained that the lemma exists only because there is no extensionality here, and
predicted that every future operator binding a variable — products, integrals, maxima — would want
one of its own. `Classical.ext` takes `G |- !x. f x = g x` to `G |- f = g`, and congruence carries
that into any binder in three steps rather than an induction.

## Consequences

**The trusted base moves by one, and the file list does not.** Eta went into the file choice was
already in, so what has to be believed grew while the set of places it can grow from did not:
`RealSpec`'s scan still returns exactly four files. A third axiom in a third file would fail there
instead, which is the property that scan exists for. Measured, not assumed:

| development | before | after |
|---|---|---|
| `Logic.standard` | 0 | 0 |
| `Classical.standard` | 1 | 2 |
| `Real.standard` | 16 | 16 |
| `Natural.standard` | 2 | 3 |
| a chain holding both the reals and the naturals | 18 | 19 |

`Real.standard` does not move, and that is what putting the extension beside `Logic` rather than
inside it was for: a session proving something about the reals is still not asked to believe choice,
and is not asked to believe eta either.

**Six drift guards fired, in four files, and one of them was asserting the opposite of the truth.**
Five were counts and moved. The sixth, in `ChainSpec`, asserted the count *as the record that
extensionality is not among what is believed*, with a comment predicting a congruence lemma per
future binding operator. Bumping its number alone would have left a test asserting the opposite of
the truth, so it was renamed and rewritten. That is what a drift guard is worth, and it is why the
number is asserted in six places rather than written in a document once.

**What eta bought is measured since 2026-09-11, and the qualification that stood here is gone.**
`Series.congruent` went through the induction until then, because `Series.scala` was outside the
change that asserted the axiom, so the justification above was an argument about what `ext` can do
rather than a measurement of a lemma that got shorter. It is a measurement now:

| | through the induction | through `Classical.ext` |
|---|---|---|
| `SUM_CONGRUENCE` | an induction over the recurrences | **258 inferences** |
| `PROD_CONGRUENCE` | the same at a second constant | **258 inferences** |
| axioms reached | choice and infinity, because the induction is over `num` and `num` is carved out of an infinite type | **eta, and nothing else** |

The second row is the one that matters more than the size. Eta was asserted for this, and this is
where it shows: the lemma that pays for an axiom now names it. `SeriesSpec` asserts both.

**The two lemmas stay**, and the reason is in `Series.congruent`'s own comment: a caller holding a
pointwise hypothesis should not have to know which of the two roads is cheaper. They are a
convenience now and not a necessity, and nothing is left for a third binding operator to want.

One thing this needed that did not exist: `Classical.ext(wider, theorem)`. Detaching eta means
specialising it **at the function type**, `num -> real` here, and `Classical.standard` has never
heard of either operator. The axiom is held in one place and the types live in another, which is the
same boundary `Divisibility` documents for quantifier introduction and `Prove.construct` for lemma
application.

**The claim that a future binding operator needs its own congruence lemma is now false, and `Prod`
is the evidence either way.** `Prod` landed the same day and did want one, `PROD_CONGRUENCE`, which
was the prediction holding for the last time.

**Three source comments are corrected, and one of them is in the trusted base.** `Classical.scala`'s
scaladoc said the excluded middle does not come for free from choice. It does. `Natural.scala`'s
scaladoc and `docs/proving.md` said the same and are corrected too. A false reason written in the
file that asserts the axiom is worse than a missing one, because it is where a reader goes to find
out what the extension costs.

**`Natural.scala`'s reason for diverging from upstream's axiom of infinity is now weaker than it
was.** It asserts the strong form directly, and the recorded argument was that deriving it from
upstream's weak form needs the excluded middle, "which this logic does not have", so the choice was
one axiom against two. This logic now has it, so the comparison is one axiom and a derivation either
way. The divergence may still be right; the reason recorded for it no longer holds, and revisiting it
is a card and not a change made in passing.

**What is still not asserted.** Infinity is HOL Light's third axiom about the formalism and it is
not in the logic: it belongs with the naturals and `Natural.scala` has it. `bool` having exactly two
elements is not asserted: upstream's `BOOL_CASES_AX` is reachable from `cases` and is a theorem
here, undelivered because nothing has asked for it. And the reals are still axiomatised, which is
what `docs/adr/0007` turns into theorems and has not started.

**The formalism side is now exactly upstream's, and the remaining difference is nameable.** HOL Light
asserts three axioms about the formalism, `ETA_AX`, `SELECT_AX` and `INFINITY_AX`; so does this
system, under its own spellings. Confidence high and **not verified here**: there is no HOL Light
source in this tree and fetching one is an action nobody has approved. What that says is worth more
than the parity: the whole remaining difference between the two trusted bases is the sixteen axioms
about the reals, which is precisely what `docs/adr/0007` plans to remove.

**It cuts against the one axis this system claims, and the comparison should change shape.** An
adversarial review the same day found that every document here compares itself with Mathlib, that
the real comparator is HOL Light, and that the axis where the loss is largest is the size of the
trusted base. This change makes that base larger. What it does not do is make it larger than
upstream's.

**A case split can now be made about a proposition rather than only about an order.** Until
`Classical.cases` existed, `LT_TOTAL` was the only supplier of a case split in this system, so a
proof by cases could only be about the reals. That is the practical content of the change, and it is
what makes a classical propositional procedure ordinary work rather than a request for an axiom.

## Alternatives rejected

**Assert `p \/ ~p` directly.** This was the recommendation this change was launched on, and the
measurement refuted it: the excluded middle needs no axiom at all. Asserting it would have bought a
theorem the system already had, at the price of the most expensive statement available.

**Assert extensionality in the pointwise form, `!f g. (!x. f x = g x) ==> f = g`.** It is what the
derivations use, so it looks like the honest thing to assert. Rejected because `ETA` yields it in 242
steps and is the smaller statement, and a smaller axiom that gives the larger one is the trade this
development makes everywhere else. `FUNCTION_EXTENSIONALITY` is therefore a theorem, and
`ClassicalSpec` asserts its name is absent from the axiom list.

**Derive the excluded middle and stop, leaving eta for the derivation that needs it.** A strict
reading of `docs/adr/0007`'s rule, and it was seriously considered once the measurement showed the
excluded middle to be free. Rejected because `docs/proving.md`'s own build order names the classical
axioms as a pair, choice and extensionality, and because `SUM_CONGRUENCE` is a derivation already in
the repository paying for eta's absence. The qualification above is the price of that reading: the
payment is not yet collected.

**Stay intuitionistic and route around the excluded middle where something wants it.** The position
until 2026-09-10, and defensible. The owner decided otherwise, and that decision is recorded here
rather than argued.

## What this does not cover

It gives no decision procedure and no model finder: a propositional premise set still comes back
`Survived` from `Refutation` rather than decided, which is separate work that this change makes
cheaper rather than does. It says nothing about the three unrepaired findings of the same day, on
`Term.abs`, the checker's definition branch, and the origin of a declared constant. And it does not
make the reals constructed.
