# 0025. A goal's own hypotheses are facts, and the deduction theorem is what pays for them

- **Status:** accepted
- **Date:** 2026-09-18

## Context

The front page's row about proof search ends with the four things this system has none of: no
given-clause loop, no saturation, no forward inference over a clause set, and **no context from a
goal's own hypotheses, so `H ==> C` is matched whole and `H` does not become a fact**. The last of
the four is the one that costs something today, and it is the cheapest to remove.

What "matched whole" means, precisely, because it is not that the hypotheses were ignored
everywhere. `Linarith` has always assumed them: `Linarith.split` strips the quantifiers, assumes the
antecedents, splits the conjunctions, and discharges at the end, which is why a linear goal written
as an implication is decided. What could not see them is everything **above** the decision
procedures: `Prove.held`, which scans the library for a lemma whose conclusion *is* the goal, and
`Chaining`, which matches the goal against every lemma that could conclude it. Both were handed
`H ==> C` as one term. A lemma concluding `C` did not match it, so the premise the goal supplied was
syntax on the road to the conclusion rather than something known.

Two facts make that worth repairing rather than noting. Every statement of the miniF2F corpus is
written in exactly that shape, hypotheses conjoined into one antecedent. And the repository's own
library is written that way too: `INV_POSITIVE` is `!x. 0 < x ==> 0 < inv x`, so chaining it
requires proving `0 < x`, and where `0 < x` is the goal's own premise there was nothing to prove it
with.

## Decision

A goal's antecedents become **assumed theorems** for the length of one question, and the deduction
theorem puts them back.

`Context.of` strips the goal's universals, peels every antecedent, and assumes each one with
`Kernel.assume`, giving `A |- A`. A conjunction is split with `conjElim`, halves and whole both
kept. Those theorems are candidates like any other: `Apply` already decides what a lemma's variables
must be for its conclusion to be the goal, and an assumed theorem is a lemma with no variables of
its own, or with some, or with an antecedent of its own that `Apply` peels and owes. No matching
rule learned what a hypothesis is.

`Prove.underHypotheses` is where the pair is spent: the conclusion alone goes to the scan, to the
decision procedures and to the chaining search with those facts in hand, and `Context.discharge`
puts the antecedents back in the order they were written and quantifies again. The result is
compared against the goal as asked and must rest on nothing.

Three rules fall out of that and are written where they are enforced:

- **The hypothesis test is relaxed, in exactly two places, and to exactly one set.** `Prove.held`
  and `Chaining` refused a candidate carrying any hypothesis, because their answer claims to be
  unconditional. Under a context they refuse a candidate carrying a hypothesis **other than what
  this goal assumed**. What restores the promise is the check at the end, which is the same check
  `Chaining` already applies to its own answer.
- **The discharge happens once, at the top, by the caller that assumed.** A search does not
  discharge as it goes.
- **The route is asked last**, after the whole goal has been put to the scan, the procedures and
  the chaining search. It can add a theorem and it takes no refusal away, which is this
  repository's rule for a search that recognises no shape.

The decision procedures get the context too, and that is a second half rather than a detail. A
subgoal produced by chaining is a bare term, and LINARITH cannot know what was assumed two levels
above it, so `Prove.decidedUnder` writes the premises back on, decides the implication, and detaches
them again with `mp`. Without it the facts reach the library lookup and not the arithmetic.

## Consequences

- A goal `H ==> C` whose conclusion follows from a lemma at the cost of an obligation `H` states is
  now proved. The witness in `ContextSpec` is `!x. 0 < x ==> 0 < inv (inv x)`: two uses of
  `INV_POSITIVE`, the second obligation discharged by the goal's own premise, and refused before
  this existed.
- The invariant that a candidate carries no hypothesis is gone, replaced by a check at one place.
  That is a real loss of local reasoning: a defect in the fold is now caught at the end rather than
  being unrepresentable in the middle. It is the same trade `Chaining` already made and argued.
- Nothing already proved changes route or price, because the route is asked after everything else
  and the procedures still see the whole implication first.
- A disjunctive hypothesis is not split. That would be `disjElim` and a case analysis, which is a
  proof strategy rather than a context, and nothing here would know which case to try.

### What it reaches, measured rather than predicted

All of this on 2026-09-18, over `248a4c4` plus the change, laptop, and every figure from a run
rather than from a reading.

**The prediction was wrong about where the gain is.** The card that asked for the work says this
absence is "the cheapest and the one that moves the measurement most", and the measurement it meant
is miniF2F. That one does **not** move: 21 proved and 18 unsettled before and after, the same
statements by name. What stops those eighteen is nonlinear arithmetic over several unknowns, and a
premise nobody could see was not among the obstacles.

**Where it moves is the showcase, and the direction is the one that reads as embarrassing.** Of the
fourteen theorems `docs/theorems.md` publishes, the tactic surface settled six and now settles
twelve. The six that moved are `NUM_BEZOUT`, `NUM_EUCLID`, `NUM_FACTORISATION`,
`NUM_FACTORISATION_UNIQUE`, `NUM_SQUARE_NOT_DOUBLE` and `NUM_PROV_DEDUCTION`, and not one of them is
newly **proved**: every one is a lemma this library holds, stated as `hypotheses ==> conclusion`.
A lemma that *is* the goal was refused, because `Apply` specialises it and then reads the
instance's own antecedents as obligations, and `Prove.held` takes only a candidate owing nothing.
So the system was refusing claims it had written down, and this is the size of that.

The same defect is what `RefusalSpec` had been using as a witness for the message that names a
denominator: `!x. 0 < x ==> 0 < inv x` is `INV_POSITIVE` verbatim and was refused. It is proved now,
and the witness is the same claim with nothing assumed.

**The cost is on the one suite that is already most of the build, and it was measured three
times.** Same command (`tools/sbt "tactics/testOnly …ReachSpec"`), same worktree, same corpus, one
configuration changed between runs. The machine was busy throughout and not equally busy, so read
the three as an ordering with sizes rather than as three figures to a second.

| configuration | the corpus pass | the whole spec |
|---|---|---|
| no route, at `248a4c4` | 2 min 22 s | 2 min 56 s |
| the route, without `decidedUnder` | 3 min 36 s | 4 min 13 s |
| the route, as it ships | 4 min 47 s | 5 min 47 s |

So the route doubles the most expensive suite in the repository, and half of that doubling is
`decidedUnder` alone. The corpus result is identical in all three, so none of it is buying a proof
**there**: what it buys is elsewhere and is the showcase count above.

**What `decidedUnder` is worth, asked as a measurement rather than argued.** Removed, the showcase
settles **eleven** rather than twelve: `NUM_FACTORISATION_UNIQUE` is the one that needs a subgoal
decided with the goal's premises in front of it, and the other five do not. `ContextSpec` and
`RefusalSpec` pass without it. So the price of that one theorem is about seventy seconds of
`ReachSpec`, and it is kept, for the reason the section above gives: the facts reaching the library
lookup and not the arithmetic is half a capability, and the half that is missing is the one a
corpus of arithmetic statements would need. **That is the line to reconsider first if the wall
clock becomes the binding constraint**, and reconsidering it is deleting one method.

## Alternatives rejected

**Adding the assumptions to the `Library` and building a `Chaining` per goal.** It is the obvious
implementation and it destroys the thing that makes the search usable: the index over the library is
built once, and it is what makes a question milliseconds. A per-goal index over every entry, at
every subgoal, is the cost of the search multiplied by the size of the library. The facts are few
and about this goal, so they are carried beside the index and tried first.

**Asking the route before chaining over the whole goal.** A lemma that concludes the implication
itself is the cheaper proof and the one a reader expects, and moving the route in front of it would
change what already-proved goals rest on. A search may add a theorem and must never take a refusal
away; the order is what makes that true here.

**Discharging inside the search, so that each candidate closes its own assumptions.** The
assumptions are needed by later steps of the same fold, and the search's end check is about the
target rather than about the goal. Discharging there would mean re-assuming immediately afterwards,
and the theorem the caller wants would still have to be rebuilt at the top.

**Relaxing the hypothesis test everywhere rather than under a context.** A one-line change, and it
makes `Prove`'s `Right` a lie: a theorem resting on something nobody assumed would be returned as
unconditional, which is the failure this repository exists not to have.

**Saturating forwards from the facts.** Deriving the consequences of `H` before anything asks for
one is the next absence on the front page's list and a different piece of work: it needs a
redundancy criterion and a bound, and `docs/adr` will record it when it is built.
