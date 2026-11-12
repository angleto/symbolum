# 0077. A point where a premise fails did not test the claim

- **Status:** accepted, revises 0005
- **Date:** 2026-11-12
- **Card:** Mycelium `1e3ef954`

## Context

`Refutation.counterexample` samples a grid of points and looks for one where every premise holds and
the conclusion fails. Until this record it counted a point where some premise was **false** as a
point that had answered, and with no witness the answer was `Survived(n)`, which `Remedy` prints as
"the claim survived n points, which is evidence and not a decision". An entailment is put to the
test only where its premises hold, so a point where one fails says nothing about the conclusion.

The proof language found it on 2026-11-10: a goal under the hypotheses `x < 0` and `0 < x` was
reported as having survived a hundred points, none of them a point where the hypotheses held. The
linear case was repaired the next day on the proof-language branch, `Refutation.impossible`, by
asking whether the premises can hold before sampling, which the solver decides for a linear set.
That left the case no solver reaches. Measured on 2026-11-10 with classes from `ab5ed2ca`:
`{x * x < 0}` with the conclusion `x = 7` came back `Survived(100)`, and it still did after the
linear repair, because a product of two unknowns is not an atom the solver admits.

This is the confusion `docs/adr/0005` exists to prevent, "I could not ask" read as "I asked and it
was fine", in a form 0005 did not list: the model answered at every point, and the answer it gave
was about the premises, not the claim.

## Decision

**`counterexample` counts only the points where every premise held.** `Survived(n)` from it now
means n points at which the premises held and the conclusion did too. `Found` carries the same
count.

**When the model answered and some premise was false at every point that answered, the outcome is
`Refutation.PremisesNeverHeld(answered)`**, a separate answer and not one of the existing ones:

- Not `Survived`: no point tested the claim, and a count of points that did not test it reads as
  evidence when it is not.
- Not `NeverAsked`: its message says no point could be evaluated, and here every point was
  evaluated. Saying it would be false.
- Not `Contradictory`: that is a decision over every point. `{x * x < 1 / 1000000000}` holds at
  `x = 0` and comes back `PremisesNeverHeld` exactly like `{x * x < 0}`, which holds nowhere. A
  sampler cannot tell an empty set from a thin one, so it decides neither.

**`satisfying` is unchanged.** Its question is about the premises alone, so a point where a premise
fails is the answer it asks for and counts in its `Survived`. The two callers share one walk over
the grid (`Refutation.Walk`), which keeps the two counts apart and leaves each caller to read them.

**`Remedy` maps it to `AskDifferently`**, naming the question that moved: whether the premises can
hold together. `APersonLooks` is what `Survived` gets and would read as the claim having held up.
`RestateTheProblem` is what `Contradictory` gets and would assert what sampling cannot decide. The
proof language reports it as the kind `premises-never-held`.

## Consequences

- A `Survived` count from `counterexample` is now smaller wherever a premise fails at some points.
  Nothing pinned those counts. `RefutationSpec` asserts that the count lies strictly between zero
  and the number of points for `{0 < x * x * x}`, where the premise holds at about half of them.
- The sentences that counted the outcomes as seven (`AGENTS.md`, `docs/proving.md`,
  `docs/language.md`, `Abduce`, `Consistency`, `Elaborate`) now name them without a number. A count
  written in prose next to a sealed trait the compiler already enumerates is a second copy that
  nothing checks. `RemedySpec` keeps the list of every outcome and asserts its size, and that list
  is where a ninth would have to be added.
- `docs/adr/0005` keeps its text, as decision records here do. Its status line and its index row
  say that this record revises it.

## Alternatives rejected

- **`NeverAsked` with a different message.** This was the card's second option. It would make one
  outcome mean two things, "the model had nothing to say" and "the model said the premises fail".
  `Remedy` treats the first as `InterpretMore`, which here sends the reader to interpret constants
  that are already interpreted.
- **Answer `Contradictory` when the premises failed at every sampled point.** The thin set above is
  the counterexample to that: it would report satisfiable premises as contradictory.
- **Count premise-false points in `Survived` and add a second field.** Every reader of `Survived`
  would have to know to subtract. The defect was a reader taking the count at face value, so the
  count is what changed.

## What it does not cover

Points where the premises held at only a few of the hundred. `Survived(3)` is now honest about
having three points behind it, and how much three points are worth is left to the reader, as it
always was. Making the grid look for points where the premises hold, for example by solving the
linear part first and sampling only the rest, would raise that number. It is a separate change.
