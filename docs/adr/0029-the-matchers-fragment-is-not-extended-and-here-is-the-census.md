# 0029. The matcher's fragment is not extended, and the census is why

- **Status:** accepted
- **Date:** 2026-09-18

## Context

`Matching.matchTerm` decides one-way matching on the **Miller fragment**: a pattern variable applied
to distinct bound variables and nothing else. `README.md` states that as a limit — *instantiating a
lemma whose parameter is a predicate: yes, on the Miller fragment* — and the card that asked for
this work asked for the limit to be pushed: a larger named fragment, plus a refusal saying which
case it met.

Full higher-order unification is undecidable (Huet 1973), so "remove the limit" is not a thing that
can be asked for. What can be asked for is a **bigger decidable fragment**, and the two candidates
anybody reaches for are non-linear patterns (`P x x`) and patterns applied to closed arguments.
Before building either, the question is which of them the system actually asks for, and nobody had
measured it.

## The census

`Matching.matchTerm` answers `None`, which says nothing about which of its conditions fired, so the
four conditions were counted by instrumenting the file and running the suite. The instrumentation
is **not** in the tree: it is a probe, it was removed in the same session, and `StyleSpec` refused
it independently for holding mutable state.

Over `tactics/test`, one run, 2026-09-18:

| what the fragment met | count |
|---|---|
| a pattern variable applied to something that is not a binder, **with no binder in scope at all** | 4377 |
| the same, **with binders in scope** | **250** |
| a binder applied twice | 0 |
| the target using a binder the pattern variable was not applied to | 0 |

Over `tactics/testOnly ReachSpec` alone — the miniF2F corpus, which is the population the card names
and the one holding the eighteen goals the prover attempts and cannot settle:

| what the fragment met | count |
|---|---|
| no binder in scope | 278 |
| every other condition | **0** |

**Three things had to be true for those zeros to mean anything, and each was checked.**

1. *The instrument was armed in that run.* It recorded 278 events in it. A zero from an instrument
   that read nothing is the failure this repository has met before.
2. *The counters are reachable.* Run against `MatchingSpec`, which exercises the fragment's
   boundary deliberately, the escaping-binder counter fires once. So its zero on the corpus is an
   absence rather than a dead branch.
3. *One counter is not.* The non-linear counter reads **zero even on `MatchingSpec`**, which holds
   two tests written on `\x. F x x`. The reason is in those tests: the first-order walk decomposes
   the application first and reaches `F x` against `g2 (h x)`, which **is** a Miller pattern, and
   answers. The repeated-argument case is answered by the decomposition rather than refused where
   the counter sits, so that zero says nothing about demand and is reported as unmeasured.

## Decision

**The fragment is not extended, and the refusal learns to say which case it met.**

`Matching.why` is added: a caller that has to explain a refusal gets one of four `Refusal` values
back, and `None` where the pair was not refused by the fragment at all. It is a second pass rather
than a reason threaded through the walk, because the walk reaches its higher-order fall-through
70 314 333 times in one run of `tactics/test` and almost every one of those is an ordinary
first-order miss: a reason built at each is a cost paid by everything to explain the few anybody
asks about.

**Non-linear patterns are not built**, and the reason is the census rather than the difficulty: the
corpus never reaches the branch that would refuse them, and where it does meet a repeated argument
the matcher already answers through the decomposition. Building the extension would be building for
a population nobody has shown exists.

**Patterns with a non-binder argument are not built either**, on a weaker argument, which is why it
is written down separately: 250 occurrences is not nothing, and they are dominated by the shape
`P (SUC n)` — a pattern variable applied to a **term built from** a binder, which is what a
recurrence wants. None of them is in the corpus, so none of them is a goal this system fails to
settle today; every one is a consumer that already reached its answer another way or asked a
question it did not need answered. Which of the two, per site, is the measurement this record does
not have and `Matching.why` now makes cheap.

## Consequences

**The README line stands, with the measurement beside it.** Replacing a true boundary with silence
would be worse than the boundary; what changes is that a reader is told it was measured and when.

**A zero in this record is a zero over one corpus on one day.** The eighteen unsettled miniF2F goals
are blocked by nonlinear arithmetic, which this repository already said and which this census
confirms from the other side: they do not die at the matcher. A corpus that asked different
questions could move every figure here, and the next census costs a call to `why` rather than a
patched source and an eleven-minute run.

**The card's own acceptance criterion cannot be met as written**, and that is the finding rather
than a failure to deliver: it asks for a goal outside the fragment, refused today, to be proved, and
the corpus contains no such goal. What the card becomes is a decision for whoever owns it.

## Alternatives rejected

**Building the non-linear extension anyway, because it is the textbook next fragment.** It is, and
the measurement says the system does not ask for it. A decidable extension nobody exercises is a
second thing to keep correct in the one file where a wrong answer is a wrong instantiation of a
theorem.

**Threading the reason through `matchTerm`, so that every refusal carries one.** It is the design a
reader expects and it is refused on a measurement: 70 million fall-throughs in a run, almost all of
them ordinary misses. `why` re-walks and is called by the caller that wants to explain.

**Leaving the refusal silent and instrumenting again next time.** That is what this session did, and
it cost a patched source, three runs of a corpus suite, and a guard going red on the probe. The
diagnostic makes the same census a call, which is the difference between a measurement somebody
takes and one somebody talks about taking.
