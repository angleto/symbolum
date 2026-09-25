# 0041. A series is decided against closed forms, and in both directions

- **Status:** accepted
- **Date:** 2026-09-25
- **Extends:** 0017, 0023

## Context

Until this record the answer set about a series was {converges, silence}. `Limit` could obtain a
convergence (monotone convergence, the comparison test, absolute convergence, the Cauchy product)
and nothing anywhere in the proof side could say that a series fails to converge, so a question
whose answer is "no" came back as a refusal indistinguishable from "I could not read it".

The surface did not reach even the "yes" half. Measured on 2026-09-18 with `Ask`: the positive
control `converges (\n:num. (1:real)) (1:real)` was proved, because `CONVERGES_CONSTANT` **is** that
goal and the library scan runs before the address rule; but
`?l:real. converges (Sum (\i:num. Power ((1:real) / 2) i)) l` came back unsettled, with a message
listing four shapes to restate it as, none of which a convergence is. Two things stood in the way
and only one of them was a missing lemma:

- **The address.** `Prove.addressOf` had no address for a convergence, so the goal was sent to
  nobody. No lemma added to the library could change that for a goal the scan cannot close.
- **The shape of the lemmas.** `SUM_COMPARISON` concludes `?l. converges (Sum f) l`, and matching
  a goal against that conclusion determines `f` and says **nothing** about the dominating series
  `g`, which occurs only in the hypotheses. The ratio test has the same defect with its ratio and
  its index. No search that specialises a lemma by matching its conclusion can use either, whatever
  its obligations cost. Something has to construct the missing argument, and nothing that matches
  can construct anything.

The request was that convergence become something the system determines. It cannot be complete: for
any decidable `P` on `num` the summand `COND (?j. NUM_LE j i /\ P j) 1 0` diverges exactly when
`?j. P j`, so a procedure answering every convergence question answers every `Pi-0-1` question.
"Determines" therefore has to name a fragment, and the procedure has to refuse outside it.

## Decision

**A divergence is a constant.** `diverges s` is defined as `~(?l. converges s l)`. The negation
would say the same, and a constant is chosen for what reaches a reader and a router: a theorem
`diverges (Sum f)` names its predicate where a refusal is prose, and `Prove.addressOf` would send
`~(...)` to LINARITH as a denial and refuse it there.

**The criteria are published in both directions, in `Limit`, derived in `Criteria`.** The term test
and the terms of a convergent series vanishing; the powers of a number inside the unit interval
vanishing; the geometric series at a symbolic ratio, **with its value** `inv (1 - q)`, and its
divergence at a ratio of magnitude one or more; the ratio test and its other side; and a constant
factor carried out of a convergence and, where it is not zero, out of a divergence. The exponential,
the cosine and the sine get the value of their series, `EXP_CONVERGES`, `COS_CONVERGES` and
`SIN_CONVERGES`, in `Transcendental`. None of it costs an axiom.

**The procedure, `Convergence`, reads a summand against closed forms and does not apply the ratio
test.** Its fragment is a summand `Power q i`, `Power t i / real_of_num (NUM_FACT i)`, the cosine's
or the sine's term, or a constant times one of those. On a numeral ratio the geometric series is
decided in both directions; the others converge at every argument and are answered with their value.

**It refuses in three ways and keeps them apart.** A summand outside the fragment is named, and
nothing was learned. A summand that is a rational function of the index is named as that, because
there the ratio of consecutive terms tends to one and no ratio test decides anything: also nothing
learned, and a different next move (Raabe, Gauss, the p-series), so a different sentence. And a goal
the procedure refutes comes back as `Denied`, a new refusal carrying the theorem that denies it,
with standing `Decided`. `NotOfForm` would have said nothing was learned, which is false, and
`DoesNotFollow` speaks of a combination of LINARITH's hypotheses, which is not this.

**`Prove` gains a sixth address, `Series`,** for `?l. converges (Sum f) l`, `converges (Sum f) v` and
`diverges (Sum f)`. It is asked first among the addresses, because none of the arithmetic ones reads
a convergence and each would fall through to `Nobody`. The library scan still runs before any
address, so a series some lemma states outright is still settled there.

**The Collatz claim is `Conjugacy.GAMMA_CONVERGES`, beside the chain.** It is the one real series the
Collatz investigation holds, section 3.1.10 B of `collatz@8b991e5`, and it is a function of the
chain rather than a link, for the reason `Collatz` is: a fact about one investigation's series does
not belong in the vocabulary a question about the reals is typed in.

## Why closed forms and not the ratio test

The ratio test is the obvious engine, and it is published. It is not what the procedure applies,
and the reason is the cost of its hypothesis rather than a preference. Applying it to a summand
means proving `abs (f (SUC n)) <= r * abs (f n)` at a **symbolic** `n`; for the exponential's series
that is `POWER_SUC`, `NUM_FACT` at a successor, `real_of_num` across a product and a cancellation of
a reciprocal, all before LINARITH is asked anything, and a different sequence of those for every
shape. Every shape in the fragment already has a published theorem saying what its series does,
and specialising it costs one step. So the procedure is closed forms plus a scaling, and the ratio
test is a lemma for a hand derivation, which `LimitSpec` spends on one.

What this gives up is named: **the hypergeometric terms**, whose ratio is a rational function of
the index, are decided by the ratio test whenever the limit of the ratio is not one, and are outside
this fragment. `real_of_num i * Power (1/2) i` converges and is refused. Widening the fragment to
that class is the work the ratio test is for, and it is a card of its own rather than a line here.

## Consequences

- A convergence goal in the fragment is settled by `Ask` and by `Prove`; one outside it is refused
  by name, and one the procedure refutes is refused with the refutation.
- `Remedy` gains an arm for `Denied`, and it is `Settled`: no restatement of a goal that the
  procedure has refuted changes the answer.
- The geometric series at one half, which `LimitSpec` obtained in ninety lines of kernel calls and
  without its value, is one specialisation of `SUM_GEOMETRIC_CONVERGES` and converges to `2`.
- LINARITH refuses an equation whose left side occurs inside its right side, `x = c * x`, with a
  message about RING that names neither the goal nor the cause, and takes the same content with the
  right side named. Met in `Criteria.powerOfAFraction` and worked around there; it is a defect of
  LINARITH and has a card of its own.

## Alternatives rejected

- **The negation instead of a constant.** Rejected for the router and the reader, above.
- **The ratio test as the procedure's engine.** Rejected for the cost of its hypothesis per shape,
  above; kept as a published lemma.
- **The algebra half proposing a witness**, which is `docs/adr/0003`'s arrangement. `core` has no
  notion of a series or of a limit, so the proposer would have to be built before it could propose,
  and the closed forms need no witness at all.
- **`NotOfForm` for a refuted goal.** Rejected: it reports that nothing was learned.

## What is not here

- The hypergeometric fragment, as above.
- Anything at ratio limit one: Raabe's and Gauss's tests, the p-series, Cauchy condensation.
- The sharp form of section 3.1.10 B, convergence **exactly** on the expanding words: its divergence
  half wants the root test, and so a `limsup` and `n`th roots.
