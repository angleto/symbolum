# 0011. The numeric screen has two stages, and the second is arbitrary precision

- **Status:** accepted
- **Date:** 2026-09-11

## Context

`Discovery` screens a candidate identity by evaluating both sides at a hundred points and certifies
whatever survives. The evaluation is `Expr.eval`, which answers in `Double`, and the screen's
tolerance is `Discovery.Tolerance`, which is `1e-8` and relative. `docs/adr/0005` records the same
choice on the other side of the border, for `Model`, and neither is being reopened as an error:
sixteen digits is the right size for a filter whose job is to throw away what is obviously
different, and whose false positives cost one refusal each.

Two things the declared purpose needs do not fit inside sixteen digits, and both were written down
before this change rather than discovered by it.

**Integer relation detection does not work there at all.** Finding integer coefficients that
annihilate a combination of `k` real values costs roughly `k` times the number of digits in the
coefficients. The discoveries in that family, the BBP formula for pi and the Ramanujan-type series,
were made at hundreds of digits. At sixteen, an accidental agreement among a handful of values is
ordinary, so the method does not return bad answers: it returns nothing that can be told from noise.
That is the source the conjecture generator does not have, and it is the one that has actually
discovered new mathematics elsewhere.

**The screen already lets a measured false positive through.** `x + x/1000000000` against `x`
differs by one part in a thousand million, which is under the tolerance. It survived the screen,
reached the kernel, and came back refused, and `DiscoveryPrecisionSpec` carried that as its closing
assertion with a comment saying in as many words that a loop which screened and reported would have
called it a discovery. Nothing reports the survivors today. A generator proposing at volume would,
and the noise would be proportional to the volume.

## Decision

The screen has two numeric stages, and the kernel is the third thing rather than the second.

1. `Double`, at `Discovery.Tolerance`, unchanged and still first. A candidate that already differs
   at sixteen digits is finished, and nothing more expensive is spent on it.
2. `Precise`, over `Arbitrary`, at fifty digits for the standard screen and at whatever a caller
   asks for otherwise. Run **only** on what the first stage could not separate.
3. The kernel, for what neither stage can separate at any precision.

`Arbitrary` is arithmetic to a stated number of digits over the JDK's `BigDecimal`, with pi, e, the
exponential, the logarithm, the three circular functions and the power written out as series with
their argument reductions. It lives in `modules/core`, which is the untrusted half: a wrong digit
costs a wrong candidate and can never cost a theorem, and that is what makes hand-written series a
reasonable thing to have rather than an alarming one.

**The two stages produce different outcomes, and they are not merged.** A pair the first stage
separates is `Discovery.Disproved`. A pair the second separates is `Discovery.Separated`, and it
carries the number of digits the two agreed to. They are the same verdict in the ledger, because
what a verdict answers is whether asking again could give a different answer; they are different
facts about the candidate, because one was written wrongly and the other agreed to forty digits
everywhere it was asked.

**A tolerance is a property of a stage.** `Discovery.Tolerance` is the first stage's and keeps the
measurement that chose it. `Discovery.Slack` is the second's, and it counts digits given away rather
than taking a ratio.

## The alternatives, and why not

**A library instead of `BigDecimal`.** The card asked for this to be decided by measuring rather
than argued. Measured: six hundred transcendental evaluations at two hundred digits take about a
third of a second, which is half a millisecond each, and the screen asks for a few thousand of them
per run. A dependency would have to beat that by enough to be worth being a dependency, and nothing
in reach does. `ArbitrarySpec` carries the timing so that the answer can change when the measurement
does.

**Replacing `Double` rather than following it.** The first stage throws away almost everything for
almost nothing. Running fifty digits over every pair would multiply the cost of a screening run by
the ratio of the two arithmetics and change no answer, because every candidate the second stage
kills the first stage also kills, except the ones the first stage cannot see.

**Folding `Separated` into `Disproved`.** This repository has merged two different outcomes three
times and been wrong each time, which is what `docs/adr/0005` is largely about. A near-identity that
survived to the fortieth digit is the most interesting thing a screening run can produce short of a
theorem, and it would be indistinguishable from a candidate with a sign error.

## Consequences

`KnownSurvivors` in `DiscoveryPrecisionSpec` is empty. It held one entry, which was the false
positive above, and the assertion that named it now asserts the second stage catches it at the ninth
digit. The list stays, because it fails when a member stops failing as well as when one starts.

The margin the second stage rests on is measured rather than assumed, and it is wide: over the
twenty-one labelled candidates, every true one agrees to 49 or 50 digits at its worst point and the
false one agrees to 9. There is nothing in between. That gap is what makes the stage safe, and not
the precision by itself: a true identity does **not** agree to every digit, because every step of an
expression rounds.

The integer relation source is unblocked and is not built here. What this decision buys it is
arithmetic it can run on; the detection itself is a separate piece of work with its own calibration,
and the calibration is whether it can rediscover a relation that is invisible at sixteen digits.

`Precise` refuses `Derivative` and `Integral` rather than evaluating them, because both are
approximations whose error comes from a step size rather than from the arithmetic, and fifty digits
of a five-point finite difference is fifty digits of which six are about the derivative.
