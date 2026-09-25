# 0045. A polynomial in the index times a geometric term: the ratio test at degree one, a comparison for each degree after it

- **Status:** accepted
- **Date:** 2026-09-25
- **Extends:** 0041

## Context

`docs/adr/0041` decided that `Convergence` reads summands against closed forms and does not apply
the ratio test it publishes, and it named what that leaves out: the summands whose ratio of
consecutive terms is a rational function of the index with a limit other than one. Its witness was
`real_of_num i * Power (1/2) i`, which converges and was refused. `SUM_RATIO_TEST` had been proved
and had no consumer but a spec that detached it at a series the closed forms already settled.

## Decision

**Degree one is the ratio test, and the index it asks for is a term.** `SUM_INDEX_GEOMETRIC_CONVERGES`
is `SUM_RATIO_TEST` at `f i = i s^i` and `r = (1 + s) / 2`, from the index
`NUM_CEIL (2 s / (1 - s))` on, where `(i + 1) s <= r i` holds. The test's `N` is therefore built once,
inside a published lemma quantified over every `s`, rather than computed as a numeral by the
procedure per call; the procedure specialises the lemma.

**Every degree after that is a comparison, by induction on the degree.** With `s' = (1 + s) / 2`,
`s <= s' * s'` because the difference is `(1 - s)^2 / 4`, so `i^(k+1) s^i <= (i s'^i)(i^k s'^i)`.
The first factor is the term of the degree-one series at `s'`, which vanishes and so is bounded; the
second is degree `k` at `s'`. That is `SUM_POLY_GEOMETRIC_CONVERGES`, and `CONVERGES_BOUNDED` is
published for it.

**The divergent side is the term test**, `SUM_INDEX_GEOMETRIC_DIVERGES` and
`SUM_POLY_GEOMETRIC_DIVERGES`: at `1 <= abs q` every term from index one on has magnitude at least one.

**`Convergence` reads the two shapes**, `real_of_num i * Power q i` and
`Power (real_of_num i) k * Power q i`, and answers with those lemmas. It names no value for them,
so its answer is a fourth kind beside the three `docs/adr/0041` kept apart: a convergence to a value
it does not name, which answers `?l. converges (Sum f) l`, refutes `diverges (Sum f)`, and is
refused, saying why, as an answer to `converges (Sum f) v`.

## Why not the other roads

- **The ratio test at every degree, with the procedure computing `N`.** The inequality it needs,
  `(n + 1)^k abs q <= r n^k` from some `n` on, is of degree `k` in `n`, and LINARITH reaches degree
  three and stops. The comparison asks LINARITH for nothing above the products it already names.
- **A second ratio `t = s / s'`, so that `s^i = s'^i t^i`.** It is the textbook split and it is a
  quotient by a symbol, which LINARITH does not reason about and `Field` only cancels. Using `s'`
  twice needs no division at all.
- **Square roots**, `s = sqrt s * sqrt s`. `Root` is built above `Limit`, and the square of the
  half-way point does the same job below it.

## Consequences

- `SUM_RATIO_TEST` has a consumer that is not a spec.
- The refusal "the ratio tends to one" is narrower and right: it used to fire wherever the index
  occurred only inside `real_of_num`, and `inv (real_of_num (NUM_FACT i))`, whose ratio tends to
  zero, was refused with it. It now asks that the argument of `real_of_num` be a polynomial in the
  index.
- A summand that is a rational function times a geometric term, `Power q i / real_of_num (SUC i)`
  for one, is still outside the fragment, and so is anything at ratio limit one.
