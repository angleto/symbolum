# 0063. Finite distributions are functions on an initial segment, and the value of an experiment divides by nothing

- **Status:** accepted
- **Date:** 2026-10-22

## Context

Mycelium cards `38b56577`, `a5c6f793`, `443e4c06` and `1535fdb7`, opened on 2026-10-22 at Angelo's
request from the essay "Sull'utilità e il danno della storia per i modelli linguistici"
(`thinktank/utitlita_e_danno`). The essay uses one theorem, the easy direction of Blackwell's: an
experiment obtained from another by a random garbling is worth no more in any decision problem. It
then prints a counterexample to the conditional reading of that theorem, its case E5, with three
values, `7/20`, `9/16` and `1/8`. Measured on `0363b677`, this repository had no probability at all:
`git grep -i -l` over `docs` and `modules/theories` finds `Blackwell`, `stochastic`, `garbling`,
`Bayes` and `posterior` nowhere, and the hits for `probabilit` and `expectation` are prose.

## Decision

**A distribution on `n` outcomes is a function `p : num -> real` read on `[0, n)`**, not a type of
its own, and a defined predicate says which functions qualify:

    DISTRIBUTION n p  =  (!i. i < n ==> 0 <= p i) /\ Sum p n = 1
    CHANNEL n m k     =  !y. y < n ==> DISTRIBUTION m (k y)

A channel from `n` states to `m` signals is `k : num -> num -> real`, row `y` its distribution of
signals in state `y`. An expectation is `Sum (\i. p i * f i) n` and gets no constant: it is a sum,
and every fact about sums already applies to it.

**The probabilities are reals, and the rationals are what an instance writes.** The essay wants exact
arithmetic, and a numeral of the reals is exact: `7 / 20` is a term the arithmetic decides. The
alternative, the type `rat` of `Fraction`, holds the same values with a fraction of the library: no
`Sum`, no order procedure, no `RING` over it. Every statement here is about all real-valued
distributions, so it is about the rational ones in particular.

**A finite maximum over an index, by recursion,** because the library holds `max` of two reals and
nothing over a set:

    Maximum f ZERO     = f ZERO
    Maximum f (SUC n)  = max (Maximum f n) (f (SUC n))

so `Maximum f n` ranges over `[0, n]`, closed, and an action set is never empty. Its facts are that it
bounds every term, that it is one of them, that it is the least bound, that it is monotone, and that
it commutes with a non-negative scale. Beside it `Argmax f n`, the first index where the maximum is
taken, also by recursion: it is the optimal rule as a function, which the essay's E5 evaluates on a
sub-population, and `ARGMAX_ATTAINS` says it lies in `[0, n]` and takes the maximum.

**The value of an experiment divides by nothing.** With `top + 1` actions, utility `u a y` of action
`a` in state `y`, prior `prior` and channel `k` to `m` signals,

    VALUE n m top prior k u  =  Sum (\s. Maximum (\a. Sum (\y. prior y * k y s * u a y) n) top) m

which is the expected utility of the Bayes-optimal action, summed over signals before conditioning.
The posterior form divides the inner sum by the probability of the signal, and that probability can
be zero; this form needs no case for it. The two agree wherever every signal has positive
probability, by the scale fact, and that agreement is a published theorem, `VALUE_POSTERIOR`, rather
than a remark.

**Blackwell's easy direction is stated with only the hypothesis it uses:**

    BLACKWELL_GARBLING
      !n m r top prior k g u. CHANNEL m r g ==>
        VALUE n r top prior (\y t. Sum (\s. k y s * g s t) m) u <= VALUE n m top prior k u

Neither the prior nor `k` has to be a distribution. The proof is
`sum_t max_a sum_s g s t X a s <= sum_t sum_s g s t max_a X a s = sum_s max_a X a s`, where the first
step needs `g` non-negative and the second needs the rows of `g` to sum to one, and nothing in it
reads `X`. A statement that also asked for the prior and `k` would be a weaker theorem, and a reader
would believe the extra hypotheses were needed.

**E5 is certified in the test scope and shown as an example, not published as library facts.** Its
values are facts about one model of eight answers, and a library lemma is a fact a search should be
able to use; `Find` returning `E5_VALUE_NEW_TASK` for a question about sums would be noise. The
certifying spec derives each value with no hypotheses and asserts the conclusions as text, which is
what makes them theorems of the kernel and not computations beside it.

## Consequences

One link, `Decision`, over the end of the chain, reading `Series` for the sums and `Magnitude` for
`max`. Six defined constants, `Maximum`, `Argmax`, `DISTRIBUTION`, `CHANNEL`, `VALUE` and
`INDEPENDENT`, and no axiom; `Derivation.axiomsOf` over every fact is asserted equal to the chain's
three. Six rows join `docs/reading-register.md`, one per constant.

**The rest of a distribution's arithmetic is facts, not constants**, and the second change on the
link added it on 2026-10-22: a marginal through a channel is a distribution
(`DISTRIBUTION_MARGINAL`), two channels in a row are a channel (`CHANNEL_COMPOSE`), the expectation
`Sum (\i. p i * f i) n` is monotone and keeps a constant (`EXPECTATION_MONOTONE`,
`EXPECTATION_CONSTANT`) and is linear (`EXPECTATION_LINEAR`, which assumes nothing of `p`), the product of two
distributions on `[0, m * n)` read at `m * a + b` is one (`DISTRIBUTION_PRODUCT`) and is independent
(`PRODUCT_INDEPENDENT`), and the posterior at a signal below `m` of positive probability is a
distribution (`POSTERIOR_DISTRIBUTION`). Independence is the one that is a constant, because it is a
property a joint distribution has or lacks rather than an operation, and a statement about it has to
be able to name it.

**The linearity was left to `SUM_LINEAR` on 2026-10-22 and is a fact of its own since 2026-10-23**,
for the reason `Series` publishes `SUM_ADD` beside `SUM_LINEAR`: a rewrite rule is matched
syntactically, and `SUM_LINEAR` reads a summand `a * f i + g i`, where an expectation of a
combination is written `p i * (a * f i + b * g i)`. Reaching one from the other takes a pointwise
identity, a congruence under the sum and `SUM_SCALE`, which is the derivation `EXPECTATION_LINEAR` is.

The derivations are written in `ComplexKit`'s steps over this link's own theory, with a driver whose
complex components are empty: every goal here is real, and the driver closes a real goal with `RING`
after rewriting, which is what `Series` does by hand. A second kit for the reals would be the copy that
file exists to prevent.

## Alternatives rejected

**A type of distributions**, carved with `Kernel.defineType` from the functions satisfying
`DISTRIBUTION n`. The type would depend on `n`, which this logic cannot say, and a type per support
size is a family nobody could write a theorem over.

**The posterior form of the value**, `Sum (\s. q s * Maximum (\a. post a s) top) m` with `post` a
quotient by `q s`. It is the form textbooks print, and it needs a case split at every signal of
probability zero, which an instance with sixty-four signals and a channel with zero entries has.

**The full Blackwell–Sherman–Stein theorem**, both directions. The converse needs a separating
hyperplane in the simplex of posteriors, and the essay uses only the direction proved here.

## What was measured and what was not

Measured before this record: the absence above, and the three values of E5 recomputed outside the
kernel with exact fractions from the model as the essay describes it, `V0 = 7/20`, `V1 = 9/16` on
average and `1/8` on new tasks at `phi = 1/2`, `7/20` everywhere at `phi = 1/10`, with **no tie** for
the optimal action at any of the sixty-four signals, so `1/8` does not depend on how a tie is broken.

Measured after it, on 2026-10-22: the kernel derives the three values of E5 with nothing assumed, in
58 to 80 seconds after the chain is built, on a machine running two other builds. It does not
compute sixty-four maxima of eight numbers. At the signal `8 s + g` the score of answer `a` is
`1/8 * P(s | a) * P(g | a)`, and three case splits on `a = g`, `s = a` and `s = g` show it largest at
`a = g`, strictly, the closest comparison being `49/2240 < 117/2240` between the products
`P(s | a) P(g | a)`, the factor `1/8` common to both sides left out. The sums over the signals then
close by `SUM_GROUPS`, `SUM_INDICATOR` and `SUM_COND_COUNT`. The strictness is what `ARGMAX_UNIQUE`
needs to name the reader's rule for the third value, so the absence of ties measured outside the
kernel is also a theorem inside it.

One thing the arithmetic taught and the record keeps: the closing step reads rational numerals as
numbers only when `Linarith` is called on them directly. Through `ComplexKit.linAfter` every
quotient is abstracted into an atom, which is right for `x / y` and turns `8 * (1 / 8) = 1` into
`8 * q = 1`, so the essay's case closes with its own step that rewrites and then calls `Linarith`.
