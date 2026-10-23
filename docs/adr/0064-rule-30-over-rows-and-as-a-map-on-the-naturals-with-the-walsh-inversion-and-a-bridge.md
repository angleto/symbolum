# 0064. Rule 30 over rows and as a map on the naturals, with the Walsh inversion and a bridge between them

- **Status:** accepted
- **Date:** 2026-10-23

## Context

Mycelium card `25c7d137` asks for Rule 30 in the kernel as a second instance of the method of
[`0062`](0062-the-finite-fourier-inversion-and-the-collatz-iterate-over-characterising-equations.md):
a closed projector for one step, a finite dependence on the start, and an inversion that turns the
dependence into a series. Angelo asked for both formulations the card's note (Mycelium 917b3939)
explored, and for a theorem tying them together.

The two are the same automaton read two ways. Over **rows**, cell `i` at time `t + 1` reads three
cells at time `t`. Over **the naturals**, the rows grown from a single cell, read as numbers, are
the orbit of 1 under `F n = n XOR (2 n OR 4 n)`, bit `j` of `F n` reads bits `j`, `j - 1` and
`j - 2` of `n`, and the centre column is bit `t` of `F^t(1)`. The second reading puts the questions
of the Rule 30 prize in the shape `CollatzFourier` already has: an iterate on the naturals, its
residues modulo a power of two, and a transform over those residues.

## Decision

**Nothing is declared, as in `0062`.** Every statement is over the equations that characterise its
object, and two existence theorems show the equations can hold. Over rows the object is
`run : (num -> bool) -> num -> num -> bool` with

    run x 0 i = x i
    run x (SUC t) i = ~(run x t i = (run x t (i + 1) \/ run x t (i + 2)))

which is Rule 30 in a frame moving one cell per step, so that every position is a natural and the
cell reads itself and the two to its right. Over the naturals it is `g : bool -> bool -> num -> num`
and its iterate, with

    g p q (2 m)     = COND (p \/ q) 1 0 + 2 * g F p m
    g p q (2 m + 1) = COND (p \/ q) 0 1 + 2 * g T p m
    iterate n 0 = n
    iterate n (SUC t) = g F F (iterate n t)

`g p q n` is the map with the two bits below `n` given as `p` and `q`, and `F n = g F F n`. The
library has no bitwise operations, and these are the equations on halving that the shortcut Collatz
map is given by in `0062`. **They need no base case**: at `m = 0` the first reads
`g F F 0 = 2 * g F F 0`, which forces zero, and that was measured on `F n = g F F n` for `n < 5000`
before it was written.

**A cell is a sign, `COND b (0 - 1) 1`.** XOR becomes a product and the step a polynomial,
`RULE_THIRTY_SIGNED`, which is the counterpart of `0062`'s cosine projector.

**One Walsh inversion, stated as `REAL_DFT_INVERSION` is**, at a residue modulo `2^k`, with the
character of a subset `s` of the low `k` bits at `n` the product over the bits of `s` of the sign of
bit `j` of `n`:

    WALSH_INVERSION
      !f k n. f (NUM_MOD n (NUM_POW 2 k)) =
        Sum (\s. Sum (\y. f y * chi s y) (NUM_POW 2 k) / real_of_num (NUM_POW 2 k) * chi s n) (NUM_POW 2 k)

The card's first plan had an inversion over rows for formulation A as well. It is not stated: the
row form of a cell reaches this one through a code of its window as a number, which `ENCODE` reads
back, and a second inversion would have been a copy.

**What is published, fifteen facts**, each compared with its written statement in
`Complex.construct`, with no hypotheses and resting on no axiom beyond the three of the chain:

- over rows: `RULE_THIRTY_SIGNED`, `RULE_THIRTY_EXISTS`, `RULE_THIRTY_SHIFT` (the automaton
  commutes with translation), `RULE_THIRTY_CONE` (cell `(t, i)` depends on cells `i .. i + 2t`),
  `RULE_THIRTY_LEFT_PERMUTIVE` (changing cell `i` alone among those changes cell `(t, i)`),
  `RULE_THIRTY_WALSH_FORM`, `RULE_THIRTY_BALANCED` (over all `2^(2t+1)` windows the cell is on half
  the time);
- over the naturals: `RULE_THIRTY_MAP_EXISTS`, `RULE_THIRTY_MAP_RESIDUES` (`iterate n t` modulo
  `2^k` depends on `n` modulo `2^k`), `RULE_THIRTY_MAP_INJECTIVE` (and is injective there),
  `RULE_THIRTY_MAP_ROW_LENGTH` (`F^t(1)` has `2t + 1` bits), `RULE_THIRTY_MAP_BALANCED`,
  `RULE_THIRTY_MAP_WALSH_FORM`;
- shared: `WALSH_INVERSION`, and `RULE_THIRTY_BRIDGE`: on the row whose cell `p <= k` is bit
  `k - p` of `n` and whose cells past `k` are off, cell `(t, i)` is bit `j` of `iterate n t`
  whenever `i + j = k`.

**The balance of the map is stated modulo `2^(j+1)` for bit `j`.** That is the form that follows
from injectivity by pairing `n` with `n + 2^j`. The form over any `2^k` with `j < k` would need a
lemma that a sum is unchanged under a permutation of its index, which the library does not have and
this card does not need.

## Alternatives rejected

**Declaring the automaton or the map as constants.** Four equations say what they are, and a
constant would be a row in `docs/reading-register.md` for what the equations already say; `0062`
made the same choice for the same reason.

**The map through a constant for XOR on the naturals.** It would make `F` a one-line definition and
put three bitwise constants, their laws and their register rows in front of every theorem here. The
halving equations cost one construction, the existence theorem, and nothing downstream.

**Only one formulation.** Rows are the automaton in its generality; the naturals are where the
prize's questions and the Collatz shape are. The bridge is what lets a fact proved in one be read in
the other, and it is the cheaper of the two halves.

## Consequences

`Complex` publishes fifteen more facts and declares nothing. `RuleThirty` sits beside
`CollatzFourier`, reads none of the complex numbers, and is there because the steps it is written
in are that link's; `ComplexKit` now also holds the helpers the two had each written for
themselves (`substitute`, `predicateOf`, `introduce`, `sumCongReal`), and `FiniteFourier`'s own copy
of `sumCongReal` is gone with them.

Nothing here settles a problem of the prize, and the reason is stated with the theorems rather than
left to a reader: the bridge says the centre column is bit `t` of `F^t(1)`, and every structural fact
proved is about all starts at once or about a fixed bit, while the column reads one orbit along a
bit that moves with time. Note 917b3939 is the account in prose, with the measurements and the
scripts that reproduce them.
