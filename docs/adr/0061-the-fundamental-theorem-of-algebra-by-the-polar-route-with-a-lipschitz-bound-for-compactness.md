# 0061. The fundamental theorem of algebra by the polar route, with a Lipschitz bound standing in for compactness in the plane

- **Status:** accepted
- **Date:** 2026-10-21

## Context

Mycelium card `b244157b` is the fourth of the four Angelo opened on 2026-09-27, and the route is his
choice: **polar**, the least value of `|p|` and d'Alembert's lemma, rather than Littlewood's argument
with square roots only. It depends on the second card, the complex numbers of
[`0060`](0060-complex-is-a-type-of-its-own-because-the-operators-are-shared.md), for the `k`-th
roots that d'Alembert's lemma spends.

The card lists five pieces (the continuity of a polynomial, its growth, compactness in two
dimensions by Bolzano-Weierstrass, d'Alembert's lemma, the theorem) and asks that the form of a
polynomial be decided in writing before anything is proved. It also records that the library had no
Bolzano-Weierstrass, measured on the day it was opened. What the library had was the extreme value
theorem in one variable, relative to an interval (`CONTINUOUS_ATTAINS_MIN_WITHIN`), and every
consumer of compactness so far had needed nothing finer.

## Decision

**A polynomial is a coefficient function and a finite sum.** The theorem is

    !c:num->complex. !n:num. 0 < n /\ ~(c n = complex_of_real 0) ==>
      ?z:complex. complex_sum (\k:num. c k * complex_pow z k) (SUC n) = complex_of_real 0

with `c n` the leading coefficient and nothing said about `c` past `n`. No constant is declared, so
the statement is read in the signature the complex numbers already have and costs no row in
`docs/reading-register.md`. `~(c n = 0)` makes `n` the degree, and `0 < n` is needed rather than
cautious: at degree zero the claim is false, and `ComplexSpec` proves that the constant polynomial
one has no root.

**Compactness in the plane is the one-variable theorem used twice, because `|p|` is Lipschitz on
bounded sets.** `|z^k - w^k| <= k S^k |z - w|` when `|z|` and `|w|` are at most `S >= 1`, by
induction on `k`, and summed over the coefficients that is a Lipschitz constant for `p` on the disc
of radius `S`, written down from the coefficients rather than obtained by an epsilon argument. On the
square of half-side `R`, for each `x` the modulus along the vertical line through `x` is Lipschitz,
so continuous relative to `[-R, R]`, so it has a least point `g x`, chosen by `select`. The value
`|p (x + i g x)|` is Lipschitz in `x` with the same constant, because the least value on one line is
at most the other line's value at the same height plus the horizontal distance times the constant.
So it has a least point `x0`, and `x0 + i g x0` is least on the square. A growth estimate,
`|p z| > |c 0|` outside a disc whose radius is read off the coefficients, makes the least point of a
square containing that disc least everywhere, since `0` is in the square and `|p 0| = |c 0|`.

**The shift `p (z + w)` is written by Horner, not by the binomial theorem.** d'Alembert's lemma
needs `p (z + w)` as a polynomial in `w` with the same leading coefficient. By induction on the
degree over `p z = c 0 + z * p' z`, the shifted coefficients are built with `COND` from those of
`p'`, and the claim carries that they vanish past the degree, which is what makes the top one come
out equal to `c n`. Nothing is summed twice and no binomial coefficient appears.

**d'Alembert's lemma** takes the least index `k > 0` with a coefficient `b k` that is not zero
(`NUM_LEAST`), writes `p (z + w) = b 0 + w^k s w` with `s 0 = b k`, takes `u` with
`u^k = -b 0 / b k` (`COMPLEX_ROOT`) and `w = t u` for a real `t` in `(0, 1]`, and bounds
`|p (z + w)|` by `(1 - t^k) |b 0| + t^k |u|^k |s w - s 0|`. The same Lipschitz bound, applied to
`s`, makes the second term at most `t^(k+1)` times a constant, and `t` is the smaller of one and a
quotient chosen so that the constant times `t` is under `|b 0|`.

**The derivation is a file beside `Complex`, and `Complex` publishes it.** `Fundamental.scala`
stands to `Complex.scala` as `ExtremeValue.scala` stands to `Continuity.scala`. Seven facts are
published: the theorem as `FUNDAMENTAL_THEOREM_OF_ALGEBRA`, its two halves as
`COMPLEX_POLY_MINIMUM` and `DALEMBERT`, and four facts of the norm a consumer of the complex
numbers reaches for and nothing published until now: `COMPLEX_NORM_OF_REAL`, `COMPLEX_NORM_NEG`,
`COMPLEX_NORM_POW` and `COMPLEX_NORM_TRIANGLE`. The lemmas in between are not published, because
several are stated over the free variables of the square they are used on.

## Alternatives rejected

**Bolzano-Weierstrass in two dimensions, as the card proposed.** A bounded sequence in the plane
has a convergent subsequence, from the one-dimensional theorem through a monotone subsequence and
`MONOTONE_CONVERGES`, and then `|p|` attains its infimum on a closed disc. It is the textbook
route and it is longer here by everything it needs that the library does not have: subsequences as
compositions with a strictly increasing index map, the infimum of `|p|` on the disc as a constant
with its approximating sequence, and the continuity of `|p|` at the limit as a statement about
sequences. The argument above needs none of it, because a polynomial carries its own modulus of
continuity. What it does **not** give is Bolzano-Weierstrass itself: the library still has no
compactness in two dimensions for a function that is merely continuous, and the next development
that needs one meets that gap as this card would have.

**A list of coefficients.** `Listing` exists, and a polynomial as a list folded by Horner's rule is
how several systems write it. The statement would then name a fold where a reader expects a sum, and
the leading coefficient would be "the last element of a non-empty list whose last element is not
zero", which is three facts about lists where `~(c n = 0)` is one about a function. The function
form leaves the coefficients past the degree unconstrained, and no lemma here needed them to be
anything.

**A constant `poly` for evaluation.** It would shorten the statement and add a constant to the
signature and a row to the reading register, for a sum that is already readable as written.

**A link of its own above `complex`.** The theorem declares nothing, and a link is what a
development with constants needs; a file of derivations beside the link it belongs to is the
arrangement `ExtremeValue` and `Within` already have.

## Consequences

The complex numbers read four more links below them than they did (`Classical`'s derived facts,
`Magnitude`, `Limit` and `Continuity`), all of which were already under them in the chain, and
`Complex.construct` takes the reals and the definition of `continuous_within`.

The facts rest on choice, eta and infinity and on nothing else, which `ComplexSpec` asserts over
every fact the complex numbers publish. Every published implication is discharged at a polynomial
somebody can name, `1 + z + z^2`, and `ComplexSpec` also proves that no real number is a root of
it, so the root the theorem gives there is not real.

Building the complex numbers now builds this derivation too, every time the chain is built. That is
a cost in the time and the live heap of every suite that builds a chain; it is measured where the
change landed rather than written here, since a figure of that kind depends on the machine.
