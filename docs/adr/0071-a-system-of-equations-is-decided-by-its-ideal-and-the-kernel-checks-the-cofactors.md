# 0071. A system of equations is decided by its ideal, and the kernel checks the cofactors

- **Status:** accepted, takes up item 2 of 0029
- **Date:** 2026-11-10

## Context

`docs/adr/0029` sorted the miniF2F statements this system reads and does not settle by what a
prover would have to be able to do, and its item 2 was **deciding a system**: producing what a set
of equations forces and substituting it. Eight statements sat there, six under "a system, nonlinear
or with division" and two under "substitute or solve". On 2026-11-10 all eight were still
`Unsettled` in `ReachSpec`.

`Ring` decides identities of commutative rings and refuses `H ==> C` whenever `C` is not one on its
own. `Linarith` reads the hypotheses as linear facts over atoms, so a conclusion that follows from
equations by multiplying them by polynomials is out of its reach. Neither is a defect; neither is
the procedure for this.

## The measurement that decides it

Read by hand off the eight statements, which is a screen and not a settlement, and then measured:

| statement | what it needs | |
|---|---|---|
| `aime_1990_p15` | `s5 - 20` is in the ideal of `s1 - 3, .., s4 - 42` (`p + 14` and `q + 38` are, the determinant being `-1`) | ideal |
| `mathd_algebra_338` | a linear system and a product | ideal |
| `mathd_algebra_478` | substitution | ideal |
| `amc12_2000_p20` | `(t - 1)^2` is in the ideal, then `t = 1`; denominators from positivity | the radical |
| `amc12b_2002_p19` | `(abc)^2 = 518400`, then the sign | ideal and order |
| `amc12b_2002_p7` | `(a + 6)(a - 4) = 0` over the naturals, then `a > 0` | ideal, domain, order |
| `mathd_algebra_362` | the unique real root of `b^9 = c` | the order of the reals |
| `amc12b_2021_p3` | a continued fraction, all denominators | division |

So **membership in an ideal is the part every one of the first six needs and three need alone.**
The measurement after the decision is in Consequences.

## Decision

1. **The search is Buchberger's algorithm over the exact rationals, and it is not trusted.**
   `theories/Groebner.scala`. Graded reverse lexicographic order, the product criterion and no
   other refinement, every polynomial carrying its expression in the generators. It answers
   `Member` with cofactors, `NotMember` with a remainder, or `Exhausted` past a budget counted in
   coefficient multiplications.
2. **The procedure is `theories/Ideal.scala`, and the kernel checks the certificate through
   `Ring`.** `Gl = Gr + (c1 * D1 + ... + ck * Dk)` with `Di = Li - Ri` is a ring identity and
   `Ring` proves it; each `Di = 0` comes from its hypothesis by congruence; the congruence
   `Gr + (... ci * Di ...) = Gr + (... ci * 0 ...)` is built on a term this file constructed, so
   it involves **no matching**; and `Ring` closes `Gr + (... ci * 0 ...) = Gr`.
3. **Its refusal "not in the ideal" is `Unread`, never `Decided`.** `OutsideTheIdeal` in
   `modules/logic`. `x * x = 0 ==> x = 0` is true of the reals and `x` is not in the ideal of
   `x * x`; deciding would be the defect `NotEqualAsRead` was written to repair.
4. **`Prove` asks it third at the equation address, for a theorem only.** After `Ring` and
   `Linarith`; its refusal is never the one reported.

## Alternatives rejected

**The search in `core`.** `core` is the algebra system and the obvious home for a Groebner basis,
and its rational is a pair of `Double`s that falls back to a quotient past 2^53. A certificate is an
identity that has to hold exactly, and the exact rational is `theories.Rational`; a second one in
`core` would be two implementations of one rule. `Farkas` beside `Linarith` is the precedent.

**Substituting by rewriting with the assumed equations**, which is what `Algebraic` does in the
triangular case. An assumption `b = a + 1` rewrites every `b`, including those inside the other
hypotheses' differences, which then no longer vanish, and a rule whose right side contains its left
does not terminate. `IdealSpec` carries the case.

**F4, or the chain criterion.** At four unknowns and degree five they buy nothing measurable here
and each is a second argument for the search's completeness.

**A radical, the order and denominators in the same change.** Each is a step of its own, with its
own refusal; the table above says which statements wait on which.

## Consequences

**Measured on 2026-11-10, `ReachSpec` in two whole-suite runs.** Before: Proved 23, Unsettled 16,
at `6c9e0f31`. After: **Proved 26, Unsettled 13**, at `77096477` with this change. The two bases
differ by a release note and by Mycelium card `354256d9`, which changed the reals' model and was
measured moving no outcome of `Cost`; so the delta is this record's. The three that moved are the
three the table calls "ideal", by name:
`aime_1990_p15`, `mathd_algebra_338`, `mathd_algebra_478`. The other five stay Unsettled and the
table says what each waits on. These are figures of one day; `ReachSpec` prints the live ones.

**What a proof costs.** `IdealSpec` prints it: `aime_1990_p15` is 131525 inferences and
`mathd_algebra_338` 176754, and the search spent 10103 and 80 units of its budget on them. How the
inferences divide between the identity, the congruence and the discharge has not been measured.

**The kernel is what is trusted, and that was observed rather than argued.**
`tools/verify/perturb-ideal.sh` flips the sign of every cofactor the search returns: `GroebnerSpec`
goes red, and `IdealSpec`'s four goals come back `NotRebuilt` with no theorem. The same harness
fires the three other guards: the refusal called decided, the route unwired, and IDEAL's refusal
reported in place of RING's.

**A refusal nobody reads first.** Asked third, IDEAL's refusal is never the one `Prove` reports, so
`OutsideTheIdeal` reaches a reader only through a direct call. `Remedy` sends it to a person, naming
the three things an ideal does not see.

**What is next, in the order of the table:** the radical, for `amc12_2000_p20`, which is
`G^k` in the ideal and a lemma that a product of reals is zero only if a factor is; that lemma is
**not** in the library under any name, searched by shape on 2026-11-10. Then the order, combining
this with `Linarith`, for the two statements that need a sign. Neither is in this record.
