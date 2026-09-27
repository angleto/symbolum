# 0056. pi is twice the zero of cos, and the bounds that pin it are Taylor polynomials reached through the derivative

- **Status:** accepted
- **Date:** 2026-09-27

## Context

Mycelium card `4bcfc8b9` is the first of four that Angelo opened on 2026-09-27 to reach the complex
numbers, the fundamental theorem of algebra by the polar route, and the discrete Fourier form of the
Collatz formula (`collatz`, `documents/02-closed-form-formula.md` §2.3). All three want `pi`: the
polar form wants an argument in `[0, 2 pi)`, and the Fourier form wants the roots of unity
`cos (2 pi h / M)`. Measured on 2026-09-27 over the 808 lemmas of `7.0`: `sin`, `cos`, their
addition formulas, the square identity, their derivatives, the intermediate value theorem and
the monotonicity lemmas exist; no constant `pi`, no period, and no inverse of `cos`.

## Decision

**`pi` is twice the zero of `cos` in `[0, 2]`, chosen:**

```
pi = 2 * select (\z. 0 <= z /\ z <= 2 /\ cos z = 0)
```

and `acos y = select (\t. 0 <= t /\ t <= pi /\ cos t = y)`. Both are definitions; nothing is
asserted. The choice pins something because the zero exists and is the only one in `[0, 2]`:

- **Existence** is the intermediate value theorem on `[3/2, 8/5]`, where `cos` changes sign.
- **Uniqueness** is `cos` falling strictly on `[0, 2]`, because its derivative `0 - sin` is
  negative there.

**The sign changes come from six polynomial bounds, each proved by monotonicity from the one
before**, starting at `sin x <= x` and alternating up to `1 - x²/2 + x⁴/24 - x⁶/720 <= cos x`, all
for `0 <= x`. The difference between a function and its polynomial has as derivative the previous
bound's difference, so `DERIVATIVE_NONNEG_MONOTONE` closes each step, and the first step's slope is
`1 - cos t`, non-negative by the square identity. The fourth bound at `8/5` and the sixth at `3/2`
give the two signs; the third makes `sin` positive on `(0, 2)`. What lands is `3 < pi < 16/5`.

**The six derivatives are `Slope`'s**, a differentiator for sums, differences and products of `t`,
constants, `sin t` and `cos t`, and quotients by a constant. Each case is a published fact of
`Derivative` at the pieces. The function and the slope the facts produce are carried to what the
caller wrote by extensionality and `Ring`, so a wrong slope is `Ring` refusing an equation.

**`Circle` is a link**, the fifteenth, above `Integral`. `pi` is a constant a question about an
angle is typed in, so it has to be reachable from `Ask`, `Find` and the library.

## Consequences

- Twenty-one facts, two constants, no axiom. Every fact rests on choice, eta and infinity, and no
  axiom of the reals is among them, because since `docs/adr/0053` the reals have none.
  `CircleSpec` asserts the set.
- The six bounds are results in their own right, with the same statements a first course states.
  The third and the fourth are what make `sin` and `cos` computable to a sign at a written point,
  which is the thing this record needed.
- Two consequences a consumer spends are derived in `CircleSpec` from the published facts alone,
  `acos 0 = pi / 2` and `sin (2 * pi) = 0`, so the facts are shown to compose and not only to be
  stated.
- `pi` is pinned to `(3, 16/5)`. A consumer needing a tighter bound needs a longer polynomial,
  which is one more monotone step each.

## Rejected

- **The series with a bound on its tail**: `cos 2 = 1 - 2 + 2/3 - ...` with the rest under a
  geometric series, as `EXP_ONE_ABOVE_TWO` does for `exp 1`. It proves one inequality at one point,
  and carrying `EXP_TAIL_GEOMETRIC` to the cosine's even terms wants sums split at an index and
  compared term by term. The bounds reach the same Taylor polynomials through the derivative and
  hold at every point.
- **Taylor's theorem with the Lagrange remainder**, which exists (`TAYLOR`). It wants the whole
  family of derivatives `cos, -sin, -cos, sin, ...` as one function of the order, a case split on
  six orders to check its hypotheses, and a partial sum evaluated at six terms. The monotone steps
  are the same argument one order at a time, without the family.
- **`pi` as the least positive zero, or as the period.** "Least" wants the set of positive zeros to
  have a least element, and the period wants periodicity before `pi` exists. The zero in `[0, 2]`
  is characterised by a closed interval and a monotonicity proved in the same file.
- **`pi` asserted as an axiom with its properties.** That would add to what the reader has to
  believe, and nothing needs it.
