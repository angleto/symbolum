# 0062. The finite Fourier inversion, and the Collatz iterate as its instance over the equations that characterise the map

- **Status:** accepted
- **Date:** 2026-10-21

## Context

Mycelium card `1ab3b15f` is the third of the four Angelo opened on 2026-09-27, and it spends the
roots of unity and their orthogonality from the second, the complex numbers of
[`0060`](0060-complex-is-a-type-of-its-own-because-the-operators-are-shared.md). It asks for two
things. First the inversion theorem of the finite transform with its real reading in cosines. Then
the Collatz instance, form (C) of `collatz@8b991e5` `documents/02-closed-form-formula.md` section
2.3, with the statement brought into the kernel decided in writing before it is proved. This record
is that writing.

Form (C) reads, for the shortcut map `T n = n / 2` on even `n` and `(3 n + 1) / 2` on odd `n`,

    T^t(n) = Sigma_{s=0}^{2^t - 1} [ (A_s n + B_s) cos(2 pi s n / 2^t) + (C_s n + D_s) sin(2 pi s n / 2^t) ]

with the coefficients "themselves DFTs of the slope sequence and the offset sequence over residues".

## Decision

**The inversion is stated at the residue, not under a periodicity hypothesis.**

    COMPLEX_DFT_INVERSION
      !f m n. 0 < m ==> f (NUM_MOD n m) = complex_of_real (inv (real_of_num m)) *
        complex_sum (\h. complex_sum (\r. f r * complex_pow (cnj w) (h * r)) m * complex_pow w (h * n)) m
      with w = cis (2 * pi / real_of_num m)

It holds of every `f` and says that only the values below `m` matter; for a periodic `f` the left
side is `f n`. `w^(-h r)` is written `cnj(w)^(h r)`, because `num` has no negative exponent and the
conjugate of a root of unity is its inverse. `REAL_DFT_INVERSION` is the real part at
`complex_of_real o f`, with each angle written `2 * pi * real_of_num (s * n) / real_of_num m`,
which is how the source writes it.

**The Collatz map is given by its equations, not declared.** The theorems are stated over any
`step : num -> num` and `iterate : num -> num -> num` with

    (!k. step (2 * k) = k) /\ (!k. step (2 * k + 1) = 3 * k + 2) /\
    (!x. iterate x 0 = x) /\ (!x t. iterate x (SUC t) = step (iterate x t))

and `COLLATZ_SHORTCUT_EXISTS` exhibits a pair that satisfies all four, the map by cases on the
remainder and its iterate by the recursion theorem, so the hypotheses are not vacuous.

**What is brought in from (C) is two theorems, and the second carries the first.**

    COLLATZ_AFFINE_ON_CLASSES   ... ==> !t. ?a b. !n. real_of_num (iterate n t) =
                                        a (NUM_MOD n (2^t)) * real_of_num n + b (NUM_MOD n (2^t))
    COLLATZ_DFT_FORM            ... ==> !t. ?a b. (that) /\ (!n. real_of_num (iterate n t) =
                                        Sum (\s. (A_s * n + B_s) * cos (...) + (C_s * n + D_s) * sin (...)) (2^t))

with `A_s` the transform of `a` against the cosine divided by `2^t`, `B_s` that of `b`, and `C_s`,
`D_s` the same against the sine. The class form stands beside the series so that `a` and `b` are
known to be the slope and the offset of the class, which is what the source says the coefficients
are transforms of.

**The class form is proved by a shift.** `iterate (r + 2^t q) t = iterate r t + c q`, for a `c`
depending on `r` and `t` alone, by induction on `t` over every `r`. One step more is one step of the
map first. The map halves `2 (j + 2^t q)` to `j + 2^t q` and takes `2 (j + 2^t q) + 1` to
`(3 j + 2) + 2^t (3 q)`, and the hypothesis at `j` or at `3 j + 2` finishes it.

## Alternatives rejected

**The source's own route through the parity sequence.** It needs the parity of `T^j(n)` for each
`j < t` as a function of `n mod 2^t`, which is a statement about residues of residues
(`(T n) mod 2^t` from `n mod 2^(t+1)`) at every step, and the library has none of those. The shift
needs the division of a natural by two and nothing else.

**Constants `COLLATZ_T` and an iterate.** Two rows in `docs/reading-register.md` for what four
equations say, and a reader of the theorem would have to open the definition to see the map; the
equations are the definition, written where the theorem is.

**Periodicity as a hypothesis of the inversion.** `!n. f (n + m) = f n ==> f n = ...` is how the
card worded it. It is weaker than the residue form, which it follows from, and the Collatz instance
would have had to prove the slope and offset periodic first, when they are only ever read at a
residue.

**The slope as `3^s / 2^t`.** That is the source's Theorem 1 and needs the number of odd steps as a
function. Form (C) does not need it, since it speaks only of the transform of whatever the slope is.

## Consequences

`Complex` publishes five more facts and declares nothing. The two derivations, `FiniteFourier` and
`CollatzFourier`, sit beside it as `Fundamental` does, and `ComplexKit` now holds the steps the
three share. `Complex.construct` takes `Peano`, for the semiring the arithmetic of exponents and
residues is decided in.

The source says, just before (C), that "`T^t(n)` is a function of the residue class". It is not:
`T^t` is affine on each class, which is why (C) has `A_s n + B_s` and not a constant. It also cites
"Theorem 4 below" for the parity sequence depending on the residue. That is its Theorem 2, residue
determinism; its Theorem 4 says `T^t` is not a polynomial. Both are the collatz repository's to settle, and they are
reported there as questions rather than edited from here.
