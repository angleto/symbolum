# 0079. The ideal pins one unknown at a time

- **Status:** accepted, extends `docs/adr/0075`
- **Date:** 2026-11-12

## Context

After `docs/adr/0075`, `mathd_algebra_362` was the miniF2F statement nearest to the ideal and still
out of it:

```
mathd_algebra_362   x^2 * y^3 = 32/27 /\ x / y^3 = 27/4 ==> x + y = 8/3
```

Two things stopped it, each general.

- **A denominator nobody stated is non-zero.** `x / y^3` is read as `x * inv (y^3)`, and under
  `docs/adr/0072` `y^3 * inv (y^3) = 1` joins the equations only when a hypothesis says `y^3` is
  not zero. None does here; the first equation does, since `x^2 * 0` is not `32/27`. Without that
  equation `inv (y^3)` is a free unknown and `x` is not determined at all.
- **The target's own polynomial is too high.** With the inverse in, the system has nine complex
  solutions, `x^3 = 8` and `y^3 = 4x/27`, and `x + y - 8/3` takes a different value at most of
  them, so its least polynomial has degree nine, past `Ideal.Degree`. One unknown at a time is
  degree three: `x` is a root of `x^3 - 8`, and `y`, once `x` is known, of `27 y^3 - 8`. Each has
  one real root, which is the order's to pick, as in `docs/adr/0075`.

## Decision

1. **A denominator the equations force non-zero is cleared.** For each `inv r` that no
   hypothesis covers, the search asks whether `1` is in the ideal with `r` added. Where it is, the
   membership is rebuilt as `G, r = 0 |- 1 = 0`, set against `~(1 = 0)` from `0 < 1` and
   `NON_ZERO`, and discharged into `G |- ~(r = 0)`. From there it is the hypothesis case of
   `docs/adr/0072`: `MUL_INVERSE` gives `r * inv r = 1`, which joins the equations. Where `1` is
   not a member, or the search runs out, `inv r` stays an unknown as before.
2. **An unknown with one real root the order picks is pinned, and the goal asked again.** When the
   goal is still outside the ideal after the order's turn, the least polynomial of every unknown is
   asked over one basis, `Groebner.minimalPolynomials`. An unknown of degree two or more is a
   candidate, and its rational roots are found exactly by `Groebner.rationalRoots`. For a root `c`,
   `v = c` is put to the same procedure as any goal: membership, the radical, and the order, which
   is where `docs/adr/0075` proves the cofactor's sign. A proved `v = c` joins the equations and
   the goal is asked again; while it is still outside, the next unknown is tried. An unknown of
   degree one is not a candidate, since the ideal already pins it.
3. **The cofactor's sign is asked as written as well as in normal form.** `docs/adr/0075` asks
   `Linarith` for the sign of the cofactor's normal form, because that is where the order
   hypotheses' products land. Normal form can also hide a square: in `mathd_algebra_362` the
   cofactor for `x` is `x * x + 2 * x + 4`, and modulo the basis `x * x` becomes a multiple of
   `inv (y * y * y)`, which `Linarith` cannot complete. Both are asked, normal form first; the two
   differ by a member of the ideal, so either serves.

## Alternatives rejected

**A higher `Ideal.Degree`.** Nine would reach `mathd_algebra_362`'s least polynomial directly, at
the cost of ten powers reduced for every goal that reaches the order, and the sign asked would be
of a cofactor of degree eight in two unknowns. Not tried: in `mathd_algebra_362` one unknown at a time
asks only for the signs of two quadratics in one unknown each, which is the case `Linarith`'s
completed squares were built for.

**Assuming the denominator is not zero.** A goal proved under a side condition nobody stated is
the failure `docs/adr/0072` was written against; the condition is proved here or the inverse
stays unknown.

## Consequences

**miniF2F.** Before: **Proved 29, Unsettled 10**, the figure `docs/adr/0075` closed on and the
one CI printed for `97eaa80e`. After: **Proved 30, Unsettled 9**, read off `ReachSpec` on
2026-11-16, run alone through the build cap on this change over `97eaa80e` and, minutes later, on
`97eaa80e` itself in the same checkout. The one that moved is `mathd_algebra_362`, the statement
this record was written for, named in the run's list of proved statements; Unreadable 161,
Outside 9 and ForeignType 35 did not move. These are figures of one day; `ReachSpec` prints the
live ones.

**What it costs a goal that fails.** Not separable from the noise in that pair of runs, and
that is the reading rather than a gap in it. The pass over the corpus took 116 seconds with this
change and 156 without; the goals left unsettled in both moved in both directions,
`mathd_numbertheory_234` from 28.7 to 37.9 seconds and `amc12b_2021_p3` from 27.4 to 15.6, which
is the machine and not the pinning. What the change does spend on a failing goal is bounded by
construction: a pin is tried only on an unknown whose minimal polynomial has degree two or more,
and only after the goal was refused as outside the ideal. `mathd_algebra_362` itself went from
20.4 seconds unsettled to under 4 proved.

**The root search is bounded.** `Groebner.RootSearch` stops the divisor enumeration where either
end coefficient, cleared to integers, is past ten billion. A root beyond it is a pin nobody makes,
which costs a proof and not a wrong one, since every candidate is checked by evaluation and every
pin is proved by the kernel.

**`tools/verify/perturb-ideal-pin.sh`** carries the guards. Run through scala-cli over the perturbed
source before the harness ran under sbt: with nothing forced non-zero, `mathd_algebra_362` and the
forced denominator go red; with nothing pinned, `mathd_algebra_362` and the two unknowns pinned one
after the other; with the sign asked in normal form only, `mathd_algebra_362` alone.
