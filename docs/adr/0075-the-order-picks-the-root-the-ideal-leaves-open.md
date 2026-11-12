# 0075. The order picks the root the ideal leaves open

- **Status:** accepted, takes up the item `docs/adr/0072` left next
- **Date:** 2026-11-12

## Context

`docs/adr/0071` sorted two of miniF2F's statements under "ideal and order":

```
amc12b_2002_p19   0 < x /\ 0 < y /\ 0 < z ==> x(y + z) = 152 ==> y(z + x) = 162 ==> z(x + y) = 170
                  ==> x * y * z = 720
amc12b_2002_p7    0 < a /\ 0 < b /\ 0 < c ==> b = a + 1 ==> c = b + 1 ==> a * b * c = 8(a + b + c)
                  ==> a^2 + b^2 + c^2 = 77
```

Neither difference is in the ideal of its equations, nor is any power of it, because each system
has more than one solution and the conclusion holds at only some of them: `x * y * z` is `720` or
`-720`, and `a` is `4`, `-1` or `-6`. What separates the solutions is the sign of something, which
is the order's to say and not the ideal's. `Linarith` alone did not reach them either: it reads a
product of unknowns as an atom, and the first of the two cost it 439 seconds before
`Linarith.Facts` bounded it.

## Decision

1. **The search looks for the least polynomial in the difference that the ideal holds.** Once `D`,
   `D^2` and `D^4` are all outside it, the remainders of `1, D, D^2, ...` modulo one basis are
   compared, and the first linear dependency among them is a monic `p` with `p(D)` in the ideal,
   up to `Ideal.Degree`. It is written `D^m * q(D)` with `q(0)` not zero. That is all untrusted
   search, in `Groebner.minimalPolynomial`.
2. **The order is asked for the sign of `q(D)`, and a proved sign becomes an inverse.** `Linarith`
   is asked for `0 < Q`, and then `0 < -Q`, with `Q` the normal form of `q(D)`. A sign it proves
   gives `~(Q = 0)` through `NON_ZERO`, and `Q * inv Q = 1` through `MUL_INVERSE`, which joins the
   equations exactly as a cleared denominator does under `docs/adr/0072`. In that larger ideal
   `D^m` is a member, and the radical of `docs/adr/0072` finishes the proof. The kernel sees
   memberships, a sign proved by `Linarith`, and squarings, and never `p`.
3. **The sign is asked in normal form, and so are the order hypotheses.** `Linarith` multiplies
   hypotheses as they are written, and the products a sign needs are often of hypotheses the
   equations rewrite: in `amc12b_2002_p7` the cofactor reduces to a multiple of `(c - 1)^2`, and
   what makes it positive is the square of `0 < a` read as `0 < c - 2`. So each hypothesis
   `l < r` or `l <= r` over atoms the ideal knows is reduced first: `r - l = N`, with `N` the
   normal form, is a membership rebuilt like any other, `0 < N` follows from it linearly, and the
   sign is asked from those reduced facts.
4. **Every refusal is still the one the plain difference earned**, `OutsideTheIdeal` with its
   remainder and so unread, except a budget run out, which stays `BoundReached`.

## Alternatives rejected

**A lemma `x * y = 0 ==> ~(y = 0) ==> x = 0`.** It is the textbook step and the library has no
such lemma for the reals. The inverse needs none: `MUL_INVERSE` and `NON_ZERO` are already how
`docs/adr/0072` pays for a denominator, so the order's contribution enters the certificate through
a door the kernel half already checks.

**Asking `Linarith` the sign over the hypotheses as written.** Measured on this change before
the reduction was added: both statements refused, because the products the sign needs are not
products of anything written.

**Elimination by a lexicographic order.** It finds the same polynomial as the univariate
generator of the elimination ideal, at the cost of a second monomial order in `Groebner` and a
basis computation that is usually far dearer than grevlex. The linear algebra on remainders
answers the same question over the basis already computed.

## Consequences

**miniF2F.** Before: **Proved 27, Unsettled 12**, the figure `docs/adr/0072` closed on. After:
**Proved 29, Unsettled 10**, read off `ReachSpec` twice. First in a `clean test` of this change
on `d47d4901`, which was stopped later inside `ProposeSpec`, after `ReachSpec` had finished. Then
in an integration run of this change with five other branches onto `6c98f0d7`, whose corpus
suites were all green but one `ProposeSpec` pin that another branch moved. The two that moved are
the two this record was written for, `amc12b_2002_p19` and `amc12b_2002_p7`, both named in the
first run's list of proved statements; Unreadable 161, Outside 9 and ForeignType 35 did not move.
These are figures of one day; `ReachSpec` prints the live ones.

**The bound is chosen, not measured.** `Ideal.Degree` is four. By hand, both statements need
two: `t * (t + 1440)` for `t = x * y * z - 720`, and `t * (t + 75)` for `amc12b_2002_p7`'s
difference. The first perturbation of the harness below is what checks that degree one is not
enough.

**A test went red because the procedure got stronger.** `IdealSpec` drew the ideal's line at
`0 < a ==> a * a = 4 ==> a = 2`, refused as outside the ideal. It is proved now, and the refusal
the line rests on is `x * x = x ==> x = 1`, where neither root is excluded.

**The kernel checks the step.** `tools/verify/perturb-ideal-order.sh` lowers the degree, asks one
sign only, hands the order hypotheses unreduced, and drops the inverse from the larger ideal.
