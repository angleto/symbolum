# 0056. The second source of squares is a Gram matrix, and at degree two it needs no search

- **Status:** accepted, extends 0032
- **Date:** 2026-09-27

## Context

`docs/adr/0032` gave `Linarith`'s fact pool a source that is not read off the goal: a square
completed over an atom that is one unknown times itself, justified by `Order.SQUARE_NONNEG`. Its
point 3 deferred the second source, "a semidefinite search", to a record of its own, and until
Mycelium card `4d7d0dc6` no card carried it.

The goal that card names is `x * x + y * y >= 2 * (x * y)`, which is `0 <= (x - y) * (x - y)`. It
has no hypotheses, so the products are empty at every degree for the reason 0032 measured, and the
completion does not reach it: over the atoms the goal names, its obstacle is `x * y`, a product of
two different unknowns, and a square completed over `x` or over `y` alone carries no such atom.
`LinarithSquareBoundarySpec` held it as a refusal naming that atom.

## The measurement that decides it

**Over the monomials of degree at most one, a quadratic form has exactly one Gram matrix.** Write
the form over the unknowns `x1 .. xn` and the constant as `v^T Q v` with `v = (x1, .., xn, 1)`.
Every entry of `Q` is read off one coefficient: the square `xi * xi` is `Q(i, i)`, the cross term
`xi * xj` is `Q(i, j) + Q(j, i)` and the matrix is symmetric, a linear `xi` is `Q(i, n+1)` twice,
and the constant is `Q(n+1, n+1)`. There is no freedom left, so there is nothing to search for.

The semidefinite program 0032 anticipated is the search for a positive semidefinite matrix among
the Gram matrices of a form, and it exists because at degree `2d` with `d > 1` a monomial like
`x * x * y * y` is `(x * y) * (x * y)` and also `(x * x) * (y * y)`, so the coefficient is split
between entries and the split is the unknown. At `d = 1` that does not happen.

And for a quadratic the question the matrix answers is the right one: the form is non-negative at
every point exactly when `Q` is positive semidefinite, by homogenising, `t * t * q(x / t)` being
non-negative for every `t` other than zero and so, by continuity, for zero too. A symmetric
decomposition `Q = L D L^T` in exact rational arithmetic says whether it is, and when it is, the
columns of `L` are the linear forms and the entries of `D` their weights. Pivoting on the unknowns
first and the constant last makes each step the completion of one square, so the decomposition is
0032's construction applied once per unknown rather than a different idea.

## Decision

1. **`SumOfSquares` decomposes the Gram matrix of a form, and `Linarith.squares` offers the result
   beside the completed squares.** Each base is turned into a term, `SQUARE_NONNEG` is instantiated
   at it, and the fact goes to the certificate search with everything else, which is 0032 point 1:
   the pool is extended, the certificate is not. The forms decomposed are the goal's and the
   hypotheses', which are the forms the completion already reads.
2. **Untrusted, exactly as the forms are.** The decomposition proposes squares; `Ring` checks the
   combination the certificate search returns. A wrong decomposition costs a proof and cannot
   produce one, so it lives beside `LinearForm` and is tested for reach by `SumOfSquaresSpec`, not
   for soundness.
3. **Only positive pivots become squares.** A zero pivot with a row that is not zero, or a negative
   one, means the matrix is not semidefinite; the squares already found are still offered, because
   combined with the hypotheses they may be what a certificate needs, and a goal that is false
   stays refused because every fact in the pool is true.
4. **A form with an atom of more than two factors gets no squares.** That is the case where the
   Gram matrix stops being unique, and choosing among them is the semidefinite search this does not
   do. It is still a second increment with its own record, and it is where the six statements
   `docs/adr/0029` calls genuinely hard inequalities would be spent.
5. **The refusal says what the squares reach.** Without hypotheses they are the only facts there
   are, so the message names the atom furthest out of reach first, an atom of more than two
   factors before a cross term and a cross term before a square, and says that the squares reach
   degree two. It said until this record that the only fact available was a square completed over
   one unknown times itself, which this change makes false.

## Consequences

**`x * x + y * y >= 2 * (x * y)` is proved with no hypothesis**, and `Linarith.support` reports
`0 <= (x - y) * (x - y)` in its `squares` field and no premise, which is 0032 point 4 carried over
unchanged: a square is a fact nobody wrote and is reported beside the premises.

**`Support.squares` can now hold a square over several unknowns.** Its docstring gives
`0 <= (x + c) * (x + c)` as the example and that is still one shape it takes; the base is written
with a subtraction where a coefficient is negative so that it reads as the square a person would
write.

**What miniF2F does is measured, not predicted.** `ReachSpec` puts the corpus to the whole surface
and reports it; the figures before and after this change are on card `4d7d0dc6`, because a count
written into a decision record is a photograph and the corpus moves for other reasons.

**Rejected: an external semidefinite solver.** It answers a question this degree does not ask, and
it would bring floating point into a place where the answer has to be rounded back to rationals and
then rechecked, for a matrix that exact elimination already decides.

**Rejected: offering the decomposition only for the goal's own form.** The completion reads the
hypotheses' forms as well, and a square found in a hypothesis's quadratic part is as true as one
found in the goal's; reading one set and not the other would make the two sources disagree about
where a square is worth having.
