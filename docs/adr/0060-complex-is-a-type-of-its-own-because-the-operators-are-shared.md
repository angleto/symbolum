# 0060. `complex` is a type of its own over the pairs of reals, because the operators it shares are picked by type

- **Status:** accepted
- **Date:** 2026-10-05

## Context

Mycelium card `92c368a1` is the second of the four Angelo opened on 2026-09-27 (the first, `pi`, is
[`0057`](0057-pi-is-twice-the-zero-of-cos-and-the-bounds-are-taylor-polynomials.md)). It asks for
the complex numbers as a type defined over `prod(real, real)` with no axiom, `+`, `*` and `-`
written as for `num`, `cis`, De Moivre, the polar form and the `n`-th roots that the fundamental
theorem of algebra spends, and the roots of unity with the orthogonality of their powers that the
discrete Fourier form of the Collatz formula spends.

Two records already stood in the way of the obvious reading of that request, and each was right
about the case it was written for.

- **`Matrix` argues against `Kernel.defineType` for a type that is all of its representation.**
  Every element of `prod(prod(real,real), prod(real,real))` is a matrix, so carving it out buys a
  name and a distinct equality and costs a bijection to cross in every derivation. The same is true
  of `prod(real, real)` and the complex numbers.
- **`Integer.scala` and [`0033`](0033-the-integers-arrive-as-a-prerequisite-and-not-as-stage-four.md)
  refused a third candidate for `+`, `*`, `<` and `<=`** until somebody measured what it does to the
  statements that already read, because the elaborator refuses a text nothing determines and every
  symbol with one more candidate gains a way of being undetermined.

## Decision

**`complex` is `Kernel.defineType` over `\p:prod(real,real). T`**, the whole of the pairs, with
`mk_complex` and `dest_complex` the bijection. `COMPLEX x y` is `mk_complex (PAIR x y)`, `Re` and
`Im` read the two components back, and every operation is a definition in constructor form:
`complex_add`, `complex_neg`, `complex_sub`, `complex_mul`, `cnj`, `complex_norm_sq`,
`complex_norm` (as `sqrt` of the last), `complex_inv`, `complex_sum` (componentwise over `Sum`),
`cis`, `complex_arg` (by choice) and `complex_pow` (by the recursion theorem). Nothing is asserted.

**What separates this from `Matrix` is the notation, and it is the whole argument.** `+`, `*` and
`-` stand for the complex operations at `complex`, as they stand for the reals' at `real`
([`0018`](0018-an-operator-symbol-stands-for-more-than-one-constant.md)): the elaborator picks a
candidate by the type its operands settle. Over `prod(real, real)` that type is also a row of a
matrix and the carrier of anything else built from two reals, so `p * q` would read as the complex
product for every pair of reals in the signature, and nobody checking a statement could see which
pairs were meant. A type of its own keeps the overload to the numbers it is about. `Matrix` names
its operations `MAT_ADD` and `MAT_MUL` and overloads nothing, which is why its argument holds for it
and not here.

**The bijection is crossed once, not per derivation.** `Re (COMPLEX x y) = x`, `Im (COMPLEX x y) =
y`, `COMPLEX_SURJECTIVE` and `COMPLEX_EQ` (`z = w` exactly when the parts agree) are proved by hand
from the two theorems `defineType` returns; after that nothing mentions `mk_complex`. One driver,
`Complex.prove`, proves every identity: `COMPLEX_EQ` splits it into its two parts, a component rule per
operation (`RE_ADD`, `IM_MUL` and the rest, each one definition opened) pushes `Re` and `Im` through it,
and `Ring` closes the real identity left. A constant the rules do not open, a power or a
variable, is an atom: `Re (complex_pow z n)` is a real like any other, which is what lets the power
laws be proved by induction with the driver as the closer.

**`complex_inv 0 = 0` is a theorem and costs no case split.** The inverse is
`COMPLEX (Re z / |z|^2) (-(Im z) / |z|^2)` with no condition, and at zero both parts are
`0 * inv 0`, which is zero whatever `inv 0` is. So nothing here depends on what the reals' interface
says about `inv 0`, which it does not publish (card `4938e4e4`).

**`Linarith` is handed quotients as variables.** It refuses a goal that divides by anything but a
numeral, because cancelling a symbolic denominator is `Field`'s to assume. Nothing here asks it to
cancel one: `inv (complex_norm z)` is an atom whose value no step depends on. So `Complex.conclude`
replaces every atom holding `inv` or `div` by a fresh variable, proves the implication at the
variables, and instantiates back, which the kernel checks like any instantiation.

**What is proved.** The field (`COMPLEX_MUL_INVERSE` under `~(z = 0)`, `COMPLEX_ENTIRE`), the
embedding of the reals, the conjugate and `z * cnj z = |z|^2`, the norm and its multiplicativity,
the power and sum laws, `cis` with `CIS_ADD`, `CIS_PERIODIC` and `|cis t| = 1`, `DE_MOIVRE`,
`COMPLEX_POLAR` and `ARG_SPEC` (the chosen argument lies in `[0, 2 pi)`), `COMPLEX_ROOT` (every `z`
has an `n`-th root for `n > 0`), `ROOT_OF_UNITY`, and the two halves of the orthogonality,
`ROOTS_OF_UNITY_SUM_DIVIDES` (the sum is `M` when `M` divides `h`) and
`ROOTS_OF_UNITY_SUM_NOT_DIVIDES` (zero otherwise). Four facts about the reals land here because
nothing published them and the argument needs them: `COS_NEG`, `SIN_NEG`, `SIN_NONNEG` on
`[0, pi]` and `EXP_POWER`, `Power (exp u) n = exp (n u)`.

## Consequences

`complex` is the chain's last link and `widest` moves to it, so `Ask`, `Find`, the notebook and
`docs/lemmas.md` read it. Its facts rest on choice, eta and infinity and on nothing else, which
`ComplexSpec` asserts over every fact.

**`-` now has two candidates where it had one.** `num` never had a `-` because its subtraction is
truncated, so until this change a text `0 - 1` with nothing else in it read at `real` because no
other reading existed. It is now refused as undetermined at the widest signature, like `0 < 1`
already was, and `ComplexSpec` pins both readings. A text whose operands are typed reads exactly
as before. The measurement `0033` asked for, taken on 2026-10-05 by the whole suite over this
change: the miniF2F corpus reads **244 statements: Proved 23, Unsettled 16, Unreadable 161,
Outside 9, ForeignType 35**, the same figures as before it, so no statement of the corpus was
determined only by `-` having one candidate. And over the library, printed by the widest signature
and read back by it, a probe on the same day found **the same six refusals before and after**, of
957 entries and of 1037: `ONE_NOT_ZERO` and `ZERO_LT_ONE` (twice) for a numeral nothing types,
`PROD_ABS_REP`, `WORD_ABS_REP` and `WORD_EMPTY_LENGTH` for a polymorphic variable. None is about
an operator, and none of the eighty new entries is refused. The probe is not a test and is not
kept; that every printed statement reads back is checked by nothing in the suite.

**The roots are written with `inv`, not `/`, where `Linarith` has to read them**, and
`ROOT_OF_UNITY` and the two sums keep the textbook's `2 * pi / real_of_num m` because nothing
arithmetic is asked of them after they are stated.

## Rejected

**`complex` as `prod(real, real)` spelled out, as `Matrix` is.** Rejected for the reason above: the
operators are picked by type, and the type would be shared.

**A `COND` in `complex_inv` to say what happens at zero.** It is what a reader expects and it adds a
case to every derivation that opens the inverse. The unconditional quotient already gives zero at
zero, for a reason that holds whatever `inv 0` is.

**Numerals at `complex`.** `complex_of_real 1` is written where `1` is meant. A third numeral type
would make every digit string nothing else determines ambiguous in a third way, which is
[`0012`](0012-a-numeral-belongs-to-the-type-its-context-forces.md)'s question and not this one.

**Overloading the prefix `-`.** `Notation` holds one constant per prefix symbol and has no way to
pick between two; `complex_neg z` is written instead.
