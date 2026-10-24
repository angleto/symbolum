# 0067. The family of rules `l XOR h(c, r)` proved once, with Rule 30 and the Pascal map as instances

- **Status:** accepted
- **Date:** 2026-10-24

## Context

Mycelium card `9b41023d`, split from the card that delivered `0066`. The linear map
`D n = n XOR 2n`, whose orbit from 1 is Pascal's triangle modulo 2, was the third instance of
triangular maps that note 917b3939 names and the kernel did not have: the library has no XOR, and
Rule 30's map `F` had been given by two equations on halving through `g p q n`, with `p` and `q`
the two bits below, and an existence theorem with a counter. Those equations are Rule 30's only
through one subterm, `COND (p \/ q)`: every rule of three cells whose left cell enters through an
XOR, `R(l, c, r) = l XOR h(c, r)`, has the same equations with `h p q` in its place. That family
is also the ladder of strategy 2 of the note.

Klimov and Shamir (CHES 2002, attached to the note) call a map whose bit `k` depends only on bits
`0` to `k` a T-function and prove, as their Lemma 3, that an invertible one has cycles whose lengths
from one word size to the next stay or double, which is `TRIANGULAR_PERIOD` of `0066`. Their
invertible T-functions are the triangular maps here, and their closing remark, that iterating a
T-function never moves information from the high bits to the low ones, is the reason given in the
note for why these theorems stop short of the centre column.

## Decision

**The family is proved once, over `h : bool -> bool -> bool` as a variable, in `RuleFamily`, and
nothing is declared.** The equations are `g p q (2 m) = COND (h p q) 1 0 + 2 * g F p m` and
`g p q (2 m + 1) = COND (h p q) 0 1 + 2 * g T p m`; the map is `g F F`. Every case analysis in the
proofs is on the proposition `h p q` itself and never on `p` and `q`, so nothing depends on which
rule it is.

**Existence needs `~(h F F)`.** At `m = 0` the even equation for `g F F` reads
`g F F 0 = COND (h F F) 1 0 + 2 * g F F 0`, which has a natural solution only when `h F F` is false:
a rule that turns a white background black has infinite rows and no map on the naturals. So
`RULE_FAMILY_EXISTS` is `!h. ~(h F F) ==> ?g. ...`, and the theorems over the equations are vacuous
for the other eight rules, which `RuleFamilySpec` checks rather than assumes.

**What is published, nine facts**, each compared with its written statement in `Complex.construct`,
with no hypotheses and resting on no axiom beyond the three of the chain:

- `RULE_FAMILY_STEP`: the two equations as one;
- `RULE_FAMILY_TRIANGULAR`: every member is triangular, from its residues being kept and separated
  and `TRIANGULAR_OF_INJECTIVE`;
- `RULE_FAMILY_EXISTS`: every member that keeps white white has a map;
- `RULE_FAMILY_BIT_ZERO`, `_BIT_SUC` and `_BIT_RULE`: bit 0 of `g p q x` is bit 0 of `x` XOR
  `h p q`, bit `j + 1` is bit `j` of `g` at the half, and bit `j + 2` is bit `j + 2` of `x` XOR
  `h` of bits `j + 1` and `j`, which is what the equations mean;
- `PASCAL_MAP_EXISTS`, `PASCAL_MAP_TRIANGULAR` and `PASCAL_MAP_BITS`: the instance `h c r = c`,
  whose bit 0 is bit 0 of the argument and whose bit `j + 1` is bit `j + 1` XOR bit `j`, that is
  `n XOR 2n`.

**Rule 30's map becomes the instance `h c r = c OR r`, and every one of its statements is kept.**
Its private `G_STEP` and `G_BIT_ZERO`, `_SUC` and `_RULE` are the family's at `OR`;
`RULE_THIRTY_MAP_TRIANGULAR` is `RULE_FAMILY_TRIANGULAR` at `OR` instead of a derivation from
`G_RESIDUES` and `G_INJECTIVE`, which are gone; `RULE_THIRTY_MAP_EXISTS` takes the map from
`RULE_FAMILY_EXISTS` and adds the iterate by the recursion theorem. What stays proved in
`RuleThirty` is what is Rule 30's own: `G_ZERO`, `G_LENGTH` (a row grows two bits a step) and the
bridge to the rows. `RuleFamily` is proved after `Triangular`, whose facts it reads, and before
`RuleThirty`. Eight lemmas about halving that `RuleThirty` proved for itself (`MOD_TWO_SHIFT`,
`BIT_HALVE`, `COND_BELOW_TWO`, `MOD_DOUBLE`, `DIV_MOD_SHIFT`, `BELOW_POWER`, `DIV_ONE`, `BIT_LOW`)
move to `NumberSteps`, which both instantiate.

## Alternatives rejected

**Bitwise operations on the naturals, with the family as `n XOR H(2n, 4n)`.** It is the general
form, and Klimov and Shamir's construction (any composition of addition, multiplication and the
bitwise operations is a T-function, and `x -> x + 2 f(x)` is invertible for every such `f`) would
then be within reach. It is a library of its own, an XOR, AND and OR on `num` with their algebra,
and it decides more than this card asks: the family is the object the note's ladder is about, and
it needs one subterm generalised, not a new vocabulary. It is the natural next card if the
Klimov-Shamir theorems are wanted in the kernel.

**Naming the instance by its rule number.** `D` is Rule 60, 102 or 90 depending on the frame the
rows are drawn in, so the name would be true in one picture and false in another. Its orbit from 1
is Pascal's triangle modulo 2 in every frame.

**Keeping `G_RESIDUES` and `G_INJECTIVE` in `RuleThirty` as copies.** They would be the family's
proofs again with `p \/ q` written in, and two proofs of one fact drift apart.

## Consequences

`Complex` publishes nine more facts and declares nothing. `RuleFamilySpec` reads the family's
equations off `RULE_FAMILY_EXISTS` and interprets them in `Long` for all sixteen rules: for the
eight that keep white white they are the map whose bit `j` is bit `j` of `n` XOR `h` of the two
bits below, below 2048, and for the eight others the even equation at 0 has no solution. It checks
that the family's equations at the two rules are, term for term, the Pascal map's and the first two
of Rule 30's, and reads `PASCAL_MAP_BITS` on `n XOR 2n`, where it holds, and on Rule 30's map,
where it must not. The closed form of the Pascal map through Lucas' theorem, and the factor of
Gilbreath's table modulo 2 that the note proposes, are not proved here; the second has what it
needs now.
