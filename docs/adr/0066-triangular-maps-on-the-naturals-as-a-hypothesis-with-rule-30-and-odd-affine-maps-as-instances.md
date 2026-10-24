# 0066. Triangular maps on the naturals as a hypothesis, with Rule 30 and the odd affine maps as instances

- **Status:** accepted
- **Date:** 2026-10-24

## Context

Mycelium card `09bca345` takes strategy 1 of note 917b3939, part 4. Rule 30's map `F`, the
linear map `n XOR 2n` and `n -> 3n + 1` share one structure: bit `j` of the value is bit `j` of
the argument XOR something that depends only on the bits below `j`. Theorems 9, 10 and 12 of
`docs/adr/0064` (the residues of `F^t(n)` depend on those of `n`, `F^t` is injective on them, and
bit `j` is balanced over them) were proved for `F` alone, by inductions that used nothing but
that structure. The card asks for the structure as a hypothesis, the theorems proved once over it,
and the maps as instances.

Two facts about the library decide the form. It has no bitwise operations, so the structure has to
be said with remainders modulo powers of two. And `Modular` already publishes congruences and
`NUM_PRIME_POW_CANCEL`, which is what an odd multiplier needs.

## Decision

**Nothing is declared, as in `0062`, `0064` and `0065`.** A map `f : num -> num` is triangular
when, for every `k`, agreement modulo `2^k` is kept (`m` and `n` agreeing there makes `f m` and
`f n` agree there), and a disagreement first appearing at bit `k` is kept (`m` and `n` agreeing
modulo `2^k` and not modulo `2^(k + 1)` makes `f m` and `f n` do the same). The two clauses are
written out in every statement that assumes them. The second is the bit-level definition said
with remainders: the diagonal of the triangle is full.

**What is published, seven facts in `Triangular` and one in `RuleThirty`**, each compared with its
written statement in `Complex.construct`, with no hypotheses and resting on no axiom beyond the
three of the chain:

- `TRIANGULAR_INJECTIVE` and `TRIANGULAR_OF_INJECTIVE`: triangular is the same as keeping
  agreement modulo every `2^k` and being injective on the residues modulo every `2^k`;
- `TRIANGULAR_COMPOSE` and `TRIANGULAR_ITERATE`: the class is closed under composition and
  iteration;
- `TRIANGULAR_BALANCED`: over the residues modulo `2^(j + 1)`, bit `j` of the value is on as
  often as off;
- `TRIANGULAR_PERIOD`: an orbit back modulo `2^k` after `p` steps is back modulo `2^(k + 1)`
  after `2p`;
- `TRIANGULAR_AFFINE`: `n -> a n + b` is triangular for every odd `a`;
- `RULE_THIRTY_MAP_TRIANGULAR`: Rule 30's map is triangular, from `G_RESIDUES` and `G_INJECTIVE`.

**`RULE_THIRTY_MAP_RESIDUES`, `_INJECTIVE` and `_BALANCED` keep their statements and lose their
proofs**: each is now read off the iterate being triangular. `Triangular` is proved before
`RuleThirty`, which receives its facts. Six lemmas about remainders modulo a power of two that
`RuleThirty` had proved for itself (`MOD_SPLIT`, `MOD_EQ_SPLIT`, `BIT_ABOVE`, `BIT_TOP`, `MOD_ONE`,
`MOD_MOD`) move to `NumberSteps`, which both files instantiate.

## Alternatives rejected

**Bit `j` of the value as an explicit XOR with a function of the lower bits.** It is the
definition the note gives, and it would need a quantifier over functions of `j` bits and an XOR
the library lacks. The remainder form says the same and every instance proves it with the facts
it already has.

**Injectivity as the second clause.** `TRIANGULAR_OF_INJECTIVE` shows it is equivalent, and it is
what the instances prove; but the local form is the one the composition, the balance and the
period are proved from in a line, and it is the property the name describes.

**The linear map `n XOR 2n` as a third instance now.** It needs a construction like Rule 30's
`g`, and the right way to get it is to generalise `g` to the family `l XOR h(c, r)`, which also
serves strategy 2 of the note. That is its own card.

## Consequences

`Complex` publishes eight more facts and declares nothing. `TriangularSpec` reads the hypothesis
off `TRIANGULAR_INJECTIVE` and evaluates it, as the term it is, on maps computed in `Long`: it holds
of `3n + 1`, `n + 1`, Rule 30's map and `n XOR 2n`, and fails of `n / 2`, `2n` and `n * n`, so it
is neither vacuous nor trivial. That each period of an orbit is a power of two follows from
`TRIANGULAR_PERIOD` by an induction on `k` that is not written in the kernel.
