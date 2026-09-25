# 0046. Identities of a commutative ring are decided by one builder, over constants and laws

- **Status:** accepted
- **Date:** 2026-09-25
- **Extends:** 0036

## Context

`docs/adr/0036` put the rationals' carrier on `prod(int, num)` and stopped at the type, because
every lifted operation owes an obligation over `int` and nothing decided identities there:
`Semiring` was written against `Peano`'s lemmas by name and `Ring` against the reals. `Integer`
closed its own obligations with `Semiring` only because its carrier is pairs of naturals. The
question was put to Angelo on 2026-09-20 and again on 2026-09-25 (Mycelium card `fa8737ad`):
generalise the procedure, or derive each obligation by hand. **He chose to generalise.**

## Decision

**`CommutativeRing` builds the normaliser from the constants and the axioms**: associativity,
commutativity and unit of both operations, distribution on the left, and then `x * 0 = 0` for a
semiring or `x + -x = 0` for a ring. Every other rule a normaliser needs is derived there once:
both exchanges, units and zeros on the left, distribution on the right, and for a ring `x * 0 = 0`,
the inverse on the left, uniqueness of the inverse, `--x = x`, `-0 = 0`, `-(x + y) = -x + -y`,
`-x * y = -(x * y)`, `x * -y = -(x * y)` and `x + (-x + y) = y`. A caller holding one of those
under its own name hands it in, and the rules use the caller's theorem.

- **`Semiring` is its `num` instance**, with `Peano`'s laws, `Peano`'s exchange and zeros handed in,
  and the numeral and successor rules as extras. Its normal forms do not move: the order with no
  negation is the order it had.
- **`Integer.ring` is its `int` instance**, with four rules `Integer` already publishes handed in.
- **`consequence`** closes an equation that follows from premises by substitution: `L` is the
  ring's identity with `R + sum ci * (li - ri)`, the premises rewrite each `li` to `ri`, and what is
  left is the ring's identity with `R`. The coefficients are the caller's, and a wrong one is
  refused by the ring.
- **The rationals' operations are its first consumer**: `RAT_ADD`, `RAT_NEG`, `RAT_MUL`, each
  obligation one `consequence` after the stored denominator `SUC (d * e + d + e)` is read back as
  `SUC d * SUC e` (`RAT_DENOMINATOR`), and the two commutativities on classes.

## The order, which is the one decision that is not a table

Negations go down through sums and up out of products, so every monomial carries at most one, at
its head, and cancellation is between neighbours. The order compares **under the negations first**
(`Arithmetic.ringOrder`'s idea, so `m` sorts beside `-m`), **by size inside the recursion** (the
old `Semiring.order`'s idea, so a sum outranks its summands whatever the constants are called), then
by structure, and by the number of negations last.

**The first version counted a negation's node in the size**, which is the one thing that must not
count if the negation is compared last: one level down `-m` was larger than every monomial of its
shape and sorted after them. Measured, not predicted: the rationals' first obligation came back
refused with `m` and `-m` four summands apart. `tools/verify/perturb-commutative-ring.sh` puts the
counting back and `FractionSpec` goes red; `CommutativeRingSpec`'s own three-monomial case stays
green under it, and that file says so rather than claiming the case.

## Consequences

The algebra of any carrier whose laws are theorems is one call away, which is what every quotient
after `int` needed. What it does not cover: `Arithmetic`'s normalisation of the reals is still its
own, because it bootstraps the reals' negation facts through the normaliser it builds and every
derivation in the chain rests on it; moving it is a piece of its own and would move derivation
counts across the chain. And `rat` is not yet an ordered field: associativity, units, the inverse
of a non-zero element, distribution and the order are the next pieces, each a pair-level identity
carried to classes the way the two commutativities are.

Measured when `Semiring` moved onto it: every suite over `num` green, and two generated documents
whose derivations pass through `1 * x = x` seven inferences shorter, because that rule is now two
commutations rather than the route through the successor.

## Alternatives rejected

**Each obligation by hand**, over `INT_MUL_ASSOC` and `INT_MUL_SYM`. It is what `Fraction`'s
transitivity already costs, five rearrangements for one obligation, and it is paid again for
every operation of every quotient after `int`. Rejected by Angelo's decision, and the measurement
behind it is that cost.

**A second procedure beside `Semiring`, for rings only.** Two normalisers with the same six ordered
rules and the same assembly would agree on the day they were written, which is the state
`Rewrite.normaliser`'s own docstring names as the hardest one to notice drift in.
