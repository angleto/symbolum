# 0043. Recursion along a measure asks the caller for admissibility, and is proved through the graph

- **Status:** accepted
- **Date:** 2026-09-25
- **Extends:** 0042

## Context

`Recursion` recurses on the successor and reads one value back; `Descent` recurses on a number and
may read every smaller one. Neither reaches a function whose argument is not a number, and neither
lets a call land at an argument smaller only **by a measure**. `Modular`, `Peano` and `Value` each
said in their own docstrings that this was missing, and each for the same example: Euclid's
algorithm calls itself at `(n, m MOD n)`, which is below `(m, n)` in its second component and in no
sense `Recursion` knows, so `NUM_GCD` has been chosen rather than computed. Mycelium card `9b02e0ba`
lists it as the third thing missing, beside the inductive types `docs/adr/0042` builds.

## Decision

**One theorem, over the argument type `'a` and the result type `'b`:**

```
!m st. (!f g x. (!y. m y < m x ==> f y = g y) ==> st f x = st g x) ==> ?f. !x. f x = st f x
```

- **The order is a measure into `num`**, not an arbitrary well-founded relation. Every recursion
  this repository has needed is on one, and `NUM_STRONG_INDUCTION` is the induction principle the
  proof runs on; a relation that is not a measure wants an induction principle of its own first.
- **Admissibility is the caller's hypothesis**, said extensionally: `st` gives the same answer to
  two functions that agree below `x`'s measure. It is a fact about a step, and a step is a term, so
  nothing general can derive it; `EuclidAlgorithm` discharges it for one step, and the discharge is
  a case split and `NUM_MOD_LT`.
- **The proof is `docs/adr/0042`'s graph with the constructors replaced by the measure**: the least
  set of pairs `(x, st f x)` over every `f` whose pairs below `x` are in the set, strong induction
  on `m x` to show it functional, and the choice of the value at each argument. It reuses the
  builder's moves rather than a second copy of them.

`EuclidAlgorithm` is the consumer: `NUM_EUCLID_GCD a b = COND (b = 0) a (NUM_EUCLID_GCD b (NUM_MOD a b))`,
and `EuclidAlgorithmSpec` computes `NUM_EUCLID_GCD 4 6 = 2` by those equations alone. It is named so
because `NUM_EUCLID` is already Euclid's lemma.

## What it measured, 2026-09-25

The theorem costs **choice and infinity and not eta**, which `WellFoundedSpec` asserts as an
equality: there is no node to compare by extensionality here, where `Datatype`'s recursion has one.
And the hypothesis carries weight, which the same spec shows by refuting the conclusion without it
at `st f x = SUC (f x)`.

## Consequences

A function whose recursion descends by a measure is a definition here now, with an equation that
computes. What it does not give is the theorem such a definition is usually wanted for: that
`NUM_EUCLID_GCD a b = NUM_GCD a b` off both zero is not proved, and it wants the common divisors of
`(a, b)` to be those of `(b, a MOD b)`. `EuclidAlgorithm` sits beside the chain as a debt, the
standing `Fraction` has, because wiring it into the chain moves `Chain.widest`, the reading
register and the guide's map.

## Alternatives rejected

**An arbitrary well-founded relation**, with its induction principle as a hypothesis. It is the
general form and it is rejected for now on consumers: nothing here recurses along anything but a
measure, and the general form asks every caller to prove an induction principle where a measure
asks for a function into `num`.

**Deriving admissibility syntactically**, by reading the step for calls below the measure. It would
spare a caller the one obligation, and it would be a procedure deciding a semantic property of a
term by its shape, which is `Monotone`'s kind of thing and would refuse many admissible steps; the
obligation is small and a caller can see it.

**Through `Descent`**, recursing on the measure's value. `Descent` defines a function of a number,
and several arguments share one measure, so the function it gives is not the one wanted without a
second construction on top.
