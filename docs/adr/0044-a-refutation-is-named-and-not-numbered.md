# 0044. A refutation is named and not numbered, its size is its step count, and its width is a recursion

- **Status:** accepted
- **Date:** 2026-09-25

## Context

`Resolving` has proved since 2026-09-15 that resolution is sound: one step, a whole derivation by
strong induction on the step index, and a derivation reaching the empty clause leaving no
assignment that satisfies its inputs. It did so beside the chain and declared nothing: a
derivation is three functions `k : num -> num`, `v : num -> num -> num`, `s : num -> num -> bool`
and two numbers, and every statement was written out.

That is the floor Cook and Reckhow (1979) require of a proof system before the size of a proof
means anything. What comes after it is a lower bound, and the literature's first is Haken (1985):
resolution refutations of the pigeonhole principle for `n + 1` pigeons and `n` holes have size
`2^(Omega(n))`. Ben-Sasson and Wigderson (2001) reach it through the **width**, the largest clause
of a refutation, which is the measure that yields to induction. Any such theorem quantifies over
every refutation of a family, so it needs the refutation, its size and its width as things a
statement can name.

Mycelium card `edc1f509` asked for that, and asked first whether it needs a derivation to become
a **number**: `NUM_RES_PROOF`, a derivation coded with the beta function the way
`Provability.NUM_PROOF` codes a derivation of PA, on the reasoning that a statement over all
refutations seems to need the refutation to be an object of the logic's domain.

## Decision

**No coding.** The refutation stays three functions and two numbers, and the quantifier over all
refutations of a family is three universally quantified functions and two numbers. Four constants
name what the statements are written with, all of them definitions:

| constant | what it says |
|---|---|
| `RES_SAT a k v s j` | the assignment `a` satisfies clause `j` |
| `RES_JUSTIFIED k v s inputs j` | step `j` is an input, or two earlier steps resolve to it |
| `RES_REFUTATION k v s inputs m` | every one of the `m` steps is justified and one is empty |
| `RES_WIDTH k m` | the largest `k j` for `j < m`, and `ZERO` when `m` is |

**The size of a refutation is `m` and gets no constant.** A refutation carries its step count, so
a constant `RES_SIZE m = m` would be a second name for a variable.

**The width is defined by recursion on `m`**, with `COND` choosing the larger of the width so far
and the new clause's length, and three facts make it the largest rather than a bound:
`RES_WIDTH_BOUND` puts every clause under it, `RES_WIDTH_ATTAINED` says it is zero or one of the
lengths, and `RES_WIDTH_LEAST` is what a caller spends.

**`Resolving` becomes a link**, at the end of the chain, because a constant declared beside the
chain is where nothing above can see it.

## The measurement that decided it

`ResolvingSpec` states Haken's theorem over the four constants, with the clauses of the pigeonhole
principle written as sets of literals and the variable of pigeon `p` in hole `h` numbered
`p * n + h`:

```
?c. 0 < c /\ !n k v s inputs m.
  (!j. j < inputs ==> <clause j is a pigeonhole clause for n + 1 pigeons>) ==>
  RES_REFUTATION k v s inputs m ==> 2 ^ (n DIV c) <= m
```

and asserts that it elaborates with **nothing free in it**, which is the check that catches a
misspelt constant, since an unknown letter-initial name parses as a free variable here. It then
derives, with nothing assumed, both hypotheses at the smallest instance: at `n = 0` there is one
pigeon and no hole, its pigeon clause is the empty clause, and the one-step derivation that is
that input refutes it. A lower bound whose hypotheses nothing meets would be true and say nothing,
and would pass the first assertion.

So the premise that a statement over all refutations needs arithmetisation is false, measured,
and it is the second time it has fallen: `Resolving`'s own first paragraph records the first,
when its soundness theorems turned out to parse without any coding.

## Consequences

The chain's widest signature is `Resolving`'s, which moves what `docs/lemmas.md` is printed
through, the reading register's rows, `LibrarySpec`'s pins and `CLAUDE.md`'s two figures about the
library's leading quantifiers. The trusted base does not move: four definitions and no axiom, and
`ResolvingSpec` asserts the theory's axioms are those of the link below.

The five soundness theorems keep their written-out statements, because each is checkable against
the informal claim without trusting a definition. `RES_REFUTATION_UNSATISFIABLE` is the last of
them read through the names and derived from it by opening each definition once at the top of the
term it heads, so it rests on nothing the written-out one does not, which `ResolvingSpec` asserts
as an equality of axiom sets.

The width facts cost the naturals' two axioms and nothing else, the case split `COND` is read with
being the choice and every fact about `num` the infinity.

## Alternatives rejected

**`NUM_RES_PROOF`, a derivation as a beta-coded number.** Rejected by the measurement above: it
buys self-reference, which is what Goedel's argument needs and what proof complexity does not.
The coding would have to be taken apart by `NUM_BETA` at every step of every argument about a
refutation, for nothing a statement needs.

**The width as the predicate "some clause has at least `w` literals" rather than a function.**
That is exactly what a lower bound states, and it would have needed no recursion. It was not taken
because an upper bound, the other half of every width argument, wants the function: "every clause
has at most `w` literals" is `RES_WIDTH k m <= w` with `RES_WIDTH_LEAST` behind it, and the
predicate form would have to be complemented under a quantifier every time.

**The width as `NUM_LEAST` of the bounds.** It avoids `COND`, and its existence needs an induction
anyway, since a bound on finitely many lengths has to be built; the recursion builds the value
itself and the existence is then free.

**Restating the five soundness theorems through the names.** Every one would then be read through
a definition by a reader checking it against the textbook, which is the trust the written-out
statements were chosen to avoid; the named form is derived for the one of them a lower bound spends.

## What is not here

The lower bound itself. Haken's statement is written and not proved, and proving a width lower
bound for the pigeonhole principle is Mycelium card `01520749`. What that work will spend of this
record is the four names and the three width facts, and what it will need that is not here is the
behaviour of the width under a restriction of the variables, which is the step every such
argument turns on.
