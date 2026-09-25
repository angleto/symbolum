# 0042. An inductive type is built from its constructors, over one universe of labelled trees

- **Status:** accepted
- **Date:** 2026-09-25
- **Extends:** 0006, 0020

## Context

No syntax could be a **type** here. Every type the chain holds was carved by hand with
`Kernel.defineType` — `num`, `prod`, `word`, and through `Quotient` the classes of an equivalence —
and each of those is an object, not an expression. The one way to speak of expressions was the
arithmetic coding `docs/adr/0014` chose for the object level, and every function over a code pays
for a proof that its recursion is admissible: `Language.scala` says of itself that that proof is
most of the file.

`docs/adr/0014` rejected a defined type for the object language on cost, and said the option
stays open at the meta level. The question that reached this repository through Principia
Mathematica (Mycelium card `9b02e0ba`) is the general form: a builder that takes a list of
constructors and returns a type with its induction principle and its recursion theorem, derived
and not assumed. HOL Light's `define_type` is that builder, and what it is built from was all here
by 2026-09-16: `ind` and `INFINITY`, `defineType`, `INDUCTIVE` with `Monotone.prove`, `word` with
`LIST_CONS` and its injectivity, `prod`, `COND` and `select`.

## Decision

**One universe holds every such type: `word(num) -> L -> bool`, the set of pairs (path, label) of
a tree**, and a type is `Kernel.defineType` over the least set of trees its constructors reach.

- `NODE l c` is the tree with label `l` at the root and `c i` under child `i`, written as the
  term `\l c p x. (p = WORD_EMPTY /\ x = l) \/ (?i q. p = LIST_CONS i q /\ c i q x)`. Its
  injectivity is `LIST_CONS_NOT_EMPTY`, `LIST_CONS_INJECTIVE` and extensionality, proved once per
  type at that type's label.
- The label of constructor `k` is `PAIR k (PAIR v0 (PAIR v1 (... T)))`, one slot per fixed
  argument of any constructor, the slots of the others filled with `select (\z. T)`. Two
  constructors differ in the numeral; one constructor's labels differ exactly where its arguments
  do.
- The children of a node are `\i. COND (i = 0) r0 (COND (i = 1) r1 (... EMPTY))`.
- The representing set is `INDUCTIVE F`, `F` the disjunction of one clause per constructor, and
  `Monotone.prove` discharges `INDUCTIVE_INTRO`'s obligation.

From those the builder derives, for each type: injectivity of every constructor, distinctness of
every pair, the induction principle, case analysis, and the **recursion theorem**
`!f0 ... fk. ?h. h (Ck args) = fk args (h y0) ...`, through the graph of the function as the least
set of pairs closed under the equations, shown functional by induction using injectivity and
distinctness. `Datatype.defineRecursive` names a function by it and hands back the equations.

**`NODE` is a term and not a constant.** Nothing is declared for the universe, so two types
built over one theory do not meet on a name, and the builder, like `Quotient`, adds no link to the
chain and moves neither `docs/lemmas.md` nor the reading register. The cost is a discipline on the
code, stated where it lives: no derivation in the builder normalises a term holding a node, and
every reduction is at the root.

**The builder refuses a type none of whose constructors is free of recursive arguments**, and
that refusal is exact rather than a restriction: every clause of `F` then asks a member of `S` for
its children, so the empty set is closed and the least set is empty.

## What it measured, 2026-09-25, on `7.0` at `057a584b`

`Syntax` is the consumer the acceptance criterion asks for: the terms of Peano arithmetic as a
type `pterm` with the five constructors `Language` numbers `0` to `4`, `PSUBST` defined by the
recursion theorem, and `PSUBST_SELF`, `!t i. PSUBST i (PVAR i) t = t`, proved by induction. Built
over `Chain.standard.widest` in under a second, after a chain that takes fifteen.

- **Induction and case analysis spend no axiom at all.** `Derivation.axiomsOf` is empty for
  `PTERM_INDUCT` and `PTERM_CASES`: `INDUCTIVE_INDUCT` and `INDUCTIVE_INTRO` cost nothing, the type
  definition asserts nothing, and the propositional steps are `Intuitionistic`'s.
- **Injectivity, distinctness and recursion spend exactly choice, eta and infinity**: the choice
  through `COND` and the witness of the graph, eta through extensionality in `NODE`'s injectivity,
  infinity through `num`, which the paths and the constructor indices are written in. All three
  are already in the chain's nineteen, so the trusted base does not move.

`DatatypeSpec` asserts both as equalities.

## Consequences

A type is now a value a caller builds in one call, with the facts a reader expects of it, and a
function over it is an equation rather than an admissibility proof. The object level is
unchanged: `docs/adr/0014`'s reason for numbers there is that the embedded theory quantifies over
codes, and a datatype at the meta level does not give the embedded theory anything. What it makes
statable is the bridge, that the code of `PSUBST` of a term is `NUM_SUBST_TERM` of its code, which
nothing here proves yet.

What the builder does not do, named: **one type at a time**, recursive only through arguments of
the type itself, so no mutual recursion and no recursion under `word(t)` or `num -> t`; and **no
uniqueness** in the recursion theorem, which a caller who wants it gets by induction.

## Alternatives rejected

**HOL Light's `recspace` as a link of the chain**, the universe and its constructors declared once
as constants. It is the more economical proof, since `NODE`'s injectivity would be proved once
rather than per type, and it is rejected for what it moves: a link declaring constants becomes
`Chain.widest`, enters the reading register and `docs/lemmas.md`, and makes every type built later
depend on the chain's order, which is exactly what `Quotient` avoided by being a function. The
per-type proof of `NODE`'s injectivity is a few hundred inferences and is measured above as part
of the second the whole type costs.

**Children as a list of trees rather than a function from `num`.** It would reuse `LIST_CONS`'s
injectivity for the children too, and it is wrong: `NODE l [EMPTY]` and `NODE l []` are the same
set of pairs, so the node would not be injective in its children. A function with the empty tree
past the last child has no such collision.

**A tree type per datatype, carved by hand the way `word` was.** That is what four types cost
here, and it is the cost this record exists to stop paying.
