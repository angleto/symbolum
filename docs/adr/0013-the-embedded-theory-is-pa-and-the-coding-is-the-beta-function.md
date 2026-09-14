# 0013. The embedded theory is PA, and the coding is the beta function

- **Status:** accepted
- **Date:** 2026-09-13

## Context

The system is to state and prove Goedel's incompleteness theorems, and on 2026-09-13 the target was
fixed at the **second** theorem rather than the first. That is not a matter of going further along
one road. It changes three decisions that sit upstream of the first piece of work, and two of them
would have been decided the other way for a G1 target.

What is being built is the incompleteness of an **embedded** theory: a first-order language and
proof system represented inside this logic, with a provability predicate that is a formula of
arithmetic. The incompleteness of *this* system, proved *in* this system, is not what is being
built and cannot be: that is what the second theorem says about anything strong enough to state it.

The first theorem, in the Rosser form, asks for syntax, a proof predicate, representability and the
diagonal lemma. Most of that work is carried out **about** the embedded theory, in the logic that
contains it. The second theorem asks in addition for the three derivability conditions, and D3,
`Prov(p) -> Prov(Prov(p))`, is Sigma-1 completeness formalised **inside** the embedded theory.
That single difference is what the decisions below follow from: for G2, a large body of the work is
object-level, and the embedded theory has to be able to reason about its own syntax.

## Decision

**The embedded theory is Peano arithmetic**, with the induction scheme, and not Robinson's Q.

**A finite sequence is coded by Goedel's beta function**, `beta a b i = a mod (1 + (i + 1) * b)`,
and not by iterated pairing or by a product of prime powers.

**A development whose product is object-level derivations is planned as its own piece of work**,
not as a helper inside the development that first needs one.

## Consequences

The trusted base does not move. All three are definitions and derivations inside the existing
foundation; no axiom is added and `docs/adr/0007`'s count is unaffected.

`Modular` turns out to be most of the ground floor and was not built for this: divisibility,
Bezout, Euclid's lemma and division with remainder are what the beta function's proof needs. What
is missing in front of it is the factorial, the fact that every `d <= k` divides `k!`, and the
Chinese remainder theorem, which `Modular` does not have.

PA rather than Q costs an axiom **scheme** rather than a finite list, so the embedded theory's
axioms are a decidable set of codes and not an enumerated handful. Everything that quantifies over
the theory's axioms has to be written against a predicate from the start. Q would have allowed a
finite list and a simpler `Prov`.

The object-level layer is the part most likely to be underestimated, and it is the reason this
record exists rather than a note. D2 and D3 are theorems **of PA**, so producing them means
building PA-derivations from here, in quantity. A G1-only target needs the same machinery in a
bounded and schematic form, once, for the representability of the primitive recursive functions; G2
needs it to be reusable and reasonably automated, or D3 is thousands of derivations built by hand.

## Alternatives rejected

**Robinson's Q as the embedded theory.** It is the usual choice for G1 and it is the weaker and
therefore stronger result: incompleteness of Q implies it for everything above. It cannot carry
G2. D3 is an induction over the structure of Sigma-1 formulas carried out inside the theory, and Q
has no induction. Choosing Q would mean discovering at the last piece of work that the theory the
whole development is about is the wrong one.

**A product of prime powers, which is Goedel's own coding.** Rejected on the criterion that decides
this whole question: the decoding must be **Delta-0**, so that `Prov` is Sigma-1 and its being so
is provable inside the theory. Extracting an exponent is not bounded, and exponentiation is not
Delta-0. This is the standard reason modern treatments do not use it, and it is a reason that only
bites at G2: for G1 the coding merely has to be representable.

**Iterated Cantor pairing**, which an earlier scoping in this repository preferred and which is
genuinely cheaper **in this logic**: it needs `NUM_DIV` and the least number principle, both of
which exist, and it needs neither the factorial nor the Chinese remainder theorem. It loses on the
same criterion. A sequence built as nested pairs answers "the element at `i`" by iterating the
decoding `i` times, which is a recursion and not a bounded formula, so the property that makes the
beta function worth its cost is exactly the one pairing does not have. The earlier preference was a
measurement of the wrong thing: it compared what the two cost **here**, and what decides it is what
they cost **inside PA**.

**Stopping at the first theorem, or proving the abstract form** in which D1, D2 and D3 are
hypotheses and the conclusion is Loeb's theorem. Both are real theorems and the second is a
fraction of the work. Neither is what was asked for, and the abstract form in particular does not
establish that any actual theory is incomplete. It stays available as an honestly labelled
milestone, and it is not the destination.

## What was measured and what was not

The repository's side of this is measured: `Modular` holds 38 published lemmas and no factorial, no
Chinese remainder theorem and no unique factorisation, and `Descent` (2026-09-13) supplies the
recursion that the syntactic predicates need, at no axiom.

The argument that selects the beta function is **not** a measurement. It is a claim about
Delta-0 definability, taken from the standard treatment of the second theorem, and nothing here has
been formalised far enough to check it. A reader who doubts it should doubt it: it is the load
bearing step in this record, and the first piece of work that would expose it as wrong is the
formalisation of Sigma-1 completeness, which is the last one planned.
