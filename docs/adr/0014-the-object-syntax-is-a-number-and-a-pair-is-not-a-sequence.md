# 0014. The object syntax is a number, and a pair is not a sequence

- **Status:** accepted
- **Date:** 2026-09-14

## Context

`docs/adr/0013` fixed the embedded theory at PA and the coding of **sequences** at Goedel's beta
function, and left the arithmetisation itself as work not yet scoped. That work starts by deciding
what a term and a formula of the object language **are** here, and the decision has to be made
before a line of it is written, because everything above it is about the representation chosen.

Two things push in opposite directions.

At the **meta** level, which is this logic, a reader wants an inductive datatype: a term is zero, a
variable, a successor, a sum or a product, and a formula is built from terms by the connectives and
a quantifier. Structural induction is then the kernel's, and every proof about syntax is a proof
about a datatype.

At the **object** level, which is PA, the syntax has to be **arithmetic**: `Prov` is a formula of
arithmetic about the code of a formula, and D3 is an induction inside the theory over the structure
of Sigma-1 formulas. A datatype is not available there. Whatever the meta level uses, the object
level sees numbers, and the theory has to be able to take a code apart using bounded quantifiers
alone, since that is what keeps `Prov` Sigma-1.

`docs/adr/0013` already recorded the consequence of the second half and did not draw it out: the
decoding must be Delta-0, and that is what selected the beta function over a product of prime
powers and over iterated pairing.

## Decision

**A term and a formula of the object language are numbers.** There is no datatype and no new type:
`num` is the carrier, and being a term or being a formula is a **predicate** on `num`.

**A constructor of fixed arity codes its arguments with a pairing**, and the pairing is Cantor's,
`NUM_PAIR a b = NUM_TRI (a + b) + a`, built on the triangular numbers.

**A sequence of unbounded length is coded by the beta function**, as `docs/adr/0013` decided, and
not by iterating the pairing.

**The recursion that defines a syntactic predicate is `Descent`**, the course-of-values recursion on
`num` that `docs/adr/0013` already named as the reason it exists. What makes it applicable is a fact
about the pairing rather than about syntax: both components of a pair are at most the pair.

## Consequences

The trusted base does not move. The pairing is a definition and its facts are derived.

**`docs/adr/0013` rejected "iterated Cantor pairing" and this record uses Cantor pairing, and the
two do not conflict.** That rejection is about **sequences**, and the reason it gives is exact: a
sequence built as nested pairs answers "the element at `i`" by decoding `i` times, which is a
recursion and not a bounded formula. A constructor of arity two decodes in **two** steps, and two is
a constant. The criterion that rejected pairing for sequences is the criterion that admits it here,
and the sentence to carry away is that a pair is not a sequence: the objection was never to the
pairing, it was to the iteration.

Anybody reading this repository in six months will see `NUM_PAIR` and `NUM_BETA` both used in the
coding of one formula and think one of them is redundant. They are not, and this is the paragraph
that says which job each has.

**Both components are bounded by the pair**, and that fact is doing two jobs rather than one. It is
what lets `Descent` define a predicate by recursion on a code, since every sub-code is a smaller
number; and it is what will let the object theory's version of the same predicate quantify over
sub-codes **boundedly**, which is what Delta-0 means. The bound is not a convenience of the
construction, it is the construction's reason.

Working with codes rather than with a datatype **costs meta-level convenience** and this is the
consequence to be honest about. A proof about formulas is a proof about numbers satisfying a
predicate, with no structural induction from the kernel and no pattern match. What is bought is that
the coding needed by the object level exists from the start rather than being bridged to a datatype
by a representability argument; a datatype would need the numeric coding **as well**, and then a
theorem relating the two for every construction.

## Alternatives rejected

**A defined type for terms and a defined type for formulas**, carved out of `num` the way `num` is
carved out of `ind`, with structural recursion derived the way `Natural.scala` derives it. This is
the comfortable answer at the meta level and `docs/adr/0006` makes it available. It is rejected on
cost rather than on correctness: it does not remove any of the numeric work, since the object theory
still needs codes, so it **adds** two type definitions, two recursion theorems and a coding function
with its injectivity, in exchange for making meta-level proofs pleasanter. It stays available: a
type can be carved out of the predicate later without anything below it changing, which is the
property that makes rejecting it now reversible.

**A product of prime powers for the constructors**, which is Goedel's own and would make one
mechanism serve both jobs. Rejected by `docs/adr/0013`'s criterion, unchanged here: extracting an
exponent is not bounded.

**Using the beta function for the constructors too**, which would also make one mechanism serve
both. Rejected because the beta function does not give a **coding function**: `NUM_BETA_SEQUENCE`
says that for every finite sequence there **exist** two numbers that code it, and nothing picks one
out. A syntax needs a definite code for a definite term, and the pairing is a function where the
beta function is an existence statement. This is the sharpest reason the two are both here and it
was not obvious until the sequence lemma was proved and its statement read back.

## What was measured and what was not

Measured: `Peano` has no monotonicity of addition against the order and no triangular numbers;
`Modular` has `NUM_DIV`, which a Cantor pairing would need if it were written with a division, and
the form chosen needs none. `Descent` exists and costs no axiom.

Not measured, and it is the same load-bearing claim `docs/adr/0013` ends on: that a decoding written
with bounded quantifiers over sub-codes is Delta-0 **in the object theory**. Nothing here has been
formalised far enough to check it, and the first work that would expose it as wrong is the same one
that record names, Sigma-1 completeness.
