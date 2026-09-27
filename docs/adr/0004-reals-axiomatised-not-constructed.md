# 0004. The reals are axiomatised, not constructed

- **Status:** superseded by [0053](0053-the-sixteen-are-theorems-and-real-is-the-cut-type.md), revised by 0007
- **Date:** 2026-09-03

## Context

The domain this system exists to serve is elementary real analysis: algebraic identities,
derivatives, integrals, limits. All of it needs a type of real numbers with completeness, because
without completeness there are no limits and therefore no calculus.

There are two ways to have one. Build it, from the naturals through the integers and rationals to
a completion, each step a definitional extension that introduces no new axiom. Or assume it, by
asserting the axioms of a complete ordered field and defining everything else on top.

The first is the honest one and it is what the mature systems did. It is also months of work that
teaches this project nothing it wants to know, and it is entirely upstream of the first result
anyone would want from the system.

## Decision

The reals are introduced by axiom: a complete ordered field, stated as fewer than twenty axioms
in a single file, which together with the logic's own axioms is the entire non-definitional
content of the theory.

Everything else is a definitional extension. No other file introduces an axiom.

A test pins the sixteen statements, as the theory prints them, in a copy written out by hand in
the theory's own test file, so a changed or added axiom fails the build until the copy is changed
in the same commit. The same test scans the main sources and fails if `assertAxiom` is named
anywhere but the kernel that defines it and this file. An earlier version compared the theory
against its own list parsed again, which passed any edit; an audit pointed it out.

## Consequences

Calculus is reachable in weeks rather than after the construction, which is the reason for the
decision.

The trusted base grows by those axioms. They are standard and their consistency is a known
result, but the assumption that the file states them correctly is ours alone, and it is the
sharpest risk in the system: a mis-stated axiom makes everything provable, every test still
passes, and nothing anywhere reports a problem. The mitigations are that the file is small, that
the axioms are stated once and read against a textbook, and that the drift test above makes the
axiom set impossible to grow by accident.

Replacing this later with a construction is a change to one file's contents and to nothing that
depends on it, as long as the constructed type ends up satisfying the same characterising
theorems under the same names. That is the property to preserve if the construction is ever
attempted, and it is why the axioms are stated as the properties consumers use rather than as a
minimal presentation.

What this does not cover: nothing here establishes that the axioms are consistent. If they are
mis-stated they may not be, and the system would then prove false theorems while behaving
exactly as it does now.

## Alternatives rejected

**Construct the reals from the naturals.** Introduces no axiom beyond the logic's, which is the
strongest possible position, and is what HOL Light and the other mature systems do. It loses on
schedule: it is months, it is upstream of every result the project wants, and the risk it removes
is one that a single small file plus a drift test already bounds.

**Work over a computable subfield: rationals, or rationals extended by algebraic numbers.**
Everything becomes decidable and the arithmetic is exact and fast. It loses because it has no
completeness, so limits, derivatives and integrals cannot be stated, and those are the domain.

**Axiomatise more than the field: assert the facts about transcendental functions as axioms too.**
Tempting, because it makes `sin` and `exp` available immediately. Rejected because the number of
axioms would then grow with every function added, each one a fresh chance to state something
false, and the drift test would be watching a list that changes constantly instead of one that
never does. Transcendental functions are defined, not assumed.
