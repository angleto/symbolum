# 0053. The sixteen are theorems: `real` is the type of the cuts, and its constants are aliases

- **Status:** accepted, completes step 4 of 0007 and supersedes 0004
- **Date:** 2026-09-26

## Context

[`0007`](0007-the-reals-are-constructed.md) decided that the reals would be constructed and listed
the last step: the sixteen of `Real.scala` become theorems under the same names and the same
printed forms, and `Real.scala` stops asserting. [`0052`](0052-the-reals-are-lower-cuts-on-the-rationals.md)
chose lower cuts on `rat` and built them beside the chain: a type carved out of `rat -> bool`, its
order, completeness, addition, negation, multiplication by sign and the inverse, every one of the
sixteen provable in the vocabulary of the cuts. Phase 5a moved the construction below the reals
inside the chain, so that a theory holding the cuts exists where the reals are built.

What was left is how the two vocabularies meet. `Cut` publishes `CUT_ADD_SYM`; every consumer of the
reals, 179 call sites of `axiom(` among them, asks for `ADD_SYM` about `real_add`.

## Decision

**The type the cuts are carved as is `real`.** `Cut.TypeName` is `Real.TypeName`, so there is one
type of real number and no second type beside it with a bijection to carry facts across.

**Each of the seven primitives is defined as the operation on cuts it names**: `real_zero` is
`CUT_OF_RAT RAT_ZERO`, `real_one` is `CUT_OF_RAT RAT_ONE`, and `real_add`, `real_mul`, `neg`,
`inv` and `real_lt` are `CUT_ADD`, `CUT_MUL`, `CUT_NEG`, `CUT_INV` and `CUT_LT`. The five
abbreviations over them, subtraction, division, `real_le` and the two numeral bits, are defined as
they always were.

**Each of the sixteen is proved by unfolding it and comparing terms.** The statement is parsed in
the reals' theory and normalised in two passes: the aliases and `real_le` first, then `CUT_LT` into
the negation of `CUT_LE` it abbreviates and `CUT_LT x y \/ x = y` into `CUT_LE x y`. The source
theorem's conclusion goes through the second pass, and the two normal forms must be the same term.
Eleven sources are facts `Cut` already publishes, completeness among them; five are short arguments
in `Real.scala`: `ONE_NOT_ZERO` from the injectivity of the embedding, and irreflexivity,
transitivity, totality and translation of the strict order from the facts about `CUT_LE`.

**Each of the sixteen is cited under its name**, as every published fact is
([`0047`](0047-a-report-stops-at-a-cited-fact-and-a-checker-does-not.md)). A report over a proof
that used `ADD_SYM` showed the axiom by name while it was one, and it shows the fact by name now
rather than walking into the cuts; `Derivation.axiomsOf` still answers the foundation through the
citation.

**`Real.standard` is the construction.** `Real.construction` builds the naturals' arithmetic that
names no real, the pairs, the integers, the rationals, the cuts and the reals, in `docs/adr/0016`'s
order; `Real.constructed` is that over the standard classical logic, and `Chain.standard` shares it
rather than building a second copy.

## Consequences

**The trusted base is choice, eta and infinity.** `Kernel.assertAxiom` is called by `Classical.scala`
and `Natural.scala` and by the two files that assert on a caller's request, and `RealSpec`'s
allowlist says so. The reals' theory asserts exactly what the naturals' does, and every one of the
sixteen spends a subset of it.

**A development about the reals is asked to believe choice.** `Real.standard` sat over
`Logic.standard` until today, so the reals alone cost sixteen and no classical axiom, and the two
configurations were the point of `ClassicalSpec`'s first assertion. A construction cannot offer
that: the rationals are a quotient and the cuts are carved, and both spend choice. What it asks
instead is three, where the axiomatised reals asked sixteen.

**The naturals and the reals stop being siblings.** The reals are built over the naturals, so
`Real.standard` reads every theorem about `num`, and the caller that used to build the naturals
over the reals to get one signature gets it from the construction. `Natural.construct` over another
theory stays, and is called by nothing that builds the reals.

**Four overloads of `Peano.construct` are gone.** Each built the stages of `num` arithmetic that
name no real over a theory of the reals, and every theory of the reals holds those stages now, so
each could only refuse with `NUM_ADD` declared twice. `Peano.standard` is the chain's own
development rather than a second build over the chain.

**`inv 0 = 0` is a theorem of the construction and not yet of the reals.** `CUT_INV_ZERO` is
proved, and through the alias it says `inv 0 = 0`; nothing publishes it under the reals' name, and
`Ring`'s refusals on the ring corpus are unchanged. Publishing it is a decision about the reals'
interface and not this one.

**What it costs, measured on 2026-09-26 on scala-cli-compiled classes of this branch**: the chain
builds in about 25 s and retains 591 MB after a collection, against 544 MB for phase 5a's chain,
whose reals were asserted over the cuts; `Real.standard` alone builds in 12 s and retains 67 MB.
These are photographs of one machine on one day.

## Alternatives rejected

**Renaming `Cut`'s constants to the reals' names.** `CUT_ADD` would be `real_add` and the sixteen
would be `Cut`'s own statements. It moves the aliases into fifty-one statements and a harness that
names them, and it makes the construction read as if it were about the field before anything is
proved about it; an alias is one definition per constant and leaves `Cut` saying what it built.

**A second type with a bijection.** Carving `real` again from the cuts, or declaring it and relating
it, would carry every fact across a map that proves nothing: the cuts already are a type.

**Keeping the axiomatised `Real.standard` beside the construction.** It would keep a development of
the reals free of choice, at the price of `Kernel.assertAxiom` in `Real.scala`, sixteen statements
nothing checks, and two theories naming `real_add` with different content. The trusted base would
not shrink for anybody who reached for the standard theory, which is most callers.
