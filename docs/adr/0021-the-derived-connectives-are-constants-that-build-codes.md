# 0021. The derived connectives are constants that build codes

- **Status:** accepted
- **Date:** 2026-09-16

## Context

`docs/adr/0014` decided that a term and a formula of the object language are numbers, and it
recorded, without drawing the consequence out, what the object theory then has to be able to do:

> the theory has to be able to take a code apart using bounded quantifiers alone, since that is
> what keeps `Prov` Sigma-1.

`Language.scala` gives the formulas four tags, `5` for an equality, `6` for a negation, `7` for an
implication and `8` for a universal, and says twice why there are not six:

> Four connectives and not six, because the others are definitions in the object language rather
> than syntax: disjunction, conjunction and the existential are abbreviations built from these, and
> giving each a tag would mean proving every clause of `Prov` four more times for nothing.

That is the right decision and it leaves an obligation behind. **Until this record, no code
anywhere built one of those abbreviations.** There was no constant, no constructor of the `Obj`
tree, no helper, and nothing in the printer. A reader meeting the sentence above would take it for
a description of something implemented; what it described was an intention.

The obligation came due because of the bounded quantifier, and the chain that leads to it is forced
rather than chosen. The object signature has **no relation symbol at all**: `NUM_TERM` admits a
variable, zero, a successor, a sum and a product, and nothing else. So `i < t` has to be
`?z. i + S z = t`, which needs an existential, which is `~!z.~(...)`. Three abbreviations deep
before a bound can be written, and `NUM_ALL_BELOW` is the first of them anybody actually wants.

`Peano`'s `NUM_LT` is not this and cannot be. It is the ambient logic's order on `num`, the thing
the meta level reasons **with**; what a bounded quantifier of PA needs is a piece of syntax the
embedded theory reasons **about**.

## Decision

**The derived connectives are constants of the ambient logic that build codes**, in the way
`NUM_NUMERAL` is a constant of the ambient logic that builds the code of a numeral. Six of them:
`NUM_AND`, `NUM_OR`, `NUM_EXISTS`, `NUM_LESS`, `NUM_ALL_BELOW` and `NUM_EXISTS_BELOW`.

**No new tag, and therefore no new clause of any recursion.** Every code the six build is a code
the existing four tags already accept, which is what the `NUM_FORM_` fact published about each of
them derives rather than asserts.

**Each is defined over the ones before it**, so that `NUM_ALL_BELOW` is written with `NUM_LESS` and
not with a comparison expanded a second time by hand. The proofs follow the same order for the same
reason.

**The witness index of `NUM_LESS z s t` is a parameter**, not a fixed number.

## Consequences

The trusted base does not move: six definitions, no axiom. Each defining equation costs nothing at
all, for the reason `NUM_PA`'s membership facts cost nothing: it is a definition unfolded and
generalised, with no recursion to justify along the way. `LanguageSpec` asserts that in both
directions rather than as a ceiling.

**What the six buy is that a bounded quantifier is now a sentence this repository can write.**
Before them it was not, and the failure was not a refusal a reader could learn from: there was
simply no way to build the code.

**What they cost is six rows in `docs/reading-register.md` that nobody has read**, and the ordinary
price of a constant in the signature.

**The witness index being a parameter is a cost as well as a decision.** Every statement about
`NUM_LESS` and about the two bounded quantifiers carries one more binder than a reader expects, and
the caller has to choose an index. The alternative is worse and is why: a fixed index needs `z` to
be fresh for `s` and for `t`, and nothing in this development can discharge that. `Language.notFreeIn`
walks a concrete **closed** code and refuses exactly the codes that have a free variable in them,
which is the case such a condition is about. Tag `8` already makes the same decision by accepting a
quantifier over an index that does not occur.

**And the substitution's blindness to capture now has a second index to be blind about.**
`NUM_SUBST_FORM` replaces every occurrence without asking whether the replacement gets captured,
which is sound for a closed replacement and for nothing else. Under `NUM_LESS z s t` the bound
index is `z`, so a replacement mentioning `z` comes out captured. Nothing about the rule changed;
what changed is where a reader has to look for the index, and that is why it is written beside the
clauses rather than left in a docstring elsewhere.

**`NUM_LESS` is a word away from `NUM_LT` and that is a hazard this repository has paid for once**,
with `NUM_PRIME_FACTOR` and `NUM_PRIME_DIVISOR`. The defence here is mechanical rather than
attentive: `NUM_LT` is a predicate and `NUM_LESS` is a function into `num`, so a caller who reaches
for the wrong one gets a type error and not a theorem about something else.

## Alternatives rejected

**A tag apiece for the conjunction, the disjunction, the existential and the bound.** Rejected by
`Language.scala`'s own argument, which is unchanged and is about cost rather than taste: each new
tag is a clause in `NUM_TERM`'s and `NUM_FORM`'s recursions, an entry in the clause descriptor, a
case in every substitution and every freeness walk, and four more clauses of `Prov` to prove. What
it would buy is shorter codes, which nobody reads.

**Scala-level builders and no constants**, producing the codes as terms without naming them.
Rejected because every statement about them would then be a nest six deep, and `docs/lemmas.md`
would carry sentences no reader could check against the informal claim they translate. The `Obj`
tree exists precisely because that nesting is unreadable, and it is private to one file.

**A fixed witness index**, with a freshness side condition on `s` and `t`. Rejected above: the
condition is undischargeable here, so the two bounded quantifiers would be theorems nobody could
apply, which is the shape of defect that fails no test.

**Defining `NUM_LESS` as its full expansion rather than through `NUM_EXISTS`.** It would remove the
ordering constraint between the six definitions, and it was rejected because the defining equation
is what a reader checks: `NUM_EXISTS z (...)` says what the constant means and a nest of six
`NUM_CODE`s says what it is made of.

## What was measured and what was not

Measured: the object signature holds no relation symbol, so a bound cannot be abbreviated without
the existential first; nothing in `modules/` built any of the three abbreviations the file names;
`NUM_FORM_CASES` enumerates exactly tags `5` to `8`; the six need no new `Clause` shape because
they introduce no tag.

Not measured, and it is the same claim `docs/adr/0014` ends on: **that a decoding written with
these bounded quantifiers is Delta-0 in the object theory.** These six make that claim
*expressible*, which it was not before, and they do not settle it. The first work that would expose
it as wrong is still the formalisation of Sigma-1 completeness, which `docs/adr/0013` puts last.
