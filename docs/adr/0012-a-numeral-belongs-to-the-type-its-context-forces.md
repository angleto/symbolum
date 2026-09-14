# 0012. A numeral belongs to the type its context forces

- **Status:** accepted
- **Date:** 2026-09-12

## Context

`Parser` decided a numeral's type from the declared type of the constant the notation names as
`1`, and its docstring said why: *"numerals here belong to one theory and one type, and a
polymorphic numeral would need the elaborator to decide which."* That was correct while the reals
were the only type with numerals, which they were from the first day until `num` was defined on
2026-09-10.

What it cost is one line. `Power : real -> num -> real` wants a real base and a natural exponent,
so `Power 2 3` could not be written at all: one digit string cannot be both, and the exponent had
to be spelled `SUC (SUC (SUC ZERO))`. An index written as an expression, which is most of the
indices anybody writes, had to be spelled that way throughout. It is the numerals of item A2 in the
consumer's gap audit, and with the rotation of A3 it was one of the last two items of that audit's
Part A that were neither done nor a decision.

The pressure is therefore a consumer's and not an aesthetic one: the collatz repository writes
`NUM_POW (SUC (SUC ZERO)) t` in four places for exactly this reason.

## Decision

**A numeral takes a metavariable and is expanded once unification has said what its surroundings
required.** The expansion happens between `unify` and `build`, and it can be in neither: inside
`infer` the context has not spoken yet and the numeral would fix a type the term around it was
going to disagree with; inside `build` the nodes above have already read their types off and are
left holding a metavariable the application then refuses.

A `Notation` therefore carries a **sequence** of numeral encodings rather than one, and `Peano`
declares the second: `NUM_ONE`, `NUM_BIT0` and `NUM_BIT1`, all defined, no axiom.

**`ZERO` is that encoding's zero rather than a fourth constant beside it**, so `0:num` and `ZERO`
are the same term.

**A numeral whose type nothing determined is refused where the theory reads two encodings, and
taken where it reads one.** One encoding is not a choice, so there is nothing for a context to
decide. The escape is an annotation, `2:num` or `2:real`, which this parser did not read before.

**A caller that knows the type says so in the call**, through
`Parser.term(theory, notation, text, expected)`, rather than by annotating inside the text.

## Consequences

**`ZERO` now prints as `0`**, everywhere, including inside `SUC` chains: `NUM_SUB (SUC 0) (SUC (SUC
0)) = 0`. That is the direct consequence of `ZERO` being the encoding's zero, and it moved
sixty-five lines of the consumer's certified artefact with no statement, verdict or hypothesis
count changing.

**`SUC ZERO` and `NUM_ONE` are different terms with the same value**, and the library is written
with the first. `NUM_ONE_SUC` is the bridge. This is the one thing that got worse: a rewrite that
hooks `SUC ZERO` does not hook a statement written `1`, and a reader has to know which spelling a
lemma uses.

The consequence above is still exactly true and is no longer the end of it. On 2026-09-13
`Successor` carried the bridge the whole way: it puts a numeral of `num` into the successor form
every recurrence over that type is stated at, so a caller holding one spelling can reach lemmas
written in the other by carrying its claim across an equation. It declares nothing and costs no
axiom, and the five facts it needs are the ones this decision introduced. `Power x 2 = x * x` had
not been provable between these two dates and is.

**Two statements print oddly and are honest**: `NUM_ONE_SUC` reads `1 = SUC 0` and `NUM_REAL_ONE`
reads `real_of_num 1 = 1`, whose two numerals are at different types. Both read back to the term
they were printed from, which `NotationRoundTripSpec` asserts; HOL Light prints `&1 = 1` for the
same reason and with less to go on.

**`Show`'s annotated form now annotates numerals.** `~(1 = 0)` is `ONE_NOT_ZERO` over the reals and
is genuinely ambiguous in the widest signature, so it stopped reading back; the annotated form
exists for free names for the identical reason and this is the same repair.

**Every development above `Peano` must take Peano's notation**, not the reals'. They were one table
until this landed. `Series` took the reals' and was changed, because `chain.series` and
`chain.widest` would otherwise answer differently about the same digit string.

**The reading register gains a row per encoding.** One flat `notation numerals` label put two
spellings under one statement, which a reader cannot attest to.

## Alternatives rejected

**A separate `NUM_ZERO` constant for the encoding's zero.** Attractive: `ZERO` goes on printing
`ZERO`, no churn anywhere, and the two documents do not move. Rejected because `NUM_ZERO` and
`ZERO` would then be different terms denoting the same thing, so every lemma stated about `ZERO`
would be out of reach of every statement written with `0`, and the failure mode is a rewrite that
quietly stops matching rather than an error anybody sees. The churn is one evening; that is
permanent.

**Default an undetermined numeral to the first encoding instead of refusing.** Attractive: nothing
breaks, no call site changes, and `1 = 1` goes on parsing. Rejected because it makes the meaning of
a text depend on the order in which encodings were declared, and a consumer adding an encoding
would silently change what its existing statements mean. A translation that is wrong in a way its
reader cannot see is the one failure this repository will not accept, and refusing to translate is
the better failure: it is the same rule `Translate` follows when it refuses a claim the theory has
no constant for, by name.

**Refuse an undetermined numeral in every theory, including one with a single encoding.** More
consistent, and one rule instead of two. Rejected on a measurement: forty call sites in
`modules/theories` parse the bare text `"0"` or `"1"` against a signature holding only the reals,
and every one of them is unambiguous. A refusal there protects nobody from a second reading that
does not exist.

**Make the numeral constants polymorphic instead of declaring a second set.** This is what a
type-class language would do, and it would give one encoding at every type. Rejected because this
kernel's constants are monomorphic by declaration and a polymorphic `1` would have to be a schema
the kernel instantiates, which is a change to the trusted base for a notation problem.

**Annotate inside the text as the way out of the refusal.** This was the recommendation for the
first few hours and it is wrong, which a consumer established by migrating seven call sites: all
seven knew the type, because each was about to hand the term to a lemma whose signature says it.
The text is what a reader compares against the informal claim a formal statement translates, so
putting the type there is paying in the worst available place. The expected-type parameter puts it
in the interface of the code that already knew it. Seven out of seven is recorded in
`Parser.term`'s docstring as a prediction: if the next consumer also produces only refusals its
caller could have resolved, then offering a parse with no expected type as the first signature is
the wrong default rather than a convenience.
