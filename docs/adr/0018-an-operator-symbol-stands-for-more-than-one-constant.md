# 0018. An operator symbol stands for more than one constant, and the elaborator picks which

- **Status:** accepted
- **Date:** 2026-09-15

## Context

[`0016`](0016-what-the-construction-needs-in-front-of-it.md) leaves two questions open deliberately
and says of this one that it is "a record of its own and it comes **before** the integers, not after
them". This is that record. What forced it was not the integers, which do not exist yet, but five
measurements taken on 2026-09-15 against the chain and the library as they stand, two of which say
that the decision has already been half taken in the other direction and nobody noticed.

**Every operator the chain declares belongs to the reals, and `num` has had none since it landed.**
`Real.scala` lines 204 to 218 are the whole of it: `<`, `<=`, `>`, `>=`, `+`, `-`, `*`, `/` and a
prefix `-`. No other development calls `withInfix` at all. The type `num` has been in the chain
since 2026-09-10 and every arithmetic statement about it is a prefix application.

**That is 172 of the library's 427 printed statements, forty per cent.** Taken from
`docs/lemmas.md`: 172 name at least one of `NUM_ADD`, `NUM_MUL`, `NUM_LE`, `NUM_LT`, `NUM_SUB`,
`NUM_DIV`, `NUM_MOD` or `NUM_POW`. `NUM_DIVISION_UNIQUE` is what that costs a reader:

```
!x:num. !y:num. !z:num. !u:num. !v:num.
  NUM_ADD (NUM_MUL x y) z = NUM_ADD (NUM_MUL x u) v /\ NUM_LT z x /\ NUM_LT v x
    ==> y = u /\ z = v
```

against what it says, which is the uniqueness of quotient and remainder:

```
!x:num. !y:num. !z:num. !u:num. !v:num.
  x * y + z = x * u + v /\ z < x /\ v < x ==> y = u /\ z = v
```

`Notation`'s own first paragraph is the argument, written before any of this existed: *"a theory of
arithmetic is twenty axioms that a person has to read against a source, and `(!x. (!y. ((+ x) y =
(+ y) x)))` is not something anyone checks; `!x y. x + y = y + x` is."* The layer does that job for
one of the two numeric types the chain holds.

**The LaTeX surface already overloads, and it has drawn the line this record arrives at.**
`Spellings.scala` gives `NUM_ADD` the template `#1 + #2`, `NUM_MUL` `#1 \cdot #2`, `NUM_LE`
`#1 \le #2` and `NUM_LT` `#1 < #2`: the same marks the reals get, for the same operations. And it
gives `NUM_SUB` `#1 \mathbin{\dot-} #2` and `NUM_DIV` `#1 \operatorname{div} #2`, which are
**deliberately not** `-` and `/`. Somebody writing that table from the literature made a decision
per operator before anybody asked the question, and the two output surfaces of this repository have
disagreed since. A printer has no reader, so that table never had to answer the
question this record does.

**The machinery to resolve by type exists and is already used once.**
[`0012`](0012-a-numeral-belongs-to-the-type-its-context-forces.md) put two numeral encodings behind
one digit string, and `Notation.withNumerals`'s docstring says how: the encodings are *"kept as a
sequence rather than a map keyed by type because a `Notation` has no theory to ask what type a
constant was declared at; the parser, which does, picks the encoding whose `one` matches the type
the numeral's context forced."* `Parser.encodings` is two lines and `Parser.expand` has the three
refusals such a resolution needs.

**And the objection to reusing it is written down in `Peano`.** That file defers overloading and
says why the numerals were affordable while `+` is not: *"`+` would have to be resolved by the types
of its arguments **before** those types are known, since they are what the operator is being applied
to."* That sentence is what this record had to answer rather than repeat, and the answer is that it
describes resolving eagerly, which is not what the numerals do either. A numeral is not resolved
when it is read; it takes a metavariable, unification runs, and `expand` reads the answer back
afterwards. An overloaded operator can be deferred the same way, because every candidate for one
symbol has the **same shape**: `+` is `t -> t -> t` at both types and `<=` is `t -> t -> bool` at
both, so the elaborator constrains the shape, lets the arguments settle `t`, and picks afterwards.

That last sentence is a restriction and not a description, and it bites immediately.
`Power` takes a real base and a natural exponent and `NUM_POW` takes two naturals, which the
library says in its own statements, `Power x (NUM_ADD y z) = Power x y * Power x z` at `x:real` and
`real_of_num (NUM_POW m n) = Power (real_of_num m) n` at `m:num`. They do **not** share a shape, so
`^` cannot be overloaded across them however much the LaTeX table writes both `#1^{#2}`.

## Decision

**A symbol may stand for more than one constant, and which one is decided by unification, exactly as
a numeral's encoding is.** `Notation.infix` is already a `Vector` and may hold several entries for
one symbol. The parser gathers the entries for a symbol, looks each entry's constant up in the
theory to learn the type it was declared at, elaborates the application against the shape those
candidates share, and picks the candidate at the type unification settled. The three refusals are
the numeral's three, in the same words: no candidate this theory declares, a type nothing
determined, and no candidate at the type that was determined.

**`Notation` gains no types.** It stays a table of symbols, constants, precedences and
associativity, with no way to ask what anything means. Keying it by type would make the notation
layer depend on a theory, which is the coupling `withNumerals` refused for the same reason.

**A symbol is overloaded only where it names the same operation, and only where the candidates share
a shape.** Two conditions, and the first is a judgement about mathematics while the second is
mechanical:

| | `num` | integers | rationals |
|---|---|---|---|
| `+`, `*` | yes | yes | yes |
| `<`, `<=` | yes | yes | yes |
| `-` | **no**, truncated | yes | yes |
| `/` | **no**, floor | **no**, floor | yes |
| `^` | no, no shared shape | | |

`Peano`'s own docstring is the reason for the first refusal, and it is a section heading rather
than an aside: *"The subtraction here is truncated, and a reader who forgets that will write a false
lemma"*. `x - y` written for `NUM_SUB` would be read as the field's subtraction by every reader who
has one in mind, and the lemma they would then write is false at `y > x`. `NUM_DIV` is floor
division named by `select` and is not the field's `/` either. Those two keep a spelling of their
own, and the LaTeX table already has both.

**The prefix spelling is not removed.** `NUM_ADD x y` keeps reading. What changes is what a term
prints as, because the printer is keyed by constant and gives each constant one symbol.

**The symbol is a spelling and never a name.** `Real.Addition` is the string `"+"`, so the reals'
addition is a constant **named** `+`, and the same is true of `*` and `<`. That was harmless while
one type had the symbols and becomes a trap the moment two do: a reader meeting `+` in a list of
constants, in `docs/reading-register.md` or in a refusal, cannot tell whether it is a spelling or a
name. The four become `real_add`, `real_mul`, `real_lt` and `real_le` in the same change. It is
cheap and it was measured: 83 call sites reach them through `Real.Addition` and its siblings and
therefore do not change, and the axiom texts are in concrete syntax and are spelled by the notation.
Four `val`s and two regenerated documents.

**Three of the four carry the defect and the fourth does not**, which was measured while building
this and is worth correcting here rather than leaving the paragraph above to be believed.
`NonStrictOrder` was already `"le"`, a word: nobody could have mistaken it for a notation. It is
renamed for uniformity of the four, and 14 of the 83 call sites counted above are its. **And two
constants this record never looked at have exactly the defect it argues from**: `Zero` is `"0"` and
`One` is `"1"`, so the reals' zero is a constant named `0` where `num`'s is `ZERO`. They are
deliberately **not** renamed here. They belong to [`0012`](0012-a-numeral-belongs-to-the-type-its-context-forces.md),
and taking them in passing would settle the interaction of two records in one commit.

**The claim that no code writes `"+"` as a constant name is false by one**, and the one is harmless:
`RemedySpec` builds `AlreadyDeclared("+")` as a sample refusal in a rendering test, where the string
is an argument and not a lookup. `Arithmetic` passes `"+"` and `"*"` to `compute`, which was the
other candidate and is **not** an instance: those reach `reals.term(s"$left $operator $right")` as
concrete syntax, so they are spellings the notation resolves, which is what this record is about.

**No implicit coercion.** `real_of_num` stays written where a natural is used as a real. Overloading
decides which constant a symbol names; it does not insert a function nobody wrote, and the four
miniF2F statements `docs/evaluation.md` records as blocked by a coercion stay blocked. A record that
decided both at once would be deciding the second one silently.

## Consequences

**138 lines of `docs/lemmas.md` change, and it is regenerated in the same change.** That is a large
diff in which no statement means anything different, which is the diff this repository finds hardest
to review and the reason the guard below matters more than the reading.

**This paragraph said 172 until the change was built, and the number was wrong in kind rather than
stale.** 172 counted the statements naming any of **eight** `NUM_` constants, and this record
decides that four of those eight are **not** overloaded. Measured against the implementation: of
436 printed statements, 175 name one of the eight, **135** name one of the four that get a symbol
and are the ones whose form moves, and the other 40 name only `NUM_SUB`, `NUM_DIV`, `NUM_MOD` or
`NUM_POW` and are byte-identical. The three lines beyond the 135 are the rename showing up in the
document's **name** column, where `le`'s definition row becomes `real_le`, and two statements that
go the other way, described below. The risk measurement under it was taken on the population of
eight and is right on that population; read as a fraction of what changes it is 9 of 135, not 10 of
172.

**Two statements get less readable, which is the cost this record did not price.** `ZERO_LT_ONE`
printed `0 < 1` and now prints `(0:real) < (1:real)`, in both the sections that carry it. Nothing is
wrong: `0 < 1` no longer reads back, since both the numerals and the order are now two, and
`Signature.legible` falls to the annotated form exactly as it was built to. It is the mechanism
working, and it is still a statement a reader now has to read twice. 135 improved against 2 worsened
is the trade, and it is worth stating in those terms rather than leaving the second number to be
discovered.

**`NotationRoundTripSpec` is what makes this safe, and it already exists.** It reads every statement
in `docs/lemmas.md` back and asserts it is the theorem it was printed from, over the whole
population rather than a sample. If overloading makes any statement ambiguous, that suite goes red
and names it. The risk was measured in advance as well: of the 172, **all 172** carry a `:num`
annotation on a binder, and only **ten** genuinely mix `num` arithmetic with a real operator. In
every one of the ten the `num` side sits under an application whose function type is known,
`real_of_num`, `Power` or `Sum`, so the type is forced by something other than the operator. The
prediction is that nothing is refused; the guard is what settles it.

**A text that used to parse can stop parsing, and that has happened here before.** `0016` records
the chain failing to build when the numerals widened, because `real_of_num ZERO = 0` became
ambiguous in its own statement. The operator case has the same shape and the same escape, which is
the annotation `0016` says the reader narrows rather than the text gains: a caller that knows the
type says so in the call, through `Signature.term(text, expected)`.

**The LaTeX table loses four rows to the notation.** `LatexSpec` requires a spelling for every
constant the notation does not spell, and `NUM_ADD`, `NUM_MUL`, `NUM_LE` and `NUM_LT` move from one
side of that subtraction to the other. Their `Spellings` rows become dead and are removed, which is
the two surfaces agreeing in one place instead of twice.

**`docs/reading-register.md` changes four rows for the rename and gains rows for the precedence
table**, and it is regenerated rather than edited.

**What this does not prevent.** A reader who meets `x + y` and does not look at the binder still
does not know which addition it is. The answer is that the binder is printed, always, and that this
is the same answer the whole system gives for every other polymorphic-looking thing. It is weaker
than a notation that marks the type in the operator, and that is the trade the first alternative
below is about.

**Four consequences this record did not foresee, found by building it.** None of them changes the
decision and all four are things the next overload will meet again.

**The mirror spellings had to come too.** `>` and `>=` are `<` and `<=` read from the other end, so
overloading the two orders at `num` and not their mirrors would have left `!n:num. n < n` reading
while `!n:num. n > n` refused. Worse than an asymmetry: `Counterpart` used to answer that refusal
out of the very rows overloading removes, so this record would have **introduced** a case where a
reader is refused and given nothing. `Peano` declares both mirrors, at no constant and no axiom.

**`Counterpart` loses four of its five rows and keeps one.** A row whose symbol is overloaded is not
idle, it is **wrong**: it tells a reader to rewrite a text that now works. What is left is `-`, the
one symbol whose two readings are different operations, which is this record's own refusal seen from
the reader's side.

**The reading register's rows were keyed by symbol, so `notation infix +` became two statements
under one name.** That is the defect the numerals hit when `num` got a second encoding, and the row
carries `via ${constant}` now for the same reason: a reader cannot attest to a statement that is
silently two. Nothing was attested, so nothing was lost; the `via` is unconditional so that a future
overload cannot silently transfer an attestation.

**And the one that would have gone unnoticed.** `Arithmetic.ringOrder` needs the product to sort
before the sum or associativity stops flattening, and until this change that came out of ASCII,
because the constants were literally named `*` and `+`. Renaming them to `real_mul` and `real_add`
reverses the comparison, and the file's own docstring had already written down what that does, in
the paragraph explaining why `num` uses a different order. **One corpus entry in `PolynomialSpec`
caught it and **no other test in the repository** did.** The ranking is now stated in the code rather than
inherited from spelling, which is the repair the case asks for: an order a canonical form depends on
cannot be a property of how two constants happen to be spelled.

**The work is a parser change and a table, not a theory change.** No constant is added, no axiom
moves, nothing becomes provable that was not. Anyone judging it by what the prover can newly reach
will judge it wrongly, which is the same sentence `0016` had to write about the construction.

## The two this decision left behind, renamed on 2026-09-16

This record argued from a defect — a constant whose **name** is a symbol, so that a reader meeting
it in a list of constants cannot tell a spelling from a name — and renamed three constants for it,
plus `le` so the four read alike. It left two with the identical defect: `Real.Zero` and `Real.One`
were the strings `"0"` and `"1"`.

**They were left deliberately, and not by oversight.** They belong to `0012` rather than here: that
record decides how a numeral is elaborated, and renaming them while implementing this one would have
settled the interaction between two decisions inside a commit about something else. They are renamed
separately, to `real_zero` and `real_one`, on the argument this record already makes. Since
2026-09-12 two encodings are declared, so `0` names one of them and not the other, which is the same
sentence this record writes about `+`.

**The objection that had to be measured, because it would have been decisive.** A numeral must print
as `0`, so it looks as though its constant had better be called `0` — the one case where a symbol
*should* be the name. It does not depend on the name: `Show` asks `notation.valueOfNumeral` **before**
the case that prints a constant's name, so a term any encoding recognises comes out as digits
whatever its constants are called. Two measurements beside it, both taken before the rename: nothing
in any main source compares a constant's name to `"0"` or `"1"`, and the parser picks between the two
encodings by the **type** `one` was declared at rather than by its spelling, which is what
`Notation.withNumerals` says of itself.

So the reason to keep the symbols could not be the one that would have justified keeping them, and
what was left was an asymmetry no document explained. What it cost to remove: two `val`s, three call
sites, one row of `docs/reading-register.md` whose key carries the name. No statement changes its
printed form, which is the difference from this record's own rename, where 135 of 436 did.

## Alternatives rejected

**Accept `+` at `num` for reading and keep printing `NUM_ADD`.** This is exactly the discipline
`withFlippedInfix` already has, and its docstring states it: *"the surface may accept two spellings,
the settled form is one"*, so that the printed form of a term stays the one form that reads back to
it. It is the cheapest option and the round-trip risk vanishes entirely. Rejected because it serves
the writer and the notation layer exists for the **reader**: `Notation`'s first paragraph is about
somebody checking twenty axioms against a source, and under this option `NUM_DIVISION_UNIQUE` is
still printed in the form nobody checks. The flipped case is not a precedent for it either, because
there both spellings denote the same term and the choice is cosmetic; here the prefix form is the
only form 172 statements have.

**A distinct symbol per type: `+.`, `+n`, `⊕`.** No ambiguity anywhere, no elaborator change, and
the printed form says the type. Rejected because a statement written that way is not what anybody
checks against a source either, so it pays the whole cost of the change and buys back none of the
reason for making it; and because it puts one entry per type per operator into the lexer's symbol
table, which is sorted longest-first and shared by every theory.

**Key the notation by type.** A map from symbol and type to constant, resolved in `Notation` rather
than in the parser. It is the obvious shape and it is what `withNumerals` already refused, in
writing: a `Notation` has no theory to ask what type a constant was declared at. Adopting it would
make the notation layer depend on a theory, and the layer is deliberately outside both the theory
and the kernel because a precedence table in the trusted base grows the trusted base every time
somebody wants to write `+` infix.

**Overload every arithmetic operator, `-` and `/` included.** One rule, no table of exceptions, and
the integers and rationals would need no further thought. Rejected on the measurement that opens
this record: the LaTeX table already refuses it, the literature it was written from refuses it, and
`Peano` says in its own first paragraphs that a reader who forgets the subtraction is truncated will
write a false lemma. A notation that makes that lemma easier to write is worse than no notation.

**Defer again until the integers land.** It is what `Peano` decided and the deferral has stood since
2026-09-12. Rejected because `0016` puts the construction next and a user writing `x + y` over the
rationals would have no way to say so; and because the cost of deferring is now measurable rather
than hypothetical, at 172 statements, and every development added over `num` before the decision
adds to it.

**Rename `NUM_ADD` to `+` and let the theory hold two constants of that name.** It would make the
notation table trivial, one entry per symbol, and is the shape somebody expects who has not read
[`0008`](0008-a-constant-carries-what-defined-it.md). Rejected there and not here: two developments
declaring one name produce different constants, so a claim naming both would not be a proposition,
and `SoundnessAttackSpec` still derives `|- F` from the arrangement that allows it.
