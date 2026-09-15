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
therefore do not change, no code anywhere writes the literal `"+"` as a constant name, and the axiom
texts are in concrete syntax and are spelled by the notation. Four `val`s and two regenerated
documents.

**No implicit coercion.** `real_of_num` stays written where a natural is used as a real. Overloading
decides which constant a symbol names; it does not insert a function nobody wrote, and the four
miniF2F statements `docs/evaluation.md` records as blocked by a coercion stay blocked. A record that
decided both at once would be deciding the second one silently.

## Consequences

**172 statements change their printed form, and `docs/lemmas.md` is regenerated in the same
change.** That is a large diff in which no statement means anything different, which is the diff
this repository finds hardest to review and the reason the guard below matters more than the
reading.

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

**The work is a parser change and a table, not a theory change.** No constant is added, no axiom
moves, nothing becomes provable that was not. Anyone judging it by what the prover can newly reach
will judge it wrongly, which is the same sentence `0016` had to write about the construction.

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
