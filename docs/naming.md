# How a lemma is named here

Read off the names the library holds rather than invented for them, and written down now
because the moment to write a naming convention is before the size forces one. Mathlib's convention
is the reason two hundred thousand lemmas are findable; here the size does not impose it yet, and a
convention adopted after the fact is a rename.

`LibrarySpec` asserts the rules below against every name in `docs/lemmas.md`, so a name that breaks
one fails the build rather than being noticed a year later.

## The shape

`SCREAMING_SNAKE_CASE`: uppercase letters and digits, single underscores between parts, no leading
or trailing underscore. Every fact name matches it, and `LibrarySpec` asserts that **name by name**
against a pattern rather than by counting how many do. The definitional entries are the exception
and are not a lapse: they are keyed by the constant rather than by a lemma, which is a separate
question, and the section on constants below is about those.

**The counts live in the one sentence below and that sentence is written by the test.**
`LibrarySpec` builds it from the live library and fails when this file stops containing it verbatim,
so it is one sentence rather than figures scattered through the prose. Scattered figures cannot
fail: a small number recurs in a document for unrelated reasons, so a check that merely looked for
each of them somewhere would pass whatever the real counts were.

This paragraph carried two such figures until 2026-09-14 and they were stale by forty, with a
sentence beside them saying they were pinned. It carried a third, a count of how often a small
number appears here, which was also wrong. Three hand-maintained counts inside the passage that
argues against hand-maintained counts, which is the fourth time this document has recorded that
shape and the first time it was the passage itself.

    the library holds 604 entries, 601 distinct names, 595 facts and 6 definitional entries

Pinning them is the third repair this paragraph has needed and the first that can hold. It said
120 on 2026-09-11 and 132 later that day, and neither could be reproduced from the library it
claimed to count. It said 242 and 239 from 2026-09-12 until `SUM_CONSTANT` landed that
afternoon and made them 243 and 240, which nobody noticed until a reader quoted a number out of
here at a session that had the real one. It said 246 and 243 since `NUM_SUM` and its three facts,
and that delta was derived before it was measured: three facts under three names no development
already held, and a definitional entry that belongs to the register's table rather than to this
count. It says 252 and 249 since the numerals on `num`, and that delta was derived the same way and
by the same split: **six** facts under six names nothing already held, and **three** definitions
that are the register's three rather than this count's, so the two documents move by six and by
three on one change. **The sentence this document has been making since its
first draft is that a count maintained by hand drifts from the thing it counts and a count asserted
in a test cannot, and it went on maintaining four counts by hand while saying so.**

There is a second lesson in the same paragraph and it is about how the drift happened. The
prose used to run "from 183 to 195, and those twelve were proved ... all twelve are `Modular`'s".
Somebody later corrected two of those numbers and not the other two, leaving "those nineteen" in a
sentence that went on to say "all twelve" twice. A partial edit to a count reads as a whole one.

So the running totals are gone, and what they were carrying is kept as the two facts worth having,
both of which can still be checked. **Forty-eight names appeared on 2026-09-12 without a single
lemma being proved**: they were held by five developments that sat *beside* `Chain` rather than in
it, `Divisibility`, `Modular`, `Product`, `Word` and `Bounded`, and `Library.of` collects the
chain's developments, so a fact of one of the five was in no library and in no document. Threading
all five into `Chain` is what put them here. `Bounded` contributes none of them and is not missing:
it holds no facts of its own, only a procedure that proves a caller's. **Twelve more were proved
that day and not merely revealed**, all of them `Modular`'s and all in the `NUM_` namespace, which
is the section below: `NUM_DIV` and `NUM_MOD` as functions that denote, Bezout, the greatest common
divisor's divisibility form, and Euclid's lemma with a definition of prime. That twelve is
`2db47fb` and is the one number here anybody can reproduce, by diffing `docs/lemmas.md` across it.

```
[A-Z][A-Z0-9]*(_[A-Z0-9]+)*
```

## The subject comes first

The operator or the type the lemma is about leads the name, and the rest qualifies it:
`ADD_ASSOC`, `MUL_SYM`, `LT_TOTAL`, `SUM_TELESCOPES`, `POWER_ZERO`. A reader scanning
`docs/lemmas.md` for what is known about multiplication looks at one run of lines.

**The naturals carry a namespace**, `NUM_`, because every one of their operations shares a name
with a real one: `NUM_ADD_SYM` is the commutativity of `NUM_ADD` and `ADD_SYM` is the commutativity
of `+`. The embedding is `NUM_REAL_`, which reads as the pair of subjects it is about.

**The integers carry one for the same reason and it is `INT_`**, since 2026-09-18: `INT_ADD_SYM`,
`NUM_ADD_SYM` and `ADD_SYM` are three facts about three different operations that a reader would
otherwise have to tell apart by what the statement is at. It is a third namespace rather than a
second use of the first, and the rule that decides it is the one above read at a third type: a
prefix marks a **clash**, and every arithmetic name the integers introduce clashes with both of the
others. `INT_OF_NUM` is the embedding, which reads as the pair of subjects it is about the way
`NUM_REAL_` does, and `INT_OF_PAIR` is the projection of the quotient, which is not an embedding of
one numeric type into another and is named for what it takes rather than for a pair of subjects.

## Constants are a different question, and today they have three answers

Everything above is about the name of a **fact**. A constant is named by whatever development
introduced it, and the styles in the chain's widest signature are these:

| style | constants |
|---|---|
| a symbol, printed as itself | `+`, `*`, `<`, `=`, `/\`, `\/`, `==>`, `~`, `!`, `?`, `0`, `1`, `T`, `F` |
| lowercase | `div`, `inv`, `le`, `neg`, `sub`, `select`, `real_of_num`, `mk_num`, `dest_num`, `converges`, `lim`, `exp`, `ln`, `sin`, `cos`, `sinh`, `cosh` |
| `UPPER_SNAKE` | `ZERO`, `SUC`, `PRE`, `NUM_ADD`, `NUM_MUL`, `NUM_SUB`, `NUM_LE`, `NUM_LT`, `NUM_REP`, `IND_0`, `IND_SUC`, `BIT0`, `BIT1`, `NUM_DIVIDES`, `NUM_CONG`, `NUM_GCD`, `PAIR`, `FST`, `SND`, `WORD_PAD`, `WORD_LENGTH`, `WORD_NTH`, `WORD_MAKE`, `MAT2`, `MAT_E11`, `MAT_E12`, `MAT_E21`, `MAT_E22`, `MAT_ADD`, `MAT_SMUL`, `MAT_MUL`, `MAT_ID`, `MAT_TRANSPOSE`, `MAT_DET`, `INT_SAME`, `INT_OF_PAIR`, `INT_OF_NUM`, `INT_ADD`, `INT_NEG`, `INT_MUL`, `INT_ZERO`, `INT_ONE`, `INT_DIVIDES` |
| `CamelCase` | `Sum`, `Power`, `Prod`, `Divides` |

Every one of those is in the chain's widest signature since 2026-09-12. Ten of the `UPPER_SNAKE`
row and `Divides` were listed here as "outside the chain" before that, which was true and is the
kind of true thing a document should stop having to say; the eleven `MAT` names arrived after the
move and have never been outside it.

**`MAT2` carries a digit, and it is the dimension rather than an index.** The development is about
2x2 matrices and nothing else, so the name says which, and a 3x3 development would define `MAT3`
without renaming this one. `IND_0` is the precedent for a digit in a constant's name and is a
different case: there the digit is a subscript.

The split follows the development rather than a stated rule: the reals' unsymbolled operations are
lowercase, the naturals' are upper, and the three operators that bind a function and a length are
capitalised. The eight that landed on 2026-09-15, `converges` and `lim` with the six transcendental
functions, are lowercase by that description and by one thing it does not say: `sin` and `exp` are
written lowercase in every book there is, so a convention that produced `SIN` would be a convention
arguing with its own subject. That is a **description and not a rule**, which is why `LibrarySpec` checks the fact
names and not these.

**A type definition names four constants and two facts off the type's own name.** `prod` gives
`mk_prod` and `dest_prod` for the bijection and `PROD_ABS_REP` and `PROD_REP_ABS` for the two halves
of it, and `word` gives the same four spelled `word`. The pair of fact names is read in the order
the equation is written: `PROD_ABS_REP` is `mk_prod (dest_prod p) = p` and `PROD_REP_ABS` is the
characterisation in the other direction. That is a description of what `Kernel.defineType` produces
rather than a rule anybody chose, and the next type defined here will produce the same six.

**Inside the naturals the `NUM_` on a constant marks a clash rather than a type.** `NUM_ADD` and
`NUM_SUB` carry it because the reals hold a `+` and a `sub`; `ZERO`, `SUC` and `PRE` do not, because
nothing else in the chain is called any of those. The **facts** about all five carry it either way,
which is why `NUM_PRE_SUC` is a fact about a constant spelled `PRE` and is not a misspelling of it.

What to do with a new one, until somebody decides otherwise: name it the way its neighbours in the
same development are named. A constant that looked like the reals' and behaved like the naturals'
would be worse than either convention.

## A constant is spelled the way the constant is spelled

`NUM_REP_0` is about `IND_0` and `SUM_ZERO` is about `ZERO`, and the difference is not an
inconsistency: the first names a constant called `IND_0` and the second names one called `ZERO`. A
name that renamed its own subject would be the thing worth banning.

## The suffixes, and what each means

| suffix | what the lemma says |
|---|---|
| `_ZERO`, `_ONE`, `_SUC` | the value at that argument: `SUM_ZERO`, `POWER_SUC` |
| `_ASSOC`, `_SYM`, `_DISTRIBUTE` | the algebraic law of that name |
| `_REFL`, `_TRANS`, `_ANTISYM`, `_TOTAL` | the order property of that name |
| `_CASES`, `_INDUCTION` | a case split or an induction principle |
| `_POSITIVE`, `_NONNEG` | a sign, strict and non-strict |
| `_OF_X` | this from an `X`: `NUM_LE_OF_LT` is `NUM_LE m n` from `NUM_LT m n` |
| `_TO_ZERO`, `_FROM_ZERO` | moving a relation to or from a comparison with zero |
| `_NOT_ZERO` | a non-vanishing conclusion |
| `_CANCEL` | a factor or a summand removed |

## One spelling per concept

The rule with teeth, and the one the corpus breaks in exactly three places. Where two spellings of
one idea are both in use, the **shorter** is the convention, and the longer is listed here with the
name that carries it. The list can only shrink.

| concept | the convention | still spelled otherwise |
|---|---|---|
| non-negative | `NONNEG` (7 names) | `SUM_NONNEGATIVE` |
| not zero | undecided: `NOT_ZERO` (2 names) against `NONZERO` (1) | see below |
| transitive | `TRANS` (1 name) | `LT_TRANSITIVE` |
| antisymmetric | `ANTISYM` (1 name) | `LE_ANTISYMMETRIC` |

The fourth row is the one this table cannot settle by its own rule, and it is listed rather than
decided. `POSITIVE_NOT_ZERO` and `ONE_NOT_ZERO` state a **conclusion** that something does not
vanish; `DIVIDES_NONZERO`, which arrived with `Divisibility` on 2026-09-12, carries `~(a = 0)` as a
**hypothesis**. The shorter spelling is `NONZERO` and the more used one is `NOT_ZERO`, so the rule
above and the corpus point opposite ways, and the two names are arguably about different things
anyway. `LibrarySpec` does not enforce this row, which is the honest state of it: an entry here is a
question somebody has to answer, not a rule the build checks.

Two of the first three rows are one-all ties and the shorter form wins them by the rule above rather
than by a count. **They are not renamed here**, and that is a decision rather than an omission: the three
names are referred to from another repository and from documents outside this one, and a rename is
worth doing once, deliberately, with the references moved in the same change. What the list buys
until then is that the *next* lemma cannot add a fourth spelling.

## What is not a rule

**Not a length.** `SUM_TELESCOPES` and `LT_MUL` are both good names at the size they need.

**Not a grammar.** `SUM_TELESCOPES` is a verb, `SUM_LINEAR` an adjective and `SUM_BY_PARTS` a
phrase, and forcing them into one shape would make two of the three worse.

**Not a uniqueness requirement across developments.** Two developments may hold a lemma of the same
name, and `Library.shared` reports which: `ADD_POSITIVE` is held by `Order` and by `Positivity`. A
caller that wants to rewrite with one asks the development that owns it rather than the union, for
the reason `docs/adr/0008` gives about what a constant carries.
