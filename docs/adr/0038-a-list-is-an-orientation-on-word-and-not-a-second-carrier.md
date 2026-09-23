# 0038. A list is an orientation on `word` and not a second carrier

- **Status:** accepted
- **Date:** 2026-09-23

## Context

Nothing in this repository could say "a finite sequence of objects of one type" under that name.
Contexts, sequences of formulas and hypotheses are all that shape, and the two things available
were the arithmetic coding, which costs an admissibility proof for every function that walks it,
and `word`, about which the card asking for the work said two things that were checked here.

The obvious reading is that a type is missing and that `Kernel.defineType` should carve it, beside
`num`, `prod`, `word` and `int`. That is what was asked for and it is not what landed.

## The measurement that decided it

Three readings, all off the sources rather than off the register, which stopped listing the carved
types in writing on 2026-09-19.

**`word('a)` is polymorphic.** The card said it is not. `Kernel.defineType` reads the arity off the
free type variables of the predicate it carves with, in a fixed order, and `Word.RepresentationBody`
is `\p:prod(num,num->'a). !i. ~(i < FST p) ==> SND p i = WORD_PAD`. So `word` is a type operator of
arity one, `Word.Element` is `TyVar(Classical.TypeVariable)`, and a word over any type at all is a
word. The premise does not survive.

**A second carve would be from the same predicate.** A list is a length together with the entries
below it, which is the predicate above with nothing changed. The two types would be isomorphic, and
the isomorphism would be definable — `mk_list o dest_word` — so nothing would be expressible about
one that is not expressible about the other.

**What it would cost is the seventeen facts.** `WORD_CONCAT`, `WORD_PREFIX`, `WORD_SUFFIX`,
`WORD_FACTOR`, `WORD_CONCAT_TALLY`, associativity, both units, extensionality and the rest are
theorems about `word('a)` and about no other type. A carrier carved beside it inherits none of
them, and every consumer holding one would need a coercion at each boundary, with `docs/adr/0008`
saying why two developments declaring one name do not combine.

**And what is genuinely absent is one principle, not a type.** `Concatenation.WORD_INDUCTION`
extends a word **on the right**: `P WORD_EMPTY /\ (!w x. P w ==> P (WORD_CONCAT w (WORD_SINGLETON x)))
==> !w. P w`. A definition by recursion on a sequence descends from the **left**, and that principle
did not exist. Neither did a structural recursion theorem.

## Decision

**The list interface is a link over `word` and declares no type.** `Listing` defines three
constants and no axiom:

- `LIST_CONS x w = WORD_CONCAT (WORD_SINGLETON x) w`
- `LIST_HEAD w = WORD_NTH w ZERO`
- `LIST_TAIL w = WORD_MAKE (PRE (WORD_LENGTH w)) (\i. COND (i < PRE (WORD_LENGTH w)) (WORD_NTH w (SUC i)) WORD_PAD)`

The empty list is `WORD_EMPTY` and gets **no second name**. A `LIST_NIL` defined equal to it would
be one term under two spellings with nothing keeping them in step, which is the defect this record
exists to refuse, committed at the one place it would look harmless.

What is derived on top: the two constructors' laws, their distinctness and injectivity,
`LIST_CASES`, and `LIST_INDUCT`, which is cons-induction.

## Consequences

A reader who has a word has a list. There is no coercion anywhere, `WORD_CONCAT` **is** append,
and every fact about concatenation is a fact about lists as written.

`LIST_HEAD` and `LIST_TAIL` are constants rather than terms built inside a proof, and that is a
cost this record should name rather than let a reader discover. `Concatenation` builds the front of
a word inside its own induction and says in writing that naming it would be a seventh constant
nothing had asked for. Something asks now: the structural recursion theorem's auxiliary function
recurses on a **number** and reads the head and the tail at each step, so it has to name them.

The distinctness and injectivity a carved free algebra gets from its tags are theorems here instead.
`LIST_CONS_NOT_EMPTY` is `SUC n` never being `ZERO` read through the lengths; `LIST_CONS_INJECTIVE`
is the head and the tail applied to one equation. Nothing is weaker for it.

**`LIST_TAIL` of the empty word is the empty word**, because `PRE ZERO` is `ZERO`. That is a total
function answering somewhere rather than a claim that the empty list has a tail, and it is the shape
`NUM_SUB`'s truncation already has one floor down. `LIST_HEAD` of it is `WORD_PAD`, about which
nothing is provable, and no statement here mentions a head without either a cons in it or the word's
positive length beside it.

## Alternatives rejected

**Carve `list('a)` with `defineType`, as the card asked.** Rejected on the measurement above: the
carrier would be isomorphic to one that exists and would inherit none of its facts. This was put to
the owner on 2026-09-23 with the measurement, chosen, and then reversed by him in the same session
in favour of the link; both directions are recorded because the first is what the card still says.

**Make `word` a case of the lists.** The card names this and asks that it be a decision rather than
a side effect. It is not what happened: `word` is unchanged, this link sits over it, and no existing
name moved.

**Wait for the general inductive-type constructor.** That is the parent card and is weeks of work.
Lists do not need it, which is the argument that split them off in the first place, and the same
`defineType` that carved `word` would have carved this had a carve been the answer.

## What is not here

**Nothing, since 2026-09-23, and this section is kept rather than deleted because what it said was
the reason `LIST_HEAD` and `LIST_TAIL` are constants here.** It named two things: the structural
recursion theorem, `!a g. ?f. f WORD_EMPTY = a /\ (!x w. f (LIST_CONS x w) = g x w (f w))`, and a
consumer development writing with lists what this repository today writes with the coding or with
`word`. Both landed the same day, by the route settled here — `Recursion.theorem` on `num` at result
type `word('a) -> 'b`, with `f w = F (WORD_LENGTH w) w`, and uniqueness by `LIST_INDUCT` — and
`docs/adr/0039` is the record of what the consumer decided, which is that its step discards the tail
and that it is a link of its own rather than three more facts here.

The section is updated instead of being left standing because a list of what is missing is the one
kind of list nothing goes red over: every other figure in this repository is pinned by a test that
fails when it moves, and a gap that has been filled fails nothing at all. That has happened here
once before, to the list `docs/adr/0013` keeps.
