# 0039. The fold discards the tail, and is a link of its own

- **Status:** accepted
- **Date:** 2026-09-23
- **Extends:** 0038

## Context

`docs/adr/0038` closes on a section called "What is not here", and it names two things: the
structural recursion theorem over lists, and a development that writes with lists what this
repository today writes with the arithmetic coding or with `word`. Both have landed, and this
record is what that section now points at.

`LIST_RECURSION` itself needed no decision: the route was settled in 0038 and is what was built.
`Recursion.theorem` on `num` at result type `word('a) -> 'b` gives an auxiliary
`F : num -> word('a) -> 'b`, the function is `\w. F (WORD_LENGTH w) w`, and the two equations come
out with no induction at all — the empty word's length is `ZERO` and a cons's is `SUC` of the
tail's, so each of `F`'s own equations fires once. What the theorem did need is
`LIST_RECURSION_UNIQUE` beside it, because this logic has no unique-existence quantifier, which is
the shape `Recursion.Statement` on `num` already has for the same reason.

Two things did need deciding, and they are the consumer's.

## Decision

**The fold's step is handed the letter and the value so far, and not the tail.** `LIST_FOLD g a`
satisfies `LIST_FOLD g a WORD_EMPTY = a` and `LIST_FOLD g a (LIST_CONS x w) = g x (LIST_FOLD g a w)`,
where `LIST_RECURSION` offers `g x w (f w)` and would allow the tail to be read.

**`Folding` is a link of its own and not more of `Listing`.** One constant, `LIST_FOLD`, no axiom,
no type.

## Why the step discards the tail

`LIST_FOLD_CONCAT` is the lemma this development exists for:

```
|- !g a u v. LIST_FOLD g a (WORD_CONCAT u v) = LIST_FOLD g (LIST_FOLD g a v) u
```

It is **false** for a step that can read the tail, and the refutation is in the step of its own
induction rather than in a corner case. At `LIST_CONS x u` the left-hand side reaches
`g x (WORD_CONCAT u v) (…)` and the right-hand side reaches `g x u (…)`: the same letter, the same
recursive value, and two different tails. A step that could see them would separate two things the
fold identifies, so the general recursion is the wrong instrument for a lemma of this shape and the
restriction is what makes it provable rather than a simplification of it.

What is given up is named here rather than left to be discovered: **a fold cannot express a measure
that weighs a letter by where it sits**, because the step never sees a position. That is exactly
what `Concatenation.Tally` is for, `S2_PHI` in `Collatz` is the consumer that wants it, and this
development does not supersede either. A caller wanting a paramorphism has `LIST_RECURSION`
directly, which is why that theorem is published in the general form and this constant is not.

## What the consumer measures, which is the point of having one

`Concatenation.Tally` is this repository's answer to "aggregate over the letters of a word", and it
is written the way `word` makes available:

```
NUM_SUM (\i. f i (WORD_NTH (WORD_CONCAT u v) i)) (WORD_LENGTH (WORD_CONCAT u v)) =
  NUM_SUM (\i. f i (WORD_NTH u i)) (WORD_LENGTH u) +
  NUM_SUM (\i. f (WORD_LENGTH u + i) (WORD_NTH v i)) (WORD_LENGTH v)
```

The `WORD_LENGTH u + i` is the correction every consumer of that lemma carries whether its own
aggregate cares about position or not. `LIST_FOLD_CONCAT` carries none, and that is a measurement
over the two statements rather than a remark about style: `FoldingSpec`'s last test walks the
constants each of the two names, and asserts that the tally names `NUM_ADD` and `WORD_LENGTH` and
the split names neither, with both naming `WORD_CONCAT` so that the comparison is between two
answers to one question.

## Why a link rather than three more facts in `Listing`

`LIST_FOLD` is a **constant**, and a constant declared into a theory the chain's end does not
extend is unreachable from everything above it, which is the rule `Chain.widest` exists to carry.
So the choice was between adding it to `Listing` and giving it a link, and it is a link for a
reason that is not the graph's: 0038's decision says `Listing` defines three constants, and an
interface that grew its own first consumer would make that sentence false in the record rather than
in the code. `ListingSpec` asserts the three as a difference against the theory below it and
`FoldingSpec` asserts the one, so the split is checked at both ends.

## Consequences

`Chain.widest` moves to `Folding`, which is the ninth entry in `ChainSpec`'s list of that field
moving and the first whose subject is the **consumer** of the link below it rather than a subject
of its own.

`LIST_RECURSION` is spent rather than held, and that is the half `ListingSpec` guards: an existence
theorem nobody uses is a capability, and a file that only asserts a function exists has not shown
that one can be got out. The test takes the witness at the step `\x. \w. \r. SUC r` and the start
`ZERO`, observes that `WORD_LENGTH` satisfies those two equations already — `WORD_EMPTY_LENGTH` is
the first and `LIST_CONS_LENGTH` is the second — and closes with `LIST_RECURSION_UNIQUE`. What
comes out is `select … = WORD_LENGTH`, owing nothing: the recursion produced a function this
repository defined long before it, which is the strongest available check on what the principle
produces.

## The existing consumer, since 2026-09-25

**`Collatz`'s two marker-free predicates are folds.** `S2_TAILFREE` and `S2_HEADFREE` say "no
letter is the marker", which is a conjunction along the list: they are `LIST_FOLD (\x r. ~(x = m)
/\ r) T` now, where they were a quantifier over positions. Two facts of `Folding` carry them.
`LIST_FOLD_EVERY` says a fold of conjunctions is the reading by position, and it is what lets the
predicates move without rewriting a line of the proofs built on them: `Collatz` derives the old
definitional equation from it and hands that to those proofs. `LIST_FOLD_EVERY_CONCAT` is the split
over a concatenation, from `LIST_FOLD_CONCAT` and one induction, and `S2_TAILFREE_CONCAT` and
`S2_HEADFREE_CONCAT` are it at the two markers. The positional proof they replace was 150 lines of
index arithmetic.

**What it cost, and who decided to pay it.** Every fact about a fold rests on eta, because
`LIST_RECURSION`, `LIST_INDUCT` and `LIST_CASES` turn a word back into `WORD_EMPTY`, and equality
between words is the carved type's extensionality. The three facts about the positions a cons has,
`LIST_CONS_LENGTH`, `LIST_CONS_NTH` and `LIST_HEAD_CONS`, are the only ones of the list layer that
do not. Measured over `Collatz`'s thirty-five facts on the day: six moved from two axioms to three,
the four splits over a concatenation and the two steps of the marker-free predicates, and the
other twenty-nine did not move. Eta is among the chain's nineteen already, so the trusted base did
not move either; what moved is what those six facts ask a reader to accept. The alternative was to
keep the definitions positional and use the lists only for the two splits, which would have moved
two facts and left the development not writing with lists at all. Angelo chose the first, with the
count in front of him, and `CollatzSpec` asserts the new partition by name.

**Why that development and not another, measured rather than chosen.** The verification named
seven candidates. Counting occurrences of a `WORD_` constant in each file on 2026-09-25: `Matrix`
0, `Reaching` 1, `Series` 3, so three of them do not use a word as a sequence at all. `Coding` and
`Provability` use the beta function because the embedded theory has to speak about sequences
inside PA, which `0013` decides and which no list of HOL can replace. `Rotation` (42) and `Forward`
(58) do use words, and both are links of the chain **below** `Listing`, so writing either with
lists would reorder the chain. `Collatz` (237) sits beside the chain and can be built over
`Folding`'s theory with nothing else moving. It was the only one reachable, and among its
predicates the two marker-free ones are the ones whose meaning is a fold rather than a sum weighted
by position, which `S2_PHI` is and which this record already says a fold cannot express.

## Alternatives rejected

**Publish the paramorphism as `LIST_FOLD` and state the split with a side condition.** The side
condition would be that `g` ignores its second argument, which is a statement about a function this
logic cannot make without quantifying over the tails, and every consumer would carry it. The
general form is already published as `LIST_RECURSION`; a caller who wants it takes it there.

**Put `LIST_FOLD` in `Listing`.** Rejected above: it would falsify 0038's own count, which is the
one place a reader goes to find out what a list costs here.

**Wait for a consumer somebody already has.** Rejected when the fold landed, and the rejection did
not survive the card's own criterion. The card that asked for this work named
`Coding.NUM_BETA_SEQUENCE`'s admissibility proofs as the most promising candidate, and that is a
rewrite of the Gödel layer rather than a consumer, which is still true. What was not true is that
a new development satisfied a criterion asking for an existing one: the verification of the card
said so, and on 2026-09-25 Angelo decided that the criterion stands and a migration is owed. The
next section is that migration.

## What is not here

**A fold that also sees the position**, which would be the tally's expressive equal. It is
`LIST_RECURSION` at a step carrying an index and is not written, because nothing has asked: the one
consumer that weighs by position is `S2_PHI`, and it is written with `NUM_SUM` and works.

**A bridge between the two sums**, `LIST_FOLD NUM_ADD ZERO w = NUM_SUM (WORD_NTH w) (WORD_LENGTH w)`,
which would say the structural aggregate and the indexed one agree. The bridge for conjunctions
exists, `LIST_FOLD_EVERY`, because a consumer needed it. `ListingSpec` proves the
instance of that shape which needs no reindexing lemma, `select … = WORD_LENGTH`; the general one
wants a reindexing law for `NUM_SUM` under a cons, and nothing needs it yet.
