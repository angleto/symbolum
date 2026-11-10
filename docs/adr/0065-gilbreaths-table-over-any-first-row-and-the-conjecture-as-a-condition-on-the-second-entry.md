# 0065. Gilbreath's table over any first row, and the conjecture as a condition on the second entry

- **Status:** accepted
- **Date:** 2026-10-24

## Context

Mycelium card `ddd1ba96` follows note 917b3939, whose section 5.2 measures why Gilbreath's
conjecture holds as far as anyone has computed: the table of absolute differences of the primes
starts every row after the first with 1, and the note locates the reason in a head of 0s and 2s
behind that 1, which a large value arriving from the right is absorbed into when the head keeps
producing 2s. The card asks for the part of that account that is a theorem, in the kernel, so that
what is proved and what is measured are separated where a reader can see the line.

Two facts about the library decide the form. It has no enumeration of the primes, so nothing here
can be about the primes' own table. And it has no absolute value on the naturals, while the
truncated subtraction `NUM_SUB` is in `Peano` with the lemmas a proof needs.

## Decision

**Nothing is declared, as in `0062` and `0064`.** Every statement is over a table
`d : num -> num -> num` satisfying one equation,

    d (SUC k) i = NUM_SUB (d k (i + 1)) (d k i) + NUM_SUB (d k i) (d k (i + 1))

which is `|d k (i + 1) - d k i|` written with the truncated subtraction, one of the two terms being
0. `GILBREATH_EXISTS` gives such a table for every first row, by the recursion theorem at the type
of a row, so no statement is vacuous.

**What is published, six facts**, each compared with its written statement in `Complex.construct`,
with no hypotheses and resting on no axiom beyond the three of the chain:

- `GILBREATH_EXISTS`: a table exists for every first row;
- `GILBREATH_FRONT`: a row starting with 1 passes a 1 on exactly when its entry at position 1 is 0
  or 2;
- `GILBREATH_EQUIVALENT`: when the second row starts with 1, every row after the first starts with
  1 exactly when position 1 holds 0 or 2 in every row after the first;
- `GILBREATH_EVEN`: if every entry from position 1 on is even in a row, so it is in the next. Over
  the primes every gap after the first is even, so from the second row on the condition of
  `GILBREATH_EQUIVALENT` is "position 1 is at most 2";
- `GILBREATH_HEAD`: a row starting with 1 and followed by `n + 1` entries in `{0, 2}` gives a next
  row starting with 1 and followed by `n` such entries. On `{0, 2}` the absolute difference is the
  sum modulo 4, which is why the head is closed under the step;
- `GILBREATH_WINDOW`: a head of `n` guarantees the 1 for the next `n` rows.

**The conjecture is not among them, and the line between the two is stated.** What is proved is
that the 1 survives exactly as long as a head survives; whether a head survives forever over the
primes is the conjecture, and the measurements of note 917b3939 section 5.2 are about that question
and remain measurements. They are not copied here: the note holds them with the scripts that
reproduce them.

## Alternatives rejected

**An absolute value on the naturals as a constant.** It would be a declaration, a row in
`docs/reading-register.md`, and lemmas reducing it to `NUM_SUB` anyway; the sum of the two
truncated subtractions is the definition written out where it is used.

**The table over the integers.** The entries are naturals and the step never leaves them, and the
integers would put an embedding between every statement and the table it is about.

**A head stated as a list or a finite set.** "Positions `1 .. n` hold 0 or 2" is a bounded
quantifier over the naturals and needs nothing the library lacks.

## Consequences

`Complex` publishes six more facts and declares nothing. `Gilbreath` sits beside `RuleThirty` for
that file's reason, and the steps over the naturals the two share, which `RuleThirty` had written
for itself, are now `NumberSteps`, which both instantiate. `GilbreathSpec` checks that the
existence theorem exhibits exactly the equation the other five assume, and reads the equation off
the published statement to compare it with the table of the first 400 primes.
