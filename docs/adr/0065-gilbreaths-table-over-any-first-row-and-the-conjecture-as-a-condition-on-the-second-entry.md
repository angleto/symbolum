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

## 2026-11-11: the bound, Chase's Lemma 3.2 and the counted ladder

Card `538f5094`. Six facts more, over the same tables and published the same way, with no
hypotheses beyond the table's equation and resting on choice, eta and infinity like the rest. Two
abbreviations are written out in every statement rather than declared, for the reason the first
alternative above gives: `M k n D` is "positions 0 to `n` of row `k` are at most `D`",
`!i. i <= n ==> d k i <= D`; and `B k n D m` is "every run of `m` consecutive entries in `{0, D}`
inside those positions is all zeros", the statement in which Chase's "the longest block of entries
in `{0, D}` containing a `D` has length `L`" is the case `m = L + 1`:

- `GILBREATH_BELOW`: `M k (SUC n) D ==> M (SUC k) n D`, since `|x - y| <= D` when `x, y <= D`;
- `GILBREATH_BELOW_ROWS`: `M k (n + j) D ==> M (k + j) n D`, the same over `j` rows;
- `GILBREATH_SHRINK`: `M k (SUC n) D /\ B k (SUC n) D (SUC m) ==> B (SUC k) n D m`, Chase's
  inductive step: along a run of row `k + 1` in `{0, D}`, the entries above all share the
  membership of `{0, D}` of the first one, so either they are all in it and all zero, or no
  difference can be `D`;
- `GILBREATH_DROP`: `M k n D /\ B k n D 1 ==> M k n (NUM_SUB D 1)`;
- `GILBREATH_RUNG`: `M k (n + L) D /\ B k (n + L) D (SUC L) ==> M (k + L) n (NUM_SUB D 1)`, which is
  Lemma 3.2 of Chase, *A random analogue of Gilbreath's conjecture*, in this window form;
- `GILBREATH_LADDER`: `c` rungs, the bound lowered by one per rung, row `r (SUC s) = r s + l s`,
  window `w s = w (SUC s) + l s` and the runs of stage `s` bounded at `NUM_SUB D s` by
  `SUC (l s)`; when the bound left after `c` rungs is at most 1, the entry at row `r c + w c`,
  position 0, is at most 1.

**What this replaces.** The paper proof in Mycelium note 917b3939, section 5.2, leaned on two
published lemmas, and both are now theorems here. Lemma 3.2 of Chase, *A random analogue of
Gilbreath's conjecture* (arXiv 2005.00530 v3), is `GILBREATH_RUNG`: its statement, read in the TeX
source on 2026-11-11, is that for non-negative integers with maximum `d` whose longest
`{0, d}`-block containing a `d` has length `L` at most one less than their number, `L` rows of
differences bring the maximum to at most `d - 1`; its proof is the induction `GILBREATH_SHRINK`
makes precise, and the step it calls easy to see is the membership argument above. The
inheritance lemma of Chase, Hunter and Tao, *Gilbreath's conjecture: a Cramér random model and a
deterministic analysis* (arXiv 2607.08712 v1), part (ii), that a block valued in `{0, ..., d}`
passes that to every block below it, is `GILBREATH_BELOW_ROWS`; at `d = 1` it is the heredity of
`{0, 1}` the ladder ends on. The note numbers that lemma 3.7; the TeX labels it `succ-lemma`,
and the number was not checked against a compiled copy.

**What the statements were attacked with before they were proved.** A random check in Python, run
in `scratch/` with seed 538 and so not kept here, over tables of absolute differences of 2 to 30
entries and bounds 0 to 6. These figures are that run's, a photograph: no failure in
271 901 cases of `GILBREATH_RUNG`, 331 901 of `GILBREATH_SHRINK` and 16 406 ladders, and three
controls that must fail and did: the rung read one row too early, `M (k + L - 1) (n + 1)`, false in
20 734 of 256 566; `GILBREATH_SHRINK` without the window bound, false in 17 669 of 299 334; the
ladder stopped at a bound of 2, false in 1279 of 18 356. A rung with `L` runs in place of
`SUC L` is not a control: it is a stronger hypothesis and a weaker true statement.
`GilbreathSpec` reads the published `GILBREATH_RUNG` and `GILBREATH_LADDER` with an evaluator and
compares their hypotheses with the informal ones written without the statements, and
`tools/verify/perturb-gilbreath-ladder.sh` weakens three hypotheses and shows each proof stop.

**Two choices a reader meets.** The ladder's functions are `r`, `l` and `w` rather than the card's
`t`, `L` and `n`, because `B` binds `t` and `j` and a row written `t s` inside it would be
captured. And `ComplexKit.induct` takes the step's variable when a caller names it: left to
`Logic.stripForall` it is named by type, `n` for a number whenever the body leaves `n` free, which
handed `GILBREATH_BELOW_ROWS` its own window as the induction variable and was refused when the
window was generalised.

**What is still not here** is unchanged by this: the primes, and the conjecture. The ladder says
that a first row whose blocks shrink as its hypothesis asks gives a 1 or a 0 where it lands; that
the primes' table satisfies such a hypothesis at every depth is not proved here.
