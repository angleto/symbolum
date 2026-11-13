# 0078. The object logic instantiates at any substitutable term, not only at a closed one

- **Status:** accepted
- **Date:** 2026-11-12
- **Extends:** 0040

## Context

The logical axioms of the embedded theory (`Language.logicalSchemes`) had two schemes that put a
term where a variable stood: `NUM_LOGIC_SPECIALISE`, from `!v_i. p` to `p[t/i]`, and
`NUM_LOGIC_REPLACE`, from `t = u` to `p[t/i] ==> p[u/i]`. Both asked `NUM_CLOSED t` (and
`NUM_CLOSED u`), because `NUM_SUBST_FORM` is blind to capture and a closed term has nothing to
capture. The docstring of `Language.ClosedName` named the cost: the object system could not
instantiate a universal at a variable, so it was weaker than first-order logic, and Goedel's
argument was expected not to pay it because it substitutes numerals.

`docs/adr/0040`'s dated section of 2026-11-10 measured where it is paid. Completeness for bounded
formulas needs `x < S n ==> x < n \/ x = n` and the refutation of a false order inside PA, and
every derivation of either that was tried needs an axiom of PA at an open term:
`NUM_PA_ADD_SUC` at `numeral m` and `v_z`, `S x != 0` at `a + b`. Neither scheme reached those
instances, and the induction scheme substitutes only `0` and `S i`. That section left the choice
to a decision about the object logic, taken before completeness for bounded formulas is tried
again. Mycelium card `4102f131` carries the work.

## Decision

**Both schemes ask that the term be substitutable for the index in the formula**, which is the
textbook condition, in place of closedness. `NUM_FREE_FOR i t p` is a new recursion of
`Language`, defined with the same `defineShaped` construction as `NUM_FREE_FORM`:

- an equality accepts any term;
- a negation and an implication ask it of their parts;
- `!v_j. q` accepts `t` when `j = i`, or `i` is not free in `q`, or `j` does not occur in `t` and
  `q` accepts `t`.

A number that codes no formula answers `T`; every consumer asks `NUM_FORM p` beside it.

`NUM_FREE_FOR_CLOSED`, `!i t p. NUM_FORM p ==> NUM_CLOSED t ==> NUM_FREE_FOR i t p`, is proved
by course-of-values induction over the formula. It is how a derivation that substitutes a numeral
meets the new condition: `Deduction`'s rules of equality, and specialisation at a closed term,
keep their statements and discharge it from the closedness they already held.

**`Deduction` publishes the general rule and the axioms of PA at open terms**, which is what the
change is for:

- `NUM_PROV_SPECIALISE_FREE` is specialisation at any substitutable term. `NUM_PROV_SPECIALISE`,
  the closed form, is now derived from it, so the two are one derivation.
- `NUM_PROV_SUC_NOT_ZERO` is `S t != 0` at any term, and `NUM_PROV_SUC_INJ` is
  `S a = S b ==> a = b` at any two terms, `v_1` not in `a`. Both were private steps at closed terms
  inside the proof that distinct numerals are provably distinct, and that proof now cites them.
- `NUM_PROV_SYMM_FREE`, `NUM_PROV_TRANS_FREE` and `NUM_PROV_SUC_CONG_FREE` are symmetry,
  transitivity and the successor's congruence at open terms, over a hole index `k` the caller
  chooses, asking only that the terms standing in the hole not mention `k`. The closed rules of
  the same names without `_FREE` are now derived from them at `k = 0`. The congruences of sum and
  product and the denied forms keep their closed statements and their own derivations; they move
  when a derivation needs them open.
- `NUM_PROV_ADD_ZERO` and `NUM_PROV_MUL_ZERO` lose their closedness condition and hold at any
  term. `NUM_PROV_ADD_SUC` and `NUM_PROV_MUL_SUC` lose both, and keep one condition,
  `~(NUM_FREE_TERM 1 t)`, which is the axiom's inner index showing through: `t` goes under the
  binder for `v_1` and then `v_1` is replaced, so `t` must not mention it. A closed term meets it,
  which is how the numeral inductions above them discharge it.

## Consequences

- **`NUM_PROV` grows and does not shrink.** Every instance of the two schemes at a closed term is
  an instance at a substitutable one, so every code that was provable still is. What is new is
  provability at open instances. Any argument that reads `NUM_PROV` as the least set closed under
  the old schemes, a soundness proof by induction over derivations for instance, has one more
  case to cover. None exists in the repository today.
- **The object logic is now first-order logic with equality** as far as instantiation goes. The
  remaining restriction is the induction scheme, which substitutes `0` and `S i`; neither can be
  captured, so it needs no condition.
- **Soundness rests on the definition being right**, and a wrong clause is a proof of falsity in
  PA. `LanguageSpec` therefore attacks the definition at the case that matters: `v_1` is not
  substitutable for `v_0` in `!v_1. v_0 = v_1`, while `v_2` is, and so is `v_1` where `v_0` is
  not free.
- **Six statements change their printed form** in `docs/lemmas.md`, the two schemes and the four
  arithmetic facts. The facts added are the four clauses of `NUM_FREE_FOR`,
  `NUM_FREE_FOR_CLOSED`, and the `Deduction` facts named above and below.
- **`Language.substitutableIn` and `Language.freeInTerm` decide the conditions at concrete codes**,
  both ways, by rewriting with the clauses and closing the boolean residue with `Propositional`,
  and `Language.wellFormedIn` proves a concrete code a term or a formula by walking it. A caller
  at open terms discharges every condition above with one of the three.
  `docs/reading-register.md` gains a row for the new constant, unread like every other.
- **The condition on `NUM_PROV_ADD_SUC`, `NUM_PROV_MUL_SUC` and `NUM_PROV_SUC_INJ` is an artefact**, and it is kept
  rather than hidden. Removing it means instantiating the inner quantifier first, which needs
  the two quantifiers exchanged inside PA, and nothing that consumes these facts today is
  stopped by it.
- **PA's induction is a rule and has been used once.** `NUM_PROV_INDUCTION` detaches the scheme
  at a base and a step, and `NUM_PROV_ZERO_ADD` proves `!v_0. 0 + v_0 = v_0` with it: the first
  theorem here that PA proves and Robinson's Q does not, because its variable is on the left of
  the sum where Q's axioms put it on the right. Its step is replacement read as an implication,
  weakening and modus ponens under a hypothesis, then generalisation, every one at an open term.
  `DeductionSpec` asserts on the derivation that it rests on the induction rule.
  `NUM_PROV_SUC_ADD`, `!v_0 v_1. S v_0 + v_1 = S (v_0 + v_1)`, is the second, and the first whose
  base needs the open rules of equality; it is the lemma `x < S n` unfolds towards.
- **Nothing here proves the bounded case yet.** The next increment uses the open instances for
  `x < S n ==> x < n \/ x = n`, which needs an induction carried out inside PA.

## Alternatives rejected

- **Look for a derivation of the open instances without touching the logic.** `docs/adr/0040`
  records that none was found and that underivability was not proved. Before this decision,
  the session that took it read what the attempt would have to do: reasoning under `!v_z.`
  still needs `S x != 0` at `numeral m + v_z`, which is an instantiation at an open term under
  a binder. That is the same capability, reached by a longer road, so the search was not run.
- **Capture-avoiding substitution, renaming bound variables.** It is the other textbook route,
  and it makes the condition unnecessary. It changes `NUM_SUBST_FORM`, whose clauses every fact
  of `Language`, `Deduction` and `Truth` is stated over, and renaming needs a supply of fresh
  indices that the codes do not carry. The condition costs one recursion and one lemma.
- **Instantiation at variables only**, the weakest extension that reaches the cases measured.
  `numeral m + v_z` is not a variable, so it would not have reached `NUM_PA_ADD_SUC` at that
  term. It would also have needed its own capture condition, because a variable can be captured
  too.

## What was measured and what was not

Measured on 2026-11-12, on this change over `d47d4901`:

- **The nine `theories` suites that read the change ran together**: `LanguageSpec`,
  `DeductionSpec`, `LibrarySpec`, `RegisterSpec`, `TruthSpec`, `ProvabilitySpec`, `ChainSpec`,
  `SyntaxSpec` and `ChainCoverageSpec`, after regenerating `docs/lemmas.md` and
  `docs/reading-register.md`. 128 of 131 tests passed, and the three that did not were the
  library's counts. Fourteen new names and eleven of them with two or more leading quantifiers of
  `num` were derived from the diff of `docs/lemmas.md` before the pins were read, and the pins
  moved by exactly that. `LibrarySpec`, `LanguageSpec` and `DeductionSpec` then ran again: 78 of 78.
- **The capture attack fires.** `tools/verify/perturb-substitutable.sh` writes a `NUM_FREE_FOR`
  whose quantifier clause forgets the binder, consistently in the step, the statement and the
  closedness proof, so that the chain still builds. Run on 2026-11-12: the
  control passed 38 of 38 tests of `LanguageSpec`, and the perturbed run failed exactly one, the
  capture test, at `v_1` for `v_0` in `!v_1. v_0 = v_1`, with the other 37 green. Its first
  version left out a line of `Deduction` that builds the forgotten conjunct, and that run aborted
  the suite because the chain no longer built: a red, and not the attack. The harness says so.
- **The open instances reach what `docs/adr/0040` said they were needed for**, measured by a probe
  outside the repository: PA refutes `numeral m + S v_2 = numeral n` for each of five pairs with
  `m >= n` at concrete numerals, with no hypothesis and on the chain's own axioms, from
  `NUM_PROV_ADD_SUC`, `NUM_PROV_SUC_ADD`, `NUM_PROV_SUC_INJ`, `NUM_PROV_SUC_NOT_ZERO`,
  `NUM_PROV_SPECIALISE_FREE` and replacement. That is a probe and not an assertion; the fact in
  general form is the next increment's.
- **What reads the library from outside `theories` ran too**: `ClassicalSpec` and `RewriteSpec` in
  `logic`, `EssaySpec`, and in `tactics` `ProposeSpec`, `RediscoverySpec` and the eight suites
  that read the documents. All green but the weakenings `Propose` makes, one per antecedent of
  every fact: twenty-four more were predicted before the run and came back, twenty-eight on the
  new facts less the four `NUM_CLOSED` antecedents dropped. Of the twenty-four, two landed in
  `open` and twenty-two in `unreadable`, which were read off the run and not predicted, and two
  of them name a constant of the naturals.

Not measured: `tools/sbt test` over every module, the coverage gate, and the suites of
`published` and `dist`. They run at the integration gate over every ready branch rather than
once per branch. Nothing proves `NUM_FREE_FOR` right against a semantics, since the repository
has no soundness proof for the object logic; what holds it is the case analysis above and the
attack on the one clause that can capture.
