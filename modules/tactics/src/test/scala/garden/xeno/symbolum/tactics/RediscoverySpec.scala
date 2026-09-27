package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Does the discovery loop find the things we already know?
 *
 * The card that asked for a generator calls this the first measurement and the test bench for
 * everything else, for a reason that does not need defending: a loop that cannot rediscover what is
 * already in the library will not discover what is not. Until this file the figure did not exist.
 * `Propose`'s own docstring says what the measurement needs, and says it about the operator
 * substitution in particular, which is the one source here that can produce a **different** lemma
 * rather than a weaker form of the one it came from.
 *
 * == What is asserted, and why it is not a benchmark row ==
 *
 * The counts below are calibration. They say that the loop reproduces some of the lemmas its
 * rediscovering source can reach, `propose.mutable`, that it reaches none at all by the other
 * source over every weakening it tries, and that everything it reaches it proves. None of that is
 * evidence that anything was discovered, and `docs/evaluation.md` says at length why a figure like
 * this is not a benchmark. What it is: the number that has to exist before any claim about the loop
 * is anything but anecdote.
 */
class RediscoverySpec extends AnyFlatSpec with Matchers {

  private val propose = Propose.standard
  private val recoveries = propose.recoveries
  private lazy val readings = recoveries.flatMap(recovery => propose.novelty.of(recovery.proposal.claim).toOption)

  "The generator" should "reproduce lemmas the library holds, from lemmas it does not" in {
    // 16 pairs reaching 12 distinct lemmas, measured on the tree of 2026-09-12 with 233 entries.
    //
    // The pairs are the ring's two commutative-monoid symmetries and the order's strict/non-strict
    // families, and they are worth naming because the naming is the whole evidence that the loop is
    // doing what it says: `ADD_SYM` with `+` swapped for `*` is `MUL_SYM`, and a reader can check
    // that sentence without running anything.
    //
    // 16 and not 19, which is what the first run of this printed. `Order` re-exports the facts of
    // `Positivity`, so a name held by two developments makes the same mutation twice and finds the
    // same target twice; three of those six extra rows were one sentence printed twice. The pair is
    // the object, not the row, so the result is distinct on it. That duplication is still in
    // `proposals` itself, where it inflates the two counts `ProposeSpec` pins; it is left there and
    // said here rather than repaired in passing, because those counts have a history of moving for
    // reasons nobody derived and this is not the commit to add another.
    // **18 and 14 since 2026-09-18, and the two that arrived are a matched pair rather than two
    // additions.** `Order` gained `LE_MUL_BOTH`, and the generator's own mutation travels between it
    // and `LT_MUL_BOTH` in both directions: `real_le` for `real_lt` rediscovers the strict one from
    // the non-strict and back again. So a lemma added to close a gap in the order added exactly the
    // two rows this loop exists to produce, and it was the loop that said so rather than the person
    // who added it.
    recoveries.size shouldBe 18
    recoveries.map(_.reached).distinct.size shouldBe 14

    val pairs = recoveries.map(r => (r.proposal.from, r.proposal.change, r.reached)).toSet
    pairs should contain(("ADD_SYM", "real_add became real_mul", "MUL_SYM"))
    pairs should contain(("MUL_SYM", "real_mul became real_add", "ADD_SYM"))
    pairs should contain(("ADD_ASSOC", "real_add became real_mul", "MUL_ASSOC"))
    pairs should contain(("LE_FROM_ZERO", "real_le became real_lt", "LT_FROM_ZERO"))
  }

  it should "reach none of them by dropping a hypothesis, which the file predicted and nobody had measured" in {
    // `Propose.substitutions` says in prose that dropping a hypothesis makes a lemma weaker, and
    // that a weaker form of something already held is not a lemma anybody was missing. That was an
    // argument. This is the measurement: every weakening the generator makes, the count pinned at
    // the end of this test, and not one of them states a lemma the library holds.
    //
    // It is the cleanest possible confirmation and it is also a limit, which is why it is asserted
    // rather than left as a satisfying zero. The loop has exactly **one** source that can
    // rediscover, so every figure in this file is a figure about the operator substitution and the
    // swaps in `Propose.Swaps`. A second such source would move all of them, and the day one
    // arrives this assertion is what says so.
    recoveries.count(_.proposal.source == Propose.Source.Weakened) shouldBe 0
    // 121 since the classical facts joined the library, derived at `ProposeSpec`: four of the nine
    // that arrived carry an antecedent. None of the four reaches a rediscovery, so the zero below
    // is over a larger denominator than it was and says the same thing more strongly.
    // 122 with `NUM_SUM_CONGRUENCE_BELOW`, which is the same one antecedent `ProposeSpec` counts,
    // and it reaches no rediscovery either: the library holds no unconditional congruence for a
    // partial sum at any type, which is the whole reason the bounded one was stated.
    // 123 with `Rotation`, the same one antecedent `ProposeSpec` counts, and it reaches no
    // rediscovery either: the library holds no unconditional law for an entry of a rotated word,
    // and could not, since the unguarded statement is false above the length.
    // 127 with the floor and the ceiling, and the delta is DERIVED: four lemmas carrying one
    // antecedent each, the same `0 <= x`. None of the four reaches a rediscovery either, and it
    // could not: dropping the sign condition leaves a claim about `NUM_FLOOR` at every real, which
    // is false and which the library holds nothing resembling.
    // 124 since the generator stopped proposing the same claim twice: `Order` re-exports the facts
    // of `Positivity`, and the three rows that went are `ADD_POSITIVE` twice and
    // `POSITIVE_NOT_ZERO` once, which is one row per antecedent of a name held by two developments.
    // None of the three reached a rediscovery, so the zero below is unmoved for the right reason.
    // 130 since `Magnitude` joined the chain on 2026-09-13, and the delta is DERIVED and then
    // confirmed: five of its seventeen lemmas carry a hypothesis and six between them, since
    // `MAX_LEAST` has two antecedents. None of the six reaches a rediscovery either, so the zero
    // below is unmoved again, and for the same reason the floor and the ceiling did not move it:
    // dropping the sign condition from `SGN_ZERO` leaves a claim the library holds nothing
    // resembling.
    // 132 since `Coding`, whose two hypothesis-bearing facts contribute one weakening each. Neither
    // reaches a rediscovery, so the zero below is unmoved a third time, and this time the reason is
    // sharper than "nothing resembling": `NUM_FACT` is a constant the library holds four facts
    // about and nothing else mentions, so a claim built from it has nowhere to land by construction.
    // 135 with Gauss's three, none of which reaches a rediscovery either: a claim built from
    // `NUM_GCD` with one of its premises gone is not a claim the library holds anything resembling,
    // which is the fourth time this zero has stayed put for the same reason.
    // 136 with `NUM_DIVIDES_ONE`. It reaches no rediscovery either, and here the reason is not
    // that nothing resembles it: `!d. d = SUC ZERO` is a claim the model refutes, so what stops it
    // is that it is false rather than that it is unreachable.
    // 137 with the moduli's coprimality. It reaches no rediscovery: dropping its premise leaves a
    // claim about `NUM_GCD` of two shifted multiples, and the library holds nothing of that shape.
    // 139 with the congruence that descends to a divisor, whose two weakenings reach no
    // rediscovery: the library holds nothing that resembles a congruence with its modulus loose.
    // 143 with the four, none of which reaches a rediscovery.
    // 150 with the Chinese remainder theorem's seven, none of which reaches one either, and the
    // zero here has now stayed put across every addition this file has recorded since `Modular`.
    // That is the assertion working rather than nothing happening: a weakening rediscovers a lemma
    // only where the library already holds the weaker claim, and a development building upwards
    // does not produce those.
    // 153 with the beta function's three, none of which reaches a rediscovery either.
    // 157 with the arithmetisation's four, none of which reaches a rediscovery either.
    // 158 with the constructor's injectivity, which reaches no rediscovery either.
    // 163 with the term predicate's five, none of which reaches a rediscovery either.
    // 169 with the formula predicate's six, none of which reaches a rediscovery either.
    // 170 with the numerals' injectivity, which reaches no rediscovery either.
    // 171 with course-of-values induction, which reaches no rediscovery either.
    // 173 with the two the well-formedness lemma brings, neither reaching a rediscovery.
    // 175 with the formula half of the well-formedness lemma.
    // 176 with the axioms of PA, whose one weakening reaches no rediscovery either. Eight lemmas
    // and one proposal, because seven of the eight carry no hypothesis to drop.
    // 177 with every axiom being a formula, which reaches no rediscovery either.
    // 198 with the logical axioms' twenty-one, none of which reaches a rediscovery either.
    // 200 with the proof predicate's two, neither of which reaches a rediscovery either.
    // 204 with the shift lemma's three and the monotonicity's one, none reaching a rediscovery.
    // 205 with the one the two order facts produce between them.
    // 208 with the closure under modus ponens and the cancellation it needed, three between them,
    // none of which reaches a rediscovery either.
    // 209 with the closure under generalisation's one, which reaches no rediscovery either.
    // 215 with `Deduction`'s two, whose six hypotheses between them reach no rediscovery either.
    // 216 with Euclid's theorem and its prime-factor lemma. ONE and not two: Euclid carries no
    // hypothesis at all, so there is nothing in it for this source to drop.
    // 221 with the three multiplicative lemmas, whose five hypotheses reach no rediscovery either.
    // 222 with the irrationality's one hypothesis; two being prime carries none.
    // 234 with the deduction theorem's three rules, whose twelve hypotheses between them reach no
    // rediscovery either.
    // 237 with the deduction theorem's three; its two definitions are equations and carry none.
    // 244 with the first analysis, and the seven are DERIVED before they were measured: four of the
    // twelve lemmas that landed carry an arrow at all, and they carry two, two, one and two.
    // `LE_BELOW_EVERY_POSITIVE` has `0 <= x` and the epsilon condition, `CONVERGES_UNIQUE` has a
    // convergence apiece, `LIM_OF_CONVERGES` has one, and `CONVERGES_EVENTUALLY` has the agreement
    // and the convergence. The other eight carry none: `exp 0 = 1` and its five siblings are
    // equations, and so are the two hyperbolic identities.
    // 248 with `NUM_PROV_SPECIALISE`'s four, which is the count of its antecedents and was
    // derived before it was measured.
    // 250 with the idleness of the substitution's two.
    // 256 with the monotone convergence theorem and what it needed. Six, DERIVED before the run:
    // `NOT_FORALL` carries one arrow, each of the two negated comparisons in `Order` carries one,
    // `MONOTONE_LE` carries one, and `MONOTONE_CONVERGES` carries two. The inner `NUM_LE m n ==>`
    // of `MONOTONE_LE` is not among them and that is the peeling rule rather than an oversight: it
    // sits under `!m n`, and only the antecedents in front of the leading quantifiers are peeled.
    // 274 with the three equality rules' eighteen.
    // 285 with the eleven the object theory's addition brought.
    // 289 with the four from the two recovered lemmas.
    // 299 with the concatenation's ten, none of which reaches a rediscovery either, and the
    // reason is the one the buckets give: eight are about `word` and unreadable to every
    // procedure here, and the two that are readable leave `!p m n. m < n` and `!m n. n <= m`,
    // which are false rather than lemmas somebody forgot to state.
    // 306 with the seven of `Inductive` and `Reaching`; `ProposeSpec`'s entry on the same figure
    // carries the per-lemma derivation and the count it was first wrong by.
    // 309 with the comparison test, which is curried three times and therefore carries three.
    // 312 with the algebra of limits' two: `CONVERGES_ADD` is curried twice and `CONVERGES_NEG`
    // once, so three, derived before the run by the peeling rule this file states and measured
    // identical. The sum's two leading arrows are the two convergences it takes; the negation's
    // one is the single convergence it takes.
    // 323 with the six derived connectives' eleven; `ProposeSpec`'s entry on the same figure
    // carries the per-lemma derivation. None of the eleven reaches a rediscovery either, for the
    // reason the concatenation entry gives: a weakening of a well-formedness rule is a claim that
    // every code of some shape is a formula, which is false rather than a lemma somebody forgot.
    // 327 with the right forward closure's four. **FOUR, derived before the run and then
    // measured**, by the peeling rule these entries state, and the derivation is one per lemma
    // because not one of them is curried: `WORD_RFC_RIGHT` takes `R l r`; `WORD_RFC_INSIDE` and
    // `WORD_RFC_EXTEND` each take a single conjunction, of two conjuncts and of four, under one
    // arrow; `WORD_RFC_INDUCT` takes the three closure hypotheses as one conjunction. A conjunct
    // is not an antecedent here and that is the whole of the arithmetic: read as conjuncts the
    // four lemmas would carry ten.
    //
    // `WORD_RFC_INDUCT` is the case the `MONOTONE_LE` caveat is about and it does not bite: its
    // consequent is `!w. WORD_RFC R w ==> S w`, an arrow under a quantifier, which the peeling
    // stops at rather than counting. Counting it would propose dropping the membership from an
    // induction principle, which is not a weaker lemma somebody forgot but the statement that
    // every word satisfies the carrier.
    //
    // 331 with the two bounds on a limit, `CONVERGES_LE` and `CONVERGES_GE`. **FOUR, derived
    // before the run and then measured**, by the peeling rule these entries state: each of the two
    // is curried twice, the convergence and the eventual bound being two arrows in front, so two
    // apiece. The `MONOTONE_LE` caveat does not bite on either, because what follows the second
    // arrow is a comparison and not an arrow under a quantifier.
    //
    // 342, and **eleven of the fifteen since the last line above are not this session's**. The
    // factorisation merge `627ceec` added five lemmas and did not move this figure, so the tree it
    // landed on was red here; the eleven are derivable from their statements by the peeling rule
    // these entries state and were derived after the failure rather than before it: one each for
    // `NUM_PROD_CONG` and `NUM_FACTORISATION`, two each for `NUM_PRIME_DIVIDES_PROD` and
    // `NUM_PRIME_PROD_ONE`, and five for `NUM_FACTORISATION_UNIQUE`, whose four guarded
    // hypotheses and one equation are five arrows in front. The remaining four are the two limit
    // bounds', two apiece.
    //
    // 343 with `WORD_LENGTH_ZERO`'s one, and this line is the tip plus this branch's delta rather
    // than a total carried forward. It is one arrow over a single equation, so it offers one
    // weakening: `!w. w = WORD_EMPTY`. Every other addend here belongs to work already on the tip
    // and is taken from it wholesale.
    // 347 with `LE_MUL_BOTH`'s two and `INV_ANTITONE`'s two, which is one weakening per hypothesis
    // and each of those lemmas has two. Tip plus this change's delta, as the line above says.
    // 349 with `NUM_ADD_LE_BOTH`'s one and `NUM_SUM_MONOTONE_BELOW`'s one, and this line went red
    // before it was moved: `45416c8` added those two lemmas to `Peano` and left this figure at
    // 347, which is the second time the comment above has had to record that. A change that moves
    // a figure a test pins moves the pin in the same commit, whatever module that test lives in,
    // and running the suite of the module that changed is not evidence about the figure
    // elsewhere. **Which lemmas moved it was measured and not assumed**: `docs/lemmas.md` is
    // generated from the library, so `git show 9734bf7:docs/lemmas.md` against the current one,
    // diffed by name, says exactly two entries arrived since the commit that wrote 347 and names
    // them, with none removed and none restated. The card that opened this guessed `Collatz.scala`
    // instead, and that is refuted by the same diff: `Collatz` sits beside the chain, so
    // `Library.of` never sees it and it cannot move this figure whatever it adds.
    //
    // One apiece rather than two, and the arithmetic is the peeling rule these entries state.
    // `NUM_ADD_LE_BOTH` carries `x <= y /\ z <= u` as ONE antecedent under one arrow, which is
    // the same reading the `WORD_RFC` entry above gives: a conjunct is not an antecedent here.
    // `NUM_SUM_MONOTONE_BELOW` carries `!u. u < z ==> x u <= y u`, which is one antecedent too,
    // and what is inside it is an arrow under a quantifier that `Propose.peel` never reaches
    // because it stops at the first thing that is not an implication.
    // 362 with the four facts that put PA's multiplication to work and prove it on numerals, and
    // the thirteen are derived from the statements rather than read off the failure: seven for
    // `NUM_PROV_ADD_CONG`, whose three terms each owe a `NUM_TERM` and a `NUM_CLOSED` and which
    // then asks for one provable equation; four for `NUM_PROV_MUL_SUC` at two terms; two for
    // `NUM_PROV_MUL_ZERO` at one; and **none** for `NUM_PROV_NUMERAL_MUL`, which carries no
    // hypothesis at all and is the point of it. The gate said 362 and the peeling rule says
    // 349 + 13, which is the check this comment exists to make possible.
    // 379 with the integers' seventeen, 2026-09-18, and the seventeen were **predicted before
    // the run and are what came back**: of the forty-one facts `Integer` publishes, twelve carry
    // an antecedent, and counting arrows the way `Propose.peel` does gives one each for
    // `INT_SAME_SYM`, `INT_DIVIDES_INTRO`, `INT_DIVIDES_ELIM`, `INT_DIVIDES_MUL`,
    // `INT_DIVIDES_NEG`, `INT_ZERO_DIVIDES` and `INT_ADD_LE_MONOTONE`, and two each for
    // `INT_SAME_TRANS`, `INT_DIVIDES_TRANS`, `INT_DIVIDES_LINEAR`, `INT_LE_TRANS` and
    // `INT_LE_ANTISYM`. Twelve of the seventeen were predicted at twelve before the order was
    // written, and the order added the other five. Tip plus this branch's delta, as the
    // paragraph above insists: never a total carried forward against an earlier base.
    // 380 with the bridge into the reals, the same day, and the **one** was derived before
    // the run: of `Inclusion`'s eight facts exactly one carries an antecedent, which is
    // `INT_REAL_INJECTIVE`, and counting arrows the way `Propose.peel` does gives it one.
    // The other seven are equations with nothing owed. Tip plus this branch's delta.
    // 381 with the order map, the same day, and the **one** was derived before the run: of the
    // pair that landed, `Peano.NUM_REAL_LE_BACK` carries one antecedent under one arrow and
    // `Inclusion.INT_REAL_LE` is an equation between propositions with nothing owed. The same
    // figure is pinned in `ProposeSpec` with the same derivation, which is the two places the
    // entry above calls out. Tip plus this branch's delta.
    // 383 with the three facts about `abs`, 2026-09-20, and the **two** were derived before the
    // run: of `ABS_OF_NONNEG`, `ABS_OF_NONPOS` and `ABS_MUL`, the first two carry one antecedent
    // each, the sign of the argument, and the third is an equation with nothing owed. Tip plus
    // this branch's delta.
    // 384 with `INT_MUL_CANCEL_NUM`, 2026-09-20, and the **one** was derived before the run: the
    // lemma carries a single antecedent, the equation between the two products, so `Propose.peel`
    // counting arrows gives it one. Tip plus this branch's delta.
    // 386 with `CONVERGES_MUL`, 2026-09-20, and the **two** were derived before the run: the
    // limit of a product carries two antecedents, one convergence per sequence, each under its own
    // arrow, so `Propose.peel` gives it two. Tip plus this branch's delta.
    // 387 with the Cauchy product's finite half, 2026-09-20, and the **one** was derived before the
    // run: of the six facts that landed, exactly one carries an antecedent, which is
    // `Peano.NUM_SUC_SUB` and its bound `n <= m`. The other five are equations owing nothing, and
    // `NUM_SUC_SUB_SELF` is that lemma with its bound already spent. Tip plus this branch's delta.
    // 389 with the two facts the binomial theorem wants in front of it, 2026-09-21, and the
    // **two** were derived before the run: `NUM_CHOOSE_ABOVE` carries the bound `n < k` and
    // `NUM_LE_OF_LT_SUC` carries `i < SUC n`, one antecedent each under one arrow. Tip plus this
    // branch's delta.
    // 390 with the absolute convergence theorem, 2026-09-21, and the **one** was derived before
    // the run: it carries a single antecedent, the convergence of the absolute series, under one
    // arrow. Tip plus this branch's delta.
    // 393 with the two tail facts, 2026-09-21, and the **three** were derived before the run:
    // `SUM_BELOW_LIMIT` carries two antecedents, the non-negativity of the terms and the
    // convergence, and `CONVERGES_TAIL` carries one. Tip plus this branch's delta.
    // 394 with the bounded monotone, 2026-09-21, and the **one** was derived before the run: it
    // carries a single antecedent, the comparison below the bound. Tip plus this branch's delta.
    // 400 with the sandwich and what it wanted in front of it, 2026-09-21, and the **six** were
    // derived before the run: one antecedent each on `SUM_GROWS` and `Peano.NUM_LE_DOUBLE_SUB`,
    // two each on the sandwich's two halves. Tip plus this branch's delta.
    // 404 with the Cauchy product, 2026-09-21, and the **four** were derived before the run:
    // it carries four antecedents, two non-negativities and two convergences, one weakening
    // each. Tip plus this branch's delta.
    // 411 with the general Cauchy product and the three lemmas under it, 2026-09-21, and the
    // **seven** were derived before the run and met: four antecedents on the product, two on
    // the squeeze, one on the stretch, and `SUM_ABS` carries none at all. Tip plus this
    // branch's delta.
    // 412 with `ABS_POWER_LE`, which carries one antecedent.
    // 414: one antecedent each on the halving and the geometric tail, none on the convergence.
    // 418 with `MUL_INV_COMBINE`'s four antecedents; the other two carry none.
    // 420 with the list interface, 2026-09-23, and the **two** were derived before the run:
    // `LIST_CONS_INJECTIVE` and `LIST_INDUCT` each carry one antecedent, and the other six
    // facts of that development carry none.
    // 421 with the structural recursion theorem and the fold, 2026-09-23. The **one** is
    // `LIST_RECURSION_UNIQUE`'s single antecedent, the two developments' other four facts carrying
    // none: `LIST_RECURSION` is an existential owing nothing and the three fold facts are bare
    // equations. Read off the run and reconciled against that reading rather than predicted before
    // it, which is the difference this file's rows are careful to record.
    // 425 with the square root, 2026-09-24: `SQRT_EXISTS`, `SQRT`, `SQRT_UNIQUE` and
    // `SQRT_SQUARE` carry one antecedent each and the two values carry none. Reconciled against
    // that reading after the run rather than predicted before it.
    // 426 with `SQRT_TWO_IRRATIONAL`'s one antecedent, `0 < q`, the same day.
    // 427 with the trigonometric identity's five facts, the same day, and the **one** was derived
    // before the run: `CONVERGES_SHIFT` carries one antecedent, and `SUM_EVEN_ODD`, the two
    // absolute convergences and `SIN_COS_SQUARED` carry none.
    // 431 with continuity, the same day, derived before the run: `INTERMEDIATE_VALUE` carries four
    // antecedents and the two facts about particular functions carry none.
    // 441 with the logarithm, the same day, derived before the run: ten antecedents over twelve
    // facts, two each on `EXP_SMALL_ABOVE` and `LN_MUL` and one on six others.
    // 451 with the extreme value theorem, 2026-09-25, derived before the run: ten antecedents over
    // five facts, three on the gluing, one on the negation and two on each of the other three.
        // 466 with the convergence criteria, 2026-09-25, and the **fifteen** were derived before the
    // run and met: three on `SUM_RATIO_TEST`, two each on `SUM_DIVERGES`, `SUM_RATIO_DIVERGES` and
    // `SUM_SCALE_DIVERGES`, one each on the six other facts of `Limit`, and none on the three
    // values in `Transcendental`, which are bare convergences.
    // 472 with the polynomial-times-geometric criteria, 2026-09-25, derived before the run: one
    // antecedent on each of the six.
    // 491 with resolution as a link, the same day, derived before the run: nineteen antecedents
    // over twelve facts, which `ProposeSpec` lists one by one. Tip plus this branch's delta.
    // 504 with the derivative and Rolle's theorem, the same day, derived before the run: thirteen
    // antecedents over six facts, four on each interior lemma and on `ROLLE`, one on the negation.
    // 533 with the closed terms, the same day, tip plus this delta, derived before the run: seven on each of
    // the three new congruences, five, two and one on the other three.
    // 542 with the mean value theorem, the same day, derived before the run: nine antecedents over
    // four facts, two on each linearity and on uniqueness, three on the theorem. Tip plus this
    // branch's delta.
    // 545 with the product rule, the same day, derived before the run: three antecedents over two
    // facts, one on `DERIVATIVE_CONTINUOUS` and two on `DERIVATIVE_PRODUCT`.
    // 547 with the chain rule, the same day, derived before the run: its two antecedents.
    // 548 with the exponential's slope, the same day, derived before the run: the estimate's one
    // antecedent, and the slope has none.
    // 554 with the sign of a derivative on an interval, the same day, derived before the run: two
    // antecedents on each of the three, the continuity and the slope; the `!x` or `!u v` after them
    // is under a binder and is not peeled.
    // 562 with Fermat's little theorem, the same day, derived before the run: eight antecedents over
    // five facts, three, two, one, one and one; the binomial theorem and the two sums carry none.
    // 565 with uniform continuity, the same day, derived before the run: its three antecedents.
    // Tip plus this branch's delta.
    // 583 with the gauge integral, the same day, derived before the run and read off the probe
    // after it: eighteen antecedents over nine facts, three on `HAS_INTEGRAL_UNIQUE`, one on
    // `FINE_SUM_PIECE` and two on each of the other seven. Tip plus this branch's delta.
    // 586 with the sine's and the cosine's derivatives, the same day, derived before the run: the
    // three estimates near zero carry `abs h <= 1 / 2` each, and the other four carry nothing.
    // 600 with Euler's theorem, the same day, derived before the run: fourteen antecedents over
    // seven of its nine facts. Tip plus this branch's delta.
    // 604 with the existence of the integral, the same day, derived before the run: two
    // antecedents on each of `CONTINUOUS_HAS_INTEGRAL` and `CONTINUOUS_INTEGRAL`.
    // 637 with the textbook forms of the interval theorems, 2026-09-25, derived before the run:
    // thirty-three antecedents over fourteen facts, the count `ProposeSpec` gives by fact.
    // 645 with the fundamental theorem relative to `[a, b]`, the same day: eight over four facts.
    // 646 with the logarithm's slope, 2026-09-26, derived before the run: its one antecedent, `0 < x`.
    // 652 with the integral's linearity, 2026-09-26, derived before the run and read off the probe:
    // two antecedents on each of the three.
    // 662 with additivity and the second half of the fundamental theorem, 2026-09-26, derived before
    // the run: four antecedents on `HAS_INTEGRAL_JOIN`, three on each of the two derivatives.
    // 676 with integration by parts and the change of variables, 2026-09-26, derived before the run
    // and confirmed by it: four antecedents on each form of parts and three on each form of the
    // substitution.
    // 709 with the p-adic valuation, 2026-09-26, derived before the run: thirty-three antecedents
    // over fourteen facts, the count `ProposeSpec` gives by fact. Tip plus this branch's delta.
    // 714 with Taylor's theorem, 2026-09-26, derived before the run and confirmed by it: two
    // antecedents on `CONTINUOUS_MUL` and three on `TAYLOR`, and none on `DERIVATIVE_POWER`.
    // 732 with the integral's relative forms, 2026-09-26, derived before the run: eighteen
    // antecedents over seven facts, the count `ProposeSpec` gives by fact. Tip plus this branch's
    // delta.
    // 737 with Wilson's theorem and the product over paired indices, 2026-09-26, derived before the
    // run: four antecedents on `NUM_PROD_PAIRED` and one on `NUM_WILSON`. Tip plus this branch's
    // delta.
    // 740 with `TAYLOR_WITHIN`'s three antecedents, 2026-09-27, derived before the run.
    // 802 with the rationals and the cuts collected, 2026-09-27, card `e4a90d43`: sixty-two
    // antecedents over the facts of `Fraction` and `Cut`, measured by a probe of `ProposeSpec` with
    // its numeric assertions printed. Tip plus this branch's delta.
    propose.weakenings.size shouldBe 802
    recoveries.map(_.proposal.source).distinct shouldBe Vector(Propose.Source.Substituted)
  }

  it should "be measured against what its source can reach and not against the whole library" in {
    // 55 of the 233 entries write one of `+`, `*`, `<` or `le` outside a lambda, which is what the
    // substitution needs to produce anything at all from. Reporting "12 of 233" would invite a
    // reader to conclude the loop misses nine tenths of what it was shown; what it misses is
    // forty-three lemmas whose swapped form is either absent from the library or false, and a
    // hundred and seventy-eight it was never in a position to say anything about.
    //
    // The containment is asserted rather than argued: a lemma reached by a swap writes the operator
    // that was swapped in, so it is itself one the source could mutate. If that ever stops holding,
    // the denominator has stopped meaning what this comment says it means.
    // 59 with the floor and the ceiling, and the delta is DERIVED: all four of their lemmas write
    // `<=` outside a lambda, so all four are reachable by the substitution. None of the four
    // produces a rediscovery, so this denominator grew while the numerator did not, which is the
    // direction a denominator should be allowed to move without anybody being pleased about it.
    // 71 since `Magnitude`, and the delta is MEASURED and then read rather than derived, because
    // guessing it would have been guessing which of seventeen statements writes a swappable
    // operator outside a lambda. TWELVE of the seventeen do; the five that do not are `ABS_CASES`,
    // `ABS_ZERO`, `MAX_CASES`, `MIN_CASES` and `SGN_ZERO`, and looking at them says why: each is
    // written with `=` and `\/` alone, and neither is one of the four this source swaps.
    //
    // None of the twelve produces a rediscovery, so this denominator grew by twelve while the
    // numerator did not move at all. That is the direction it is allowed to move in, and it is
    // worth one line that nobody should be pleased about it: the source can now mutate seventeen
    // per cent more of the library and reaches nothing more.
    // 72 with `POWER_MULTIPLICATIVE`, and ONE of the three lemmas that landed with it rather
    // than all three, which is the part worth measuring. It writes `*` outside a lambda and is
    // reachable; `POWER_NEG_DOUBLE` and `SUM_GEOMETRIC` are not in `mutable` and this file does
    // not claim to say why, because that would be describing a source's reach from the outside.
    //
    // The one mutation it produces is `Power (x + y) z = Power x z + Power y z`, which is false,
    // and it is the SAME statement `SeriesSpec` already carries by hand as that lemma's false
    // control. Written independently, hours apart, by a person choosing the likeliest error and
    // by a generator swapping an operator. Worth a line because it is the only evidence in this
    // file that the source's idea of a plausible mutation and a writer's coincide at all, and
    // the denominator grew by one while the numerator did not, which is the direction it may go.
    // 73 with the first analysis, and ONE of its twelve rather than the two a reader would count
    // off the statements. `COSH_PLUS_SINH` writes `+` outside a lambda and is reachable.
    // `LE_BELOW_EVERY_POSITIVE` writes `<=` and looks reachable and is not: `Propose.swapped`
    // strips the LEADING quantifiers and then refuses at any `Abs`, and that lemma's body carries
    // `!e. 0 < e ==> x < e`, which is a lambda under the binder. The same rule excludes
    // `CONVERGES_CONSTANT`, whose sequence is a lambda, and `CONVERGES_EVENTUALLY`, whose
    // agreement is quantified inside. The rest write none of the four operators at all.
    //
    // Derived that way first and measured after, and the derivation was WRONG until the reason was
    // read off `swapped` rather than off the statements: two, and then one.
    // 75 with the two negated comparisons, and TWO of the five facts that landed with them. Their
    // bodies write `<` and `le` and carry no lambda once the leading quantifiers are stripped.
    // `NOT_FORALL` writes neither and its body is a quantifier; `MONOTONE_LE` and
    // `MONOTONE_CONVERGES` write `<=` inside `!n. ...`, which is a lambda, so `swapped` refuses at
    // it. Derived that way and then measured, which is the second time this entry has been able to
    // predict itself.
    // 77 with the two the order gained on 2026-09-18. `LE_MUL_BOTH` writes `le` and `INV_ANTITONE`
    // writes both `lt` and `le`, and neither body carries a lambda once the leading quantifiers come
    // off, which is the condition `swapped` refuses at.
    // 79 with the bridge into the reals, and TWO of its eight, derived the same way the two
    // rows above are: `INT_REAL_ADD` writes `real_add` and `INT_REAL_MUL` writes `real_mul`,
    // and neither body carries a lambda once the leading quantifiers come off, which is the
    // condition `swapped` refuses at. The other six write none of the four operators at all:
    // four are equations whose only operation is `real_of_int`, and `INT_REAL_PAIR` and
    // `INT_REAL_NEG` write `sub`, which is not among the four `Propose.swapped` exchanges.
    // 81 with the order map, and BOTH of the pair are here where the weakenings row above takes
    // only one, which is the difference between what a lemma owes and what it writes.
    // `NUM_REAL_LE_BACK` writes `real_le` in its antecedent and `INT_REAL_LE` writes it on the
    // right of its biconditional; neither body carries a lambda once the leading quantifiers come
    // off, which is the condition `swapped` refuses at. That both produce a residue and only one
    // of them is weakenable is the whole of why this figure and the one above move by different
    // amounts on one change.
    // 82 with `exp 1 > 2`, 2026-09-20, and ONE of the two facts that landed with it, which is the
    // same split the rows above keep drawing. `EXP_ONE_ABOVE_TWO` is `2 < exp 1`: it writes
    // `real_lt`, binds nothing at all and so carries no lambda for `swapped` to refuse at.
    // `Coding.NUM_POW_LE_FACT` writes `NUM_LE`, `NUM_POW`, `NUM_MUL` and `NUM_FACT` and not one of
    // the four operators `Propose.swapped` exchanges, all four of which are the reals', so it
    // produces nothing here. Derived that way and then measured.
    // 85 with the three facts about `abs`, 2026-09-20, and here **all three** are counted where
    // the weakenings row above takes two: `ABS_OF_NONNEG` and `ABS_OF_NONPOS` write `le` in their
    // antecedents and `ABS_MUL` writes `real_mul`, and no body carries a lambda once the leading
    // quantifiers come off, which is the condition `swapped` refuses at. Three and two on one
    // change is the same difference between what a lemma owes and what it writes that the row
    // above draws.
    // 86 with `ABS_POWER_LE`, 2026-09-21, which writes `real_le` and carries no lambda once its
    // three leading quantifiers come off. It is counted here and once in the weakenings row, and
    // **that pair is where the prediction for it went wrong**: `open` is over every proposal,
    // weakenings and substitutions together, and the prediction counted only the first kind.
    // 87 with the halving alone, 2026-09-21, and the prediction was 88. **Two** of the three
    // new facts are refused by `swapped` rather than one, and the condition it refuses at is
    // the same for both: a lambda in the body once the leading quantifiers come off.
    // `EXP_ABSOLUTE` is a `converges` of a `Sum` of one, which was predicted; `EXP_TAIL_GEOMETRIC`
    // carries `!j. ...` **inside** its implication, and a universal quantifier is a lambda here,
    // which was not. Reading `stripForall` as removing every quantifier rather than the leading
    // ones is what the prediction did.
    // **87 still**, with `NUM_CHOOSE_ALL` and `NUM_CHOOSE_FACTORIAL`, and the prediction was 89.
    // Neither carries a lambda, which is what was checked and is not the whole condition:
    // `Propose.Swaps` holds **four** constants and all four are the reals' — addition against
    // multiplication and the two orders. A lemma written entirely in `num` constants has nothing
    // to swap, so it produces no substitution and is not mutable at all. The prediction read
    // `swapped`'s refusal condition and not the table it ranges over, which is the same half-read
    // selector the note beside `ProposeSpec`'s buckets is about.
    // 89 with `MUL_INV_COMBINE` and `EXP_ADD`, which write `real_mul` and carry no lambda.
    // `EXP_CONVOLUTION` is refused: its body is a `Sum` of one.
    // 91 with the two hyperbolic facts, which write `real_mul` and carry no lambda.
    // 94 with the square root, 2026-09-24: `SQRT`, `SQRT_UNIQUE` and `SQRT_SQUARE` write
    // `real_mul` with no lambda in the body. `SQRT_EXISTS` writes it too and is refused, its body
    // being an existential, and the two values write no operator `Propose.Swaps` holds.
    // 95 with `SIN_COS_SQUARED`, which writes `real_mul` and `real_add` with no lambda in the body,
    // derived before the run. The other four facts of that change are refused: `SUM_EVEN_ODD` and
    // `CONVERGES_SHIFT` carry a lambda once their quantifiers come off, and the two absolute
    // convergences are existentials.
    // 102 with seven of the logarithm's twelve, derived before the run: every fact writing an order
    // or a sum or product between reals with no lambda in the body. `EXP_CONTINUOUS`,
    // `EXP_INJECTIVE`, `LN_EXP` and `LN_ONE` write none of the four, and `EXP_ONTO` is an
    // existential.
    // 103 with `EXP_NEAR_LINE`, 2026-09-25, read off a probe of `Propose.audit` filtered by `from`:
    // it writes the order and the product between reals with no lambda in the body, and swaps to
    // two substitutions. `DERIVATIVE_EXP` writes none of the four outside `derivative`.
    // 107 with four of the integral's nine, derived before the run and read off the probe: the two
    // rules of a fine sum and the two uniquenesses write an order, a sum or a product between reals
    // with no lambda in the body. The other five each carry a quantifier inside, which is a lambda.
    // 111 with four of the seven the sine's and the cosine's derivatives brought, the same day,
    // derived before the run and read off a probe of `Propose.audit`: the two addition formulas
    // and the two estimates near zero write a sum, a product or an order between reals with no
    // lambda in the body. `EXP_TAIL_BOUND` carries a quantifier inside and the two slopes write
    // none of the four.
    // 112 with `CONTINUOUS_EXTENSION_AGREES`, 2026-09-25: it writes an order between reals, `x < a`
    // and `b < x` inside `COND`, with no lambda in the body, and a probe of `Propose.audit` found its
    // two substitutions and no other from the fourteen textbook forms. Every other one carries a
    // quantifier inside, and `CONTINUOUS_WITHIN_OF_CONTINUOUS` writes none of the four.
    // 113 with `DERIVATIVE_WITHIN_INTERIOR`, the same day, derived before the run: `a < x` and
    // `x < b` are an order between reals with no lambda in the body. The two forms of the
    // fundamental theorem carry a quantifier inside, and `DERIVATIVE_WITHIN_OF_DERIVATIVE` writes
    // none of the four.
    // 114 with the logarithm's slope, 2026-09-26, derived before the run: `0 < x` is an order
    // between reals with no lambda in the body.
    // 115 with `HAS_INTEGRAL_JOIN`, the same day, derived and not probed: `u <= v` and `v <= w` are
    // an order between reals with no lambda and no quantifier in the body. The two forms of the
    // derivative of an integral carry a quantifier inside.
    // 118 with the reals built from the cuts, 2026-09-26, read off a probe: `real_add`, `real_mul`
    // and `real_lt` are definitional entries since `docs/adr/0053`, each an equation that writes the
    // operator itself with no lambda in the body. Tip plus this branch's delta.
    propose.mutable.size shouldBe 118
    recoveries.map(_.reached).distinct.foreach(name => propose.mutable should contain(name))
  }

  it should "prove every one, with the price separating them" in {
    // Every one comes back `Proved`, which is the least surprising fact here: they are lemmas this
    // library holds, so a failure would be a finding about the tactic surface and not about the
    // generator. It is asserted because that is exactly why it is worth knowing.
    //
    // **The interesting half is the price.** The ones the ring normalisation settles at once come
    // back `Immediate`, at 77 and 108 inferences; the rest are order facts the ring does not
    // decide, come back `Known`, and cost between 3706 and 7351. Forty to seventy times more for a
    // claim of the same standing, and the novelty scale calls every one of them not-news
    // either way, which is correct and is the scale doing its job on its own hardest case: a
    // rediscovery is precisely a claim that looks new and is not.
    // **The two that arrived on 2026-09-18 are both `Known` and neither is `Immediate`**, which is
    // the split staying where it was rather than moving: four is still the number the ring
    // normalisation settles outright, and the order pair the generator now travels costs what every
    // other order fact here costs. A reader who expected the four to move was expecting a new
    // lemma to be an identity, and `LE_MUL_BOTH` is not one.
    readings.size shouldBe 18
    readings.map(_.report.outcome).distinct shouldBe Vector(Cost.Outcome.Proved)

    readings.count(_.standing == Novelty.Standing.Immediate) shouldBe 4
    readings.count(_.standing == Novelty.Standing.Known) shouldBe 14
    readings.count(_.standing == Novelty.Standing.Earned) shouldBe 0

    val immediate = readings.filter(_.standing == Novelty.Standing.Immediate).map(_.inferences)
    val known = readings.filter(_.standing == Novelty.Standing.Known).map(_.inferences)
    immediate.max should be < known.min
  }
}
