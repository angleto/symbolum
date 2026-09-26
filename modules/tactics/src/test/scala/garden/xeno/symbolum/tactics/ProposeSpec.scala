package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.{Abs, App, BVar, Const, FVar, Term}

/**
 * The discovery loop with its first step attached, run end to end against this repository's own
 * library.
 *
 * Everything else in the loop takes a candidate. This produces them, and the source it produces
 * them from was chosen for having a result on the first run rather than for being exciting: applied
 * to the library it asks, of every lemma, whether each of its hypotheses was needed.
 *
 * The counts below are the calibration and are asserted rather than printed. What they say is that
 * the loop works and finds nothing, which for a curated library is the right answer and is only
 * worth anything because the machine is demonstrably running: the proposals `decidedFalse` counts
 * below are decided **false**, each a dropped hypothesis that was load-bearing, correctly refuted.
 *
 * That sentence carried the count and the total as digits copied from the assertions, and they
 * were not moved when the assertions below were, on 2026-09-11 and again after it; it names the
 * assertion now rather than restating it.
 *
 * **Every count here moved on 2026-09-12 and one lemma was not proved to move it.** Five
 * developments that sat beside `Chain` went into it, so the library the generator reads went from
 * 138 entries to 186, and forty-one further proposals came out of the forty-eight facts that
 * arrived. What each count did with them is the interesting half and is written at each assertion:
 * three are decided false, nineteen are open, and nineteen are **unreadable**, which took that
 * bucket from three to twenty-two and is the largest single move any of these numbers has made.
 */
class ProposeSpec extends AnyFlatSpec with Matchers {

  private val propose = Propose.standard
  private lazy val findings = propose.audit

  "The generator" should "propose one weakening per hypothesis of every lemma that has one" in {
    val proposals = propose.weakenings

    // 48 until 2026-09-11, when `Chain` gained `Peano` and the library gained thirty lemmas about
    // arithmetic on `num`. Four of them carry a hypothesis, so four more weakenings.
    //
    // 54 later the same day: `Peano` gained the three lemmas that carry a bound on an index into
    // the reals, and two of them are implications, so each gives up its antecedent here.
    //
    // 57 with the predecessor and the truncated difference, later the same day again. `Peano`
    // gained fourteen lemmas and exactly three of them carry a hypothesis: `NUM_SUB_EQ_ZERO`,
    // `NUM_SUB_ADD` and `NUM_REAL_SUB`, each stated under a bound because each is **false** without
    // it. The other eleven hold everywhere and a source that drops hypotheses has nothing to take.
    //
    // 64 when the strict order's own facts moved into `Peano` from `Modular` and `Bounded` and the
    // two order principles landed, later the same day again. Eleven lemmas arrived and exactly
    // seven are implications: `NUM_LE_CASES`, `NUM_LT_SUC_CASES`, `NUM_REAL_INJECTIVE`,
    // `NUM_LE_OF_LT`, `NUM_LE_ZERO`, `NUM_LEAST` and `NUM_GREATEST`. Seven of the eleven were
    // already proved before this count last moved and were invisible here, because `Library.of`
    // collects the chain's developments and `Modular` is not one; moving them is what made them
    // countable.
    //
    // 65 with `NUM_ADD_CANCEL_LEFT`, which `Modular.DivisionUnique` could not be proved without.
    // Cancellation is an implication and its antecedent is the whole of it, so it gives one here.
    //
    // 101 on 2026-09-12, when the five developments beside `Chain` were threaded into it and the
    // library went from 138 entries to 186. Thirty-six of the forty-eight facts that arrived carry
    // a hypothesis: nine from `Divisibility`, twenty-three from `Modular` and four from `Word`.
    // `Product` contributes none, which is a fact about it rather than an omission: every one of
    // its eight facts holds unconditionally, so a source that drops hypotheses has nothing to take.
    // This is the largest single move this count has made and no lemma was proved to make it.
    //
    // 113 later the same day, and these twelve **were** proved: `Modular` gained the quotient and
    // the remainder as functions, Bezout, the gcd's divisibility form and Euclid's lemma. One
    // weakening per hypothesis, and the hypotheses are where the count comes from rather than the
    // lemmas: `NUM_MOD_LT`, `NUM_DIV_MOD_UNIQUE`, `NUM_BEZOUT` and `NUM_PRIME_ABOVE_ONE` carry one
    // each, and `NUM_DIVIDES_SUMMAND`, `NUM_GCD_DIVIDES`, `NUM_PRIME_DIVISOR` and `NUM_EUCLID`
    // carry two each. The four that carry none are the ones stated without a guard at all, which
    // is a fact about the definitions: `NUM_DIV_MOD` holds at a modulus of `ZERO` because the
    // constants were defined to make it hold there.
    // 115 after `NUM_DIV_MOD_BELOW` and `NUM_DIV_MOD_STEP` landed the same day. Both carry exactly
    // one hypothesis, `NUM_LT m n`, so they contribute one weakening each and the delta is +2 with
    // no interaction: this figure counts hypotheses and those two lemmas added two.
    // 117 after `NUM_LT_TRANS` and `SUM_CONGRUENCE_BELOW`, and the delta is DERIVED rather than
    // read off a failing run: both carry exactly one antecedent -- a conjunction and a bounded
    // agreement are each one -- so one weakening each, +2 with no interaction.
    // 121 since `Classical` joined the library on 2026-09-12. The delta is DERIVED: of the nine
    // things that arrived, exactly four carry an antecedent, and this figure counts antecedents
    // rather than lemmas. `COND_TRUE` and `COND_FALSE` are guarded by the condition and its
    // negation, `DOUBLE_NEGATION` is `~(~x) ==> x`, and `FUNCTION_EXTENSIONALITY` is agreement at
    // every point implying equality. The other five hold outright: the two De Morgans and `COND`
    // are equations, the excluded middle is a disjunction, and `T` is not `F` is a negation.
    // 122 with `NUM_SUM_CONGRUENCE_BELOW`, and the delta is DERIVED: of the three facts that
    // arrived with `NUM_SUM`, exactly one carries an antecedent, and this figure counts antecedents
    // rather than lemmas. The two recurrences hold outright and have nothing to take.
    // 123 with `Rotation`, and the delta is DERIVED the same way: of its three facts only
    // `WORD_ROTATE_NTH` is an implication. `WORD_ROTATE_LENGTH` and `WORD_ROTATE_ZERO` are
    // equations that hold outright, and the second of them deliberately so -- it is unguarded at
    // length zero on purpose, which is the one place a guard would have made this figure 124.
    // 127 with the floor and the ceiling, and the delta is DERIVED: their four lemmas carry one
    // antecedent each and it is the same one, `0 <= x`, which is the written sign condition. The
    // fifth thing that arrived with them, `NUM_ARCHIMEDES`, carries none and contributes nothing
    // here, which is right: there is no hypothesis in it to find unnecessary.
    // 124 since the generator stopped proposing the same claim twice. The delta is DERIVED and
    // the rows are nameable: `Order` re-exports the facts of `Positivity`, so three names are held
    // by two developments each, and of those three `ADD_POSITIVE` has two antecedents and
    // `POSITIVE_NOT_ZERO` one, while `ZERO_LT_ONE` has none. Two plus one is the three rows that
    // went. This figure had been counting the library's holdings rather than its lemmas.
    // 130 since `Magnitude` joined the chain on 2026-09-13, and the delta is DERIVED and then
    // confirmed against the regenerated `docs/lemmas.md`: of the seventeen facts it brought, FIVE
    // carry a hypothesis and they carry SIX between them, because `MAX_LEAST` has two antecedents
    // and `ABS_ZERO`, `SGN_NEGATIVE`, `SGN_POSITIVE` and `SGN_ZERO` have one each. The other
    // twelve are unconditional and contribute nothing here, which is right: there is no hypothesis
    // in them to find unnecessary.
    // 132 since `Coding` joined the chain later the same day, and the delta is DERIVED and then
    // measured: of its four facts TWO carry a hypothesis, `NUM_FACT_DIVIDES` and `NUM_CRT_PAIR`,
    // and each carries ONE, because what looks like two and three antecedents is in both cases a
    // single conjunction on the left of a single arrow. The two recurrences of the factorial are
    // equations and contribute nothing, which is right for the reason above.
    // 135 since the finite product and Gauss's lemma. The product's two recurrences are equations
    // and carry nothing; `NUM_GAUSS` carries THREE, because its premises are three arrows and not
    // one conjunction, which is where it differs from the two facts above it and is why the delta
    // is three rather than one.
    // 136 with `NUM_DIVIDES_ONE`, which carries one hypothesis and so contributes one.
    // 137 with the moduli's coprimality, whose premise is one conjunction and so contributes one.
    // 139 with the congruence that descends to a divisor: two premises as two arrows, so two.
    // 143 with the four: `NUM_MUL_POSITIVE` carries two premises as two arrows and contributes
    // two, and the two product lemmas one each.
    // 150 with the Chinese remainder theorem over many moduli and the two coprimality lemmas under
    // it, and the delta is DERIVED and then measured: `NUM_GCD_MUL` writes its three premises as
    // three arrows and contributes THREE, while `NUM_GCD_PROD` and `NUM_CRT` carry two each. None
    // of the seven is a conjunction on the left of one arrow, which is why this is seven and not
    // three.
    // 153 with the beta function's four lemmas, and the delta is DERIVED and then measured: only
    // two of the four carry a hypothesis at all. `NUM_MOD_OF_CONG` writes two as two arrows and
    // contributes two, `NUM_LE_LT_TRANS` writes one conjunction and contributes one, and
    // `NUM_GCD_SYM`, `NUM_FACT_POSITIVE` and `NUM_BETA_SEQUENCE` carry none. A lemma that says
    // something unconditionally produces no weakening, which is this generator's whole shape.
    // 157 with the arithmetisation's first slice, derived and then measured: of its eight lemmas
    // four carry one hypothesis each and four carry none. The two recurrences of the triangular
    // numbers are equations and the two bounds on the pairing are unconditional.
    // 158 with `NUM_CODE_INJECTIVE`, the only one of the constructor's four facts that carries a
    // hypothesis. The two strict bounds and the non-vanishing are unconditional, which is the point
    // of them: a constructor that had to be guarded would guard every syntactic predicate above it.
    // 163 with the term predicate of the embedded theory. Five of its seven facts carry no
    // hypothesis at all: the recursion equation is an equation, a variable and zero are terms
    // unconditionally, and nothing codes a term at zero. The successor rule carries one and the
    // two binary rules carry two each, which is five.
    // 169 with the formula predicate: two arrows each for the equality and the implication, one
    // for the negation, one for the quantifier, and none for the recursion equation or the refusal
    // at zero. The quantifier carries one and binds two, because its first component is a variable
    // index and an index has nothing to satisfy.
    // 170 with the object language's numerals, of which only the injectivity carries a
    // hypothesis: the two recurrences are equations and every numeral being a term is
    // unconditional.
    // 171 with course-of-values induction, whose one hypothesis is the step it is given.
    // 173 with substitution keeping a term a term, whose two premises are two arrows.
    // 175 with the same lemma for formulas, whose two premises are two arrows.
    // 176 with the axioms of PA, which add EIGHT lemmas and exactly one proposal. Derived before
    // it was measured and the derivation is the interesting part: six of the eight say a fixed
    // code is an axiom and carry no hypothesis at all, the seventh is the equation that
    // characterises the set, and only the induction scheme has an arrow, `NUM_FORM p`. A bucket
    // that counts hypotheses rather than lemmas is the one place where the largest addition this
    // library has taken is also nearly the smallest.
    // 177 with every axiom being a formula, whose one hypothesis is the membership it drops.
    // 198 with the logical axioms, which is the largest jump this figure has taken and is the
    // shape of the addition rather than its size: eight schemes carrying twenty conditions between
    // them, plus the one `NUM_LOGIC_FORM` carries. A set of axioms that are all schemes is a set
    // whose every member arrives with side conditions, and this bucket counts side conditions.
    // 200 with the two facts that say the proof predicate is inhabited, one hypothesis each.
    // 204 with the shift lemma's three hypotheses and the monotonicity's one.
    // 205, and only one of the two facts added produces anything: `NUM_LE_ADD` has no hypothesis.
    // 208 with the closure under modus ponens and the cancellation it needed. THREE and not two,
    // and the session that added them derived this figure as UNCHANGED, on the reasoning that
    // neither lemma is about the reals and neither is reachable from a proposal. That is not what
    // this bucket counts. It walks the whole library and counts hypotheses, so a lemma is reached
    // whatever it is about: the cancellation drops its one comparison and the closure drops each
    // of its two, and the wrong derivation was about the generator's reach rather than its
    // subject. The three figures below moved with it and the same derivation missed all three.
    // 209 with the closure under generalisation, which has one hypothesis. Derived from the
    // arithmetic of hypotheses this time and right, which is the correction the entry above is
    // about: the question is how many arrows a lemma carries, never what it is about.
    // 215 with `Deduction`'s two, and the six is the clearest case yet of why this bucket counts
    // arrows rather than lemmas: the identity carries one hypothesis and the syllogism carries
    // five, so two lemmas are six proposals.
    // 216 with Euclid's theorem and its prime-factor lemma, and the one is the arithmetic again:
    // the factor lemma carries `SUC ZERO < n` and Euclid carries nothing, so two lemmas are one
    // proposal. A bucket that counted lemmas would have said two.
    // 221 with the three multiplicative lemmas: one hypothesis, two and two.
    // 222, and the one is worth reading beside the entry above: two lemmas arrived and only one
    // carries an arrow, because `NUM_PRIME_TWO` is a claim about a single number.
    // 234 with the deduction theorem's three rules: three hypotheses, five and four. The largest
    // single move this figure has taken, and it is the shape rather than the size, the same way the
    // logical axioms' was: a rule stated over provability facts carries a side condition per
    // formula it mentions.
    // 237 with the deduction theorem's three hypotheses. Its two definitions add nothing here,
    // being equations: this bucket counts arrows and an equation has none.
    // 244 with the first analysis, and the same rule reads it: of its twelve lemmas, four carry an
    // arrow and eight do not. Two from `LE_BELOW_EVERY_POSITIVE`, two from `CONVERGES_UNIQUE`, one
    // from `LIM_OF_CONVERGES`, two from `CONVERGES_EVENTUALLY`. The six values at zero and the two
    // hyperbolic identities are equations and contribute nothing, which is this bucket behaving
    // exactly as the entry above describes.
    // 248 with `NUM_PROV_SPECIALISE`, and four is the whole of it: one lemma with four
    // antecedents, the formula, the term, its closure and the provability of the quantified
    // formula. The rule the entry above states reads it exactly, a side condition per thing it
    // mentions.
    // 250 with the idleness of the substitution, which carries two antecedents.
    // 256 with the monotone convergence theorem's six, by the same count the entry in
    // `RediscoverySpec` derives: one arrow each for `NOT_FORALL`, the two negated comparisons and
    // `MONOTONE_LE`, and two for `MONOTONE_CONVERGES`.
    // 274 with the three rules of the embedded theory's equality, whose antecedents are five,
    // eight and five: each asks its terms to be terms and to be closed before it asks anything
    // about provability, and transitivity asks it of three terms rather than two.
    // 285 with PA's own addition on numerals and the six facts under it. Eleven and not fourteen:
    // the theorem itself has no hypothesis to drop, and neither has `NUM_CLOSED_ZERO`.
    // 289 with the two lemmas recovered from the `prime-power-cancellation` branch: one
    // antecedent and three.
    // 299 with `Concatenation`'s fifteen and the three facts about `num` proved in front of
    // them. TEN and not eighteen, DERIVED before the run and then measured: eight of the
    // eighteen are equations and have nothing to drop -- the associativity, both units, both
    // length laws, the empty word's length, the singleton's entry and `NUM_SUB_SUB` -- and the
    // other ten carry exactly one antecedent each. No lemma here carries two, which is what a
    // development whose statements are guarded by a single bound looks like.
    // 306 with `Inductive` and `Reaching`. **Seven**, derived before the run from the rule this
    // file states: the antecedents IN FRONT are peeled, meaning the curried arrows, not the
    // conjuncts inside one antecedent. One each for the three `INDUCTIVE` facts, none for
    // `REACH_START` which has no hypothesis, and one each for `REACH_COUNTED`, `REACH_PLAIN`,
    // `REACH_INDUCT` and `REACH_POTENTIAL`, whose antecedents are conjunctions of three, three, two
    // and two under a single arrow.
    //
    // It was first derived as THIRTEEN by counting those conjuncts, and the entry above about
    // `MONOTONE_CONVERGES` carrying two says why that is wrong -- it is curried twice. Kept beside
    // the right figure because the error was in reading the rule, not in adding up.
    // 309 with the comparison test, which is curried three times and therefore carries three.
    // 312 with the algebra of limits' two: `CONVERGES_ADD` is curried twice and `CONVERGES_NEG`
    // once, so three, derived before the run by the peeling rule this file states and measured
    // identical. The sum's two leading arrows are the two convergences it takes; the negation's
    // one is the single convergence it takes.
    // 323 with the object language's six derived connectives. **ELEVEN, derived before the run
    // and then measured**, by the peeling rule this entry states: the six defining equations are
    // equations and have nothing to drop, and the six well-formedness rules carry two antecedents
    // each except `NUM_FORM_EXISTS`, which asks only that its body be a formula. Two, two, one,
    // two, two, two. Nothing here is curried under a nested quantifier, so the caveat the
    // `MONOTONE_LE` entry above records does not arise.
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
    // before the run and then measured**: each is curried twice, the convergence and the eventual
    // bound being two arrows in front, so two apiece. What follows the second arrow is a
    // comparison rather than an arrow under a quantifier, so the `MONOTONE_LE` caveat above does
    // not bite on either.
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
    // 347 with the four the order gained on 2026-09-18: `LE_MUL_BOTH` and `INV_ANTITONE` have two
    // hypotheses apiece, and this source offers one weakening per hypothesis.
    // 349 with `Peano`'s two, `NUM_ADD_LE_BOTH` and `NUM_SUM_MONOTONE_BELOW`, one apiece. This is
    // the second site carrying the same total and it went red with `RediscoverySpec`'s, which is
    // the argument for the question that entry raises: a running total kept by hand in two files
    // is two places to forget. Both lemmas carry one antecedent under one arrow, the first a
    // conjunction and the second a bounded quantifier, and `Propose.peel` counts arrows and not
    // conjuncts. Which lemmas moved it is measured off `docs/lemmas.md` at `9734bf7` against the
    // current one, and the derivation is written out where `RediscoverySpec` pins the same figure.
    // 362 with the four `Deduction` facts that put PA's multiplication to work, and the thirteen
    // are derived from their statements: seven arrows on `NUM_PROV_ADD_CONG`, four on
    // `NUM_PROV_MUL_SUC`, two on `NUM_PROV_MUL_ZERO`, none on `NUM_PROV_NUMERAL_MUL`, which owes
    // nothing and is what the other three were built for. `RediscoverySpec` pins the same figure
    // and carries the same derivation, which is the two places this comment's neighbour calls out.
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
    // 381 with the order map, the same day, and the **one** was derived before the run: the pair
    // that landed is `Peano.NUM_REAL_LE_BACK`, one antecedent under one arrow, and
    // `Inclusion.INT_REAL_LE`, an equation between propositions with nothing owed. So one and not
    // two, and the asymmetry is the point rather than an accident of counting: a biconditional
    // owes nothing to weaken, and the implication under it owes everything it crosses on. Tip
    // plus this branch's delta.
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
    // 420 with the list interface, 2026-09-23: `LIST_CONS_INJECTIVE` and `LIST_INDUCT` carry one
    // antecedent each and the other six facts of that development carry none.
    // 421 with the structural recursion theorem and the fold, 2026-09-23: `LIST_RECURSION_UNIQUE`
    // carries one antecedent and the other four facts of those two developments carry none.
    // 425 with the square root, 2026-09-24: one antecedent each on `SQRT_EXISTS`, `SQRT`,
    // `SQRT_UNIQUE` and `SQRT_SQUARE`, none on the two values.
    // 426 with `SQRT_TWO_IRRATIONAL`'s one antecedent, the same day.
    // 427 with `CONVERGES_SHIFT`'s one antecedent, the same day; the trigonometric identity and the
    // three other facts that came with it carry none.
    // 431 with `INTERMEDIATE_VALUE`'s four antecedents, the same day; `CONTINUOUS_CONST` and
    // `CONTINUOUS_ID` carry none.
    // 441 with the logarithm's ten antecedents, the same day.
    // 451 with the extreme value theorem's ten, 2026-09-25: three on `INTERVAL_GLUING`, two each
    // on `CONTINUOUS_BOUNDED` and the two attainments, one on `CONTINUOUS_NEG`.
    // 466 with the convergence criteria's fifteen antecedents, 2026-09-25, derived before the run:
    // three on `SUM_RATIO_TEST`, two on each of the other three that carry more than one, one on
    // each of six, and none on the three values in `Transcendental`.
    // 472 with the polynomial-times-geometric criteria's six, 2026-09-25, derived before the run:
    // one antecedent on each of the six facts.
    // 491 with resolution as a link, the same day, and the **nineteen** were derived before the
    // run: six on `RES_STEP_SOUND_OF_RESOLVENT`, four on `RES_STEP_SOUND`, two each on `RES_SOUND`
    // and `RES_REFUTES`, one each on `RES_EMPTY_UNSATISFIABLE`, the width's bound and least bound,
    // and the two facts about a refutation; the width's two equations and its attainment carry
    // none. Tip plus this branch's delta.
    // 504 with the derivative's thirteen, the same day: four on each interior lemma, four on
    // `ROLLE`, one on `DERIVATIVE_NEG`. Tip plus this branch's delta.
    // 533 with the closed terms, the same day, tip plus this delta, derived before the run: seven antecedents
    // on each of the three new congruences, five on `NUM_PROV_TRUE_EQ`, two on `NUM_PROV_VALUE`
    // and one on `NUM_PROV_REFL`.
    // 542 with the mean value theorem's nine, the same day: two each on the two linearities and on
    // uniqueness, three on `MEAN_VALUE`. Tip plus this branch's delta.
    // 545 with the product rule's three, the same day: one on the continuity of a differentiable
    // function, two on the product rule.
    // 547 with the chain rule's two, the same day.
    // 548 with the estimate's one, the same day; `DERIVATIVE_EXP` has no antecedent to drop.
    // 554 with the sign of a derivative on an interval's six, the same day: two on each fact.
    // 562 with Fermat's little theorem, the same day, derived before the run: eight antecedents,
    // three on `NUM_PRIME_DIVIDES_CHOOSE`, two on `NUM_PRIME_NOT_DIVIDES_FACT`, one each on
    // `NUM_DIVIDES_SUM`, `NUM_FRESHMAN` and `NUM_FERMAT`, none on the three equations.
    // 565 with uniform continuity's three, the same day, derived before the run: `a <= b`, the
    // continuity on `[a, b]` and `0 < e`. Tip plus this branch's delta.
    // 583 with the gauge integral's eighteen, the same day. Tip plus this branch's delta.
    // 586 with the three estimates near zero, one each, the same day.
    // 600 with Euler's theorem, the same day, derived before the run: fourteen antecedents, three on
    // `NUM_PROD_PERMUTE`, two each on `NUM_PROD_POINT`, `NUM_INVERSE`, `NUM_GCD_MOD`,
    // `NUM_UNIT_COPRIME` and `NUM_EULER`, one on `NUM_PROD_CONG_MOD`. Tip plus this branch's delta.
    // 604 with the existence of the integral, the same day, derived before the run: two antecedents
    // on each of its two facts, `a <= b` and the continuity. Tip plus this branch's delta.
    // 637 with the textbook forms of the interval theorems, 2026-09-25, derived before the run:
    // thirty-three antecedents over fourteen facts, four each on `INTERMEDIATE_VALUE_WITHIN` and
    // `ROLLE_WITHIN`, three each on the uniform continuity, `DERIVATIVE_LOCAL` and the mean value
    // theorem, two on each of seven more, and one each on `CONTINUOUS_WITHIN_OF_CONTINUOUS` and
    // `CONTINUOUS_EXTENSION_AGREES`.
    // 645 with the fundamental theorem relative to `[a, b]`, the same day, derived before the run:
    // eight antecedents over four facts, three on `DERIVATIVE_WITHIN_INTERIOR`, two on each form of
    // the theorem and one on `DERIVATIVE_WITHIN_OF_DERIVATIVE`.
    // 646 with the logarithm's slope's one, 2026-09-26.
    // 652 with the integral's linearity's six, 2026-09-26.
    // 662 with additivity and the second half of the fundamental theorem, 2026-09-26, derived before
    // the run: four antecedents on `HAS_INTEGRAL_JOIN` and three on each derivative.
    // 676 with parts' and the substitution's fourteen, 2026-09-26.
    // 709 with the p-adic valuation, 2026-09-26, derived before the run: thirty-three antecedents
    // over fourteen facts, five on `NUM_VALUATION_DIV`, four on `NUM_DIV_VALUATION`, three each on
    // `NUM_VALUATION_MUL`, `NUM_VALUATION_OTHER_PRIME`, `NUM_VALUATION_EXT` and
    // `NUM_DIVIDES_MUL_VALUATION`, two each on `NUM_VALUATION_UNIQUE`, `NUM_VALUATION_SPEC`,
    // `NUM_VALUATION_DIVIDES` and `NUM_DIVIDES_VALUATION`, one on each of the other four. Tip plus
    // this branch's delta.
    // 714 with the five residues of `CONTINUOUS_MUL` and `TAYLOR`, 2026-09-26.
    // 732 with the integral's relative forms, 2026-09-26, derived before the run: eighteen
    // antecedents over seven facts, four on `DERIVATIVE_WITHIN_CONGRUENCE`, three each on the two
    // derivative twins and two on each of the other four. Tip plus this branch's delta.
    proposals.size shouldBe 732
    proposals.map(_.from).distinct.size should be > 10
    proposals.map(_.source).distinct shouldBe Vector(Propose.Source.Weakened)
    proposals.count(_.change.isEmpty) shouldBe 0
  }

  it should "propose a lemma with one operator swapped for another, which is the source that can rediscover" in {
    // Dropping a hypothesis makes a lemma weaker, and a weaker form of something already held is
    // not a lemma anybody was missing. Substituting one operator for another gives a DIFFERENT
    // lemma, which is what a measurement of rediscovery needs.
    val proposals = propose.substitutions

    proposals.map(_.source).distinct shouldBe Vector(Propose.Source.Substituted)
    proposals.map(_.change).distinct.sorted shouldBe
      Vector(
        "real_add became real_mul", "real_le became real_lt",
        "real_lt became real_le", "real_mul became real_add"
      )
  }

  "Hiding half the library from the generator" should "let it find some of what was hidden" in {
    // The calibration the card asks for before anything is called a discovery: if the loop cannot
    // re-propose what we already know, it will not propose what we do not. Measured rather than
    // argued, and the figure is small on purpose — this is the arithmetic half of the library,
    // whose lemmas are symmetric enough for an operator swap to reach across.
    val whole = garden.xeno.symbolum.theories.Library.of(garden.xeno.symbolum.theories.Chain.standard)
    val names = whole.names.distinct
    val hidden = names.zipWithIndex.collect { case (name, at) if at % 2 == 1 => name }.toSet

    val visible = garden.xeno.symbolum.theories.Library.of(
      Vector("half" -> whole.entries.filterNot(entry => hidden.contains(entry.name))
        .map(entry => entry.name -> entry.theorem).toMap)
    )

    val partial = Propose(propose.novelty, visible, propose.logic)
    val proposed = partial.substitutions.map(_.claim).toSet

    val recovered = whole.entries
      .filter(entry => hidden.contains(entry.name))
      .filter(entry => proposed.contains(entry.theorem.conclusion))
      .map(_.name)
      .distinct

    info(
      s"${hidden.size} of ${names.size} lemmas hidden, ${proposed.size} proposals, " +
        s"${recovered.size} of the hidden ones re-proposed: ${recovered.mkString(", ")}"
    )

    recovered should not be empty
  }

  "The audit of this repository's own library" should "find no unnecessary hypothesis" in {
    // The right answer for a curated library, and worth asserting because it is the outcome the
    // machinery exists to be able to reach honestly. If a lemma is ever over-stated this fails and
    // names it.
    val slack = findings.filter(_.unnecessary)

    withClue(s"stated with a hypothesis it does not need: ${slack.map(_.proposal.from).mkString(", ")}\n") {
      slack shouldBe empty
    }
  }

  it should "decide most of the proposals false, which is the machine working" in {
    // A dropped hypothesis that was load-bearing makes the claim false, and the procedure says so
    // with the point it fails at. That count is the evidence that the loop is running rather than
    // returning nothing because it does nothing.
    val decidedFalse = findings.count(_.standing.contains(Novelty.Standing.False))

    // 25 until 2026-09-11, when the operator-substitution source arrived and a swap that makes a
    // false statement is the ordinary outcome of it, as it is of a weakening.
    //
    // 40 later the same day, and the five that moved came out of `Unreadable` rather than out of
    // `Open`. They are claims wholly about the naturals or about truth values, where the model
    // computes every value exactly, so the point the search finds is a **refutation** and not
    // evidence about a model. `Abduce.Gap.decisive` is that distinction and `Cost` is where it
    // changes the outcome. Over the reals it stays untrue, because the model there is `Double` and
    // a counterexample can be a rounding artefact.
    //
    // 45 when the order principles landed. The five are the weakenings of `NUM_LE_CASES`,
    // `NUM_LT_SUC_CASES`, `NUM_LE_OF_LT`, `NUM_LE_ZERO` and `NUM_REAL_INJECTIVE`, and each is false
    // for the obvious reason: `!x y. NUM_LE x y` and `!x y. x = y` are what is left of a lemma
    // whose whole content was its hypothesis. The other two of the seven are higher order and are
    // in the two buckets below.
    //
    // 46 with cancellation, whose weakening is `!x y a. x = y` and is false at any two numbers.
    //
    // 48 once the model was given `PRE` and `NUM_SUB`. Those two came out of `Unreadable` for the
    // same reason the five above did, and the bucket below records what they were doing there.
    //
    // 51 when the five developments joined the chain on 2026-09-12, and **three of forty-one new
    // proposals** is the number worth reading rather than the fifty-one. The three are the
    // weakenings of `NUM_DIVIDES_ANTISYM`, `NUM_DIVIDES_LE` and `NUM_DIVISION_UNIQUE`, which are
    // `!x y. x = y`, `!x y. NUM_LE x y \/ y = ZERO` and `!x y z u v. y = u /\ z = v`: each is left
    // with no `NUM_DIVIDES` in it at all, so each is a claim wholly about `num` where the model is
    // exact and the point is a decision. The other thirty-eight still name a relation nothing
    // interprets, and they are in the two buckets below.
    //
    // 52 on 2026-09-12 with the quotient, the remainder, Bezout and Euclid, and **one of twelve**
    // is the number to read. Eleven of the twelve weakenings keep a `NUM_DIV`, `NUM_MOD`,
    // `NUM_DIVIDES`, `NUM_GCD` or `NUM_PRIME` in them, the model interprets none of the five, and a
    // term with no value cannot be decided at a point. The twelfth is `NUM_PRIME_ABOVE_ONE`
    // weakened to `!x. NUM_LT (SUC ZERO) x`, which is a claim wholly about `num` where the model is
    // exact, and it is false at `ZERO`.
    // 53 with the two above, and only ONE of them lands here, which is the whole of the delta.
    // `NUM_LT_TRANS` weakened is `!m n p. NUM_LT m p`, a claim wholly about `num` where the model
    // is exact, and it is false. `SUM_CONGRUENCE_BELOW` weakened is `!f g n. Sum f n = Sum g n`,
    // which names `Sum`; the model has no value for it and a term with no value cannot be decided
    // at a point, so it is not refuted here but in the bucket below.
    // 54 with the classical facts, and the one that lands here is worth naming because of what it
    // turns out to be. `DOUBLE_NEGATION` with its antecedent dropped is `!x:bool. x`, which is not
    // merely false: it is the definition of falsity, since `Logic.falsity` IS `!x:bool. x`. So the
    // weakening of double negation elimination is `F` written out, and the machine decides it
    // false without being told. The other three new weakenings are in the bucket below.
    // 54 still with the bounded congruence at the naturals, and the reason is the one its twin at
    // the reals gives two paragraphs up: `NUM_SUM_CONGRUENCE_BELOW` weakened is
    // `!f g n. NUM_SUM f n = NUM_SUM g n`, which names a constant the model has no value for, and a
    // term with no value cannot be decided at a point. It is in the bucket below instead.
    // 50 with the duplicates gone, and the delta is DERIVED: of the seven rows that went, four were
    // false and three were not. The four: both weakenings of `ADD_POSITIVE`, which drop one of two
    // positivity hypotheses and are false at a negative; the weakening of `POSITIVE_NOT_ZERO`,
    // which claims every real is non-zero; and `POSITIVE_NOT_ZERO` with `<` swapped for `<=`,
    // which claims it of every non-negative. The three that were not false are `ADD_POSITIVE`
    // swapped two ways, which give `ADD_NONNEG` and `MUL_NONNEG_BOTH`, and `ZERO_LT_ONE` swapped,
    // which gives `0 <= 1`: all three are lemmas this library holds, so they were never in this
    // bucket and their leaving does not move it.
    // 51 since `Magnitude`, and the one that arrived is nameable: the weakening of `SGN_ZERO`,
    // which drops `x = 0` and claims `sgn x = 0` of every real. The model refutes it at any
    // non-zero point. The other five weakenings it brought are about `abs` and `max`, which no
    // procedure here reads, so they do not land in this bucket; they are in the one below.
    // 52 with `NUM_DIVIDES_ONE`, and this is the first addition in a long run to land HERE rather
    // than in the two buckets below. Dropping its premise leaves `!d. d = SUC ZERO`, every number
    // is one, and what makes that refutable at a point is what the residue does NOT mention: no
    // `NUM_FACT`, no `NUM_GCD`, no `abs`, nothing the model has no value for. The floor, the
    // ceiling, the factorial and Gauss all left a claim naming a constant nobody interprets, so
    // they grew the bucket that asks what a claim mentions and left this one standing still.
    // 54 with both weakenings of `NUM_MUL_POSITIVE`, which the model refutes: dropping either
    // positivity leaves a claim false at the zero the other one was excluding, and the residue
    // names only `NUM_LT` and `NUM_MUL`, both of which the model reads.
    // 55 with one of the beta function's three, and it is the one about the two orders:
    // `NUM_LE_LT_TRANS` weakened is `!m n p. NUM_LT m p`, which is false and is written in `NUM_LT`
    // alone, so the model computes it exactly. The two weakenings of `NUM_MOD_OF_CONG` are not
    // here, and the reason is `NUM_MOD` and `NUM_CONG`: a residue nothing interprets is attempted
    // and not settled rather than refuted.
    // 58 with three of the four, and the fourth is in `unreadable` because its residue names
    // `NUM_TRI`, which nothing interprets. The three that are here are refuted at a point and two
    // of them are about nothing but the order: `!x y z. NUM_LE (x + y) (x + z)` and
    // `!x y z. NUM_LT x z`. The third is the one worth reading, because what is left of
    // `NUM_PAIR_INJECTIVE` when its premise goes is `!x y z u. x = z /\ y = u`, which mentions no
    // constant at all and is false at any two distinct numbers.
    // 59 with the weakening of `NUM_CODE_INJECTIVE`, which is the same residue as
    // `NUM_PAIR_INJECTIVE`'s to the letter: `!x y z u. x = z /\ y = u`, false at any two distinct
    // numbers and mentioning no constant at all. The second time this bucket has taken a row that
    // `aboutNumbers` below cannot see, and for the same reason.
    // 60 with the weakening of `NUM_NUMERAL_INJECTIVE`, whose residue is `!m n. m = n`. It is the
    // THIRD injectivity to leave a residue of that shape, after the pairing's and the
    // constructor's, and all three are false at any two distinct numbers and name no constant at
    // all. A file that pinned a count without the reason would look like a coincidence here.
    // 61 with the weakening of `NUM_ADD_LT_MONOTONE`, whose residue is `!p m n. NUM_LT (p+m) (p+n)`.
    // Derived here rather than measured, and it is the first addition in a while that lands in this
    // bucket rather than beside it: the residue is false and is written ENTIRELY in constants the
    // model computes, so the sampler finds a point. Everything the Goedel work has added for two
    // days has been unreadable instead, because its residues name predicates on codes.
    // 62 with the weakening of `NUM_LT_NOT_LE`, whose residue `!m n. ~(NUM_LE n m)` is false and
    // written in a constant the model computes.
    // 63 with the weakening of `NUM_ADD_LE_CANCEL`, whose residue `!p m n. NUM_LE m n` is false and
    // written in a constant the model computes, so the sampler finds a point. It is the only one of
    // the three this commit adds that lands here: the other two drop a premise of `NUM_PROV_MP` and
    // their residues are about codes, which is the split the entry two above already describes.
    // 68 with the three multiplicative lemmas `Peano` had the additive versions of and not
    // these: monotonicity, strict monotonicity at a positive factor, and cancellation by
    // one. Every one of their five residues is false and is written entirely in `NUM_MUL`,
    // `NUM_LE`, `NUM_LT` and equality, all of which `Model.Numbers` computes exactly, so all
    // five land here rather than in either bucket of the unsettled.
    // 70 with the first analysis, and TWO of its eight new proposals rather than any of the other
    // six. Both are `LE_BELOW_EVERY_POSITIVE`'s and both are false for the same reason the lemma
    // carries two hypotheses: without `0 <= x` the residue is refuted at any negative number, and
    // without the epsilon condition it is refuted at `1`. Both are written entirely in `<=`, `<`
    // and equality over the reals, which the sampler computes exactly. The other six mention
    // `converges`, `lim`, `cosh` or `sinh`, which no model here interprets, so none of them can be
    // decided either way. Derived and then measured, and both halves came out.
    // 74 with the monotone convergence theorem's neighbourhood, and the four are two pairs. The
    // weakenings of `LE_OF_NOT_LT` and `LT_OF_NOT_LE` drop the negated hypothesis and leave
    // `!x y. y <= x` and `!x y. y < x`, which are false and written in nothing but the order. The
    // substitutions of the same two, with `le` swapped for `<`, leave `~(x < y) ==> y < x`, false
    // at `x = y`, and both sources produce it, so it is decided twice from two rows.
    // 76 with the concatenation's ten, and TWO of the ten rather than any of the other eight,
    // which is the split this figure exists to show. The two are the weakenings of
    // `NUM_ADD_LT_CANCEL` and `NUM_LE_OF_NOT_LT`: dropping the antecedent leaves `!p m n. m < n`
    // and `!m n. n <= m`, both false and both written in nothing but the order on `num`, which
    // the sampler computes exactly. The other eight are about `word`, which no model here
    // interprets, so not one of them can be decided either way and all eight land in the
    // bucket below. Derived and then measured, and both halves came out.
    // 77 with ONE of `Peano`'s two rather than both, which is the split this figure exists to
    // show. `NUM_ADD_LE_BOTH` weakens to `!x y z u. x + z <= y + u`, false at `x = 1` with the
    // rest zero and written in nothing but `NUM_ADD` and `NUM_LE`, which `Model.Numbers` computes
    // exactly. `NUM_SUM_MONOTONE_BELOW` weakens to `!x y z. NUM_SUM x z <= NUM_SUM y z`, which is
    // false too and quantifies over two SEQUENCES: the sampler has no reading of a function
    // variable, so it lands in `unreadable` below and not here. Derived and then measured, and
    // both halves came out.
    // 79 with the ONE weakening the Cauchy product's finite half brings, and it was derived before
    // the run: of the six facts only `Peano.NUM_SUC_SUB` owes anything, and dropping its bound
    // leaves `!m n. NUM_SUB (SUC m) n = SUC (NUM_SUB m n)`, false at `m = 0, n = 1` where the left
    // side is `0` and the right is `1`. It is written in nothing but `NUM_SUB` and `SUC`, which
    // `Model.Numbers` computes exactly, so it is decided here rather than left open. Truncation is
    // the whole of why it is false, which is what the lemma's bound is for.
    // 78 with ONE of the order map's three residues, and which one was derived before the run.
    // `Peano.NUM_REAL_LE_BACK` is the only one of the pair that owes anything, so it is the only
    // weakening, and dropping its antecedent leaves `!m n. NUM_LE m n`: false at `m = 1, n = 0`
    // and written in nothing but `NUM_LE`, which `Model.Numbers` computes exactly. The other two
    // residues are substitutions and neither is here, for two different reasons the two buckets
    // below give.
    // 80 with ONE of the two weakenings of 2026-09-21, and **which one was derived before the
    // run**: `NUM_LE_OF_LT_SUC` weakens to `!n i. NUM_LE i n`, false at `i = 1, n = 0` and
    // written in `NUM_LE` alone, which `Model.Numbers` computes exactly. `NUM_CHOOSE_ABOVE`
    // weakens to `!n k. NUM_CHOOSE n k = ZERO`, which is false too and is about a constant no
    // model here reads, so it cannot be decided and is not here. The split is the point.
    // 81 with ONE of the six weakenings of 2026-09-21, and which one was derived before the run:
    // `Peano.NUM_LE_DOUBLE_SUB` weakens to `!x y. x <= NUM_SUB (x + x) y`, false at `x = 1,
    // y = 2` where the right side is zero, and written in `NUM_SUB` and `NUM_LE`, which
    // `Model.Numbers` computes exactly. The other five are about `Sum` over the reals and are
    // not decided by any model here.
    // 82 with ONE of the logarithm's residues, read off a probe of `Propose.audit` rather than
    // predicted: `EXP_INJECTIVE` weakens to `!x y. x = y`, false at any two distinct reals and
    // written in nothing but equality. The other twenty-four are in the two buckets below.
    // 83 with ONE of resolution's nineteen, read off the run, and which one is derived from the
    // constants rather than probed: `RES_REFUTATION_NONEMPTY` weakens to `!k v s inputs m. 0 < m`,
    // false at `m = 0` and written in `NUM_LT` alone. Every other one of the nineteen names a
    // `RES_` constant or applies a function variable, and no model here reads either.
    // 84 with the p-adic valuation, 2026-09-26, read off a probe of `Propose.audit` filtered by
    // `from`: one of its thirty-three residues, `NUM_VALUATION_EXT` with the agreement of the
    // registers dropped, `!x y. 0 < x ==> 0 < y ==> x = y`, refuted at `x = 4, y = 8`.
    decidedFalse shouldBe 84

    // Most of those come with the point they fail at, and some do not: the claim is decided false
    // by quantifier elimination and the abduction that would name a point comes back with none.
    // That is two different answers and the gap between `decidedFalse` and `withAPoint` is asserted
    // rather than asserted away, because "decided false" and "decided false, here" are worth
    // different amounts to a reader and merging them is the habit this repository does not have.
    val withAPoint = findings
      .filter(_.standing.contains(Novelty.Standing.False))
      .flatMap(_.reading)
      .count(_.report.point.isDefined)

    // 31 until the naturals were modelled, and 36 now: the five that arrived came in carrying the
    // number they fail at, which is what made them decidable in the first place.
    //
    // 41 with the order principles, and all five of the new ones carry a point: they are claims
    // about two naturals and `Model.Numbers` computes every value of those exactly. 42 with
    // cancellation, which is a sixth of the same kind. 44 with the truncated difference, which is a
    // seventh and an eighth, and every one of these eight is the same story: a claim wholly about
    // `num`, where the model is exact, so the point is a decision rather than evidence.
    //
    // 47 with the three above, and the two counts moved together for the first time in a while:
    // all three are decided false **and** carry the number they fail at, because what is left of
    // each after the hypothesis goes is written in constants `Model.Numbers` computes exactly.
    //
    // 48 with the quotient, the remainder, Bezout and Euclid, and the two counts moved together
    // again for the same reason: the one of the twelve that is decided false is decided **at a
    // point**, because what is left of `NUM_PRIME_ABOVE_ONE` after its hypothesis goes is
    // `!x. NUM_LT (SUC ZERO) x`, written in constants `Model.Numbers` computes exactly.
    // 49 with `NUM_LT_TRANS` and `SUM_CONGRUENCE_BELOW`, and the two counts moved together AGAIN
    // but only for one of the pair: `!m n p. NUM_LT m p` is decided false and is decided at a
    // point, being written in constants `Model.Numbers` computes exactly. The `Sum` weakening is
    // not decided by a procedure at all and so cannot be here.
    // 50 with the classical facts, and the two counts move together once more for a reason that is
    // the same in form and quite different in content. `DOUBLE_NEGATION` weakened is `!x:bool. x`,
    // and every earlier entry in this paragraph was written in constants `Model.Numbers` computes
    // exactly; this one is written over `bool`, whose carrier is two values, so the grid enumerates
    // it outright. The point it comes back with is `x = F`, which is the proposition itself.
    // 48 with the duplicate proposals gone, and the delta is DERIVED and is smaller than the one
    // above: of the four false rows that went, only two carried a point, and they are the two
    // weakenings of `ADD_POSITIVE`, refuted at `x = -1, y = 1` and at `x = 1, y = -1`. The other
    // two are about `POSITIVE_NOT_ZERO`, whose weakened and swapped forms conclude a **negated
    // equation**, and the sampler has no witness to hand back for one. So this figure and
    // `decidedFalse` move by two and by four on the same change, which is the split this pair of
    // counts exists to show.
    // 49 since `Magnitude`, and it is the same one row `decidedFalse` gained: the weakening of
    // `SGN_ZERO`, refuted at any non-zero point, so the sampler has a witness to hand back and
    // this figure and that one move together by one. The pair moving by the same amount is the
    // ordinary case; the paragraph above records the change where they did not, which is what
    // this pair of counts exists to show.
    // 50 with `NUM_DIVIDES_ONE`, whose weakening leaves `!d. d = SUC ZERO` and is refuted at any
    // point but one, so the pair moves together by one again, which is the ordinary case.
    // 52, moving with the bucket above as it usually does: each of the two has a witness.
    // 53, moving with the bucket above by one as it usually does: the one row that arrived is
    // decided false AND at a point, because what is left of `NUM_LE_LT_TRANS` is a comparison of
    // two naturals and `Model.Numbers` is exact there.
    // 56, moving with the bucket above by three as it usually does: every one of the three is
    // written in constants `Model.Numbers` computes exactly, and the third in no constants at all.
    // 57, with the bucket above as usual.
    // 58, with the bucket above as usual.
    // 59, with the bucket above as usual, and the monotonicity's residue is a comparison of two
    // naturals, which `Model.Numbers` is exact on.
    // 60, with the bucket above as usual.
    // 61, with the bucket above as usual: the cancellation's residue is a comparison of two
    // naturals and `Model.Numbers` is exact there, so the point comes back with the refutation.
    // 66, with the bucket above by five as usual: every one of the five residues is a comparison
    // or an equation between naturals, and `Model.Numbers` is exact on those.
    // 67 with the first analysis, and it moves by ONE where `decidedFalse` moved by two, which is
    // the split this pair exists to show and the first time the two residues of a SINGLE lemma have
    // landed either side of it. `LE_BELOW_EVERY_POSITIVE` without `0 <= x` leaves
    // `(!y. 0 < y ==> x < y) ==> x = 0`, which is false and whose hypothesis is a quantifier over
    // the reals: `Evaluate` answers nothing there, so no point can be produced and the claim is
    // decided by elimination instead. Without the epsilon condition it leaves `0 <= x ==> x = 0`,
    // which is refuted at `1` and comes back with it. Derived after the fact and not before, which
    // is worth admitting: the derivation that predicted `decidedFalse` moving by two did not
    // predict which of the two would arrive here.
    // 69 with the monotone convergence theorem's neighbourhood, and TWO of the four that arrived
    // in the bucket above rather than all four. The two weakenings, `!x y. y <= x` and
    // `!x y. y < x`, are comparisons of two arbitrary reals with no hypothesis at all: the sampler
    // takes them and finds a point. The two substitutions carry a negated hypothesis,
    // `~(x < y) ==> y < x`, which `addressOf` declines, so they are decided by elimination, which
    // settles and names no witness.
    //
    // **Written here first as 67 and unchanged**, on the reasoning that all four carry a negation
    // somewhere. Two of them do not: the weakening drops exactly the negated hypothesis, which is
    // the whole of what makes it readable. Measured at 69, and the wrong derivation is kept
    // because it is the same mistake this entry has recorded twice before, reading the family
    // rather than the residue.
    // 71 with the concatenation's two, and they are the naturals' twins of the pair two entries
    // above: `NUM_ADD_LT_CANCEL` and `NUM_LE_OF_NOT_LT` weaken to `!p m n. m < n` and
    // `!m n. n <= m`, comparisons of two arbitrary numbers with no hypothesis left, so the
    // sampler takes them and finds a point. The other eight weakenings are about `word` and are
    // unreadable, so nothing here could have found a witness in them.
    //
    // 72 with the one of `Peano`'s two that `decidedFalse` above took: `!x y z u. x + z <= y + u`
    // is a comparison of two sums of arbitrary numbers with no hypothesis left, so the sampler
    // takes it and finds a point. **Derived in advance this time**, which the entry above says was
    // not done the last time this pair moved, and derived because the entry above says why: this
    // assertion sits behind `decidedFalse` in the same test, so a red `decidedFalse` means this
    // line never runs and its silence is not evidence.
    //
    // **This entry was not derived in advance and the reason is worth more than the number.** The
    // change that moved it predicted `decidedFalse` by two and `aboutNumbers` by five, and both
    // came out; this assertion and the one at the end of the naturals' test were never consulted,
    // because an earlier assertion in the same test had already failed and ScalaTest stops there.
    // So a change that moves a count needs as many runs as the deepest test has assertions, and
    // reading the first failure as the whole of the damage is how two of these were found on a
    // second pass rather than a first. That is a different mistake from the one recorded above,
    // which was a wrong derivation; this one is a derivation that was never asked for.
    //
    // 73 with the order map, moving with `decidedFalse` by one rather than splitting from it: the
    // one residue that is false is `!m n. NUM_LE m n`, written in `NUM_LE` alone, which
    // `Model.Numbers` computes exactly, so the search finds `m = 1, n = 0`. The other two
    // residues are not false at all — one is true and one is about `int` — so neither could reach
    // this count. **And this entry was again not derived in advance**, for the third time and by
    // the mechanism the paragraph above describes in full: `decidedFalse` went red first and
    // ScalaTest stopped, so this line never ran. What found it was the second pass the paragraph
    // prescribes, which means the paragraph is being read and not acted on. A change that moves a
    // count is not finished when the suite is green once; it is finished when it has been green
    // after a run in which every assertion behind the moved one executed.
    // 74 with the ONE weakening the Cauchy product's finite half brings, moving with
    // `decidedFalse` rather than splitting from it, for the reason that entry gives:
    // `!m n. NUM_SUB (SUC m) n = SUC (NUM_SUB m n)` is written in `NUM_SUB` and `SUC` alone, both
    // of which `Model.Numbers` computes exactly, so the search finds `m = 0, n = 1`.
    //
    // **The mechanism was derived in advance and this number was not**, which is the distinction
    // the paragraph above is really asking for and which is worth separating from its complaint:
    // the single false residue and why the sampler can refute it were both written down while
    // `decidedFalse` was being moved, and this line still went red on the next run, because
    // deriving what moves a count is not the same as editing every count it moves. That is the
    // fourth time, and what the paragraph prescribes — a second pass in which every assertion
    // behind the moved one executes — is what found it again.
    // 75, moving with `decidedFalse` and by the same single residue: `!n i. NUM_LE i n` is
    // written in `NUM_LE` alone and the sampler finds `i = 1, n = 0`. **Edited in the same pass
    // as `decidedFalse` this time**, which is what the paragraph above has asked for four times
    // and did not get; what was still missing on the run before this one was the two rows below
    // and above it, not this one.
    // 76, moving with `decidedFalse` and by the same single residue, the one on `num`.
    // 77, moving with `decidedFalse` by the logarithm's one false residue, `!x y. x = y`, which the
    // search refutes at two distinct reals. **Not moved in the same pass as `decidedFalse`**, and
    // found the way the paragraph above says it is found: the next run, in which this line ran.
    // 78 with resolution's one false residue, `!k v s inputs m. 0 < m`, refuted at `m = 0`. **Not
    // moved in the same pass as `decidedFalse` either**, and found the same way, on the second run.
    // 79 with the valuation's one false residue, the same as `decidedFalse`'s, which carries the
    // point `x = 4, y = 8`. Moved in the same pass as `decidedFalse`, from the same probe.
    withAPoint shouldBe 79
  }

  it should "leave the rest in the two buckets that mean different things" in {
    // `Open` is a proposal no procedure here settles: it might be true and might be false and the
    // system says neither. `Unreadable` is a proposal about a shape no procedure can take, which is
    // a different fact and is kept apart for the reason `Refutation` keeps seven outcomes apart.
    //
    // The counts moved on 2026-09-11 and the direction is the finding: `Open` rose from 16 to 19 and
    // `Unreadable` fell from 6 to 3, by exactly three. `Prove` now asks its library before it asks a
    // procedure and the negation-free propositional fragment has an address, so three proposals that
    // were a shape nobody could take are now ones somebody attempted and did not settle. That is a
    // different and more informative answer, and the two buckets are still counted apart.
    val open = findings.count(_.standing.contains(Novelty.Standing.Open))
    val unreadable = findings.count(_.standing.contains(Novelty.Standing.Unreadable))

    // The subject the address is read on, asserted rather than left to a reading, because this
    // is where the fourth wrong prediction was made and an address is not visible in a count.
    // `Novelty.of` asks `addressOf` of the whole claim: a weakening of a lemma with antecedents
    // is an implication whatever its conclusion is about, so it has a propositional address even
    // where nothing can read one word of it. A residue that arrived at `Nobody` here would mean
    // the propositional route had stopped taking implications, which is a different defect from
    // any count moving and is invisible to every other assertion in this file.
    def addresses(name: String): Vector[Prove.Address] =
      findings.filter(_.proposal.from == name).flatMap(_.reading).map(_.address)

    //
    // **The two Cauchy products left that address on 2026-09-25, and the paragraph above is why
    // they could.** A weakening is addressed by its conclusion under its antecedents, and theirs
    // is a convergence of a series, which `Prove.Address.Series` reads before the propositional
    // fallback is asked. The standing is unchanged, `Open`, because the series procedure cannot
    // read a convolution of two unknown sequences; what changed is who was asked, and it is now
    // the procedure whose question it is. `CONVERGES_TO_ZERO`'s residues conclude a convergence
    // of a sequence that is not a series, so they stay where they were.
    addresses("SUM_CAUCHY_PRODUCT_NONNEG") shouldBe Vector.fill(4)(Prove.Address.Series)
    addresses("SUM_CAUCHY_PRODUCT") shouldBe Vector.fill(4)(Prove.Address.Series)
    addresses("CONVERGES_TO_ZERO") shouldBe Vector.fill(2)(Prove.Address.Propositional)

    // And the one that is **not** propositional, which is where the fifth wrong prediction was
    // made. `SUM_TAIL_ABS` has a single antecedent, so its residue is an order between two reals
    // rather than an implication, and `Linarith` takes that shape and fails on it. `Nobody` here
    // would mean the order fragment had stopped recognising its own goals.
    addresses("SUM_TAIL_ABS") shouldBe Vector(Prove.Address.Order)

    // `SUM_ABS` carries no antecedent, so it produces no weakening and nothing to address.
    addresses("SUM_ABS") shouldBe empty
    // **Two**, not one: the weakening that drops `abs x <= c`, and the substitution that puts
    // `real_lt` where `real_le` stands. Both are orders between two reals, so both are `Order`,
    // and the second is the one the prediction for this lemma forgot.
    addresses("ABS_POWER_LE") shouldBe Vector.fill(2)(Prove.Address.Order)

    // The third address, and the one that arrives with the addition theorem: an equation
    // between reals is `Ring`'s shape, and `Ring` failing on it is what `Open` means here.
    addresses("MUL_INV_COMBINE") shouldBe Vector.fill(5)(Prove.Address.Equation)
    addresses("EXP_ADD") shouldBe Vector.fill(2)(Prove.Address.Equation)

    // And `EXP_CONVOLUTION` produces nothing at all: no antecedent to weaken, and a body that
    // is a `Sum` of a lambda, which `swapped` refuses.
    addresses("EXP_CONVOLUTION") shouldBe empty

    // 37 since the laws of exponents landed. `POWER_ADD` has no hypothesis, so it adds no
    // weakening; what it adds is one substitution, `Power x (NUM_ADD y z) = Power x y + Power x z`.
    // `POWER_MUL` adds nothing at all: no hypothesis to drop, and no `+`, `*`, `<` or `le` in it for
    // the substitution source to swap.
    //
    // The number did not move when the model learned the naturals later the same day, and that is
    // the right answer rather than a disappointment: `Open` is decided by what a **procedure** can
    // settle, and no procedure here reads `num`. What changed is the next assertion, which is that
    // these now carry the point where they fail.
    // 43 since the embedding learned the order. The six that arrived are the weakenings and swaps
    // of `NUM_REAL_NONNEG`, `NUM_REAL_LE` and `NUM_REAL_LT`, and every one of them is a claim about
    // `real_of_num`, which no procedure here reads and the sampler now refutes with a point.
    //
    // 44 since the truncated difference, and the one that arrived is `NUM_REAL_SUB` with its bound
    // dropped: `!x y. real_of_num (NUM_SUB x y) = real_of_num x - real_of_num y`, which is false at
    // `x = ZERO, y = SUC ZERO` and is not refuted here. The sampler has no value for `NUM_SUB`, so
    // the left side has no value, so no point answers; what settles it `Open` rather than
    // `Unreadable` is that the claim is about `real_of_num` and a procedure over the reals will
    // take that shape and fail to close it. The next assertion is where the other two went.
    //
    // 45 with the order principles, and the one that arrived is `NUM_GREATEST` with its hypotheses
    // dropped: `!P. ?m. P m /\ (!k. P k ==> NUM_LE k m)`, which is false at the predicate that
    // holds everywhere and is not refuted here. It quantifies over a **predicate**, so the sampler
    // has nothing to instantiate `P` with; what settles it `Open` rather than `Unreadable` is the
    // `NUM_LE` in it, which a procedure over the chain will take and fail to close.
    //
    // 64 when the five developments joined the chain on 2026-09-12, and the nineteen that arrived
    // split nine to `Divisibility` and ten to `Modular`. Every one of them still carries the
    // relation it is about in a **hypothesis** while the conclusion is arithmetic a procedure
    // reads, or is a substitution that left the conclusion arithmetic: `Divides x y ==> Divides x z`
    // and `NUM_CONG x y z ==> NUM_CONG x (NUM_ADD y u) (NUM_ADD z v)` are the two shapes. That is
    // the same line the bucket has always drawn, and the nineteen that went the other way are in
    // the assertion below.
    //
    // 73 on 2026-09-12 with the quotient, the remainder, Bezout and Euclid. Nine of the twelve
    // weakenings land here and the line is the same one this bucket has always drawn: each keeps a
    // constant nothing interprets in a hypothesis or inside an arithmetic conclusion a procedure
    // over the chain will take and fail to close. Of the other three, one is decided false above
    // and two carry a `NUM_DIVIDES` in the conclusion itself, which is the bucket below.
    // 75 with the two division-bound lemmas, whose weakenings both keep a `NUM_DIV` or a `NUM_MOD`
    // in the conclusion after the bound is dropped, so both land here for the reason this bucket
    // has always drawn its line: a constant nothing interprets, inside something a procedure over
    // the chain will take and fail to close.
    //
    // **78 with the matrices**, and the three are `MAT_DET_MAT2`, `MAT_DET_SMUL` and `MAT_DET_MUL`
    // under operator substitution. The determinant is the only matrix operation whose value is a
    // real, so it is the only one whose substituted form is an arithmetic claim at all; the other
    // twenty-one matrix facts produce nothing here, having no hypothesis to weaken and no real
    // arithmetic to swap. The delta is derivable from what arrived, which is the only reason it
    // was set from a single run rather than investigated.
    //
    // **79 with the bounded sum congruence.** The `SUM_CONGRUENCE_BELOW` weakening keeps a `Sum`
    // in the conclusion once the bounded agreement is dropped, which is this bucket's line. The
    // `NUM_LT_TRANS` weakening is decided above and does not reach here, so that branch's delta is
    // +1 and not +2, and the two branches' deltas add here because they draw on disjoint lemmas.
    // **79 still with the bounded partial sum at the naturals, and the prediction that it would be
    // 80 was wrong in a way worth keeping.** `NUM_SUM_CONGRUENCE_BELOW` weakened is
    // `!f g n. NUM_SUM f n = NUM_SUM g n`, which reads like the `Sum` entry above and lands in the
    // other bucket. The difference is the TYPE of the equation rather than the unread constant in
    // it: `Sum f n = Sum g n` is an equation between reals, so the arithmetic procedures take the
    // shape and fail to decide it, which is what `Open` means; this one is between naturals, where
    // `Peano`'s own docstring says there is no decision procedure at all, so nothing takes it.
    // **91 with the floor and the ceiling, and the delta is DERIVED and is the whole of what they
    // added.** Twelve proposals arrive: four weakenings, one per lemma, and eight substitutions --
    // `NUM_FLOOR_LE` and `NUM_CEIL_LE` write only `<=`, so one swap each, while `NUM_FLOOR_LT` and
    // `NUM_CEIL_LT` write `<=`, `<` and `+`, so three each. All twelve land HERE and nowhere else,
    // which is the expected shape rather than a surprise: every one of them is a claim about
    // `NUM_FLOOR` or `NUM_CEIL`, and no procedure in this repository has a reading of either, so
    // nothing can decide them and nothing can refute them at a point.
    // **109 since `Magnitude`, and the delta is eighteen of the twenty-three it added.** Of its six
    // weakenings one is refuted at a point and lands above; the other five, and every one of the
    // substitutions, name `abs`, `max`, `min` or `sgn`, and no procedure in this repository has a
    // reading of any of the four. So they cannot be decided and cannot be refuted at a point,
    // which is the same shape the floor and the ceiling produced and for the same reason.
    // **110 since `Coding`, and the delta is one of its two weakenings and not both**, which is
    // the part worth measuring rather than deriving. Dropping the premise of `NUM_CRT_PAIR` leaves
    // `!m n a b. ?x. NUM_CONG m x a /\ NUM_CONG n x b`, which is false and which nothing here can
    // refute at a point, so it is attempted and not settled and lands HERE. Dropping the premise of
    // `NUM_FACT_DIVIDES` leaves `!d k. NUM_DIVIDES d (NUM_FACT k)`, also false, and that one is
    // `Unreadable`: no procedure takes its shape at all. Two claims equally false and equally
    // unrefuted, in two different buckets, which is what the two buckets are for.
    // 111, and again one of the three rather than all of them, measured rather than derived.
    // Dropping `NUM_GCD a b = SUC ZERO` leaves a claim about divisibility that a procedure attempts
    // and does not settle; dropping either of the other two leaves one whose shape nothing takes.
    // 112 with `POWER_MULTIPLICATIVE`, and this one is DERIVED and then measured. The three
    // lemmas that landed with it produce ONE proposal between them and it is a substitution:
    // swapping `*` for `+` in `Power (x * y) z = Power x z * Power y z` gives
    // `Power (x + y) z = Power x z + Power y z`, which is false. It lands HERE rather than in
    // `unreadable` for the reason that lemma exists at all: `Ring` normalises over ATOMS, an atom
    // being a term it has decided not to look inside, and a power at a VARIABLE exponent is one.
    // So the two sides are distinct atoms no ring identity relates, which is a shape a procedure
    // takes and cannot settle. The other two contribute nothing,
    // because neither is in `mutable`.
    // 114 with both weakenings of `NUM_CONG_DIVISOR`, and it is the first addition whose two land
    // TOGETHER here rather than splitting between this bucket and another. A congruence is an
    // existential over two witnesses, so the grid cannot settle either by evaluating: both are
    // attempted and neither is refuted at a point.
    // 120 with six of the seven the Chinese remainder theorem brought, and the seventh is in the
    // bucket below. **The split is inside ONE lemma**, which no earlier addition here has shown:
    // `NUM_CRT`'s two weakenings have the SAME conclusion and land in the two different buckets,
    // so what decides it is the premise that SURVIVES and not the claim being made. Dropping the
    // pairwise premise leaves the positivity one and is attempted; dropping positivity leaves the
    // pairwise one, quantified over two indices at once, and nothing takes that shape.
    //
    // Worth writing down because the derivation that put all seven here was made from the comment
    // below, which says a residue naming `NUM_GCD` lands there, and five of these name `NUM_GCD`
    // and are here. That comment is true of the residues it was written about and is not a
    // criterion; the criterion is `Novelty.Standing` and it is only ever read by running.
    // 122 with both weakenings of `NUM_MOD_OF_CONG`, landing together here the way
    // `NUM_CONG_DIVISOR`'s pair did: what is left of each is a claim about a remainder and a
    // congruence, and no procedure settles either. Dropping the congruence leaves `NUM_MOD y x = z`
    // for every `z` below `x`, dropping the bound leaves it for a congruence that need not be
    // reduced; both are false and neither is refuted.
    // 126 with four of the five, and the fifth is in the bucket below. **The split is the one
    // `NUM_CRT` showed earlier the same day and it is the same criterion**: what decides it is the
    // premise that SURVIVES, not the conclusion. All five residues conclude something about
    // `NUM_TERM` and `NUM_CODE`, which nothing interprets. The four here still carry an
    // implication, `NUM_TERM y ==> ...`, so a procedure takes the shape and does not settle it; the
    // fifth has nothing left on the left of an arrow and nothing takes it at all.
    //
    // Derived as five in the bucket below, from the conclusion naming constants no model reads.
    // That was the wrong half of the residue to look at, and this file had already recorded which
    // half is the right one.
    // 130 with four of the formula predicate's six, and DERIVED CORRECTLY this time by asking
    // which premise survives rather than what the conclusion names. The four that keep an
    // implication are the two weakenings each of the equality and the implication; the two that do
    // not are below. Two additions in a row got this wrong by reading the conclusion, and the third
    // got it right by reading the comment those two left.
    // 132 with both of them, derived by the surviving premise and right again: each residue keeps
    // one implication, so a procedure takes the shape and does not settle it.
    // 134 with its two, by the surviving premise again.
    // 152 with eighteen of the logical axioms' twenty-one, and the three that went elsewhere are
    // what refine the rule this file keeps restating. "What decides the bucket is the premise that
    // SURVIVES" is right and is not enough: two of the three have NOTHING surviving, which the rule
    // as written predicts, and the third is `NUM_LOGIC_VACUOUS` losing `NUM_FORM p` and KEEPING
    // `~(NUM_FREE_FORM i p)`. An implication survives there and it is still unreadable, because
    // what a procedure takes is a shape, and a negated premise is not one it takes. Its own sibling
    // is the control: dropping the freeness condition instead leaves `NUM_FORM p ==> ...` and lands
    // here. So the rule is the surviving premise AND whether anything takes its shape, and it took
    // a pair of siblings splitting to see the second half.
    //
    // Derived as twenty-one unreadable, from the conclusions naming `NUM_LOGIC`. That is the
    // conclusion-reading error this file has recorded three times, made a fourth time.
    // 155 with the shift lemma's three. Each drops one of three premises and keeps two, and one
    // of the two kept is always an order or an equation the procedures take the shape of.
    // 157 with the closure lemma's two. Each drops one of `NUM_PROV (p ==> q)` and `NUM_PROV p` and
    // keeps the other, so an implication survives whose premise is a predicate applied to a code,
    // and that is a shape a procedure takes even though nothing here can settle it. The control is
    // in the entry above: what lands in `unreadable` instead is a surviving premise nothing takes
    // the shape of, a negation, and neither of these is one.
    // 162 with the syllogism's five. Dropping any one of its five premises leaves four standing,
    // so an implication survives every time, and what survives is a `NUM_FORM` or a `NUM_PROV`
    // applied to a code, which is a shape a procedure takes even though nothing here settles it.
    // 163 with the prime-factor lemma's, and it is worth more than the number. It was DERIVED as
    // `unreadable` and measured here, from the rule this file keeps restating: the single premise
    // is dropped, so nothing survives on the left of an arrow, which is the shape the entries above
    // say lands there. That derivation was wrong, and the reason is that the rule is a shadow of
    // the real criterion rather than the criterion. What decides the bucket is `Prove.addressOf`:
    // it strips EVERY antecedent, asks whether the conclusion is an order or an equation between
    // reals, and where nothing answers it asks whether the minimal propositional fragment can read
    // the goal at all. Here the residue `!n. ?p. NUM_PRIME p /\ NUM_DIVIDES p n` is read
    // propositionally, so the address is not `Nobody` and the standing is `Open`.
    //
    // The surviving-premise rule is a good predictor and is not the rule. This is the fourth
    // reading error recorded in this file and the first where the rule itself, rather than a
    // careless application of it, is what misled.
    // 172 with nine of the deduction theorem's twelve, and **the split was derived before it was
    // measured**, which is the first time that has worked on this pair of buckets. The rule used is
    // the one the entry below records: what decides the address is `Prove.addressOf`, which strips
    // every antecedent and, where nothing answers the conclusion, asks whether the minimal
    // propositional fragment reads the whole goal. It declines a goal containing a negation.
    //
    // `NUM_PROV_IMP_GEN` carries `~(NUM_FREE_FORM i h)`. Three of its four residues still carry that
    // negation and land in `unreadable`; the fourth drops the negation itself and is read, so it
    // lands here. Weakening's three and the modus ponens rule's five carry no negation and are all
    // here. Nine and three, derived and then measured.
    // 173 with one of the deduction theorem's three, by the same rule as the entry above: two of
    // the three residues keep `!i. ~(NUM_FREE_FORM i h)` and so contain a negation, and the third
    // drops it. One and two, derived and then measured, which is now the second time.
    // 179 with the first analysis, and this is where six of its eight proposals land. Five are
    // weakenings whose residue names `converges` or `lim`: the sampler has no reading of either, so
    // nothing refutes them, and no procedure proves them. The sixth is the first SUBSTITUTION this
    // bucket has taken from a new development, `cosh x * sinh x = exp x` from `COSH_PLUS_SINH` with
    // `+` swapped for `*`, which is false and unrefutable for the same reason: `cosh` denotes and
    // the model cannot compute it.
    //
    // None of the six contains a negation, so `addressOf` reads every one of them and the split
    // this bucket is about does not arise. Six and zero, derived and then measured, which is the
    // third time.
    //
    // 183 with the four weakenings of `NUM_PROV_SPECIALISE`, and this bucket taking all four was
    // derived against the alternative rather than assumed: the residues differ only in which
    // condition is missing, and each has the same conclusion, `NUM_PROV (NUM_SUBST_FORM i t p)`.
    // That is an atom the model cannot compute, so nothing refutes it, and it carries no negation,
    // so `addressOf` reads it. The candidate written down beside this one was that an atomic
    // `NUM_PROV` would be declined the way a negation is and the four would land in `unreadable`;
    // that was measured and is false, and `unreadable` did not move.
    //
    // 184 with ONE of the idleness lemma's two weakenings, and the split between them is the
    // whole content of this pair of buckets. Both residues have the SAME conclusion once the
    // antecedents are stripped, `NUM_SUBST_TERM i t s = s`, so a reading that looked only at the
    // conclusion would have to put them in one bucket; they are in different ones. The one that
    // keeps `NUM_TERM s` is here and the one that keeps `~(NUM_FREE_TERM i s)` is `unreadable`
    // below, which says the propositional fragment reads the WHOLE goal and declines a negation
    // wherever it stands, antecedent included. Derived as two in this bucket and measured as one,
    // and the second was found by printing the standings rather than by the suite, because the
    // assertion below aborts on this one first and its own move was masked.
    // 187 with the monotone convergence theorem's three: the weakening of `MONOTONE_LE`, which is
    // `!s m n. NUM_LE m n ==> s m <= s n` and false of a sequence that decreases, and the two of
    // `MONOTONE_CONVERGES`, each missing one of its two hypotheses. All three quantify over a
    // SEQUENCE, and no model here interprets a function variable, so nothing refutes them; none
    // carries a negation, so `addressOf` reads them. Three and zero, derived and then measured.
    //
    // 205 with all EIGHTEEN weakenings of the three equality rules, and the pair below is why
    // that was derived rather than assumed after the last round got it wrong. Every residue
    // concludes `NUM_PROV` of a code, which the model cannot compute, so none is refutable; and
    // not one of the eighteen antecedents is a negation, so `addressOf` reads every one of them.
    // The bucket below does not move, which is the measurement that says the negation is what
    // sends a residue there and not the shape of the conclusion.
    //
    // 215 with ten of the eleven, and the eleventh is the sharpest thing this pair of buckets has
    // shown. It is `NUM_CLOSED_SUC`'s only weakening, `!s. NUM_CLOSED (NUM_CODE 2 s)`, and it goes
    // to `unreadable` while `NUM_CLOSED_ADD`'s two stay here. The three conclude the same SHAPE,
    // `NUM_CLOSED` of a code, and differ in one thing: the successor's rule has a single
    // hypothesis, so dropping it leaves a residue with no antecedent at all, where the sum's rule
    // has two and its residues keep one. Derived as eleven here and measured as ten, and the
    // eleventh was found by printing the standings rather than by the suite.
    //
    // 216 with ONE of the four new residues, and the other three are in `unreadable` below. It is
    // the same rule as the two times before, seen now on a third sample: the residue that stays
    // here is `NUM_PRIME_POW_CANCEL`'s, the one that drops `~(NUM_DIVIDES p x)`, which is the only
    // one of the four that neither carries a negation among its antecedents nor is left with no
    // antecedent at all. The negative half holds too: the weakened power's positivity is FALSE at
    // `m = ZERO` and the model can compute it, and yet `decidedFalse` does not move, because a
    // refutation goes THROUGH the address and an unreadable residue never reaches the sampler.
    // 220 with the four of `Inductive` and `Reaching` that land here. Measured, not derived: which
    // bucket a residue lands in depends on whether a procedure has an address for its shape, which
    // is not a property of the lemma the hypothesis was dropped from.
    // 225 with TWO of the three the algebra of limits brought, and the third is in `unreadable`
    // below. Measured and NOT derived, for the reason the entry above gives about the four of
    // `Inductive` and `Reaching`: which bucket a residue lands in turns on whether a procedure has
    // an address for its shape, which is a fact about the procedures and not about the lemma the
    // hypothesis came off. The count of the residues themselves was derivable and was derived,
    // three, and it is the split of those three that was not; keeping the two apart is the whole
    // reason this row says which half was predicted.
    // 235 with TEN of the eleven, and the eleventh is the rule this pair of buckets has now shown
    // three times rather than a new fact. It is `NUM_FORM_EXISTS`'s only weakening,
    // `!i p. NUM_FORM (NUM_EXISTS i p)`, and it goes to `unreadable` because dropping the single
    // hypothesis of a single-hypothesis rule leaves a residue with no antecedent at all. The
    // `NUM_CLOSED_SUC` entry above says exactly that about exactly that shape, and it was not
    // applied here in advance: this ten was read off the run, and the entry above is what makes it
    // unsurprising afterwards rather than what predicted it.
    // 236 with ONE of the four the right forward closure brought, and the other three are in
    // `unreadable` below. **Measured and not derived**, for the reason this row has now given four
    // times: which bucket a residue lands in turns on whether a procedure has an address for its
    // shape, and no procedure here has a reading of `word`. The count of the residues was
    // derivable and was derived, four; the split of those four was not, and saying which half was
    // predicted is the whole point of writing the row rather than the delta.
    //
    // That three of four are unreadable is the expected direction rather than a surprise, and it
    // is worth one line because it will be true of every development over `word` that follows:
    // this repository's procedures decide fragments of the reals and of the naturals, so a residue
    // whose atoms are `WORD_RFC` and `WORD_STEP` has no address to go to. The bucket is doing what
    // it is for, which is saying "nobody here can take this shape" rather than reporting it clean.
    // 240 with ALL FOUR of the two limit bounds'. **Measured and not derived**, for the reason
    // this row has now given five times, and this time the measurement went the other way from the
    // analysis entry three rows up: two of the three residues of the algebra of limits landed here
    // and the third did not, so a fifty-fifty prediction for these four would have been a guess
    // dressed as a derivation. What is derivable is that there are four of them, which the
    // weakenings figure derives; where they land is a fact about the procedures. `unreadable` does
    // not move at all, so nothing here was left with no address, and `decidedFalse` does not move
    // either: the residues are false, and refuting one means computing `converges`, which the
    // model has no interpretation of.
    // 250, and ten of the fourteen belong to the factorisation merge `627ceec`, which left this
    // figure at 236 while adding eleven weakenings: ten of those eleven land here and one does
    // not, measured after the failure and not derived, for the reason this row has now given six
    // times. The four that are this session's are the limit bounds', and they all land here.
    // 256 with ALL SIX the order gained on 2026-09-18, and the six are two kinds: four weakenings,
    // one per hypothesis of `LE_MUL_BOTH` and `INV_ANTITONE`, and two substitutions, which are the
    // matched pair `RediscoverySpec` reports. **The count of six was derivable and the split was
    // not**, which is the distinction this row has now drawn seven times: `decidedFalse` does not
    // move and `unreadable` does not move either, both measured after the run. That the residues
    // have an address was the likely half -- they are order claims over real atoms, which is what
    // the procedures read -- and that not one of them is refuted at a point was not: dropping
    // `0 <= c` from `LE_MUL_BOTH` leaves a claim false at any negative multiplier, and the sampler
    // did not find one.
    // 269, which is the same thirteen: every weakening of the three new facts with hypotheses is a
    // claim about the object language's codes, and no procedure here has a reading of `NUM_PROV`,
    // so each lands open rather than decided. A bucket that had taken any of them would be saying
    // it can decide provability in PA.
    // 279 with **ten** of the integers' seventeen, and the split is the half that was not
    // derived, which is the distinction this row has now drawn eight times. The seventeen were
    // predicted and met; where they land was not predicted and is read off the run. Seven go
    // somewhere other than here, and a reader wanting to know which has to ask the buckets
    // rather than this line. Asked, they answer: the other seven are `unreadable`, which is
    // the assertion further down, and the two buckets together take all seventeen with nothing
    // refuted and nothing earned. What is not surprising is that ten stay open: a weakening of
    // a claim about `int` is a claim about a type no procedure in this repository reads,
    // exactly as the thirteen above are claims about `NUM_PROV`.
    // 281 with **two** of the bridge's three, and this row can say which for once without the
    // hedge: the count of three was derived before the run, one weakening and two
    // substitutions, and the split was measured. Both substitutions land here. They are
    // `INT_REAL_ADD` and `INT_REAL_MUL` with the operator swapped, so each is an equation
    // between **reals** with `real_of_int a` as an atom, which is a shape the procedures do
    // have an address for: attempted and not settled is the honest answer and is what `Open`
    // means. The third goes to `unreadable` and the line there says why.
    // 282 with ONE of the order map's three, and the pair of new facts SPLITS across all three
    // buckets, one residue each, which is what makes this row worth reading rather than
    // subtracting. Here is `NUM_REAL_LE_BACK` with `real_le` swapped for `real_lt`, which leaves
    // `!m n. real_of_num m < real_of_num n ==> NUM_LE m n`. That claim is **true**, so nothing
    // refutes it, and it is an implication between an order on reals and an order on `num`, which
    // is a shape the procedures take and do not settle. Attempted and not settled, which is what
    // this bucket means and is a different answer from the one below.
    // 283 with the ONE residue `exp 1 > 2` produces, 2026-09-20. `EXP_ONE_ABOVE_TWO` swapped is
    // `2 <= exp 1`, which is **true**, so nothing refutes it, and `exp 1` is a constant no
    // procedure here has a value or a bound for, so nothing settles it either. Attempted and not
    // settled, which is what this bucket means. The lemma that landed with it, `NUM_POW_LE_FACT`,
    // writes none of the four operators the swap exchanges and produces no residue at all, which
    // is the same split `RediscoverySpec`'s mutable count draws on the same pair.
    // 288 with **all five** residues the three `abs` facts produce, 2026-09-20, and the split is
    // the half that was derived here rather than read off the run: two weakenings and three
    // substitutions, and every one of them lands in this bucket. The reason is one fact about the
    // model rather than five: **nothing interprets `abs`**, so a claim about it is a claim the
    // sampler cannot evaluate at any point, and `Evaluate` answering nothing is not a refutation.
    // `abs x = x` with the sign dropped is **false**, and it is here rather than among the
    // disproved for exactly that reason, which is the distinction `docs/adr/0005` keeps seven
    // answers apart for.
    // 290 with the two residues `CONVERGES_MUL` produces, 2026-09-20; 292 with two of the three
    // the tail facts bring, 2026-09-21; 293 with the bounded monotone's one, the same day.
    //
    // **Three predictions about which of these two buckets a residue lands in were made over
    // those three days and all three were wrong, and the account they were made on is corrected
    // here rather than beside each row.** It was that the split turns on what the MODEL reads:
    // `converges` is interpreted nowhere, so a claim about it cannot be evaluated, so it is not
    // refuted. Every word of that is true and none of it decides this bucket. `Novelty` does, in
    // four lines: an `Unsettled` report is `Unreadable` where the address is
    // `Prove.Address.Nobody` and `Open` otherwise. The question is whether any procedure
    // **recognised the shape**, and the model does not come into it at all.
    //
    // So `!f g n. Sum f n <= Sum g n` is here, because an order between two reals is a shape the
    // procedures take and then fail on, while `!f l. (!i. 0 <= f i) ==> !n. Sum f n <= l` is
    // below, because nothing addresses it. Read that way the three rows agree and need no story
    // about sequences or function variables.
    //
    // The criterion was written down before any of the three guesses: the bucket below opens by
    // saying "nobody here can take this shape", which is the address and nothing else. What the
    // three cost was not the numbers, which the suite catches, but three comments recording a
    // mechanism that is not the mechanism, in the place the next session reads.
    // 298 with the FIVE of the six that are about `Sum`, 2026-09-21, and **this is the first
    // entry in this file predicted right**, by the criterion the correction above states: the
    // question is the ADDRESS. An order between two partial sums is a shape the procedures take
    // and fail on, so all five land here; the sixth is arithmetic on `num` and is decided. Three
    // earlier guesses on this row used the model instead and were wrong three times.
    //
    // 302 with the Cauchy product's four, 2026-09-21. **The prediction was `unreadable` and was
    // wrong**, the fourth miss on this one split, and the miss is worth more than the number
    // because the reading that produced it was the corrected criterion applied to the wrong
    // term. The address criterion was right; what was fed to it was the claim's CONCLUSION,
    // `converges (Sum c) (A * B)`, which nothing does recognise. `Novelty.of` reads
    // `cost.prove.addressOf` on the WHOLE claim, and a weakening of this lemma is an
    // implication, which the propositional address takes.
    //
    // That is measured rather than reasoned, and the assertion below is the measurement kept:
    // all four are `Propositional`. So the three earlier guesses failed on the criterion and
    // this one failed on the subject, which is the distinction the correction above could not
    // have carried because it had not been met yet.
    // 309 with all seven of the general Cauchy product's residues, 2026-09-21, and the
    // prediction was **308**, wrong by one for the fifth time on this one split. What was
    // predicted: six, on the ground that a residue of a lemma with one antecedent is not an
    // implication and so has no propositional address. What happened: `SUM_TAIL_ABS`'s single
    // residue is here too, at the address **`Order`** — measured, not reasoned, and asserted
    // below so nobody has to reason about it again.
    //
    // The correction is not a new mechanism, which is what makes this miss worth a line rather
    // than a paragraph: the row four hundred lines above already says that an order between two
    // reals is a shape the procedures take and then fail on. Two wrong predictions in one day,
    // and both were the address criterion applied to the wrong thing rather than the wrong
    // criterion. The remedy is the assertion, not another account.
    // 311 with `ABS_POWER_LE`'s **two** residues, 2026-09-21, and the prediction was 310. The
    // address was predicted right and measured right, `Order` for both; what the prediction got
    // wrong is the population. This bucket is over every proposal, and a lemma with one
    // antecedent that also writes `real_le` produces a weakening **and** a substitution. The
    // weakenings row four hundred lines above moved by one and this one by two, which is the
    // same difference `RediscoverySpec`'s `mutable` row draws and which the prediction read as
    // one number.
    // 315 with four: two weakenings and two substitutions, every one of them an order between
    // two reals and so at address `Order`. The population was counted this time, which is what
    // the row above got wrong.
    // 322 with the addition theorem's seven, 2026-09-21: `MUL_INV_COMBINE`'s four weakenings and
    // one substitution, and `EXP_ADD`'s two substitutions. All seven are here, and the address
    // is a **third** one — `Equation`, after `Propositional` and `Order` — because all seven are
    // equations between reals and `Ring` takes that shape and fails on it.
    //
    // What was hedged rather than predicted is the only thing worth recording: these are the
    // first residues in five commits that write neither `abs` nor `converges`, so unlike those
    // the model can evaluate them, and dropping `fu * iu = 1` leaves something false. None of
    // the seven was refuted. The hedge was that some would be; it is measured and it was not.
    // 324 with one substitution each from the two hyperbolic facts, both at `Equation`.
    // 325 with the list interface, 2026-09-23. The two weakenings it adds produce **one**
    // residue here and one in `unreadable`, which is the pair of buckets doing what it is
    // for rather than a prediction met: what was predicted before the run was two here, on
    // the reading that a claim about `word('a)` is one no procedure addresses and no model
    // interprets. That reading is right about the constants and does not decide between
    // these two buckets, which is the correction the three rows above this one already
    // carry about a different pair.
    // 335 with the square root, 2026-09-24, and this one was read off the run and NOT derived:
    // ten more residues, against its four weakenings and the substitutions of its three mutable
    // facts, and which of those land here rather than in the other buckets was not measured.
    // 336 with the irrationality of the root of two, whose one weakening lands here; read off the
    // run like the row above it.
    // 338 with the trigonometric identity's change, the same day, read off the run and NOT derived
    // before it: the two are `SIN_COS_SQUARED`'s substitutions, equations between reals that `Ring`
    // takes and fails on, as `EXP_ADD`'s did. `CONVERGES_SHIFT`'s weakening is in `unreadable`
    // below, which is what accounted for the pair once that row had run.
    // 342 with the intermediate value theorem's four weakenings, the same day, read off the run:
    // each drops one antecedent and leaves an order between reals under the others, a shape
    // `Order` addresses and does not settle, so all four land here and `unreadable` below does
    // not move. That row sat behind this one again; it was predicted from this one before it ran,
    // and the run that reached it agreed.
    // 365 with twenty-three of the logarithm's twenty-five residues, read off a probe of
    // `Propose.audit` and not predicted. Several are TRUE and unproved rather than doubtful:
    // `!x. 1 + x <= exp x` and `!x. 0 <= exp x` are two, and that is this bucket's meaning, a claim
    // a procedure addressed and did not settle, not a claim believed false.
    // 374 with nine of the extreme value theorem's ten weakenings, 2026-09-25, read off a probe of
    // `Propose.audit` filtered by `from` and not predicted: every one keeps an implication and so
    // sits at the propositional address, which takes it and does not settle it. The tenth is in
    // `unreadable` below. The run that found this row red was the first to reach it; the probe is
    // what said where the other one went, since the row below had not run.
    // 387 with the convergence criteria, 2026-09-25, measured by a probe of `Propose.audit` before
    // this line was edited: twelve of their fifteen residues conclude a convergence or a divergence
    // of a series and land here through `Prove.Address.Series`, and the thirteenth is an OLD
    // residue, `CONVERGES_ABSOLUTE`'s `!f l. ?z. converges (Sum f) z`, which had no address until
    // that one existed and so moves here from `unreadable` below.
    // 392 with five of the polynomial-times-geometric criteria's six residues, 2026-09-25, measured
    // by the same probe of `Propose.audit`. The four about series land at `Prove.Address.Series` as
    // predicted; the fifth is `POWER_NONNEG`'s `!x n. 0 <= Power x n`, which **was predicted to be
    // refuted here and is not**: it is false at `x = -1, n = 1`, the audit's search does not find
    // that point, and it lands at the order's address, taken and not settled. The sampler over the
    // naturals' model does find it, and `after` below is where that shows.
    // 393 with one of resolution's nineteen, read off the run and not identified. Tip plus this
    // branch's delta, and the delta was measured on the tree before the extreme value theorem.
    // 405 with twelve of the derivative's thirteen weakenings, the same day, read off a probe of
    // `Propose.audit` filtered by `from`: the four of each interior lemma and the four of `ROLLE`,
    // each an implication with an antecedent gone, taken at the propositional address and not
    // settled. The thirteenth, `DERIVATIVE_NEG`'s, is in `unreadable` below, and the probe is what
    // placed it, since that row sits behind this one. Tip plus this branch's delta.
    // 433 with the closed terms' twenty-nine residues less one, tip plus this delta, 2026-09-25, derived before the
    // run that reached this row: every residue of the three new congruences, of `NUM_PROV_VALUE`
    // and of `NUM_PROV_TRUE_EQ` keeps at least one implication, so it sits at the propositional
    // address, which takes it and does not settle it. The one missing is `NUM_PROV_REFL`'s, which
    // has nothing left to imply and is predicted in `unreadable` below.
    // 442 with all nine of the mean value theorem's weakenings, the same day, read off a probe of
    // `Propose.audit` filtered by `from`: each keeps an implication and sits at the propositional
    // address, taken and not settled, so `unreadable` below does not move. Tip plus this branch's
    // delta, the delta probed on the tree before the closed terms landed.
    // 444 with the product rule's two weakenings, the same day, read off a probe of `Propose.audit`
    // filtered by `from`: each drops one of the two slopes and keeps an implication. The third, the
    // continuity bridge's, is in `unreadable` below.
    // 446 with the chain rule's two weakenings, the same day, read off a probe of `Propose.audit`
    // filtered by `from`: each drops one of the two slopes and keeps an implication.
    // 449 with the exponential's slope, the same day, read off a probe of `Propose.audit` filtered
    // by `from`: all three residues are `EXP_NEAR_LINE`'s, its one weakening and its two
    // substitutions, and each is about `exp`, which no procedure here has a value or a bound for,
    // so each is taken and not settled. `DERIVATIVE_EXP` produces none.
    // 455 with the sign of a derivative on an interval, the same day, read off a probe of
    // `Propose.audit` filtered by `from`: six weakenings, each dropping the continuity or the slope
    // and keeping an implication under `!f a b`, so each is taken and not settled. No
    // substitution: the bodies carry a quantifier, which is a lambda here.
    // 458 with Fermat's little theorem, the same day, measured by a probe of `Propose.audit` before
    // this line was edited: the three residues of `NUM_PRIME_DIVIDES_CHOOSE`, a divisibility the
    // propositional address takes and cannot settle. The other five are `unreadable` below. Tip
    // plus this branch's delta.
    // 461 with uniform continuity's three weakenings, the same day, read off the run on the tree
    // before the sign of a derivative and Fermat landed and then confirmed by a second run in which
    // every assertion after this row held: none went to `unreadable` or was refuted, each keeps an
    // implication and sits at the propositional address, taken and not settled. Tip plus this
    // branch's delta.
    // 484 with twenty-three of the gauge integral's twenty-four residues, the same day, read off a
    // probe of `Propose.audit` filtered by `from`: seventeen weakenings that keep an implication or
    // name `fine_sum`, `has_integral` or `derivative`, which no procedure settles, and six
    // substitutions of the order, the sum and the product. The twenty-fourth is in `unreadable`.
    // Tip plus this branch's delta, the delta probed on the tree before uniform continuity landed.
    // 495 with all eleven residues of the sine's and the cosine's derivatives, the same day, read
    // off a probe of `Propose.audit` filtered by `from`: the three estimates' weakenings, each
    // about `cos`, `sin` or a sum of the exponential's terms, which no procedure has a value for,
    // and eight substitutions of the order, the sum and the product in the two addition formulas
    // and the two estimates. None reached `unreadable`.
    // 507 with Euler's theorem, the same day, measured by a probe of `Propose.audit` before this
    // line was edited: twelve of its fourteen residues, each an implication or a congruence the
    // propositional address takes and cannot settle; the other two are `unreadable` below. Tip
    // plus this branch's delta.
    // 511 with the existence of the integral's four weakenings, the same day, read off a run on an
    // earlier tree and confirmed by a second in which every assertion after this row held: each
    // keeps an implication and names `has_integral` or `integral`, which no procedure settles. Tip
    // plus this branch's delta.
    // 545 with thirty-four of the textbook forms' thirty-five residues, 2026-09-25, measured by a
    // probe of `Propose.audit` filtered by `from` after a prediction of "thirty-three weakenings and
    // one substitution" got the total right and the parts wrong: thirty-two weakenings, each keeping
    // an implication or naming `continuous_within` or `derivative`, which no procedure settles, and
    // BOTH of `CONTINUOUS_EXTENSION_AGREES`'s substitutions of its order. The thirty-third
    // weakening is in `unreadable` below.
    // 553 with eight of the nine residues of the fundamental theorem relative to `[a, b]` and the
    // relative derivative, 2026-09-25, measured by a probe of `Propose.audit` filtered by `from`
    // after a prediction of "all eight weakenings" got the total right and the parts wrong: seven
    // weakenings, each keeping an implication or naming `derivative_within`, `has_integral` or
    // `integral`, which no procedure settles, and one substitution of the order in
    // `DERIVATIVE_WITHIN_INTERIOR`. The eighth weakening is in `unreadable` below.
    // 554 with one of the logarithm's slope's two residues, 2026-09-26: the substitution of the
    // order, `0 <= x ==> derivative ln x (inv x)`, keeps an implication and is taken and not settled.
    // Predicted at 555 before the run, counting both residues here, and the run said otherwise; the
    // probe of `Propose.audit` filtered by `from` placed the other one in `unreadable` below.
    // 560 with all six of the integral's linearity's residues, 2026-09-26, read off a probe of
    // `Propose.audit` filtered by `from`: each drops one integral, the order of the ends, or the
    // fine sum, and keeps an implication or names `has_integral` or `fine_sum`, which no
    // procedure settles. None reached `unreadable`, and the three write no operator between reals
    // outside a lambda, so none is substituted. Tip plus this branch's delta.
    // 572 with the residues of `HAS_INTEGRAL_JOIN`, `DERIVATIVE_WITHIN_INTEGRAL` and
    // `DERIVATIVE_INTEGRAL`, 2026-09-26: twelve, read off the suite's own failure after a prediction
    // of ten, so the total is measured and how it splits between weakenings and substitutions is not.
    // 586 with all fourteen residues of parts and the substitution, 2026-09-26, derived before the
    // run and confirmed by it: every fact has three antecedents or more, so dropping one leaves an
    // implication about `has_integral`, `integral` or `derivative`, which no procedure settles. The
    // bodies carry a quantifier, so nothing is substituted.
    // 609 with twenty-three of the p-adic valuation's thirty-three residues, 2026-09-26, read off a
    // probe of `Propose.audit` filtered by `from` after the run had named the total: all
    // weakenings, each keeping an implication or naming `NUM_VALUATION`, which no procedure reads.
    // Nine are `unreadable` below and one is `decidedFalse` above. Tip plus this branch's delta.
    // 614 with all five of `CONTINUOUS_MUL`'s and `TAYLOR`'s residues, 2026-09-26, measured by the
    // run: each is an implication about `continuous` or `derivative`, which no procedure settles.
    // 632 with all eighteen residues of the integral's relative forms and their congruences,
    // 2026-09-26, read off the suite's own failure: every one keeps an implication about
    // `has_integral`, `fine_sum`, `integral` or `derivative_within`, which no procedure settles.
    // The total matched the eighteen derived for `proposals` and no other bucket moved, so none
    // reached `unreadable`. Tip plus this branch's delta.
    open shouldBe 632
    // 7 earlier on 2026-09-11, when the library gained thirty lemmas about `num` and a weakening of
    // one of those was a claim about a type the arithmetic procedures have no reading of. **2 since
    // the model learned the naturals**, and the five that left are the point of this whole bucket:
    // "nobody here can take this shape" was true of all seven and was the least useful true thing
    // that could be said about five of them, which are false at a small number the search now
    // finds. The two that remain are the two the bucket is for: nothing addresses them and nothing
    // refutes them either.
    //
    // **4 when the truncated difference landed, and the two that arrived were written down here as
    // a gap rather than as a result.** They are `NUM_SUB_EQ_ZERO` and `NUM_SUB_ADD` with their
    // bounds dropped, `!x y. NUM_SUB x y = ZERO` and `!x y. NUM_ADD (NUM_SUB x y) y = x`, and both
    // are **false**: `SubtractionSpec` computes the second to `SUC ZERO = ZERO` at
    // `x = ZERO, y = SUC ZERO` and puts `NUM_SUC_NOT_ZERO` beside it. The search could not say so,
    // because `Model.Numbers` had no value for `PRE` or `NUM_SUB` and declined at every point.
    //
    // **5 with the order principles**, and the one that arrived is a different shape.
    // `NUM_LEAST` with its hypothesis dropped is `!P. ?m. P m /\ (!k. NUM_LT k m ==> ~(P k))`,
    // false at the predicate that holds nowhere, and nothing here can say so: it is a claim about
    // an arbitrary predicate over `num`, which is not a shape any procedure or sampler takes. The
    // difference from `NUM_GREATEST` weakened, which sits in `Open`, is `NUM_LE` against `NUM_LT`
    // and where the negation sits, and it is enough to move one of the pair into the other bucket.
    // That is worth knowing about how coarse the two buckets are at this shape.
    //
    // **3 once the model was given `PRE` and `NUM_SUB`**, both truncated at zero exactly as `Peano`
    // defines them, and the two subtraction claims are decided false at a point. That is this
    // bucket read the other way round, and it is the reading that makes it worth having: an entry
    // here is an invitation to interpret something, and an entry leaves when somebody does.
    //
    // The three that remain are the three nothing can reach: a predicate applied to a natural, the
    // representation of a successor in the infinite type, and the least-number principle with its
    // hypothesis gone. Interpreting a constant does not help any of them, because none of them is
    // waiting on a constant.
    //
    // **22 on 2026-09-12, and this is the count that moved most.** Nineteen arrived with the five
    // developments that joined the chain: five from `Divisibility`, ten from `Modular`, four from
    // `Word`. Every one of them is a claim whose whole content is a relation or an operation no
    // procedure here reads and `Model.Numbers` has no value for: `Divides`, `NUM_DIVIDES`,
    // `NUM_CONG`, `NUM_GCD`, `WORD_NTH`, `WORD_MAKE`. `!x y. Divides x y` and
    // `!x y. NUM_DIVIDES (NUM_GCD x y) x` are the shape.
    //
    // That is the bucket working rather than the bucket filling up, and the distinction is the one
    // the paragraph above draws: an entry here is an invitation to interpret something, and
    // nineteen of these are one invitation repeated, to give the model a divisibility. It would
    // be a cheap interpretation and it is deliberately not being written here, because writing it
    // is a decision about what the model claims to know and this change is about where the
    // developments live. The number is the measurement that says what it would be worth.
    //
    // The four from `Word` are a different case and would not be helped by a model at all: they
    // quantify over `word('a)` and `num -> 'a`, and `Refutation.grid` declines a variable of a
    // type with no carrier rather than inventing one. `RefutationSpec` asserts that directly at
    // `prod` and `word`, which it could not do before these developments were in the chain: the
    // rule was there since 2026-09-11 and nothing this repository could state reached it.
    //
    // 24 with the quotient, the remainder, Bezout and Euclid: two of the twelve weakenings carry a
    // `NUM_DIVIDES` in the **conclusion** rather than only in a hypothesis, which is the line this
    // bucket draws and the same one the nineteen above are on. Both are weakenings of
    // `NUM_EUCLID`, whose conclusion is a disjunction of two divisibilities: no procedure here
    // takes that shape, and the model has no value for the relation, so neither half of the system
    // has anything to say. Giving the model a divisibility would move these two as well, and that
    // is still deliberately not being written.
    //
    // **28 with the matrices**, and the four are `MAT_ADD_MAT2`, `MAT_SMUL_MAT2` and
    // `MAT_MUL_MAT2` twice. They are equations between MATRICES rather than between reals, and
    // `Refutation.grid` declines a type it has no carrier for, which is the same case `Word`'s
    // four are already here for. It is the bucket working as stated: nothing addresses them and
    // nothing refutes them either, and saying so is different from saying they are open questions.
    // 31 with the classical facts, and the three are `COND_TRUE`, `COND_FALSE` and
    // `FUNCTION_EXTENSIONALITY` with their antecedents dropped. All three quantify over a TYPE
    // VARIABLE (`'a`, and a function type for the last), and `Refutation.grid` declines a type it
    // has no carrier for, which is the same case the matrices and `Word` are already here for.
    // Nothing addresses them and nothing refutes them either, which is what this bucket says.
    // **32 with the bounded partial sum**, and it is here for the same single reason the bucket
    // above gives for not having it, rather than for a second one. This bucket IS
    // `Prove.Address.Nobody`: `Novelty` reads `Unreadable` off the address and `Open` off an
    // unsettled claim that some procedure did take. `Prove.Address.Equation` is an equation
    // BETWEEN REALS by its own docstring, so `!f g n. NUM_SUM f n = NUM_SUM g n` is addressed by
    // nobody and its twin `!f g n. Sum f n = Sum g n` is addressed and then not settled.
    //
    // Written out because the near-miss explanation is the one a reader reaches for first and it
    // does not survive the pair. Both claims quantify over two functions, so "the grid has nothing
    // to range over" would put the `Sum` twin here too, and it is in `Open`. What separates them is
    // the type of the equation and nothing else, which is the sharpest statement available of how
    // coarse these two buckets are.
    // 33 with `Rotation`: the weakening of `WORD_ROTATE_NTH` drops `i < WORD_LENGTH w` and what is
    // left is an equation between two `WORD_NTH`s at type `'a`, which no model here interprets.
    // It joins the bucket for the reason the paragraph above gives and not by near-miss: the grid
    // has something to range over, and what it has nothing to say about is the element type.
    // 34 with `Coding`: the weakening of `NUM_FACT_DIVIDES` drops `0 < d /\ d <= k` and leaves
    // `!d k. NUM_DIVIDES d (NUM_FACT k)`, which is over `num` and which the grid could range over,
    // so this one is not the element type again. What nothing here has is a reading of `NUM_FACT`:
    // it is a constant introduced by choice out of the recursion theorem, and no model interprets
    // it, so every point the grid tries answers nothing. Its twin from `NUM_CRT_PAIR` is equally
    // false and lands in `Open` instead, which is the pair worth reading these two buckets by.
    // 36 with Gauss's other two weakenings, which is the same split as the pair above and in the
    // same proportion: of three claims equally false and equally unrefuted, one is attempted and
    // two are not read at all.
    // 37 with the moduli's coprimality, and back to this bucket after the previous addition had
    // moved the refuted one. Its residue names `NUM_GCD`, which nothing interprets, so the grid has
    // nothing to try: the difference between this and `NUM_DIVIDES_ONE` is not how false the claim
    // is but whether anything can look at it.
    // 39 with the two product lemmas, whose residues name `NUM_PROD`, which nothing interprets.
    // The pair of additions in this same commit split cleanly between the two buckets and the
    // reason is only which constants survive the weakening, not how false the claim is.
    // 40 with exactly one of the seven the Chinese remainder theorem brought, and the note at the
    // assertion above says which and why it is the interesting one: its six siblings, five of them
    // naming `NUM_GCD`, are all `Open`.
    // 41 with the weakening of `NUM_TRI_MONOTONE`, whose residue is
    // `!x y. NUM_LE (NUM_TRI x) (NUM_TRI y)`. It is here for the reason `NUM_PROD`'s two were: the
    // claim is false and nothing can look at it, because the model has no value for `NUM_TRI`.
    // Its three siblings from the same change are all in the refuted bucket, which is this pair of
    // buckets splitting one change cleanly on which constants survive.
    // 42 with the weakening of `NUM_TERM_SUC`, whose residue is
    // `!x. NUM_TERM (NUM_CODE 2 x)`: false, and with no premise left for anything to attempt.
    // 44 with the two residues that have nothing left on the left of an arrow,
    // `!p. NUM_FORM (NUM_CODE 6 p)` and `!i p. NUM_FORM (NUM_CODE 8 (NUM_PAIR i p))`.
    // 45 with the weakening of `NUM_STRONG_INDUCTION`, whose residue is `!P. !n. P n`. This
    // bucket was NOT derived for it and was measured, because which of the two buckets takes a
    // claim quantified over PREDICATES is not something the conclusion's constants settle. It is
    // here, and the paragraph five entries up already said why: `NUM_LEAST` weakened landed here
    // for the same reason, being a claim about an arbitrary predicate over `num`, which is not a
    // shape any procedure or sampler takes. So this is the second instance of a kind of
    // unreadability that is not "the model has no value for that constant".
    // 46 with the weakening of `NUM_PA_INDUCTION`, whose residue is `!i p. NUM_PA <the instance>`.
    // Derived here rather than measured and then confirmed, by the rule the entries above keep
    // finding: what decides this bucket is the premise that SURVIVES, and dropping the only
    // hypothesis leaves nothing on the left of an arrow and a conclusion written in `NUM_PA`,
    // `NUM_SUBST_FORM` and `NUM_CODE`, none of which any model here interprets. It is a third
    // shape of unreadability only in appearance: it is the first one, no value for the constant,
    // arriving through a constant defined by disjunction rather than by choice or by recursion.
    // 47 with the weakening of `NUM_PA_FORM`, whose residue is `!n. NUM_FORM n`: false, nothing
    // left on the left of an arrow, and no model with a value for `NUM_FORM`.
    // 50 with the three above: `NUM_LOGIC_REFLEXIVE` and `NUM_LOGIC_FORM`, which have one premise
    // each and so leave nothing, and `NUM_LOGIC_VACUOUS`'s first, which leaves a negation.
    // 52 with those two, whose residue is `!n. NUM_PROV n` both times: nothing left on the left
    // of an arrow, and no model with a reading of `NUM_PROV`.
    // 53 with the closure under generalisation, whose residue is
    // `!i p. NUM_PROV (NUM_CODE 8 (NUM_PAIR i p))`: nothing left on the left of an arrow, and no
    // model with a reading of `NUM_PROV`. Its sibling's two went to `open` instead, because each
    // of those keeps one of two premises; this one has a single premise and keeps none.
    // 54 with the identity, whose single premise dropped leaves `!p. NUM_PROV (p ==> p)`: nothing
    // on the left of an arrow, and no model with a reading of `NUM_PROV`. Its own sibling is the
    // control, since the syllogism's five all land in `open` for having four premises left.
    // 55 with the irrationality's, whose residue is `!p q. ~(p * p = 2 * (q * q))`. It was DERIVED
    // as `decidedFalse` and measured here, and the derivation recorded both candidates before the
    // run, which is the only reason the answer is informative rather than a correction.
    //
    // The residue IS false, at `p = q = ZERO`, and the model computes `NUM_MUL` and equality. What
    // the derivation got wrong is the order: refutation does not happen beside the address, it
    // happens through it, so a goal nothing can address is never put to the sampler at all. The
    // conclusion here is a NEGATION, which the minimal propositional fragment declines, so the
    // address is `Nobody` and the standing is `Unreadable` with the point never looked for.
    //
    // That is the difference between "false and known to be" and "false and nobody asked", and
    // this bucket is where the second lives. It is the fifth reading error recorded here.
    // 58 with the three residues of `NUM_PROV_IMP_GEN` that keep its negated side condition. The
    // entry above has the derivation; this is its other half.
    // 60 with the two residues of the deduction theorem that keep its negated side condition.
    // 60, UNCHANGED, and the derivation that said 59 is worth keeping because of how it failed.
    // It argued from a balance: seven proposals arrived, two are decided false, the bucket above
    // gains six, and six plus two is eight, so something must have moved out of here.
    //
    // **The two numbers are over different populations.** `proposals.size` counts
    // `propose.weakenings`; these buckets count `propose.audit`, which is the weakenings AND the
    // substitutions. The twelve new lemmas produce both, so the audit grows by more than seven and
    // the arithmetic never had to close. A balance argument across two counts is worth nothing
    // until somebody checks they count the same things, and this one did not.
    // 61 with the other of the two, for the reason the entry above gives.
    // 62 with the weakening of `Classical.NOT_FORALL`, and it is the first entry in this bucket
    // that is unreadable for a reason of TYPE rather than of shape: `!P. ?x. ~(P x)` is about a
    // predicate variable at a type variable, and the procedures here read the reals and the
    // naturals. Everything else this bucket holds is a claim about a `num` the arithmetic cannot
    // take; this one is a claim about nothing in particular.
    // 63 with the one weakening above that keeps no antecedent.
    // 66 with the other three: two keep `~(NUM_DIVIDES p x)` and one, the positivity's, keeps no
    // antecedent at all.
    // 74 with the concatenation's other eight, and every one of them is unreadable for the
    // reason `NOT_FORALL` is two entries above: a reason of TYPE rather than of shape. They are
    // claims about `word('a)`, and the procedures here read the reals and the naturals. Ten
    // weakenings arrived and they split two and eight with nothing left over, which is the
    // arithmetic the note above says is worth nothing until somebody checks the two counts are
    // over the same population. Here they are: both are over the ten this development added.
    // 77 with three of `Inductive`'s, and **the direction was predicted before the run** rather
    // than read off it. The pin was left at 74 on purpose as the experiment: the eight entries the
    // line above is about are unreadable for a reason of TYPE, and nothing in these two
    // developments gives a procedure an address for a claim about `word('a)`, so the count could
    // hold or rise and could not fall. It rose by three.
    //
    // The three are the weakenings of `INDUCTIVE_INDUCT`, `INDUCTIVE_INTRO` and
    // `INDUCTIVE_FIXPOINT`, and they are unreadable for `NOT_FORALL`'s reason two entries above,
    // not for `word`'s: a residue about `('a->bool) -> 'a -> bool` is a claim about an operator at
    // a type variable, which is a claim about nothing in particular. The other four weakenings this
    // commit adds are `Reaching`'s, and they went to `Open` — `REACH` carries `SND`, `SUC`,
    // `NUM_ADD` and `NUM_LE`, which the arithmetic can take, so somebody attempted them and did not
    // settle them. Seven arrived and they split three and four with nothing left over, which is the
    // check the note above asks for: both counts are over the seven this commit added, and `open`
    // moving 216 to 220 is the other half of the same seven.
    //
    // 78 with ONE of the algebra of limits' three residues, and the split completes the derivation
    // rather than merely passing. Three residues were derived before the run from the peeling
    // rule, two landed in `open` above and this is the third, so 2 + 1 = 3 with nothing left over
    // and neither bucket is standing in for the other. That crossed check is the whole value of
    // pinning both: which bucket a residue reaches is not derivable, as the entries above say,
    // but their SUM is, and a residue quietly lost would show up as two counts that no longer add
    // to the number the rule predicts.
    //
    // The one here is the negation's, `converges (\n. -(s n)) (-a)` with its only hypothesis
    // dropped. It is unreadable for the reason two entries above give and not for `word`'s: a
    // claim that every sequence's negation converges to `-a` for an unrelated `a` is about
    // `converges`, and no procedure in this chain has an address for that constant at all. The
    // sum's two stay in `open` because each keeps the other convergence as an antecedent, so what
    // is left is still a conditional a procedure will attempt and fail to settle.
    //
    // 79 with ONE of the six derived connectives' eleven, and the pair adds up the way this note
    // asks: ten went to `open` and this one here, eleven with nothing left over. It is
    // `NUM_FORM_EXISTS`'s only weakening, and it is unreadable for neither of the two reasons
    // above: not a type nothing has an address for, and not an operator at a type variable, but a
    // residue with NO ANTECEDENT AT ALL, which is the `NUM_CLOSED_SUC` case the `open` entry
    // records. Dropping the single hypothesis of a single-hypothesis rule leaves nothing to
    // attempt.
    //
    // **This figure was explained in the `open` entry and not moved here**, and the suite is what
    // caught it: the sentence naming where the eleventh went was written in one place while the
    // count it describes stayed put in another. A derivation written down beside the wrong number
    // is worse than no derivation, because it reads as though somebody checked.
    // 82 with THREE of the four the right forward closure brought, the fourth being in `open`
    // above. **This three was arithmetic and not a prediction, and the difference is worth the
    // line**: the four residues were derived before the run, the `open` row read 236 from a failed
    // assertion, and three is four minus one. Subtracting a measured number from a derived one is
    // not the same act as deriving, and a row that presented it as a prediction confirmed would be
    // claiming an instrument it did not use.
    //
    // What IS a reading rather than arithmetic is why the split falls this way, and it holds for
    // whatever lands over `word` next: the procedures here decide fragments of the reals and of
    // the naturals, so a residue whose atoms are `WORD_RFC` and `WORD_STEP` has nowhere to be
    // addressed. The one that reached `open` did so on its propositional skeleton alone.
    // 83, and the one that arrived is the factorisation's rather than this session's: `627ceec`
    // added eleven weakenings, ten of which land in `open` above, and the eleventh lands here. The
    // two limit bounds add four and none of the four lands here, so this figure separates the two
    // pieces of work stacked on this line better than either of the other two does.
    //
    // **84 here, and the tip's 83 is right for the tip.** This branch adds one: `Propose.audit`
    // was asked which lemma each residue comes from rather than inferred from totals, and
    // `WORD_LENGTH_ZERO` makes exactly one proposal, `Weakened`, change `WORD_LENGTH x = 0`,
    // standing `Unreadable`. Its only atom is an equation between words and no procedure here
    // reads one, which is the reading above holding at a lemma with nothing to do with a closure.
    //
    // **The route is worth more than the number.** This was written 83 twice on two kinds of bad
    // evidence. First on the assertion not appearing in a failure list, which it cannot: it sits
    // in the same test as `open` and after it, so a red `open` ends the test and this line never
    // runs. Then on arithmetic over totals, where two buckets and three contributors leave the
    // attribution underdetermined and each round of subtraction produced a different hypothesis
    // that fitted the same numbers. When several hypotheses fit one total, the move is not a
    // finer subtraction, it is asking the instrument whose each element is.
    //
    // 85 with the one of `Peano`'s two that `decidedFalse` did not take, and `open` does not move
    // at all. `NUM_SUM_MONOTONE_BELOW` weakens to `!x y z. NUM_SUM x z <= NUM_SUM y z`, whose two
    // leading variables are FUNCTIONS: there is nothing for a point to be, so no procedure here
    // has an address for it and nothing refutes it either, which is the pair of facts this bucket
    // is for. The attribution is not arithmetic over totals: `decidedFalse` moved by one and this
    // by one over exactly two new residues, so one each, and which is which follows from the
    // statements rather than from the subtraction.
    // 92 with the **seven** of the integers' seventeen that `open` did not take, and the two
    // buckets together are the whole of the seventeen: ten open, seven here, nothing refuted
    // and nothing earned. That the split is ten and seven was **not** predicted, and the line
    // above says so; what this line adds is the half the other one could not: the residues have
    // an address in neither bucket for two different reasons, and the reason here is the one
    // this bucket is for. A weakening of `INT_DIVIDES_ELIM` or `INT_LE_ANTISYM` is a claim
    // about `int`, and the sampler has no point to try because nothing interprets that type,
    // so nothing refutes it either. The attribution is not arithmetic over totals, which is
    // what the paragraph above warns against: seventeen new residues went to exactly two
    // buckets, and ten plus seven is the reading rather than a subtraction that happened to
    // fit.
    // 93 with the one of the bridge's three that `open` did not take, and it is the weakening
    // rather than either substitution. Dropping `INT_REAL_INJECTIVE`'s single hypothesis
    // leaves `!a b. a = b` over `int`: false, and refuting it means producing two integers,
    // which the sampler cannot do because nothing interprets that type. So it has no address
    // and nothing refutes it, which is the pair of facts this bucket is for, and it is the
    // same reason the seven of `Integer`'s seventeen are here. What separates it from the two
    // above is not the development they come from but what a weakening leaves standing: an
    // equation between reals in one case and a claim about `int` in the other.
    // 94 with the third of the order map's residues, and it is a SUBSTITUTION where every other
    // entry on this list is a weakening. `INT_REAL_LE` with `real_le` swapped for `real_lt`
    // leaves `!a b. INT_LE a b = (real_of_int a < real_of_int b)`, which is false at `a = b` and
    // which nothing here can say so: refuting it means producing an integer, and the sampler has
    // no point to try because nothing interprets that type. Same reason as the seven of
    // `Integer`'s and the bridge's one above; different source, which is why this row now says
    // that what decides the bucket is the **type the residue is about** and not which of the two
    // generators wrote it.
    //
    // **This figure was found by a measurement and not by the run**, and that is worth the line:
    // `open shouldBe` two paragraphs up went red in the same change, and a red assertion ends its
    // test, so this one never ran and read exactly like a pass. The three residues were listed off
    // `Propose.audit` with their standings instead.
    // 95 with the residue of `INT_MUL_CANCEL_NUM`, 2026-09-20, and it is here rather than in the
    // bucket above for the reason this row has now given four times: the weakening drops the
    // equation between the two products and leaves `!a b d. a = b`, which is **false**, and the
    // sampler has no point to try because nothing interprets `int`. What decides the bucket is
    // the type the residue is about, and the three `abs` residues of the same day are the control
    // on that: they are false too, they are about reals, and every one of them is open.
    // 96 with the OTHER of the two weakenings of 2026-09-20, `!n k. NUM_CHOOSE n k = ZERO`. It is
    // here because nothing addresses a claim about `NUM_CHOOSE`, which is this bucket's criterion
    // and is not the one first written beside this row: that said the model does not interpret
    // `NUM_CHOOSE`, which is true and decides whether the claim is REFUTED rather than which of
    // these two buckets holds it. The row in `open` carries the correction for all three.
    // 97 with the residue of the absolute convergence theorem, 2026-09-21, and **this bucket was
    // predicted right this time**, which is the entry above being read rather than the prose
    // beside it: dropping the hypothesis leaves `!f l. ?m. converges (Sum f) m`, which is false
    // and is about `converges`, a constant no model here interprets. The row above records the
    // reading that sent the same prediction to `open` yesterday, and the criterion it gives —
    // the constants and not the type — is what was used here.
    // 98 with the third of those residues, `SUM_BELOW_LIMIT` with its convergence dropped. It is
    // here for the reason this bucket's own opening gives and the row above now repeats: nothing
    // addresses `!f l. (!i. 0 <= f i) ==> !n. Sum f n <= l`, where an order between two partial
    // sums IS addressed and so lands above.
    //
    // It also sat behind `open` in this same test and so never ran on the first pass, which is
    // the fourth time this file has recorded that, and the first time the number behind it was
    // also the one a prediction had wrong. The second pass found both.
    // 99 with the second of the list interface's two weakening residues, 2026-09-23. The row
    // in `open` above carries the reading that predicted both of them there and the
    // correction. **And this assertion sat behind that one again**, so it did not run on the
    // pass that moved it: the fifth time this file has recorded that, and the second time
    // the figure behind it was also moving.
    // 100 with the weakening residue of `LIST_RECURSION_UNIQUE`, 2026-09-23. Dropping its one
    // antecedent leaves `!a g f h. f = h`, which is false and which names **no constant at all**,
    // so there is nothing for a model here to address and the criterion two rows up sends it to
    // this bucket rather than to `open`. Read off the run rather than predicted.
    // 101 with `CONVERGES_SHIFT`'s weakening, 2026-09-24: dropping its antecedent leaves
    // `!s l. converges (\n. s (SUC n)) l`, about `converges`, which no model here interprets, and
    // this bucket's criterion sends it here as it sent `SUM_BELOW_LIMIT`'s. **It sat behind `open`
    // again**, the sixth time: the first pass moved `open` and never reached this line, and it was
    // the reading here that accounted for `open`'s two as `SIN_COS_SQUARED`'s substitutions.
    // 102 with `EXP_ONTO`'s weakening, `!x. ?y. exp y = x`, read off the same probe: false at
    // every non-positive `x`, and an existential over an exponential that no procedure addresses.
    // 103 with `CONTINUOUS_NEG`'s one weakening, `!f x. continuous (\y. 0 - f y) x`, from the same
    // probe: false at any function with a jump, and about `continuous`, which no procedure
    // addresses and no model interprets.
    // 105 with the same probe: three of the criteria's residues conclude a convergence of a
    // sequence that is not a series, `CONVERGES_OFFSET`'s, `SUM_TERMS_VANISH`'s and
    // `POWER_VANISHES`'s, and have no address, and `CONVERGES_ABSOLUTE`'s left for `open` above.
    // Plus three, minus one.
    // 106 with `CONVERGES_BOUNDED`'s residue, `!s l. ?B. !n. abs (s n) <= B`, which is false and an
    // existential no address takes. Predicted and met.
    // 123 with seventeen of resolution's nineteen, 2026-09-25, read off the second run: one is in
    // `decidedFalse` and one in `open`, and the other seventeen each name a `RES_` constant or
    // apply a function variable, which no procedure here addresses. **It sat behind `open` again**,
    // so the pass that moved `open` did not reach it. Tip plus this branch's delta.
    // 124 with `DERIVATIVE_NEG`'s one weakening, `!f x m. derivative (\y. 0 - f y) x (0 - m)`,
    // from the same probe as `open`'s 405: false at the identity, and about `derivative`, which no
    // procedure addresses and no model interprets. Tip plus this branch's delta.
    // 125 with `NUM_PROV_REFL`'s one weakening, 2026-09-25, predicted from the row above: dropping
    // its only antecedent leaves `!t. NUM_PROV (t = t)`, a bare application of a predicate that no
    // address takes.
    // 126 with `DERIVATIVE_CONTINUOUS`'s one weakening, `!f x. continuous f x`, from the same probe
    // as `open`'s 444: false at any function with a jump, and about `continuous`, which no procedure
    // addresses and no model interprets.
    // 131 with the same probe: `NUM_FRESHMAN`'s, `NUM_FERMAT`'s and `NUM_DIVIDES_SUM`'s one each
    // and `NUM_PRIME_NOT_DIVIDES_FACT`'s two, a congruence, a divisibility or its denial, which no
    // procedure reads.
    // 132 with `FINE_SUM_PIECE`'s one weakening, from the same probe as `open`'s 484: dropping its
    // only antecedent leaves a bare `fine_sum`, which no procedure reads.
    // 134 with the same probe: `NUM_PROD_CONG_MOD`'s one residue, a congruence with its hypothesis
    // dropped, and one of `NUM_PROD_POINT`'s, whose conclusion is an equation between naturals, which
    // no procedure reads.
    // 135 with `CONTINUOUS_WITHIN_OF_CONTINUOUS`'s one weakening, 2026-09-25, measured by the same
    // probe: without its hypothesis it says every function is continuous relative to every
    // interval at every point, and `continuous_within` has no reading in any procedure.
    // 136 with `DERIVATIVE_WITHIN_OF_DERIVATIVE`'s one weakening, the same day and probe, for the
    // same reason one notion over: without its hypothesis it gives every function every slope
    // relative to every interval, and `derivative_within` has no reading in any procedure.
    // 137 with the logarithm's slope's weakening, from the same probe as `open`'s 554: dropping its
    // only antecedent leaves a bare `derivative ln x (inv x)`, which no procedure reads, as
    // `DERIVATIVE_CONTINUOUS`'s did.
    // 146 with nine of the p-adic valuation's residues, from the same probe as `open`'s 583: one
    // each of `NUM_LT_POW`, `NUM_POW_DIVIDES_POW`, `NUM_VALUATION_NOT_DIVIDES`, `NUM_VALUATION_POW`
    // and `NUM_VALUATION_UNIQUE`, and two each of `NUM_VALUATION_SPEC` and
    // `NUM_VALUATION_OTHER_PRIME`: with the antecedent gone, what is left is a bare divisibility, a
    // bare equation of valuations or a bare `NUM_PRIME`, and no procedure reads any of them.
    unreadable shouldBe 146
    open + unreadable + findings.count(_.standing.contains(Novelty.Standing.False)) +
      findings.count(_.standing.contains(Novelty.Standing.Earned)) +
      findings.count(_.standing.contains(Novelty.Standing.Known)) +
      findings.count(_.standing.contains(Novelty.Standing.Immediate)) +
      findings.count(_.standing.contains(Novelty.Standing.Decided)) shouldBe findings.size
  }

  "The proposals about the naturals" should "carry the point they fail at, which they did not" in {
    // The measurement card `88463baa` was opened for, as an A/B on one line. `Model.Reals`
    // interprets the constants the theory of the reals declares and nothing about `num`, so
    // every claim naming `Sum`, `Power`, `Prod`, `SUC`, `NUM_ADD`, `NUM_MUL`, `NUM_LE` or
    // `real_of_num` had no point that could be evaluated, and the search truthfully reported that
    // nobody could ask. `Model.Numbers` interprets them exactly, and `Refutation.grid` samples a
    // variable of type `num` as a natural number and one of type `num -> real` as a function.
    //
    // The proposals that name one of those constants are `aboutNumbers` below, and the ones among
    // them refuted at a point a reader can check are `after`, where `before` says none was. Both
    // counts were written here as digits once and were left behind twice while the assertions at
    // the end of the test were updated, so this names the assertions instead.
    val chain = garden.xeno.symbolum.theories.Chain.standard
    // `PRE` and `NUM_SUB` joined the list when they were defined, and adding them changed no count:
    // all three proposals they produce already name `ZERO`, `NUM_ADD` or `real_of_num`. They are
    // here so that the next lemma written purely in them is not quietly outside this measurement.
    val named = Set("Sum", "Power", "Prod", "SUC", "ZERO", "PRE", "NUM_ADD", "NUM_MUL", "NUM_SUB",
      "NUM_LE", "NUM_LT", "real_of_num", "NUM_SUM")

    // `NUM_SUM` is thirteenth and was missing, which the move to term matching is what exposed.
    // Under the substring reading a claim naming `NUM_SUM` matched the entry `Sum`, so it was
    // counted for a reason nobody chose and the omission was invisible; matched as a constant it
    // dropped out, and the count going to 57 is what asked where it went. It is a constant of the
    // naturals by this list's own description and it landed on 2026-09-12 without being added,
    // which is exactly the silent exclusion the paragraph above says this list exists to prevent.

    def mentions(term: Term, names: Set[String]): Boolean = term match {
      case Const(name, _) => names.contains(name)
      case App(fn, argument) => mentions(fn, names) || mentions(argument, names)
      case Abs(_, body) => mentions(body, names)
      case BVar(_) | FVar(_, _) => false
    }

    // Membership is read off the TERM and not off the printed claim, and that is a repair rather
    // than a preference. It was `show(claim).contains(name)` until 2026-09-12, when `ZERO` began
    // printing as `0` because `num` acquired numerals; five proposals whose only naturals constant
    // was `ZERO` left this bucket that day without anything about them changing, and the bucket
    // shrinking is the exact failure the comment above this list warns about. A constant is a node
    // of the term whatever the printer does with it.
    val aboutNumbers = propose.audit.filter(finding => mentions(finding.proposal.claim, named))

    def witnesses(model: Model): Int = {
      val search = Refutation(Evaluate.over(chain.reals, model))
      aboutNumbers.count(finding =>
        search.counterexample(Vector.empty, finding.proposal.claim).isInstanceOf[Refutation.Found])
    }

    val before = witnesses(Model.Reals)
    val after = witnesses(Model.Numbers)

    info(s"${aboutNumbers.size} proposals name a constant of the naturals: " +
      s"$before were refuted with a point before the model had them, $after are now")

    // 19 when this was written and 25 since the three order lemmas landed, which added six
    // proposals all naming `real_of_num`. Five of the six are refuted at a point, and the one that
    // is not is `!x:num. !y:num. real_of_num x <= real_of_num y` with its hypothesis dropped, where
    // the sampler does find a point: the count below is what it is.
    //
    // 28 when the truncated difference landed, and `after` did not move at first: all three of the
    // new proposals mention `PRE` or `NUM_SUB`, the model had no value for either, and a term with
    // no value has no point that answers. Those three rows were the measurement saying where the
    // next interpretation would pay, and it was paid the same day: all three are refuted at a point
    // now. Two of them are decided false outright; the third crosses into the reals through
    // `real_of_num`, so its point is evidence rather than a decision and its standing stays `Open`.
    // This count is about whether a point can be found at all, and the standing is about whether
    // finding one settles anything, which is why the two move differently.
    //
    // 34 with the order principles. Six of the seven new proposals name one of the constants above;
    // the seventh is `NUM_REAL_INJECTIVE` weakened to `!x y. x = y`, which names none of them and is
    // outside this measurement for the right reason rather than by oversight. Four of the six are
    // refuted at a point and two are not, and those two are the higher-order pair: a predicate
    // variable is not something `Refutation.grid` samples, so no point answers.
    //
    // 46 on 2026-09-12. The twelve that arrived are all `Modular`'s: they are the proposals whose
    // printed form still holds a `NUM_ADD`, `NUM_MUL`, `NUM_LE`, `NUM_LT` or `ZERO` after the
    // weakening, and `Divisibility`'s are outside this measurement because `Divides` is a relation
    // over the reals and names none of these. Exactly **one** of the twelve gains a point, which is
    // `NUM_DIVIDES_LE` weakened to `!x y. NUM_LE x y \/ y = ZERO`, refuted at `x = 2, y = 1`. The
    // other eleven keep a `NUM_DIVIDES`, `NUM_CONG` or `NUM_GCD` somewhere in them, the model has
    // no value for any of the three, and a term with no value has no point that answers. That
    // eleven-to-one split is the same reading as the `Unreadable` bucket above, arrived at by a
    // different route, which is why both are asserted.
    //
    // 54 later on 2026-09-12, when the quotient, the remainder, Bezout and Euclid landed. Eight of
    // the twelve new weakenings still print a `NUM_ADD`, `NUM_MUL`, `NUM_LT` or `ZERO` after the
    // hypothesis is dropped and four do not, which is what decides membership here rather than
    // which lemma they came from. Exactly **one** of the eight gains a point, and it is the same
    // one the bucket above counts: `!x. NUM_LT (SUC ZERO) x`, refuted at `x = ZERO`. The other
    // seven keep a constant the model has no value for.
    // 56 with the two division-bound lemmas. Both print a naturals constant after the hypothesis
    // is dropped, which is what decides membership here, and neither gains a point: the model has
    // no value for a quotient, so they join the seven that keep a constant it cannot evaluate.
    // 58 with the two above, and BOTH count here where only one counted above. Membership is
    // whether the shown claim names one of the twelve, and `Sum` is one of the twelve exactly as
    // `NUM_LT` is. That is why this delta is +2 while `decidedFalse` moved by one: naming a
    // constant of the naturals and being decidable at a point are different questions, and the
    // `Sum` weakening answers the first yes and the second no.
    // Still 58 on 2026-09-12 after the numerals on `num`, and the road back to it is the point.
    // Membership moved from the printed claim to the term, `ZERO` stopped printing as `ZERO`, and
    // the count went 58 -> 53; reading the term recovered 57, and the last one was a claim naming
    // `NUM_SUM`, which had been counted all along by the substring `Sum` and is now counted by
    // being in the list. Same number, two corrections, neither of which the number shows.
    // 59 with `Rotation`, and the delta is DERIVED: its one weakening names `NUM_ADD` and
    // `NUM_MOD` under the remainder, and `NUM_ADD` is on the list above. It counts here and does
    // NOT count in `after`, which is why that figure is unmoved at 32: naming a constant of the
    // naturals and being decidable at a point are different questions, and the model has no value
    // for a word.
    // 71 with the floor and the ceiling, and the delta is DERIVED: it is the same twelve as the
    // bucket above, and they count here because every one of them names `real_of_num` and one of
    // the two new constants. `after` is again unmoved, at 32, for the reason the paragraph above
    // gives: the model has no value for `NUM_FLOOR`, so none of the twelve is refuted at a point.
    // 74 with Gauss, and here ALL THREE count where only one counted in the bucket above. The two
    // questions are different and this is the clearest case of it in the file: every one of the
    // three names `NUM_GCD`, `NUM_DIVIDES` or `NUM_MUL`, so every one is about the naturals, and
    // what separates them there is whether a procedure can take the shape, not what it mentions.
    // 75 with `POWER_MULTIPLICATIVE`'s one substitution, which names `Power` at an exponent of
    // `num` and so is about the naturals by the same reading the twelve above use. Measured
    // rather than derived: what this bucket counts is what a claim MENTIONS, and predicting it
    // would have been predicting whether the exponent counts as a constant of the naturals when
    // the operators swapped are the reals'.
    // 76 with `NUM_DIVIDES_ONE`, and unlike the additions before it this one counts in BOTH this
    // bucket and the refuted one, which is the pair working as intended rather than a coincidence.
    // 77 with the moduli's coprimality, which counts here as every one of them does.
    // **Unmoved at 77 by the congruence that descends to a divisor, and the reason is this list.**
    // `named` above holds thirteen constants and `NUM_CONG` and `NUM_DIVIDES` are not among them,
    // so a claim built only from those two is not "about the naturals" by the criterion this bucket
    // counts with, however plainly it is about them in the ordinary sense. The previous four
    // additions all moved this figure because their residues also named `SUC`, `ZERO` or `NUM_MUL`.
    //
    // Written here because the derivation that said 79 was made by reading the bucket's NAME rather
    // than its list, which is a verdict about a population nobody had established. The list is the
    // criterion and it is three lines up.
    // 80 and not 81, which is the list above biting again: of the four, the two about `NUM_MUL`
    // count and `NUM_PROD_POSITIVE`'s counts through `NUM_LT`, while `NUM_PROD_DIVIDES`'s names
    // only `NUM_DIVIDES` and `NUM_PROD` and neither is among the thirteen.
    // 87, and this time ALL SEVEN count, which is the first addition since the list started biting
    // where none is lost to it. Derived against the thirteen before it was measured: every one of
    // the seven residues names `SUC ZERO` on the right of an equation, and the three that do not
    // also name `NUM_MUL` name `NUM_LT`. The criterion is what a claim MENTIONS, and a claim whose
    // whole subject is `NUM_GCD` still mentions the successor it is being compared to.
    // 89 and not 90, which is the thirteen-name list biting for the third time and in the way the
    // paragraph above predicts. Of the three: `NUM_LE_LT_TRANS`'s residue names `NUM_LT` and counts,
    // one of `NUM_MOD_OF_CONG`'s names `NUM_LT` beside the remainder and counts, and the other names
    // `NUM_CONG` and `NUM_MOD` and NOTHING ELSE, so it is not a claim about the naturals by the
    // criterion this bucket counts with. Derived against the list and then measured, which is the
    // order this figure has needed since the derivation that said 79.
    // 92 and not 93, and the one lost is lost for a reason this bucket has not met before. The
    // thirteen-name list has been excluding residues that name `NUM_GCD`, `NUM_PROD` or `NUM_CONG`,
    // which are constants NOT on it. What is left of `NUM_PAIR_INJECTIVE` is
    // `!x y z u. x = z /\ y = u`, which names **no constant whatever**: it is an equality between
    // variables, so there is nothing for the criterion to match and it does not count as being
    // about the naturals however plainly it is. Derived as four and measured as three, and the
    // derivation was wrong because it asked which constants are on the list without first asking
    // whether there were any.
    // 93 with the induction scheme's weakening, which counts. Derived against the thirteen-name
    // list and measured after: the residue names `NUM_SUBST_FORM` and `NUM_PA`, neither of which
    // is on it, but the instance it is built from spells the object language's zero as
    // `NUM_CODE 1 0`, and that `0` is the constant `ZERO`, which IS on the list. Written here the
    // first time as "those numerals are `num`", which is not the criterion and which misled the
    // next derivation off this entry by twenty-one: `NUM_CODE 2` contributes nothing, and a tag of
    // `5` or `8` is built from `NUM_ONE` and the bit constructors and contributes nothing either.
    // 93 still, with twenty-one proposals added and not one of them counting. Derived as 114 and
    // measured as 93, and the derivation was wrong because it read the ENTRY ABOVE loosely: that
    // one says the induction scheme counts because it spells the object language's zero, and what
    // does the work there is not "a numeral of `num`" but the constant `ZERO`, which is on this
    // list. The object language's zero is `NUM_CODE 1 0` and that `0` IS `ZERO`. The logical axioms
    // carry no such code: their tags are `5` to `8`, built from `NUM_ONE` and the two bit
    // constructors, and their indices are variables. A claim can be about codes of arithmetic
    // throughout and mention no constant of the naturals at all.
    // 97 with the four this commit adds, all of which count and for the ordinary reason: the
    // monotonicity's residue names `NUM_ADD` and `NUM_LT`, and each of the shift lemma's names
    // `NUM_LE` and `NUM_ADD`. Four names on the list where the previous twenty-one had none, which
    // is the difference between a claim about arithmetic and a claim about codes of arithmetic.
    // 98 with that one, which names `NUM_LE`.
    // 99 with the cancellation's, which names `NUM_LE`. One of the three and not three, and this is
    // the split the entry above is about seen once more: the closure's two residues name
    // `NUM_PROV`, `NUM_CODE` and `NUM_PAIR`, and a tag from five up is built from `NUM_ONE` and the
    // two bit constructors, so not one constant of the naturals appears in either.
    // 104 with the three multiplicative lemmas' five, every one of which names `NUM_MUL` and most
    // of which name a comparison beside it. The largest single move this figure has taken, and the
    // plainest: these are lemmas about arithmetic rather than about codes of arithmetic.
    // 105 with the irrationality's, which names `NUM_MUL`. Worth one line because it moved while
    // `decidedFalse` did not: this figure counts what a proposal is ABOUT and that one counts what
    // was settled, so an unreadable claim about arithmetic moves this and nothing else.
    // 106 with the first analysis. ONE of its eight, and which one is the whole content of this
    // figure: the residue of `CONVERGES_EVENTUALLY` that drops the CONVERGENCE and keeps the
    // agreement, because the agreement is where `NUM_LE` is written. Its twin drops the agreement
    // and names no constant of the naturals at all, and the other six are about the reals. A
    // development of analysis whose sequences are indexed by `num` contributes one row here and
    // not eight, which is this list counting constants rather than types.
    // 108 with the two residues of the monotone family that keep a constant of the naturals:
    // `MONOTONE_LE`'s names `NUM_LE`, and the one of `MONOTONE_CONVERGES` that drops the bound
    // keeps `!n. s n <= s (SUC n)` and so names `SUC`. Its twin drops that hypothesis instead and
    // names none, which is this list counting constants rather than types: every one of the three
    // is a claim about a sequence indexed by `num`.
    // 110 with `NUM_PROV_ADD_ZERO`'s two, and two out of eleven is this figure counting
    // constants rather than subject matter: of the seven facts that landed, that one alone writes
    // the object zero as `NUM_CODE 1 0`, and the `0` in it is `ZERO`. The theorem that names
    // `NUM_ADD` outright contributes nothing, having no hypothesis to drop.
    // 113 with three of the four: the positivity's residue names `NUM_LT` and `ZERO`, and two of
    // the cancellation's three keep the antecedent that writes `NUM_MUL`. The third drops exactly
    // that one and names none of the thirteen constants on this list.
    // 118 with five of the concatenation's ten, and which five is again this list counting
    // CONSTANTS rather than subject matter. All ten are about words indexed by `num`; the five
    // that count are the ones whose RESIDUE still writes one of the thirteen. `WORD_CONCAT_NTH`
    // keeps `NUM_LT` and `NUM_SUB` inside its conditional, `WORD_CONCAT_NTH_RIGHT` keeps the
    // `NUM_ADD` in its index, `WORD_FACTOR_LENGTH` keeps `NUM_LE`, and the two weakenings of the
    // arithmetic lemmas are `!p m n. m < n` and `!m n. n <= m`. The five that do not: dropping
    // the bound from `WORD_CONCAT_NTH_LEFT` leaves an equation between two entries, and the
    // residues of the two factor lemmas, the induction and the suffix name no number at all.
    // 120 with two of `Reaching`'s. `REACH` carries `SND`, `SUC` and the pair into every statement
    // about a counted step, and the potential lemma writes `NUM_ADD` and `NUM_LE` outright.
    // Unmoved by the six derived connectives, and the entry is here because a reader who has just
    // seen eleven residues arrive will look for them. This list counts CONSTANTS, and every one of
    // the eleven is a claim about `NUM_FORM` or `NUM_TERM` of a code: what their residues write is
    // `NUM_CODE` and `NUM_PAIR`, neither of which is among the thirteen. A development about
    // syntax adds nothing to a list about arithmetic, which is the same rule the concatenation
    // entry above states from the other side.
    // 125 with two of the four the limit bounds bring, and which two is again this list counting
    // CONSTANTS. `CONVERGES_LE` and `CONVERGES_GE` each have two residues: the one that drops the
    // convergence keeps `!n. NUM_LE N n ==> ...` and so writes `NUM_LE`, and the one that drops the
    // eventual bound keeps `converges s l ==> l <= b` and writes no constant of the naturals at
    // all. Two of four, derived from the statements before the run, and the same split the
    // `CONVERGES_EVENTUALLY` entry above describes: the residue that keeps the indexed hypothesis
    // counts and its twin does not.
    // 135, and ten of the twelve are the factorisation's rather than this session's: `627ceec`
    // added eleven weakenings and left this figure at 123, and ten of the eleven write one of the
    // thirteen constants, which is what a development whose every statement is about `NUM_PRIME`,
    // `NUM_DIVIDES` and `NUM_PROD` looks like on a list that counts constants. Measured rather
    // than derived, since the residues are not this session's to predict; the two that are, from
    // the limit bounds, were derived above.
    // 137 with BOTH of `Peano`'s two, which is the one count the pair does not split on. This list
    // counts CONSTANTS: `!x y z u. x + z <= y + u` writes `NUM_ADD` and `NUM_LE`, and
    // `!x y z. NUM_SUM x z <= NUM_SUM y z` writes `NUM_LE`, so both are on it whatever the
    // procedures and the sampler make of them. "The claim mentions the naturals" and "the model
    // can compute it" are different facts, which is what the entry below says from the other side.
    // 139, and the two are `NUM_PROV_NUMERAL_MUL`'s. This list counts CONSTANTS from `named`, and
    // of the four facts that landed with the object theory's multiplication it is the only one
    // whose statement writes one: `NUM_MUL`, inside the numeral of the product. The other three
    // speak of `NUM_PROV`, `NUM_TERM`, `NUM_CLOSED` and the codes, none of which is on this list.
    // Measured rather than derived, which is what the entry above already says of its residues.
    // 142 with the same single weakening the entry in `decidedFalse` names, and it is on this list
    // for the reason that list keeps: `!m n. NUM_SUB (SUC m) n = SUC (NUM_SUB m n)` writes
    // `NUM_SUB` and `SUC`. Here the two counts move together, where the row below them is the case
    // that separates them. The other five facts of that change write `Sum`, `Power` and the reals,
    // and none of them is on this list.
    // 141, and the two are BOTH of `NUM_REAL_LE_BACK`'s while `INT_REAL_LE`'s one is not here,
    // which is this list counting CONSTANTS again. The weakening leaves `!m n. NUM_LE m n` and
    // the substitution leaves `real_of_num m < real_of_num n ==> NUM_LE m n`; both write
    // `NUM_LE`. The third residue is about `int`, and no constant of the naturals survives in it.
    // So this row moves by two where `decidedFalse` moves by one, which is the split this pair of
    // counts exists to show: "the claim mentions the naturals" and "the model can compute it" are
    // different facts, and here the second residue is on this list and in `open`.
    // 144 with BOTH weakenings of 2026-09-21, which is this list counting CONSTANTS again:
    // `!n k. NUM_CHOOSE n k = ZERO` writes `NUM_CHOOSE` and `!n i. NUM_LE i n` writes `NUM_LE`,
    // both of them the naturals'. So this row moves by two where `decidedFalse` moves by one and
    // `unreadable` by one, which is the three-way split this family of counts exists to show.
    // 145 with that same residue, and **this one was predicted wrong**. The prediction was that
    // it would not move, on the reading that a claim about `converges` and `Sum` is not a claim
    // about the naturals. `named` a hundred lines above is a written set of thirteen and it holds
    // `Sum`, `Power` and `Prod`: the summation operators are indexed by `num` and were put on it
    // deliberately. So what this list counts is that set and not the sentence describing it, and
    // the same reading that missed `unreadable` yesterday missed this today — the prose beside a
    // criterion is not the criterion.
    // 149 with the bounded monotone's residue, which writes `Sum` and so is on this list for the
    // reason the rows above give.
    // 155 with all six, which is this list counting CONSTANTS: five of the residues write `Sum`
    // and the sixth writes `NUM_SUB` and `NUM_LE`, and `named` holds all three.
    // 159 with the Cauchy product's four, which write `Sum` and are on this list for the reason
    // the rows above give. Predicted before the run and right, on the criterion those rows
    // state: this list counts CONSTANTS.
    // 164 with five of the general Cauchy product's seven, 2026-09-21. Predicted and met, on
    // the criterion these rows state: this list counts CONSTANTS. The four from the product and
    // the one from the stretch write `Sum`; the squeeze's two are about arbitrary sequences and
    // write `abs` and `converges`, neither of which is on `named`.
    // 166 with `ABS_POWER_LE`'s **two** residues, both of which write `Power`. Predicted 165,
    // by counting the weakening and forgetting the substitution.
    // 170 with the four residues the two order lemmas produce, all of which write `Power`.
    // 171 with the irrationality of the root of two, whose weakening writes `real_of_num`, which is
    // on `named`: this list counts CONSTANTS, as the rows above say.
    // 172 with `CONVERGES_SHIFT`'s weakening, which writes `SUC`, the same day. Reconciled against
    // `named` after the run had named the figure rather than predicted before it.
    // 185 with thirteen of the criteria's fifteen residues, 2026-09-25, measured by the same probe
    // and on the criterion these rows state: every one that keeps `Sum`, `Power` or `NUM_LE` is on
    // this list, and the two that do not are `CONVERGES_OFFSET`'s and `SUM_TERMS_VANISH`'s, whose
    // only naturals constant was in the antecedent they dropped. None is refuted at a point, so
    // `after` below does not move.
    // 190 with five of the six polynomial-times-geometric residues, which write `Power`, `Sum` or
    // `real_of_num`; `CONVERGES_BOUNDED`'s writes none of `named`. Measured by the probe.
    // 209 with all nineteen of resolution's, 2026-09-25, derived before the run: every one of them
    // writes `NUM_LT` or `NUM_LE`, both on `named`, since a clause is indexed by `num` throughout.
    // Seventeen keep a `NUM_LT`; the width's bound and least bound lose theirs with the antecedent
    // and keep the `NUM_LE` of their conclusion.
    // 215 with six of Fermat's eight residues, 2026-09-25, by the same probe on this list: the
    // three of `NUM_PRIME_DIVIDES_CHOOSE` and one of `NUM_PRIME_NOT_DIVIDES_FACT` keep `NUM_LT`,
    // `NUM_FRESHMAN`'s keeps `SUC` and `NUM_DIVIDES_SUM`'s `NUM_SUM`; `NUM_FERMAT`'s and the other
    // of the factorial's name nothing on it. None is refuted at a point, so `after` stays.
    // 216 with `EXP_TAIL_BOUND`'s weakening, 2026-09-25, which keeps a `Sum` of `Power`s at `SUC`
    // indices and so is on this list; the other ten residues of the sine's and the cosine's
    // derivatives name `sin`, `cos` and `abs` and nothing on it. Found by the run and not predicted
    // before it: the probe that placed the buckets was read for the buckets and not for this list.
    // 229 with thirteen of Euler's fourteen residues, the same day, by the same probe on this list;
    // none is refuted at a point, so `after` stays. Tip plus this branch's delta.
    // 259 with thirty of the p-adic valuation's thirty-three residues, 2026-09-26, by the same
    // probe on this list: the three that are not here are `NUM_POW_DIVIDES_POW`'s,
    // `NUM_VALUATION_POW`'s and one of `NUM_VALUATION_UNIQUE`'s, which write `NUM_POW`,
    // `NUM_DIVIDES` and `NUM_VALUATION` and nothing on `named`. One of the thirty is refuted at a point, so `after` moves by one.
    // 262 with `TAYLOR`'s three residues, 2026-09-26, measured by the run: each keeps the `Sum`
    // and the `Power` of the conclusion; `CONTINUOUS_MUL`'s two name nothing on this list. Tip plus
    // this branch's delta.
    aboutNumbers.size shouldBe 262
    before shouldBe 0
    // 32 with the two above, and this is the place the pair SPLITS from `decidedFalse`, which
    // moved by one. `after` is the SAMPLER over `Model.Numbers`, not the procedures: both
    // weakenings are false and both are written in constants that model computes, `NUM_LT` for
    // one and `Sum` for the other, so both are refuted at a point. A procedure having no reading
    // of `Sum` and a model having a value for it are different facts, and this line is where the
    // difference is visible.
    // 33 with `POWER_MULTIPLICATIVE`'s substitution, and this is the first addition in this file
    // to move `after` at all. Every recent one left it at 32 because the model had no value for
    // the constant the new claims named -- `NUM_FLOOR`, `NUM_FACT`, `abs` and the rest -- so
    // nothing could be refuted at a point. Here the model DOES compute `Power`, and
    // `Power (x + y) z = Power x z + Power y z` fails at x = y = 1, z = 2, where the left side is
    // 4 and the right is 2.
    //
    // So this one claim sits in `open` and in `after` at once, which is the sharpest instance
    // this file has of the distinction the paragraph above draws. The PROCEDURES cannot settle
    // it, because `Power x z` at a variable exponent is an ATOM to `Ring` -- a term it does not
    // look inside -- so the claim is an equation between two distinct atoms. The MODEL settles it in
    // one evaluation. A procedure having no reading of a constant and a model having a value for
    // it are different facts, and until now the two had only ever been shown apart by claims that
    // neither could touch.
    // 34 with `NUM_DIVIDES_ONE`, the second in a row to land here after a long run that did not.
    // Its residue names no constant at all beyond the successor, so there is nothing for the model
    // to have no value for.
    // 36 with the two `NUM_MUL_POSITIVE` weakenings, both refuted at a point.
    // 37 with the one row `decidedFalse` gained, the pair moving together as it usually does:
    // `!m n p. NUM_LT m p` is refuted at a point because the sampler reads `NUM_LT` exactly.
    // 39, and the pair does NOT move together here, which is the most useful thing this figure has
    // done. Three proposals joined `aboutNumbers` and only two joined this one. The one that did
    // not is the weakening of `NUM_TRI_MONOTONE`: its residue names `NUM_LE`, so it IS a claim
    // about the naturals by the bucket above's criterion, and `Model.Numbers` has no value for
    // `NUM_TRI`, so the sampler declines at every point and refutes nothing.
    //
    // That is exactly the distinction this pair of counts exists to show and the reason it is two
    // counts rather than one: "the claim mentions the naturals" and "the model can compute it" are
    // different facts, and the same weakening is in `unreadable` above for the same reason. It was
    // derived as 40 by assuming this figure moves with `decidedFalse`, which it usually does and
    // does not have to.
    // 40 with the monotonicity's weakening, refuted at a point like the thirty-nine before it.
    // 41, with the bucket above as usual.
    // 42 with the cancellation's weakening, which moves this figure and `decidedFalse` together
    // rather than splitting them: the residue is false, and `NUM_LE` is both a constant the model
    // computes and a shape the procedures take.
    // 47, moving with `decidedFalse` by five rather than splitting from it.
    // 48 with one of the monotone family's two: `MONOTONE_LE`'s weakening is false and written in
    // `NUM_LE` alone, which `Model.Numbers` computes exactly, so the search finds a point in it.
    // The other names `SUC` and quantifies over a sequence, which the model has no reading of, so
    // it counts in the bucket above and not here. One of two, which is this pair of counts doing
    // what it exists to do.
    // 50 with the concatenation's two, moving with `decidedFalse` and `withAPoint` together
    // rather than splitting from either: both residues are false, and both are written in
    // `NUM_LT` or `NUM_LE` alone, which `Model.Numbers` computes exactly, so each is a constant
    // the model reads and a shape the procedures take at once. The eight word weakenings split
    // the other way and completely: none of them is readable, so none reaches this count even
    // though three of them keep a constant of the naturals in the residue.
    // 51 with one of `Peano`'s two, splitting from `aboutNumbers` above, which took both. This
    // figure is the SAMPLER over `Model.Numbers`: `!x y z u. x + z <= y + u` is refuted at a point
    // and `!x y z. NUM_SUM x z <= NUM_SUM y z` cannot be, its two leading variables being
    // functions there is nothing to sample. Derived in advance for the reason `withAPoint` gives:
    // this line sits behind `aboutNumbers` in the same test and never ran while that one was red.
    // 52 with one of the order map's three, splitting from `aboutNumbers` above, which took two.
    // The sampler refutes `!m n. NUM_LE m n` at `m = 1, n = 0`; the other residue on that list is
    // `real_of_num m < real_of_num n ==> NUM_LE m n`, which is **true**, so there is no point to
    // find. Two constants of the naturals, one refutation, which is this pair of counts doing
    // what it exists to do. It was not derived in advance either, for the reason the line above
    // has now recorded three times.
    // 53 with that same single weakening, which is the sampler and `aboutNumbers` moving together
    // rather than splitting: the one residue on that list is refutable at a point, where the two
    // entries above it each had one that was not. `NUM_SUC_SUB_SELF` produces no weakening at all,
    // having no antecedent to drop, and the four facts in `Series` write no constant of the
    // naturals in a residue.
    // 54 with that same single residue, the sampler and `aboutNumbers` moving together where the
    // `NUM_CHOOSE` one moves neither: it is on `aboutNumbers` and in `unreadable`, so it is
    // counted as being about the naturals and is refuted at no point at all.
    // 55 with the bounded monotone's residue, `!f g n. Sum f n <= Sum g n`, and the mechanism
    // was **measured rather than derived**, because the entry four rows up would have predicted
    // the opposite: it says a claim whose two leading variables are functions gives the sampler
    // nothing to sample. That is true of `NUM_SUM` over the naturals and is **not** true of `Sum`
    // over the reals, which this residue settles — printing what the search refutes shows it
    // among them, beside the two residues of `SUM_CONGRUENCE` and its bounded twin, which are
    // refuted too. So the reading transfers between the two operators and the note above does not
    // say that it does not.
    // 57, and **the prediction said 56**. It was that this row moves with `decidedFalse` and by
    // the same single residue on `num`; two of the six move it. The other is one of the five
    // about `Sum`, which this sampler refutes at a point while the PROVER returns `Unsettled`
    // for it — so it is in `open` above and here, and in `decidedFalse` nowhere.
    //
    // That is the pair of instruments this row exists to separate, and the row above says so in
    // as many words: `decidedFalse` is the prover's verdict and this is the sampler's, and
    // nothing makes them move together. The prediction collapsed them again after the same
    // mistake had been made three times about `open` and `unreadable`. Both this line and
    // `withAPoint` were set in the same pass as the counts they sit behind rather than after a
    // red, which is what the paragraph four rows up has asked for five times; `withAPoint` was
    // right and this was not, and the pass is what showed it.
    // 58 with `POWER_NONNEG`'s residue, `!x n. 0 <= Power x n`, refuted at a point by this sampler
    // where the audit's search above did not refute it: the model of the naturals computes `Power`
    // at a numeral exponent, which is the difference this pair of counts exists to show.
    // 59 with resolution's `!k v s inputs m. 0 < m`, which the sampler refutes at `m = 0`: the same
    // residue as `decidedFalse`'s and `withAPoint`'s, so the three move together here, and this
    // line sat behind `aboutNumbers` on the first run.
    // 60 with the valuation's `!x y. 0 < x ==> 0 < y ==> x = y`, refuted at `x = 4, y = 8`: the
    // same residue as `decidedFalse`'s and `withAPoint`'s, the three moving together in one pass
    // from one probe.
    after shouldBe 60
  }

  /* ------------------------------------------------------ the false positive it produced */

  "The certified weakening of `MUL_INVERSE`" should "not be read as an unnecessary hypothesis" in {
    // The finding of the first run, and the reason this test exists. Dropping `~(x = 0)` from
    // `MUL_INVERSE` gives `!x. x * inv x = 1`, which is FALSE at zero, and the prover reports it
    // `Conditional`: `Field` proves it while assuming exactly the hypothesis that was dropped.
    //
    // The hypothesis had not gone anywhere. It moved from the left of the arrow to the left of the
    // turnstile, and a reading that looked at the novelty standing alone could not see the
    // difference, because `Conditional` folds into `Earned` there and rightly so.
    //
    // That is the exact merge this repository is built not to make. It is asserted here so that a
    // future reading that looks at the standing again fails.
    //
    // **The count moved on 2026-09-11 and the reading did not.** On that day there were twenty
    // earned proposals rather than one, because the substitution source produces theorems: `LT_ADD`
    // with `<` swapped for `le` is a real lemma this library did not hold. What is asserted here is
    // the weakening that is NOT one, by name, and that nothing reads it as an unnecessary
    // hypothesis.
    val earned = findings.filter(_.standing.contains(Novelty.Standing.Earned))
    val fromWeakening = earned.filter(_.proposal.source == Propose.Source.Weakened)

    fromWeakening.size shouldBe 1
    fromWeakening.head.proposal.from shouldBe "MUL_INVERSE"
    fromWeakening.head.reading.get.report.outcome shouldBe Cost.Outcome.Conditional
    fromWeakening.head.reading.get.report.conditions should not be empty
    fromWeakening.head.unnecessary shouldBe false

    // And the other side: what the substitution source earned is a gain rather than a defect, and
    // the two are different questions asked of the same word.
    earned.count(_.gained) shouldBe earned.size - 1
  }
}
