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
 * worth anything because the machine is demonstrably running: fifty-one of the hundred and
 * seventy-four proposals are decided **false**, which is a dropped hypothesis that was
 * load-bearing, correctly refuted with a point.
 *
 * The two figures in that sentence were twenty-five and forty-eight until 2026-09-11 and were not
 * moved when the assertions below were; they are read off the assertions now rather than off a
 * memory of them.
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
    proposals.size shouldBe 216
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
      Vector("* became +", "+ became *", "< became le", "le became <")
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
    decidedFalse shouldBe 63

    // Twenty-three of the twenty-five come with the point they fail at, and two do not: the claim
    // is decided false by quantifier elimination and the abduction that would name a point comes
    // back with none. That is two different answers and the number is written out rather than
    // asserted away, because "decided false" and "decided false, here" are worth different amounts
    // to a reader and merging them is the habit this repository does not have.
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
    withAPoint shouldBe 61
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
    open shouldBe 163
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
    unreadable shouldBe 54
    open + unreadable + findings.count(_.standing.contains(Novelty.Standing.False)) +
      findings.count(_.standing.contains(Novelty.Standing.Earned)) +
      findings.count(_.standing.contains(Novelty.Standing.Known)) +
      findings.count(_.standing.contains(Novelty.Standing.Immediate)) +
      findings.count(_.standing.contains(Novelty.Standing.Decided)) shouldBe findings.size
  }

  "The proposals about the naturals" should "carry the point they fail at, which they did not" in {
    // The measurement card `88463baa` was opened for, as an A/B on one line. `Model.Reals`
    // interprets the seven constants the theory of the reals declares and nothing about `num`, so
    // every claim naming `Sum`, `Power`, `Prod`, `SUC`, `NUM_ADD`, `NUM_MUL`, `NUM_LE` or
    // `real_of_num` had no point that could be evaluated, and the search truthfully reported that
    // nobody could ask. `Model.Numbers` interprets them exactly, and `Refutation.grid` samples a
    // variable of type `num` as a natural number and one of type `num -> real` as a function.
    //
    // Twenty-eight of the proposals name one of those constants. None of them is decided even now,
    // for the reason above; twenty-one are refuted at a point a reader can check, where none was.
    // Those two figures were nineteen and sixteen when this was written and were left behind twice
    // while the assertions at the end of the test were updated; they are the assertions now.
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
    aboutNumbers.size shouldBe 99
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
    after shouldBe 42
  }

  /* ------------------------------------------------------ the false positive it produced */

  "The one proposal that comes back certified" should "not be read as an unnecessary hypothesis" in {
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
    // **The count moved on 2026-09-11 and the reading did not.** There are twenty earned proposals
    // now rather than one, because the substitution source produces theorems: `LT_ADD` with `<`
    // swapped for `le` is a real lemma this library did not hold. What is asserted here is the
    // weakening that is NOT one, by name, and that nothing reads it as an unnecessary hypothesis.
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
