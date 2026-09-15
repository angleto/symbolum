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
 * The counts below are calibration. They say that the loop reproduces twelve of the fifty-five
 * lemmas its rediscovering source can reach, that it reaches none at all by the other source out of
 * a hundred and seventeen tries, and that everything it reaches it proves. None of that is evidence
 * that anything was discovered, and `docs/evaluation.md` says at length why a figure like this is
 * not a benchmark. What it is: the number that has to exist before any claim about the loop is
 * anything but anecdote.
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
    recoveries.size shouldBe 16
    recoveries.map(_.reached).distinct.size shouldBe 12

    val pairs = recoveries.map(r => (r.proposal.from, r.proposal.change, r.reached)).toSet
    pairs should contain(("ADD_SYM", "+ became *", "MUL_SYM"))
    pairs should contain(("MUL_SYM", "* became +", "ADD_SYM"))
    pairs should contain(("ADD_ASSOC", "+ became *", "MUL_ASSOC"))
    pairs should contain(("LE_FROM_ZERO", "le became <", "LT_FROM_ZERO"))
  }

  it should "reach none of them by dropping a hypothesis, which the file predicted and nobody had measured" in {
    // `Propose.substitutions` says in prose that dropping a hypothesis makes a lemma weaker, and
    // that a weaker form of something already held is not a lemma anybody was missing. That was an
    // argument. This is the measurement: 117 weakenings, and not one of them states a lemma the
    // library holds.
    //
    // It is the cleanest possible confirmation and it is also a limit, which is why it is asserted
    // rather than left as a satisfying zero. The loop has exactly **one** source that can
    // rediscover, so every figure in this file is a figure about the operator substitution and its
    // four swaps. A second such source would move all of them, and the day one arrives this
    // assertion is what says so.
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
    propose.weakenings.size shouldBe 285
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
    propose.mutable.size shouldBe 75
    recoveries.map(_.reached).distinct.foreach(name => propose.mutable should contain(name))
  }

  it should "prove every one, and the price splits them in two" in {
    // All 16 come back `Proved`, which is the least surprising fact here: they are lemmas this
    // library holds, so a failure would be a finding about the tactic surface and not about the
    // generator. It is asserted because that is exactly why it is worth knowing.
    //
    // **The interesting half is the price.** Four are settled by the ring normalisation at once and
    // come back `Immediate` at 77 and 108 inferences; the other twelve are order facts the ring
    // does not decide, come back `Known`, and cost between 3706 and 7351. Forty to seventy times
    // more for a claim of the same standing, and the novelty scale calls all sixteen not-news
    // either way, which is correct and is the scale doing its job on its own hardest case: a
    // rediscovery is precisely a claim that looks new and is not.
    readings.size shouldBe 16
    readings.map(_.report.outcome).distinct shouldBe Vector(Cost.Outcome.Proved)

    readings.count(_.standing == Novelty.Standing.Immediate) shouldBe 4
    readings.count(_.standing == Novelty.Standing.Known) shouldBe 12
    readings.count(_.standing == Novelty.Standing.Earned) shouldBe 0

    val immediate = readings.filter(_.standing == Novelty.Standing.Immediate).map(_.inferences)
    val known = readings.filter(_.standing == Novelty.Standing.Known).map(_.inferences)
    immediate.max should be < known.min
  }
}
