package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.*

/**
 * What a whole corpus costs, which is a question only the proof record made askable.
 *
 * Track R measures how many of another library's ring goals this system proves. This asks the two
 * questions that come after: how many of them are **not** identities here but identities at a
 * price, and what the corpus as a whole is **believed on**.
 *
 * The second is the one worth the suite. A prover's axioms are a list in a document, and which of
 * them a body of work actually uses has never been a number anybody could produce. Here it is one,
 * and the answer over an entire ring test file is that fifteen of the sixteen take part and
 * completeness does not: a corpus about polynomial identities never reaches the axiom that makes
 * the reals the reals rather than the rationals. Nothing about that is surprising, and the point is
 * that it is measured rather than assumed.
 *
 * The counts are asserted rather than printed. They move when the corpus moves, which is frozen at
 * the commit `RingCorpusSpec`'s notice names, or when a tactic changes what it reaches for, which
 * is the change worth being told about.
 */
class CostCorpusSpec extends AnyFlatSpec with Matchers {

  /**
   * The corpus, priced, and measured in one place rather than in each reader.
   *
   * `RingCost` holds it because `garden.xeno.symbolum.tactics.Evaluation` prints these counts into
   * `docs/evaluation.md` and this file asserts them: two readings of one corpus is how that
   * document came to carry a per-rule census summing to 196623 beside a total line saying 153953.
   */
  private val reals = RingCost.reals

  private def corpus: Vector[LeanCorpus.Declaration] = RingCost.declarations

  private def reports: Vector[Cost.Report] = RingCost.reports

  private def count(outcome: Cost.Outcome): Int = reports.count(_.outcome == outcome)

  "The corpus" should "come back with an outcome for every goal that reads" in {
    corpus.size shouldBe 75
    reports.size shouldBe 46

    count(Cost.Outcome.Proved) shouldBe 37
    count(Cost.Outcome.Conditional) shouldBe 6
    count(Cost.Outcome.Fails) shouldBe 2
    count(Cost.Outcome.Unsettled) shouldBe 1

    info(s"${reports.size} goals: ${count(Cost.Outcome.Proved)} proved outright, " +
      s"${count(Cost.Outcome.Conditional)} proved at a price")
  }

  "The six that are not identities here" should "each name the denominator they need" in {
    // Mathlib's inverse is total and this one is not, so a goal upstream states as an identity is
    // an identity away from zero here. That is a difference between two theories and not a
    // shortfall, and it is only visible because the condition comes back rather than being
    // absorbed into a refusal.
    val priced = reports.filter(_.outcome == Cost.Outcome.Conditional)

    every(priced.map(_.conditions)) should not be empty
    priced.flatMap(_.conditions).map(reals.show).distinct.sorted shouldBe
      Vector("~(x = 0)", "~(y = 0)", "~(z = 0)")
  }

  "The three the corpus does not close either" should "come back with the point they fail at" in {
    // Not a shortfall of this system, and worth the assertion for that reason. Two of the three are
    // stated upstream with a hypothesis this extraction drops, so what is asked here is a different
    // and false claim; the third, `a - b - c - d = 0`, is closed upstream with `test_sorry` and is
    // a trace test for the normaliser rather than a theorem. A point is the right answer to all
    // three, and a reader can check it without trusting anything here.
    val open = reports.filter(report =>
      report.outcome == Cost.Outcome.Fails || report.outcome == Cost.Outcome.Unsettled
    )

    open.size shouldBe 3
    every(open.map(_.point)) should not be empty
  }

  /* ------------------------------------------------- what the corpus is believed on */

  "The corpus as a whole" should "reach fifteen of the sixteen axioms, and not completeness" in {
    val reached = reports.filter(_.outcome == Cost.Outcome.Proved).flatMap(_.axioms).toSet
    val held = Real.standard.axioms.map(_._2.conclusion).toSet

    held.size shouldBe 16
    reached.size shouldBe 15

    val untouched = held.diff(reached)
    untouched.size shouldBe 1
    reals.show(untouched.head) should include("<=")
    reals.show(untouched.head) should startWith("!x:real -> bool")

    info(s"never reached by any of these proofs: ${reals.show(untouched.head)}")
  }

  it should "reach a different number of them per goal, which is what makes the question worth asking" in {
    // A single figure for the corpus would say what the theory permits. The spread is what says
    // what each proof costs: ten goals rest on one axiom and seven on fifteen, and the difference
    // is what settled them.
    //
    // **The bottom of the spread moved on 2026-09-11, from three to one, and the reason is worth
    // reading.** `Prove` now asks its library before it asks a procedure, so a goal that IS a held
    // lemma is proved by instantiating that lemma rather than by re-deriving it through the ring
    // normalisation. Ten of these are of that kind, and one axiom is exactly right for them: the
    // proof reaches the axiom the lemma is, and nothing else. The figure went down because the
    // proofs got cheaper, which is the direction this number is supposed to move in.
    val reach = reports.filter(_.outcome == Cost.Outcome.Proved).map(_.axioms.size)
    info(s"axioms per proof: ${reach.sorted.mkString(", ")}")

    reach.min shouldBe 1
    reach.max shouldBe 15
    reach.sorted.apply(reach.size / 2) shouldBe 8
    reach.count(_ == 1) shouldBe 10
  }

  "The proofs behind the corpus" should "add up to a size a second checker has to replay" in {
    // The number `modules/checker` is measured against. It is the whole of what a differential
    // benchmark costs, and until a theorem recorded its derivation there was nothing to count.
    // A floor rather than a figure, and the figure is in the `info` below. The sum fell from over
    // two hundred thousand to a hundred and ninety-six on 2026-09-11, because ten of the proofs
    // stopped being derivations and became lookups. A test asserting the old number would have gone
    // red for an improvement, which is what a floor is for.
    //
    // **Both floors came down again later the same day**, and this is the second time a floor has
    // caught an improvement rather than a regression. The rewriter stopped building a theorem to
    // report that it had done nothing, so every proof lost about a third of its nodes: the largest
    // fell from over thirty thousand to twenty-five, and the sum with it. The floors are set under
    // where they now stand rather than at it, because they exist to catch a proof that stopped
    // happening, and a floor that tracks the current figure catches nothing.
    val inferences = reports.filter(_.outcome == Cost.Outcome.Proved).map(_.inferences)

    // **Both came down a third time on 2026-09-11**, from 153953 to 122862 and from the low
    // twenty-thousands to the high teens, when `Conv.refl` began sharing the reflexivity of an
    // atom. The floors move under the new figures rather than staying where they were: a floor set
    // above the measurement stops being a guard against a proof that stopped happening and becomes
    // a guard against the proof getting cheaper.
    inferences.sum should be > 80000
    inferences.max should be > 12000

    info(s"${inferences.sum} inferences over ${inferences.size} proofs")
  }

  it should "be a shape and not only a length, which is the cost measure a machine cannot move" in {
    // The card that asks for the constant factor says, correctly, that none of its gains can be
    // shown without a cost corpus, and that the documents here record the same scale differing by
    // a factor of two in one afternoon. A wall clock measures the afternoon it was read in: this
    // suite ran in 41 seconds and in 6 minutes 39 on the same tree and the same day, because
    // something else on the machine was busy.
    //
    // A census of a proof's nodes is a function of the proof. Two runs agree, two machines agree,
    // and a change claiming to have removed work has to show the count moving. That is what makes
    // it a corpus somebody can be held to.
    //
    // What it said when it was written was the claim the card is built on: **about a third of every
    // proof here is reflexivity**, built by a rewriting pass to report that nothing happened.
    // Measured over somebody else's corpus rather than over an example, and reported rather than
    // pinned to a percentage, because the percentage moves with the tactics and the fact that it is
    // a third rather than a twentieth is the part that decides anything.
    //
    // **The repair landed on 2026-09-11 and this is what it did**, which is not what the shape of
    // the number suggests. The corpus went from 209k inferences to 154k, and the reflexivity in it
    // from 90k to 46k: nearly half of it gone, and gone along with the congruence and transitivity
    // that existed only to carry it. What is left is still about three tenths, because a congruence
    // needs an equation on both sides and the side that did not change is a reflexivity that is
    // doing work. The fraction barely moved and the proof halved, which is why a fraction was the
    // wrong thing to pin and the census is what this suite reports.
    // The census is `RingCost`'s, which is the same one `docs/evaluation.md` prints: what this file
    // asserts about it and what that document shows a reader are one measurement.
    val proved = RingCost.proved
    val whole = RingCost.census.toMap

    val total = RingCost.inferences
    val reflexivity = whole.getOrElse("Reflexivity", 0)

    info(
      s"$total inferences: " +
        RingCost.census.map { case (rule, howMany) => s"$rule $howMany" }.mkString(", ")
    )
    info(f"reflexivity is ${100.0 * reflexivity / total}%.1f%% of them")

    // Every proof has one, so the census is not empty because nothing was measured.
    every(proved.map(_.census.size)) should be > 3
    total shouldBe proved.map(_.inferences).sum

    // **The bound turned over on 2026-09-11, and the turn is the result rather than a maintenance
    // edit.** It was a floor at a fifth, because the claim it pinned was that about a third of every
    // proof is reflexivity built to report that nothing happened, and a third rather than a
    // twentieth is what decides whether repairing that is worth doing. It was repaired twice: the
    // rewriter stopped building a theorem to say it had done nothing, and then `Conv.refl` stopped
    // building the same leaf once per use. The corpus went 209386, then 153953, then 122862, and
    // the reflexivity in it 90k, then 46k, then 15385.
    //
    // A floor cannot say anything about that any more, so this is a ceiling. What is worth guarding
    // now is the opposite claim: the leaves are shared and the residue is structural, so if
    // reflexivity climbs back over a fifth something has started building them again.
    reflexivity.toDouble / total should be < 0.2
  }
}
