package garden.xeno.symbolum.checker

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.theories.*

/**
 * Every theorem this system produces, read a second time by something that is not the kernel.
 *
 * This is the differential half of track K in `docs/evaluation.md`, which the document called
 * unmeasurable for as long as a theorem recorded nothing. Two implementations agreeing is evidence
 * of a different kind from one implementation being careful.
 *
 * The theories are here at test scope only. The checker itself depends on the kernel and knows no
 * mathematics; what it needs from a development is proofs to read.
 */
class ReplaySpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[?, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  /**
   * The verdict, against the theory the proof belongs to, with the axioms checked and not counted.
   *
   * Counted was all this file did until 2026-09-11, and the gap was not small: the checker's own
   * note says it "cannot check an axiom", which is true of an axiom's **truth** and false of its
   * **membership**, and a proof of `|- F` whose derivation says `Axiom(F)` came back `Holds` with
   * `F` in the report. Every assertion here read `axioms.size`.
   *
   * **The theory is a parameter and not a constant**, and that is the question rather than a
   * convenience: checking the naturals' facts against the theory of the reals refuses them, and
   * rightly, since they rest on choice and on infinity and that theory asserts neither. The first
   * version of this file passed one theory for everything and found out by being refused, which is
   * why `Replayed` carries a theory beside each proof.
   */
  private def holds(name: String, theorem: Kernel.Thm, theory: Theory): Check.Holds =
    Check.proof(theorem, theory) match {
      case verdict: Check.Holds => verdict
      case Check.Fails(step, rule, why) =>
        fail(s"$name: the checker refused a $rule step, expecting $why, on ${step.conclusion}")
      case Check.RestsOnUnvouched(axiom, _) =>
        fail(s"$name: the proof rests on $axiom, which the theory does not assert")
    }

  "A proof resting on an axiom the theory never asserted" should "be refused, not counted" in {
    // The shape that got through, and the reason it could: a theorem is a JVM object whose
    // constructor is public in bytecode however `private` reads in the source, so a caller using
    // reflection makes one without a cast and without an access check. That is measured in
    // `TrustBoundaryTwinSpec`; what matters here is what happens next.
    //
    // A forged theorem whose derivation does not add up is refused by the walk. One whose
    // derivation says `Axiom(F)` adds up perfectly — an axiom step is a closed proposition standing
    // alone, and `F` is one. What was missing is the question with an answer: is it an axiom of
    // this theory.
    val falsity = garden.xeno.symbolum.logic.Logic.standard.falsity
    val forged = classOf[Kernel.Thm]
      .getDeclaredConstructors
      .head
      .newInstance(List.empty[Term], falsity, Derivation.Axiom(falsity))
      .asInstanceOf[Kernel.Thm]

    val theory = Order.standard.reals.theory

    Check.proof(forged) shouldBe a[Check.Holds]
    Check.proof(forged, theory) match {
      case Check.RestsOnUnvouched(axiom, asserted) =>
        asserted should not be empty
        asserted should not contain axiom
      case other => fail(s"expected the axiom to be refused, got $other")
    }

    // And the serialised route says the same thing, since it is the same question about text.
    Check.text(Proof.write(forged), theory) match {
      case Right(_: Check.RestsOnUnvouched) => succeed
      case other => fail(s"expected the serialised route to refuse it too, got $other")
    }
  }

  "Everything the tactics prove" should "hold when a second implementation reads it" in {
    // The population is `Replayed`, and it is a list this file no longer owns: `SerialisedSpec`
    // checks the same proofs as text and `garden.xeno.symbolum.tactics.Evaluation` prints their counts into
    // `docs/evaluation.md`. Three copies of one list is how the document came to report six
    // theorems where the suite replayed ten.
    Replayed.entries.foreach { entry =>
      val verdict = holds(entry.label, entry.theorem, entry.theory)
      info(s"${entry.label}: ${verdict.steps} steps, ${verdict.axioms.size} axioms")
    }
  }

  "A propositional theorem that costs no axiom" should "hold, and report none" in {
    // The claim `Minimal` exists to make, checked by something that never heard of it. A truth-table
    // procedure would have put the choice operator under this, and the axiom list a second reader
    // computes for itself is where that would show.
    val entry = Replayed.entry("`p /\\ q ==> p`, propositional")
    val verdict = holds(entry.label, entry.theorem, entry.theory)

    verdict.axioms shouldBe empty
    info(s"${verdict.steps} steps, no axiom")
  }

  "The naturals" should "hold too, and say which axioms each part rests on" in {
    val properties = holds(
      "the successor's properties",
      Replayed.entry("the successor's properties").theorem,
      Natural.standard.theory
    )
    val induction = holds(
      "induction",
      Replayed.entry("induction over the naturals").theorem,
      Natural.standard.theory
    )

    // The fact the record surfaced and no sequent could state. The successor being injective and
    // missing zero rests on both axioms, choice and infinity. **Induction rests on neither.** It
    // follows from the definition of `NUM_REP` alone: infinity is what makes the naturals infinite,
    // not what makes induction hold, and if `ind` had one element `num` would be a singleton and
    // induction would hold of it vacuously.
    properties.axioms should have size 2
    induction.axioms shouldBe empty
  }

  it should "be refused against a theory that asserts neither of the axioms they rest on" in {
    // The other half of the test above, and the reason the theory is a parameter rather than a
    // constant. The successor's properties rest on choice and on infinity; the theory of the reals
    // asserts sixteen axioms and neither of those is among them. So this proof is a proof, and it
    // is not a proof **there**, and until 2026-09-11 the checker had no way to say so.
    val properties = force(Natural.standard.fact(Natural.SuccessorProperties))

    Check.proof(properties, Order.standard.reals.theory) shouldBe a[Check.RestsOnUnvouched]
    Check.proof(properties, Natural.standard.theory) shouldBe a[Check.Holds]
  }

  "A proof of a theorem that rests on an axiom" should "report that axiom and not verify it" in {
    // The one node nothing can check, which is what a trusted base is. A checker that claimed to
    // have verified an axiom would be claiming the thing that cannot be claimed.
    val entry = Replayed.entry("`ADD_SYM`, an axiom of the reals")
    val axiom = entry.theorem
    val verdict = holds("commutativity of addition", axiom, entry.theory)

    verdict.steps shouldBe 1
    verdict.axioms should have size 1
    verdict.axioms.head shouldBe Read.expr(axiom.conclusion)
  }
}
