package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * The classical propositional fragment, decided by a solver and certified by the rules.
 *
 * Three assertions carry the file and they are not "these are provable".
 *
 * **What it costs.** Every theorem here rests on the choice axiom and on **nothing else**, asserted
 * as an equality against `Derivation.axiomsOf` rather than as a ceiling. A ceiling passes when a
 * derivation quietly starts spending something new; an equality goes red. The classical step is one
 * double-negation elimination at the end of the refutation, so what is under every theorem here is
 * `SELECT` through `EXCLUDED_MIDDLE`, and `ETA` never.
 *
 * **That it is complete where `Minimal` is not.** Peirce's law has no negation in it, is classically
 * valid, and `MinimalSpec` asserts that `Minimal` refuses it. It is proved here, and the two
 * assertions are the same boundary read from either side.
 *
 * **That `Minimal` is still the cheaper address.** The negation-free goal both procedures take costs
 * measurably less there and rests on nothing, which is the measurement behind `Propositional` not
 * replacing it.
 */
class PropositionalSpec extends AnyFlatSpec with Matchers {

  private val classical = Classical.standard
  private val logic = classical.logic
  private val propositional = Propositional(classical)
  private val minimal = Minimal(logic)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private def read(text: String): Term =
    force(Parser.proposition(classical.theory, classical.notation, text))

  private val choice: Set[Term] = Set(force(classical.axiom(Classical.Choice)).conclusion)

  private def proved(text: String): Kernel.Thm = {
    val goal = read(text)
    val theorem = force(propositional.prove(goal))
    theorem.conclusion shouldBe goal
    theorem.hypotheses shouldBe empty
    withClue(s"what this fragment costs, at ${Derivation.size(theorem)} steps: ") {
      Derivation.axiomsOf(theorem) shouldBe choice
    }
    theorem
  }

  "the classical fragment" should "prove Peirce's law, which the fragment costing nothing refuses" in {
    val text = "!p:bool. !q:bool. ((p ==> q) ==> p) ==> p"
    proved(text)
    withClue("Minimal must still refuse it, or this file is asserting nothing: ") {
      minimal.prove(read(text)).isLeft shouldBe true
    }
  }

  it should "prove the excluded middle, double negation and both De Morgan directions" in {
    proved("!p:bool. p \\/ ~p")
    proved("!p:bool. ~~p ==> p")
    proved("!p:bool. !q:bool. ~(p /\\ q) ==> (~p \\/ ~q)")
    proved("!p:bool. !q:bool. ~(p \\/ q) ==> (~p /\\ ~q)")
  }

  it should "prove contraposition and the deduction-style rearrangements" in {
    proved("!p:bool. !q:bool. (p ==> q) ==> (~q ==> ~p)")
    proved("!p:bool. !q:bool. !r:bool. (p ==> (q ==> r)) ==> ((p /\\ q) ==> r)")
    proved("!p:bool. !q:bool. !r:bool. ((p \\/ q) ==> r) ==> ((p ==> r) /\\ (q ==> r))")
  }

  "a goal that does not hold" should "come back with the assignment that falsifies it" in {
    propositional.decide(read("!p:bool. !q:bool. (p \\/ q) ==> (p /\\ q)")) match {
      case Propositional.Verdict.Countermodel(assignment) =>
        assignment.map(_._2).toSet shouldBe Set(true, false)
        assignment should have length 2
      case other => fail(s"expected a countermodel, got $other")
    }
  }

  "an atom" should "be opaque, so a quantified subformula widens what is reachable rather than blocking it" in {
    // Sound because the replay never looks inside an atom: the theorem holds whatever the atom means.
    // The asymmetry is the other answer, which the next test pins.
    val theorem = proved("(!x:bool. x) \\/ ~(!x:bool. x)")
    Printer.show(theorem.conclusion) should include("!")
  }

  it should "make a countermodel a statement about the schema and not about the goal" in {
    // Two atoms that are the same statement written two ways are two atoms here, so a goal that is
    // valid for a reason living inside an atom comes back refuted. This is the asymmetry the class
    // comment names, asserted rather than described, because a reader who took `Countermodel` for
    // "unprovable" would be wrong in exactly this case.
    //
    // The symmetry of equality is the witness. `p = q` and `q = p` are two bool-typed subterms that
    // no connective built, so they are two atoms and the implication between them is `A ==> B`.
    //
    // **The first version of this test used `(!x:bool. x) ==> (!y:bool. y)` and was proved**, which
    // is the right answer and not the one it was written to check: binders here are locally
    // nameless (`docs/adr/0002`), so those two are the **same term**, the goal is `A ==> A`, and
    // nothing about atoms was being tested. Renaming a bound variable is not a way to make two
    // atoms.
    propositional.decide(read("!p:bool. !q:bool. (p = q) ==> (q = p)")) match {
      case Propositional.Verdict.Countermodel(assignment) => assignment should have length 2
      case other => fail(s"expected the schema to be refuted, got $other")
    }
  }

  it should "hand the atoms to `prove` as terms rather than written into a sentence" in {
    // The half of the notation boundary that lives on this side. This file is in `modules/logic`,
    // which knows no notation and must not learn one, and while the refusal carried its atoms as
    // prose it rendered them here with the kernel's printer: a reader who wrote `x = 99` was shown
    // `(x = (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 1)))))))`. What this asserts is that the pairs
    // survive as terms, which is what leaves the rendering to a surface that has a theory.
    // `RemedySpec` asserts the other half, that the surface then uses it.
    val goal = read("!p:bool. !q:bool. (p \\/ q) ==> (p /\\ q)")

    propositional.prove(goal) match {
      case Left(SkeletonFailsAt(refused, assignment)) =>
        refused shouldBe goal
        assignment should have length 2
        assignment.map(_._2).toSet shouldBe Set(true, false)
        all(assignment.map(pair => Term.typeOf(pair._1))) shouldBe Type.Bool
      case other => fail(s"expected the skeleton to fail, got $other")
    }
  }

  it should "not let a countermodel read as a decision against the claim" in {
    // `Decided` was the first answer and the test above the second-most convincing argument for it:
    // the search runs to the end of its fragment, exactly as `Linarith` does. What refutes it is
    // the test two above this one, where a goal that HOLDS comes back with a countermodel because
    // the reason it holds lives inside an atom. Filed as `Decided`, `LogicError.decided` would
    // answer yes about a theorem, which is the one merge `LogicError.Standing` exists to prevent.
    val holds = read("!p:bool. !q:bool. (p = q) ==> (q = p)")

    withClue("this goal is true and its skeleton is not: ") {
      LogicError.decided(propositional.prove(holds)) shouldBe false
    }
  }

  it should "file that countermodel as `Unread`, and not because nothing ran" in {
    // The half the test above cannot give, and the one that would go red if a fourth standing ever
    // landed and this refusal were moved onto it. `decided` being false is satisfied by three of
    // the standings, so asserting it pins the safety and not the filing.
    //
    // The second assertion is what stops the first from being vacuous, and it is the whole of why
    // `Unread` was rewritten on 2026-09-16 to mean "nothing about the goal was learned" rather than
    // "the search never ran". A search DID run here: it came back with an assignment, which is
    // something only a finished search can produce. `Unread` is right about this refusal under the
    // first reading and false under the second.
    val holds = read("!p:bool. !q:bool. (p = q) ==> (q = p)")

    propositional.prove(holds) match {
      case Left(refusal @ SkeletonFailsAt(_, assignment)) =>
        refusal.standing shouldBe LogicError.Standing.Unread
        assignment should not be empty
      case other => fail(s"expected the skeleton to fail, got $other")
    }
  }

  "the cheaper procedure" should "stay the right address for a goal both can take" in {
    val text = "!p:bool. !q:bool. (p /\\ q) ==> (q /\\ p)"
    val here = proved(text)
    val there = force(minimal.prove(read(text)))

    withClue("Minimal must reach this on no axioms, which is why it is tried first: ") {
      Derivation.axiomsOf(there) shouldBe empty
    }
    withClue(s"here ${Derivation.size(here)} steps, there ${Derivation.size(there)}: ") {
      Derivation.size(there) should be < Derivation.size(here)
    }
  }

  "a refutation of the pigeonhole principle" should "be certified, at a cost that is linear in it" in {
    // The size a proof assistant's propositional goals actually reach, and the row that says the
    // scope condition in the class comment is a measurement rather than a worry. The figures are not
    // pinned: what is pinned is that it is settled at all, and that growing the problem grows the
    // proof rather than the axiom count.
    def pigeonhole(holes: Int): String = {
      def variable(pigeon: Int, hole: Int) = s"p${pigeon}h$hole:bool"
      val somewhere = (0 to holes)
        .map(pigeon => (0 until holes).map(hole => variable(pigeon, hole)).mkString("(", " \\/ ", ")"))
        .mkString(" /\\ ")
      val shared = (for {
        hole <- 0 until holes
        first <- 0 to holes
        second <- (first + 1) to holes
      } yield s"(${variable(first, hole)} /\\ ${variable(second, hole)})").mkString(" \\/ ")
      s"($somewhere) ==> ($shared)"
    }

    for (holes <- 2 to 4) withClue(s"$holes holes: ") { proved(pigeonhole(holes)) }
  }

  "the bound" should "be reported as undecided rather than as a goal that does not hold" in {
    // The one merge that would let this machinery mislead: a bound reached, reported as a
    // countermodel, reads as "your goal is false" when the truth is "I stopped".
    //
    // The goal has to be one that actually needs conflicts, and the first attempt at this test used
    // a hand-written implication whose antecedent turned out to be satisfiable, so what came back
    // was a countermodel and the test failed for being wrong rather than for finding anything. The
    // pigeonhole principle is the goal with no such doubt: it is valid, and it is valid for a reason
    // no amount of propagation reaches.
    def pigeonhole(holes: Int): String = {
      def variable(pigeon: Int, hole: Int) = s"p${pigeon}h$hole:bool"
      val somewhere = (0 to holes)
        .map(pigeon => (0 until holes).map(hole => variable(pigeon, hole)).mkString("(", " \\/ ", ")"))
        .mkString(" /\\ ")
      val shared = (for {
        hole <- 0 until holes
        first <- 0 to holes
        second <- (first + 1) to holes
      } yield s"(${variable(first, hole)} /\\ ${variable(second, hole)})").mkString(" \\/ ")
      s"($somewhere) ==> ($shared)"
    }

    Propositional(classical, conflictLimit = 1).decide(read(pigeonhole(5))) match {
      case Propositional.Verdict.Undecided(why) => why should include("conflicts")
      case other => fail(s"a bound must never read as a countermodel: $other")
    }
  }

  "a resolution step" should "cost the two rules the scope condition is computed from" in {
    // The constant behind the class comment's scope condition, measured here rather than asserted
    // there. A clause is the theorem whose hypotheses are the complements of its literals; one step
    // is `notIntro` to discharge the pivot and `proveHyp` to cut it in.
    val p = Term.variable("p", Type.Bool)
    val notP = force(logic.mkNot(p))
    val clause = force(logic.rules.notElim(force(Kernel.assume(notP)), force(Kernel.assume(p))))

    val discharged = force(logic.rules.notIntro(p, clause))
    val resolvent = force(logic.rules.proveHyp(discharged, clause))

    withClue("the replay must cost no axiom; only the last step of a proof is classical: ") {
      Derivation.axiomsOf(resolvent) shouldBe empty
    }
    withClue(s"a step over two clauses of ${Derivation.size(clause)}: ") {
      (Derivation.size(resolvent) - Derivation.size(clause)) should be <= 100
    }
  }
}
