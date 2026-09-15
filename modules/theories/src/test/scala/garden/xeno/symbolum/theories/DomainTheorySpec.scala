package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A theory that is not about numbers, proved against, and accounted for.
 *
 * The declared purpose of this repository is not only mathematics: it is to state axioms and rules
 * from domains that are neither logical nor mathematical, and settle claims about them. Nothing had
 * ever done it. The card that carries the aim lists four things missing, and reads as though the
 * first of them blocks the rest: the eight entry points in `modules/tactics` take a `RealTheory`,
 * and a domain theory is not one and never will be.
 *
 * **That is true and it does not block this.** The card's own acceptance criterion is a page: a
 * claim of some real domain formalised end to end, with the constants declared, the axioms asserted
 * and counted, the conclusion derived, and a report saying which of the assumptions it rests on and
 * which of them are foundational. Every piece of that is reachable with the kernel, the derived
 * rules and `Derivation`, and this file is the page. What the eight signatures would buy is
 * `Cost`'s formatting and the search tactics, which is convenience and automation rather than the
 * criterion.
 *
 * == The domain, and why this one ==
 *
 * A release gate: a change ships when two people have reviewed it, or when one has and the pipeline
 * is green, or when it is a revert of something already shipped, and on no other ground. It is a
 * rule about when work is allowed out, so it is as far from arithmetic as the shelf gets, and its
 * shape is what makes the accounting below worth reading: three sufficient conditions, the third
 * failing differently in kind from the other two, and one sentence saying those three are the only
 * ones there are.
 *
 * **The criterion is invented, and that is deliberate rather than a weakness.** Until 2026-09-15
 * this test asserted the four sentences of a private document's admission criterion, which made a
 * fragment of that document the subject of a public test. Nothing in the accounting depended on the
 * sentences being anybody's real rule: what the derivation spends is fixed by the logical shape,
 * and every criterion of this shape spends the same. What a real one bought was the claim that the
 * domain is in daily use rather than written for a demonstration, and that claim is given up here
 * on purpose. A reader who wants to know whether this machinery works on a rule somebody actually
 * follows should point it at their own, which is the whole use of this file.
 *
 * == What the accounting says, which is the part worth the trouble ==
 *
 * Four axioms are asserted and the conclusion rests on **one**. The three that state when a
 * change *is* admitted are not used at all; what the conclusion needs is the converse, the
 * direction that makes the criterion a gate rather than a sufficiency. A reader would not have
 * guessed that from the four, and it is exactly the question the card says is the useful one about
 * a claim of the world: not "is it a theorem" but "which of my assumptions did it actually spend".
 *
 * And it rests on **no foundational axiom at all**: not choice, not infinity, none of the reals.
 * The reasoning is propositional over the domain's own assumptions, which is what a reader should
 * be told before being asked to believe anything about a domain.
 *
 * == What automation reaches, which is half of it ==
 *
 * `Ring` and `Linarith` decide fragments of the reals and have nothing to say here, so the
 * derivation below is by hand out of the derived rules. That was the whole answer once, and this
 * section said so under the heading "what it does not show" for as long as it took somebody to
 * read the file downwards: `derivedByTactic` settles the same claim through `Propositional`, and
 * the sentence "no tactic helped" survived, in the header of the file whose own body refutes it.
 *
 * What the procedure reaches is the propositional skeleton and not the domain. The caller
 * specialises the fourth axiom and detaches by hand, so nothing here searches over an assumption;
 * what goes to `Propositional` is a tautology whose atoms are the domain's constants, and it is
 * given no meaning for any of them. It comes back as the same theorem spending the same one domain
 * axiom, and **one foundational axiom the hand derivation does not spend**, which is asserted below
 * rather than described. So the promise for a domain is still accounting rather than search: a
 * route that reaches the theorem while moving the accounting has bought fewer lines at a price
 * named in the currency this file exists to report.
 *
 * Nor is this a development of the chain, and it must not become one. A theory built beside the
 * chain is the case `docs/adr/0008` warns about, and `SoundnessAttackSpec` still carries the row
 * where two such theories produce `|- F`. What makes that nameable here is `Derivation.foreignTo`,
 * which the last assertion spends.
 */
class DomainTheorySpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def lift[T](result: Either[KernelError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val classical = Classical.standard
  private val foundation = classical.theory
  private val change = TyApp("change", Nil)

  /** The domain's own vocabulary: six names, none of which any theory here had. */
  private val declarations: Vector[(String, Type)] = Vector(
    "TwoReviews" -> Type.fun(change, Type.Bool),
    "OneReview" -> Type.fun(change, Type.Bool),
    "PipelineGreen" -> Type.fun(change, Type.Bool),
    "IsRevert" -> Type.fun(change, Type.Bool),
    "Ships" -> Type.fun(change, Type.Bool)
  )

  /**
   * The release gate, in four sentences.
   *
   * The first three are the grounds it gives, and the third is deliberately unlike the other two: a
   * revert is not a weaker review, it is a different kind of reason, and the two fail differently.
   * The fourth is the direction the prose means by "ships **when**": without it the three say only
   * that a change meeting one of them may ship, and nothing at all follows about one that meets
   * none. The conclusion below is about a change that meets none, so the fourth is the only one it
   * can possibly spend, which is the accounting this file exists to show.
   */
  private val criterion: Vector[String] = Vector(
    "!r:change. TwoReviews r ==> Ships r",
    "!r:change. OneReview r /\\ PipelineGreen r ==> Ships r",
    "!r:change. IsRevert r ==> Ships r",
    "!r:change. Ships r ==> " +
      "TwoReviews r \\/ (OneReview r /\\ PipelineGreen r) \\/ IsRevert r"
  )

  private lazy val (theory, axioms) = {
    val withType = lift(foundation.declareTypeOperator("change", 0))
    val declared = declarations.foldLeft(withType) { (current, entry) =>
      lift(current.declareConstant(entry._1, entry._2))
    }
    criterion.foldLeft((declared, Vector.empty[Kernel.Thm])) { case ((current, held), text) =>
      val proposition = force(Parser.proposition(current, classical.notation, text))
      val (extended, asserted) = lift(Kernel.assertAxiom(current, proposition))
      (extended, held :+ asserted)
    }
  }

  private lazy val logic: Logic = force(classical.logic.over(theory))
  private lazy val rules: Rules = logic.rules

  private def show(term: Term): String = Show.show(classical.notation, term)
  private def proposition(text: String): Term =
    force(Parser.proposition(theory, classical.notation, text))
  private def constant(name: String): Term =
    lift(theory.constant(name, Type.fun(change, Type.Bool)))

  /** The claim: a change meeting none of the three bases is not admitted. */
  private val statement: String =
    "!r:change. ~(TwoReviews r) /\\ ~(PipelineGreen r) /\\ ~(IsRevert r) " +
      "==> ~(Ships r)"

  /**
   * The derivation, by hand, because nothing here can be asked to find it.
   *
   * Assume the three negations and suppose the change admitted; the fourth axiom gives a
   * disjunction of three, each of which contradicts one of the three negations. The middle case
   * needs only the second half of its conjunction, which is the `PipelineGreen` the caller denied.
   */
  private lazy val derived: Kernel.Thm = {
    val subject = Term.variable("r", change)
    val antecedent = proposition(
      "~(TwoReviews (r:change)) /\\ ~(PipelineGreen r) /\\ ~(IsRevert r)"
    )
    val admitted = lift(Term.app(constant("Ships"), subject))
    val two = lift(Term.app(constant("TwoReviews"), subject))
    val one = lift(Term.app(constant("OneReview"), subject))
    val incident = lift(Term.app(constant("PipelineGreen"), subject))
    val standing = lift(Term.app(constant("IsRevert"), subject))

    force(for {
      assumed <- LogicError.lift(Kernel.assume(antecedent))
      noTwo <- rules.conjElim1(assumed)
      rest <- rules.conjElim2(assumed)
      noIncident <- rules.conjElim1(rest)
      noStanding <- rules.conjElim2(rest)

      converse <- rules.specAll(axioms(3), List(subject))
      supposed <- LogicError.lift(Kernel.assume(admitted))
      cases <- rules.mp(converse, supposed)

      firstCase <- LogicError.lift(Kernel.assume(two)).flatMap(rules.notElim(noTwo, _))
      pair <- logic.mkConj(one, incident)
      secondCase <- LogicError
        .lift(Kernel.assume(pair))
        .flatMap(rules.conjElim2)
        .flatMap(rules.notElim(noIncident, _))
      thirdCase <- LogicError.lift(Kernel.assume(standing)).flatMap(rules.notElim(noStanding, _))

      inner <- logic.mkDisj(pair, standing)
      innerAssumed <- LogicError.lift(Kernel.assume(inner))
      tail <- rules.disjElim(innerAssumed, secondCase, thirdCase)
      whole <- rules.disjElim(cases, firstCase, tail)

      negated <- rules.notIntro(admitted, whole)
      discharged <- rules.disch(antecedent, negated)
      closed <- rules.gen(subject, discharged)
    } yield closed)
  }

  /**
   * The same statement, found by a procedure instead of written out.
   *
   * The hand derivation above is forty lines of `for`-comprehension and it is what this page is
   * really about: a claim of the world, settled, with its assumptions counted. The question the
   * card carrying this work asks is whether a machine can do that part, because forty lines per
   * claim is not an instruction anybody follows.
   *
   * It can, and what it costs is measured below rather than described. Three steps: specialise the
   * fourth axiom at the subject, hand the implication from it to the goal to `Propositional`, and
   * detach. The domain's five constants are **atoms** to that procedure, which is what makes this
   * work at all: it is given no meaning for any of them and does not need one, because the argument
   * really is propositional and the spec above says so of itself.
   */
  private lazy val derivedByTactic: Kernel.Thm = {
    val subject = Term.variable("r", change)
    val body = proposition(
      "~(TwoReviews (r:change)) /\\ ~(PipelineGreen r) /\\ ~(IsRevert r) ==> ~(Ships r)"
    )

    force(for {
      converse <- rules.specAll(axioms(3), List(subject))
      bridge <- logic.mkImp(converse.conclusion, body)
      tautology <- Propositional.over(classical, logic).prove(bridge)
      applied <- rules.mp(tautology, converse)
      closed <- rules.gen(subject, applied)
    } yield closed)
  }

  "The same claim put to a procedure" should "come back as the same theorem" in {
    // Not a weaker theorem, not a conditional one, and not one about a different statement: the
    // conclusion is compared with the hand derivation's rather than with the text, because two
    // statements that print the same can be different terms.
    derivedByTactic.conclusion shouldBe derived.conclusion
    derivedByTactic.hypotheses shouldBe empty
  }

  it should "spend the same one of the four domain axioms" in {
    // The accounting the card calls the product, produced by the search instead of by reading a
    // hand derivation. Same answer: one of the four, and it is the converse.
    val spent = Derivation.axiomsOf(derivedByTactic)
    val ours = axioms.map(_.conclusion).toSet

    spent.count(ours.contains) shouldBe 1
    spent.filter(ours.contains).head shouldBe axioms(3).conclusion
    axioms.take(3).count(axiom => spent.contains(axiom.conclusion)) shouldBe 0
  }

  it should "cost one foundational axiom where the hand derivation costs none, and that is the finding" in {
    // **The honest half, and it is a gap rather than a price worth paying quietly.**
    //
    // The hand derivation spends no foundational axiom at all: assume the subject ships, take
    // the disjunction, contradict each case, conclude the negation. Every step of that is
    // intuitionistic. `Propositional` reaches the same theorem and charges the choice axiom,
    // because it decides classical validity and closes with `DOUBLE_NEGATION`.
    //
    // So neither procedure this repository has covers this argument at its real cost. `Minimal` is
    // the one that costs nothing and it refuses anything with a negation in it, which this statement
    // is made of; `Propositional` takes it and overpays. What would close the gap is a decision
    // procedure for **intuitionistic** propositional logic, negation included — Dyckhoff's
    // contraction-free calculus is the standard one and it terminates without a depth bound. That is
    // work of a known shape and it is not done here.
    //
    // Asserted rather than written in prose so that the day it stops being true, this goes red.
    val ours = axioms.map(_.conclusion).toSet
    val foundational = Derivation.axiomsOf(derivedByTactic).filterNot(ours.contains)

    foundational should have size 1
    foundational.head shouldBe force(classical.axiom(Classical.Choice)).conclusion

    Derivation.axiomsOf(derived).filterNot(ours.contains) shouldBe empty
  }

  "A theory of a domain that is not mathematics" should "be a theory like any other" in {
    theory.typeOperators.keySet should contain("change")
    (theory.constants.keySet -- foundation.constants.keySet) shouldBe declarations.map(_._1).toSet

    // Counted, which the card asks for by name. The domain's four sit on top of the foundation's,
    // and the difference is what a reader of this page is being asked to accept beyond what the
    // logic already assumes.
    axioms.length shouldBe 4
    theory.axioms.length shouldBe foundation.axioms.length + 4
  }

  it should "settle a claim about that domain, with nothing assumed" in {
    show(derived.conclusion) shouldBe
      "!x:change. ~(TwoReviews x) /\\ ~(PipelineGreen x) /\\ ~(IsRevert x) " +
        "==> ~(Ships x)"
    derived.hypotheses shouldBe empty
    derived.conclusion shouldBe proposition(statement)
  }

  "The accounting" should "name which assumptions the conclusion actually spent" in {
    // The half the card says is the product, and the half no other system packages. Four axioms
    // were asserted; the conclusion rests on one, and it is the converse rather than any of the
    // three that say when a change qualifies.
    val spent = Derivation.axiomsOf(derived)
    val ours = axioms.map(_.conclusion).toSet

    spent.count(ours.contains) shouldBe 1
    spent.filter(ours.contains).head shouldBe axioms(3).conclusion

    // And the three unspent ones are asserted and really unused, which is the statement a reader
    // would not have guessed from reading the four.
    axioms.take(3).count(axiom => spent.contains(axiom.conclusion)) shouldBe 0
  }

  it should "say that no foundational axiom was spent either" in {
    // Not choice, not infinity, none of the reals. The reasoning is propositional over the domain's
    // own assumptions, and a reader being asked to believe something about a domain should be told
    // that before anything else.
    //
    // Paired with the assertion above, because "no foundational axiom" is also what a report that
    // found nothing at all would say: one domain axiom was found, so the walk is reading something.
    val spent = Derivation.axiomsOf(derived)
    val ours = axioms.map(_.conclusion).toSet

    spent.count(axiom => !ours.contains(axiom)) shouldBe 0

    // Two paired assertions rather than one, because "no foundational axiom" is what a walk that
    // reads nothing also says, and what a walk that cannot see foundational axioms also says.
    // The first shows it reads something; the second shows that when a foundational axiom IS
    // spent, this same call reports it. The excluded middle is derived from choice and is the
    // nearest theorem that spends one.
    spent should not be empty
    Derivation.axiomsOf(force(classical.fact(Classical.ExcludedMiddle))) should not be empty
  }

  it should "be foreign to the foundation it was built on, and at home in its own theory" in {
    // What `docs/adr/0008` leaves open and what was made detectable on 2026-09-13. A theory built
    // beside the chain is the case that produces `|- F` when two of them axiomatise one name, and
    // this is how a caller at a boundary is told which theorem belongs to which.
    Derivation.foreignTo(theory, derived).clean shouldBe true

    val outside = Derivation.foreignTo(foundation, derived)
    outside.axioms should have size 1
    outside.constants should not be empty
  }

  /* ------------------------------------------- two domains at once, which is the card's fourth point */

  /**
   * A second domain, built ON the first rather than beside it.
   *
   * The card carrying the aim lists "no composition" as one of four things missing: nothing takes
   * two independent domain theories and makes one, nor says what happens if they collide on a name.
   * Both halves are answered here and neither needs machinery.
   *
   * A theory is a value, and extending one is what every development in `Chain` does. So two
   * domains compose by building the second over the first, and then one signature states a claim
   * about both. The version that cannot be made to work is the UNION of two theories built
   * independently, and it cannot be made to work because it is not sound: `SoundnessAttackSpec`
   * derives `|- F` from two theories that declare one name and constrain it differently. What is
   * right there is a refusal, and `Derivation.foreignTo` is the refusal.
   */
  private lazy val (second, secondAxiom) = {
    val declared = lift(theory.declareConstant("Frozen", Type.fun(change, Type.Bool)))
    val text = "!r:change. Frozen r ==> ~(Ships r)"
    val proposition = force(Parser.proposition(declared, classical.notation, text))
    val (extended, asserted) = lift(Kernel.assertAxiom(declared, proposition))
    (extended, asserted)
  }

  "A second domain built over the first" should "state a claim naming both vocabularies" in {
    // The composition the card asks for, which is extension and not union. `Frozen` is a second
    // domain's word and `Ships` is the first's, and the claim below names both because there is
    // one signature holding both. Nothing was written to make that possible.
    val across = force(
      Parser.proposition(
        second,
        classical.notation,
        "!r:change. Frozen r ==> ~(TwoReviews r) \\/ ~(IsRevert r)"
      )
    )

    Show.show(classical.notation, across) should include("Frozen")
    Show.show(classical.notation, across) should include("TwoReviews")

    // And the first domain's theorem is a theorem of the second, because extension only adds. That
    // is what makes building one over the other a composition rather than a coincidence.
    Derivation.foreignTo(second, derived).clean shouldBe true
  }

  it should "make the union of two INDEPENDENT domains refusable rather than silent" in {
    // The other half of the card's fourth point, and the reason union is not offered. A sibling
    // that declares the same name and constrains it its own way is the case `docs/adr/0008` leaves
    // open: the constants compare equal, the theorems combine, and `SoundnessAttackSpec` gets
    // `|- F` out of it. Nothing here makes that impossible; what `foreignTo` does is let a caller
    // at the boundary find out, and the test is that the sibling's theorem is reported foreign.
    val sibling = {
      val declared = lift(theory.declareConstant("Frozen", Type.fun(change, Type.Bool)))
      val text = "!r:change. Frozen r ==> Ships r"
      val proposition = force(Parser.proposition(declared, classical.notation, text))
      lift(Kernel.assertAxiom(declared, proposition))
    }

    // The two siblings say opposite things about one declared name, and each is consistent alone.
    Show.show(classical.notation, secondAxiom.conclusion) should include("~(Ships")
    Show.show(classical.notation, sibling._2.conclusion) should not include "~(Ships"

    // Neither is at home in the other, and it is the AXIOM that says so rather than the constant:
    // `Frozen` is declared in both with no origin in either, so nothing on the term tells them
    // apart, which is exactly what `Term`'s comment says is right for an uninterpreted name.
    val fromSibling = Derivation.foreignTo(second, sibling._2)
    fromSibling.axioms should have size 1
    fromSibling.constants shouldBe empty

    Derivation.foreignTo(sibling._1, secondAxiom).axioms should have size 1
  }

  "What a domain does not get" should "be said rather than left to be discovered" in {
    // `Ring` and `Linarith` decide fragments of the reals. A domain theory has axioms of whatever
    // shape its author wrote, so what is left is the derived rules and the rewriter, and the
    // derivation above is a hand proof of a three-way case split. The number is reported rather
    // than asserted against a bound, because what it is evidence for is the shape of the cost and
    // not a budget: a claim of this size is tens of inferences per case, and nothing searched.
    info(s"a three-way case split over four domain axioms: ${Derivation.size(derived)} inferences")

    Derivation.size(derived) should be > 0
  }
}
