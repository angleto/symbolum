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
 * The admission criterion of the engineering handbook's register, which governs this repository and
 * which somebody applied by hand on 2026-09-13 to decide that a candidate rule did not qualify. It
 * is a rule about how rules are admitted, so it is as far from arithmetic as the shelf gets, and it
 * is in daily use rather than invented for a demonstration.
 *
 * == What the accounting says, which is the part worth the trouble ==
 *
 * Four axioms are asserted and the conclusion rests on **one**. The three that state when a
 * candidate *is* admitted are not used at all; what the conclusion needs is the converse, the
 * direction that makes the criterion a gate rather than a sufficiency. A reader would not have
 * guessed that from the four, and it is exactly the question the card says is the useful one about
 * a claim of the world: not "is it a theorem" but "which of my assumptions did it actually spend".
 *
 * And it rests on **no foundational axiom at all**: not choice, not infinity, none of the reals.
 * The reasoning is propositional over the domain's own assumptions, which is what a reader should
 * be told before being asked to believe anything about a domain.
 *
 * == What it does not show ==
 *
 * No tactic helped. `Ring` and `Linarith` decide fragments of the reals and have nothing to say
 * here, so the derivation below is by hand out of the derived rules, and the card's third point is
 * confirmed rather than repaired: the promise for a domain is accounting, not automation.
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
  private val candidate = TyApp("candidate", Nil)

  /** The domain's own vocabulary: six names, none of which any theory here had. */
  private val declarations: Vector[(String, Type)] = Vector(
    "TwoIndependent" -> Type.fun(candidate, Type.Bool),
    "OneOccurrence" -> Type.fun(candidate, Type.Bool),
    "HasIncident" -> Type.fun(candidate, Type.Bool),
    "StandingInstruction" -> Type.fun(candidate, Type.Bool),
    "Admitted" -> Type.fun(candidate, Type.Bool)
  )

  /**
   * The criterion as `why/00-conventions.md` states it, in four sentences.
   *
   * The first three are the bases it gives, and the register keeps the third visibly separate from
   * the other two on purpose, because a corpus rule and an instruction rule fail differently. The
   * fourth is the direction the prose means by "is admitted **when**": without it the three say
   * only that a candidate meeting one of them qualifies, and nothing at all follows about one that
   * meets none.
   */
  private val criterion: Vector[String] = Vector(
    "!r:candidate. TwoIndependent r ==> Admitted r",
    "!r:candidate. OneOccurrence r /\\ HasIncident r ==> Admitted r",
    "!r:candidate. StandingInstruction r ==> Admitted r",
    "!r:candidate. Admitted r ==> " +
      "TwoIndependent r \\/ (OneOccurrence r /\\ HasIncident r) \\/ StandingInstruction r"
  )

  private lazy val (theory, axioms) = {
    val withType = lift(foundation.declareTypeOperator("candidate", 0))
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
    lift(theory.constant(name, Type.fun(candidate, Type.Bool)))

  /** The claim: a candidate meeting none of the three bases is not admitted. */
  private val statement: String =
    "!r:candidate. ~(TwoIndependent r) /\\ ~(HasIncident r) /\\ ~(StandingInstruction r) " +
      "==> ~(Admitted r)"

  /**
   * The derivation, by hand, because nothing here can be asked to find it.
   *
   * Assume the three negations and suppose the candidate admitted; the fourth axiom gives a
   * disjunction of three, each of which contradicts one of the three negations. The middle case
   * needs only the second half of its conjunction, which is the `HasIncident` the caller denied.
   */
  private lazy val derived: Kernel.Thm = {
    val subject = Term.variable("r", candidate)
    val antecedent = proposition(
      "~(TwoIndependent (r:candidate)) /\\ ~(HasIncident r) /\\ ~(StandingInstruction r)"
    )
    val admitted = lift(Term.app(constant("Admitted"), subject))
    val two = lift(Term.app(constant("TwoIndependent"), subject))
    val one = lift(Term.app(constant("OneOccurrence"), subject))
    val incident = lift(Term.app(constant("HasIncident"), subject))
    val standing = lift(Term.app(constant("StandingInstruction"), subject))

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

  "A theory of a domain that is not mathematics" should "be a theory like any other" in {
    theory.typeOperators.keySet should contain("candidate")
    (theory.constants.keySet -- foundation.constants.keySet) shouldBe declarations.map(_._1).toSet

    // Counted, which the card asks for by name. The domain's four sit on top of the foundation's,
    // and the difference is what a reader of this page is being asked to accept beyond what the
    // logic already assumes.
    axioms.length shouldBe 4
    theory.axioms.length shouldBe foundation.axioms.length + 4
  }

  it should "settle a claim about that domain, with nothing assumed" in {
    show(derived.conclusion) shouldBe
      "!x:candidate. ~(TwoIndependent x) /\\ ~(HasIncident x) /\\ ~(StandingInstruction x) " +
        "==> ~(Admitted x)"
    derived.hypotheses shouldBe empty
    derived.conclusion shouldBe proposition(statement)
  }

  "The accounting" should "name which assumptions the conclusion actually spent" in {
    // The half the card says is the product, and the half no other system packages. Four axioms
    // were asserted; the conclusion rests on one, and it is the converse rather than any of the
    // three that say when a candidate qualifies.
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
    val declared = lift(theory.declareConstant("Retired", Type.fun(candidate, Type.Bool)))
    val text = "!r:candidate. Retired r ==> ~(Admitted r)"
    val proposition = force(Parser.proposition(declared, classical.notation, text))
    val (extended, asserted) = lift(Kernel.assertAxiom(declared, proposition))
    (extended, asserted)
  }

  "A second domain built over the first" should "state a claim naming both vocabularies" in {
    // The composition the card asks for, which is extension and not union. `Retired` is a second
    // domain's word and `Admitted` is the first's, and the claim below names both because there is
    // one signature holding both. Nothing was written to make that possible.
    val across = force(
      Parser.proposition(
        second,
        classical.notation,
        "!r:candidate. Retired r ==> ~(TwoIndependent r) \\/ ~(StandingInstruction r)"
      )
    )

    Show.show(classical.notation, across) should include("Retired")
    Show.show(classical.notation, across) should include("TwoIndependent")

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
      val declared = lift(theory.declareConstant("Retired", Type.fun(candidate, Type.Bool)))
      val text = "!r:candidate. Retired r ==> Admitted r"
      val proposition = force(Parser.proposition(declared, classical.notation, text))
      lift(Kernel.assertAxiom(declared, proposition))
    }

    // The two siblings say opposite things about one declared name, and each is consistent alone.
    Show.show(classical.notation, secondAxiom.conclusion) should include("~(Admitted")
    Show.show(classical.notation, sibling._2.conclusion) should not include "~(Admitted"

    // Neither is at home in the other, and it is the AXIOM that says so rather than the constant:
    // `Retired` is declared in both with no origin in either, so nothing on the term tells them
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
