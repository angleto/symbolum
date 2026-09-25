package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Resolution reasoned about rather than run, and what that first theorem cost.
 *
 * Three assertions carry the file and none of them is "this is provable".
 *
 * **Which of resolution's four conditions the conclusion spends.** Two, and a reader of the
 * definition would not have guessed which two: the ones saying the pivot **occurs** are not used,
 * and the ones saying every other literal carries into the resolvent are. That is the same question
 * `DomainTheorySpec` asks of its four domain axioms, asked of a definition instead.
 *
 * **What it costs.** One axiom on the step, `SELECT`, spent on the case split over `a x`, and
 * **none at all** on the empty clause. The pair is the measurement: a file where everything cost one
 * axiom would say nothing about where the classical step is.
 *
 * **That the development declares nothing.** It sits beside the chain and hands on the theory it was
 * given, constant for constant, so a definition arriving here goes red rather than passing
 * unnoticed. `Bounded`, `Primes` and `Deduction` make the same promise.
 */
class ResolvingSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard
  private lazy val resolving: Resolving =
    Resolving.construct(chain).fold(error => fail(s"the development does not build: $error"), identity)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private def fact(name: String): Kernel.Thm = force(resolving.fact(name))

  private val choice: Set[Term] =
    Set(Chain.standard.classical.axiom(Classical.Choice).fold(error => fail(error.toString), identity).conclusion)

  "One resolution step" should "be sound, and the statement should be the one a reader checks" in {
    val theorem = fact(Resolving.StepSound)
    theorem.hypotheses shouldBe empty

    // Read back rather than described. The two halves a reader compares with resolution are that a
    // literal other than the pivot carries into the resolvent, and that the resolvent is satisfied.
    val printed = resolving.show(theorem.conclusion)
    printed should include("<")
    printed should include("==>")
    withClue(s"the statement is $printed: ") {
      printed.count(_ == '?') should be >= 3
    }
  }

  it should "cost exactly the choice axiom, which is what the case split is" in {
    // The same axiom `logic.Propositional` spends and for the same reason: deciding that a boolean
    // is one of two things is classical here. Asserted as an equality of the set rather than as a
    // ceiling, so a derivation that quietly starts spending something else goes red.
    Derivation.axiomsOf(fact(Resolving.StepSound)) shouldBe choice
  }

  "The two conditions saying the pivot occurs" should "not be spent, which is the finding" in {
    // The corollary carries resolution's four conditions; the theorem it is derived from carries
    // two. So the occurrence conditions are assumed and never used, and this is the assertion that
    // says so: the corollary's statement has two more antecedents than the theorem's, and both
    // conclude the same thing.
    val step = fact(Resolving.StepSound)
    val resolvent = fact(Resolving.StepSoundOfResolvent)

    def antecedents(theorem: Kernel.Thm): Int = {
      val logic = resolving.logic
      def peel(term: Term, seen: Int): Int =
        logic.destImp(term) match {
          case Some((_, rest)) => peel(rest, seen + 1)
          case None => seen
        }
      peel(force(Logic.stripForall(theorem.conclusion))._2, 0)
    }

    antecedents(step) shouldBe 4
    antecedents(resolvent) shouldBe 6

    // And the same conclusion under the same number of binders, so the corollary really is the
    // theorem with two conditions in front and not a claim about something else.
    force(Logic.stripForall(step.conclusion))._1.length shouldBe
      force(Logic.stripForall(resolvent.conclusion))._1.length
    resolvent.hypotheses shouldBe empty
  }

  "The empty clause" should "be satisfied by nothing, and cost MORE than the step does" in {
    val theorem = fact(Resolving.EmptyUnsatisfiable)
    theorem.hypotheses shouldBe empty

    // **The measurement, and it is the opposite way round from the guess this test first made.**
    //
    // The step above has the classical case split in it and costs **one** axiom, choice. This has
    // no case split at all and costs **two**, choice and infinity, because it is the only one of the
    // two that spends a fact about `num`: `Peano.NUM_NOT_LT_ZERO`, and `num` is a defined type
    // carved out of an infinite one, so every lemma about it carries the naturals' two.
    //
    // Read together the pair says where the cost of this development actually is, and it is not
    // where the reasoning looks hardest: the step never looks inside `num` at all. `NUM_LT` occurs
    // in its statement as a constant that is carried around and never unfolded, which is why a
    // theorem full of arithmetic notation spends no arithmetic.
    val spent = Derivation.axiomsOf(theorem)
    val stepSpends = Derivation.axiomsOf(fact(Resolving.StepSound))

    withClue(s"at ${Derivation.size(theorem)} inferences: ") {
      spent should have size 2
      spent should contain allElementsOf choice
    }
    stepSpends shouldBe choice
    withClue("the step must cost strictly less, or the pair measures nothing: ") {
      (spent -- stepSpends) should have size 1
    }
  }

  "A whole derivation" should "be sound, which is what makes this a proof system" in {
    val theorem = fact(Resolving.DerivationSound)
    theorem.hypotheses shouldBe empty

    // The shape a reader checks: two antecedents, the inputs satisfied and every step justified,
    // and a conclusion about every step rather than about one.
    val logic = resolving.logic
    def antecedents(term: Term, seen: Int): Int =
      logic.destImp(term) match {
        case Some((_, rest)) => antecedents(rest, seen + 1)
        case None => seen
      }
    antecedents(force(Logic.stripForall(theorem.conclusion))._2, 0) shouldBe 2
  }

  it should "cost what the naturals cost, because the induction is a fact about `num`" in {
    // The pair that says where the cost is. `RES_STEP_SOUND` carries the classical case split and
    // spends one axiom; this carries strong induction and the transitivity of the order, both facts
    // about `num`, and spends two. The reasoning did not get harder between them: the difference is
    // entirely that one of the two looks inside `num` and the other never does.
    val spent = Derivation.axiomsOf(fact(Resolving.DerivationSound))
    val step = Derivation.axiomsOf(fact(Resolving.StepSound))

    spent should have size 2
    spent should contain allElementsOf choice
    step shouldBe choice
    (spent -- step) should have size 1
  }

  "A derivation reaching the empty clause" should "say that NOTHING satisfies the inputs" in {
    // The statement `modules/sat` makes every time it answers unsatisfiable, and which nothing in
    // this repository could state until now.
    val theorem = fact(Resolving.Refutes)
    theorem.hypotheses shouldBe empty

    // The half that carries the claim: the assignment is quantified **inside** the negation, so the
    // conclusion is about every assignment and not about one. Without that this would be
    // `RES_SOUND` read at a point, which is a much weaker thing wearing the same words.
    val logic = resolving.logic
    val body = force(Logic.stripForall(theorem.conclusion))._2
    def conclusionOf(term: Term): Term = logic.destImp(term).map(pair => conclusionOf(pair._2)).getOrElse(term)
    val negated = logic
      .destNot(conclusionOf(body))
      .getOrElse(fail(s"the conclusion must be a negation: ${resolving.show(conclusionOf(body))}"))

    withClue(s"what is denied must itself be an existential over the assignment: ${resolving.show(negated)} ") {
      logic.destExistsPredicate(negated) should not be empty
    }

    // And the assignment must not also be bound outside, or the statement is about one after all.
    force(Logic.stripForall(theorem.conclusion))._1.map(_.ty) should not contain
      Type.fun(force(Logic.stripForall(theorem.conclusion))._1.last.ty, Type.Bool)
  }

  "This development" should "declare nothing, so it cannot become the widest signature" in {
    // The promise `Deduction` makes and the reason it can be read without checking the chain: a
    // constant arriving here would move the signature, the reading register and the three
    // comparisons against the widest signature below.
    resolving.theory.constants.keySet shouldBe chain.widest.theory.constants.keySet
    resolving.theory.typeOperators.keySet shouldBe chain.widest.theory.typeOperators.keySet
    resolving.theory.axioms.length shouldBe chain.widest.theory.axioms.length
  }

  "The statements" should "need nothing the chain does not already have" in {
    // The measurement that decided the shape of this development, kept as an assertion. The card
    // that asked for it assumed the objects would have to be arithmetised, as `Provability` codes a
    // derivation of PA; they do not, because proof complexity quantifies over derivations and does
    // not talk about itself. If this ever stops reading, the decision is back open.
    val statements = Vector(
      "!x:num -> bool. !y:num -> num. !z:num -> num -> num. !u:num -> num -> bool. !v:num. " +
        "(?w:num. w < y v /\\ x (z v w) = u v w) ==> 0 <= y v",
      "!x:num -> num. !y:num -> num -> num. !z:num -> num -> bool. !u:num. !v:num. !w:bool. " +
        "(?x1:num. x1 < x u /\\ y u x1 = v /\\ z u x1 = w) ==> 0 <= x u"
    )

    statements.foreach(text => withClue(s"$text: ") { chain.widest.proposition(text).isRight shouldBe true })
  }
}
