package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The sixteenth axiom, used, with the machine deciding what it is about.
 *
 * **Completeness is the only one of the sixteen that quantifies over a predicate, and the only one
 * that separates the reals from the rationals.** Everything else in this development holds of the
 * rationals word for word, so a system that never reaches it has never said anything about the
 * reals in particular. The corpus report has been printing "completeness never reached" over 46
 * goals and reading as a fact about the corpus; it was a fact about the matcher, which was first
 * order, and `P` occurs in the axiom applied to a bound variable.
 *
 * So this file is one theorem, and what matters about it is not the theorem. `{x | x < 1}` has a
 * least upper bound, which is not news. What is new is that **nobody wrote `\x. x < 1` down**: the
 * goal was stated, `Apply` matched the axiom's conclusion against it, and the Miller case in
 * `Matching` answered with the predicate. That is the acceptance criterion the card set, and it was
 * chosen because it cannot be met by accident.
 *
 * The two obligations are discharged the ordinary way, and the second is worth noticing: the
 * witness for "there is an upper bound" is `1`, and that it *is* one is LINARITH's to say. The
 * whole point of the arrangement is that the expensive step is the predicate and the cheap ones
 * stay cheap.
 */
class CompletenessSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private val order = Order.standard
  private val reals = order.reals
  private val linarith = Linarith.construct(order).fold(e => fail(e.message), identity)

  /**
   * The connectives over the theory that has `real`.
   *
   * `Real.standard` stays over `Logic.standard`, which has never heard of the type operator, and
   * specialising a universal means asking for the quantifier constant **at the type the universal
   * ranges over**. `Divisibility` documents the same widening for the same reason.
   */
  private val logic = force(reals.logic.over(reals.theory))
  private val rules = logic.rules

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val completeness = reals.axioms("COMPLETENESS")

  private val goal = force(
    reals.proposition(
      "?s:real. (!x:real. x < 1 ==> x <= s) /\\ " +
        "(!b:real. (!x:real. x < 1 ==> x <= b) ==> s <= b)"
    )
  )

  private lazy val application = force(Apply.to(logic, completeness, goal))

  "Applying completeness to a goal about a particular set" should "decide the predicate itself" in {
    application.instantiation.terms.size shouldBe 1

    // And it decided no type, which is the other half of the answer since 2026-09-12. Completeness
    // is stated over `real` throughout, so a match of it that had to instantiate a type variable
    // would mean the matcher had read something that is not there.
    application.instantiation.types shouldBe empty

    // The variable is asserted by its TYPE and not by its name. `Logic.stripForall` opens the
    // axiom's binder with a variable of its own choosing, so the `P` written in `Real.scala` is a
    // printed name and not something a caller can hold: what identifies it is that it ranges over
    // predicates on the reals, and that is the whole reason this axiom needed the Miller case.
    val decided = application.instantiation.terms.head
    decided._1.ty shouldBe Type.fun(real, Type.Bool)
    reals.show(decided._2) shouldBe "\\x:real. x < 1"
  }

  it should "leave exactly what the axiom assumes, and no more" in {
    application.obligations.size shouldBe 1

    // Printed with the binders the printer chose, which are not the ones `Real.scala` writes: a
    // bound variable is an index and the name is chosen at printing to avoid a clash. Asserting the
    // text this repository's own printer produces is what makes the row readable; asserting the
    // names of the axiom's source would be asserting something no term carries.
    reals.show(application.obligations.head) shouldBe
      "(?x:real. x < 1) /\\ (?x:real. !y:real. y < 1 ==> y <= x)"
  }

  it should "conclude the goal as written, with the redexes it created contracted" in {
    val (_, conclusion) = force(Logic.stripForall(application.theorem.conclusion))
    logic.destImp(conclusion).map(_._2) shouldBe Some(goal)
    application.theorem.hypotheses shouldBe empty
  }

  "The obligations" should "discharge, and the result be a theorem reaching completeness" in {
    val zero = force(reals.term("0"))
    val one = force(reals.term("1"))
    val bound = Term.variable("b", real)

    // `\x. x < 1` is not written here: it is what the matcher decided, taken back out of the
    // application. Writing it again would be the hand instantiation this file exists to avoid.
    val below = application.instantiation.terms.head._2

    val bounded = force(Term.abs(bound, force(reals.proposition("!x:real. x < 1 ==> x <= b"))))

    val nonEmpty = force(rules.existsIntro(below, zero, order.facts(Positivity.ZeroLessOne)))
    val above = force(linarith.prove(force(reals.proposition("!x:real. x < 1 ==> x <= 1"))))
    val hasBound = force(rules.existsIntro(bounded, one, above))

    val both = force(rules.conjIntro(nonEmpty, hasBound))
    val theorem = force(rules.mp(application.theorem, both))

    theorem.conclusion shouldBe goal
    theorem.hypotheses shouldBe empty

    val reached = Derivation.axiomsOf(theorem)
    withClue(s"the proof reaches ${reached.size} axioms and completeness is not among them\n") {
      reached should contain(completeness.conclusion)
    }

    info(
      s"the supremum of {x | x < 1} exists: ${Derivation.size(theorem)} inferences over " +
        s"${reached.size} axioms, and the predicate was found rather than supplied"
    )
  }
}
