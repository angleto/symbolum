package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The reals as cuts, first two stages: the type, its order, the rationals inside it and least upper
 * bounds; then addition and negation, with the additive inverse.
 *
 * == What would make this file empty, and what is asserted against each ==
 *
 * A type carved by a predicate nothing satisfies cannot be defined, so the type exists; what could
 * still be wrong is that it is too small or its order too coarse, and every law of a total order and
 * the least-upper-bound statement itself hold of a one-point type. So the first assertions are the
 * two that a one-point `cut` fails: the rationals zero and one land on different cuts, and the order
 * between them goes one way and not the other. `CUT_COMPLETE` is an implication, and one whose
 * antecedent no family meets would read like a fact, so it is detached at a concrete family.
 */
class CutSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val fractions = force(Fraction.construct(chain.classical, chain.integers, chain.product, chain.peano))
  private val cuts = force(Cut.construct(fractions, chain.peano))
  private val rules = cuts.logic.rules

  private def fact(name: String): Kernel.Thm = force(cuts.fact(name))
  private def rational(text: String): Term = force(cuts.term(text, Fraction.Classes))
  private def cut(text: String): Term = force(cuts.term(text, Cut.Classes))

  /* ------------------------------------------------------------------ the statements */

  "Every fact of the development" should "prove the statement it is published as" in {
    Cut.Statements.foreach { case (name, text) =>
      val proved = fact(name)
      withClue(s"$name: ") {
        proved.conclusion shouldBe force(cuts.proposition(text))
        proved.hypotheses shouldBe empty
      }
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    cuts.facts.keySet shouldBe Cut.Statements.map(_._1).toSet
  }

  it should "declare `cut`, the two halves of its bijection, the predicate, the order, the embedding, the sum and the negation, and nothing else" in {
    (cuts.theory.constants.keySet -- fractions.theory.constants.keySet) shouldBe
      Set(Cut.Abstraction, Cut.Representation, Cut.IsCut, Cut.AtMost, Cut.OfRational, Cut.Addition, Cut.Negation)
  }

  /* ------------------------------------------------------------------ what a one-point type fails */

  "The type" should "not collapse: zero and one are different cuts" in {
    val zero = rational("RAT_ZERO")
    val one = rational("RAT_ONE")
    val distinct = force(
      for {
        collapse <- cuts.proposition("CUT_OF_RAT RAT_ZERO = CUT_OF_RAT RAT_ONE")
        held <- LogicError.lift(Kernel.assume(collapse))
        units <- rules.specAll(fact(Cut.OfRationalInjective), List(zero, one)).flatMap(rules.mp(_, held))
        absurd <- fractions.fact(Fraction.UnitsDistinct).flatMap(rules.notElim(_, units))
        result <- rules.notIntro(collapse, absurd)
      } yield result
    )
    distinct.hypotheses shouldBe empty
    distinct.conclusion shouldBe force(cuts.proposition("~(CUT_OF_RAT RAT_ZERO = CUT_OF_RAT RAT_ONE)"))
  }

  "The order" should "go from zero to one and not back, which the trivial order would not" in {
    val zero = rational("RAT_ZERO")
    val one = rational("RAT_ONE")
    val upwards = force(
      rules.specAll(fact(Cut.OfRationalOrder), List(zero, one))
        .flatMap(Conv.sym)
        .flatMap(equation => fractions.fact(Fraction.ZeroAtMostOne).flatMap(t => LogicError.lift(Kernel.eqMp(equation, t))))
    )
    val downwards = force(
      for {
        backwardsTerm <- cuts.proposition("CUT_LE (CUT_OF_RAT RAT_ONE) (CUT_OF_RAT RAT_ZERO)")
        held <- LogicError.lift(Kernel.assume(backwardsTerm))
        rats <- rules.specAll(fact(Cut.OfRationalOrder), List(one, zero)).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, held)))
        absurd <- fractions.fact(Fraction.OneNotAtMostZero).flatMap(rules.notElim(_, rats))
        result <- rules.notIntro(backwardsTerm, absurd)
      } yield result
    )
    upwards.hypotheses shouldBe empty
    downwards.hypotheses shouldBe empty
    upwards.conclusion shouldBe force(cuts.proposition("CUT_LE (CUT_OF_RAT RAT_ZERO) (CUT_OF_RAT RAT_ONE)"))
    downwards.conclusion shouldBe force(cuts.proposition("~(CUT_LE (CUT_OF_RAT RAT_ONE) (CUT_OF_RAT RAT_ZERO))"))
  }

  /* ------------------------------------------------------------------ least upper bounds */

  "Completeness" should "be detached at the family holding only the cut of zero" in {
    // `P x` is `x = CUT_OF_RAT RAT_ZERO`: inhabited by that cut, and bounded by it, since every
    // member is it and the order is reflexive. What comes back is a least upper bound with nothing
    // assumed.
    val zeroCut = cut("CUT_OF_RAT RAT_ZERO")
    val family = force(cuts.term("\\x:cut. x = CUT_OF_RAT RAT_ZERO", Type.fun(Cut.Classes, Type.Bool)))
    val x = Term.variable("x", Cut.Classes)
    val detached = force(
      for {
        instance <- rules.spec(family, fact(Cut.Complete))
        reduced <- Conv.betaNormalise(instance.conclusion).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, instance)))
        hypotheses <- cuts.logic.destImp(reduced.conclusion).toRight(NotOfForm("an implication", reduced.conclusion))
        sides <- cuts.logic.destConj(hypotheses._1).toRight(NotOfForm("a conjunction", hypotheses._1))
        inhabitedPredicate <- cuts.logic.destExistsPredicate(sides._1).toRight(NotOfForm("an existential", sides._1))
        inhabited <- rules.existsIntro(inhabitedPredicate, zeroCut, Conv.refl(zeroCut))
        member <- cuts.proposition("x = CUT_OF_RAT RAT_ZERO").flatMap(t => LogicError.lift(Kernel.assume(t)))
        reflexive <- rules.spec(zeroCut, fact(Cut.AtMostReflexive))
        belowZero <- Conv.sym(member).flatMap { back =>
          reflexive.conclusion match {
            case App(App(relation, _), _) =>
              Conv.apTerm(relation, back).flatMap(partial => LogicError.lift(Kernel.mkComb(partial, Conv.refl(zeroCut))))
                .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, reflexive)))
            case other => Left(NotOfForm("a comparison", other))
          }
        }
        bound <- rules.disch(member.conclusion, belowZero).flatMap(rules.gen(x, _))
        boundedPredicate <- cuts.logic.destExistsPredicate(sides._2).toRight(NotOfForm("an existential", sides._2))
        bounded <- rules.existsIntro(boundedPredicate, zeroCut, bound)
        both <- rules.conjIntro(inhabited, bounded)
        result <- rules.mp(reduced, both)
      } yield result
    )
    detached.hypotheses shouldBe empty
  }

  /* ------------------------------------------------------------------ the sum */

  "The additive inverse" should "spend Archimedes, which the zero law does not" in {
    // `x + -x = 0` is where the rationals being Archimedean is needed: below zero, a member of `x`
    // whose step by `h` leaves the cut has to exist, and without Archimedes a cut could absorb every
    // step. `x + 0 = x` needs only density. A proof of the inverse that did not reach
    // `RAT_ARCHIMEDES` would be some other argument than the one `Cut` describes, and one of the
    // zero law that did would be spending a fact it has no use for.
    val archimedes = Set(force(fractions.fact(Fraction.Archimedes)).conclusion)
    Derivation.restingOn(fact(Cut.AddNegation), archimedes) should not be empty
    Derivation.restingOn(fact(Cut.AddZero), archimedes) shouldBe empty
  }

  /* ------------------------------------------------------------------ what it costs */

  "Every fact of the development" should "cost the foundation and none of the reals' sixteen" in {
    // `CUT_COMPLETE` is `COMPLETENESS` read on this type, and the whole point is that it does not
    // rest on that axiom or any other of the reals: a derivation reaching one would be a proof of
    // the axiom from itself.
    val eta = force(chain.classical.axiom(Classical.Eta)).conclusion
    val choice = force(chain.classical.axiom(Classical.Choice)).conclusion
    val infinity = force(chain.naturals.axiom(Natural.Infinity)).conclusion
    val foundation = Set(choice, eta, infinity)
    val realAxioms = Real.Axioms.map { case (name, _) => force(chain.reals.axiom(name)).conclusion }.toSet
    realAxioms should have size 16

    Cut.Statements.foreach { case (name, _) =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(fact(name)) should contain noElementsOf realAxioms
        Derivation.axiomsOf(fact(name)).diff(foundation) shouldBe empty
      }
    }
  }

  it should "spend eta on antisymmetry, where two cuts with the same members are one cut" in {
    // The positive control for the line above: an instrument that found no axiom anywhere would
    // pass it. Antisymmetry closes with extensionality and must be seen reaching it.
    val eta = force(chain.classical.axiom(Classical.Eta)).conclusion
    Derivation.axiomsOf(fact(Cut.AtMostAntisymmetric)) should contain(eta)
  }
}
