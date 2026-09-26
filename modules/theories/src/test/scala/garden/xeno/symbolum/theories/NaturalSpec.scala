package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The naturals as a defined type, and what they cost.
 *
 * `docs/adr/0007` decides that the reals are constructed rather than assumed, and this is where
 * that work starts: a type that is not finite, a successor on it, and the naturals carved out. What
 * is asserted along the way is one statement, and the point of most of this file is that it is one
 * and no more: the other two this development holds are the classical logic's and were paid for
 * before it started.
 */
class NaturalSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val naturals = Natural.standard

  "The development" should "assert the statements written out below and no others" in {
    // The copy is written out by hand, as `RealSpec` writes out the sixteen. The first two are
    // inherited from the classical logic this is built over, the third is this file's own, and a
    // changed or added axiom fails here until the copy changes in the same commit.
    //
    // **The second arrived on 2026-09-10 and is not this development's**: eta went into
    // `Classical.scala` so that `SUM_CONGRUENCE` and every future congruence lemma could stop being
    // an induction, and everything built over the classical logic carries it whether or not it uses
    // it. That is what "the axioms live where what they are about lives" costs, and `Classical`
    // reaching two rather than one is why this list is three rather than two.
    naturals.theory.axioms.map(naturals.show) shouldBe Vector(
      "!f:'a -> bool. !x:'a. f x ==> f (select f)",
      "!f:'a -> 'b. (\\x:'a. f x) = f",
      "?f:ind -> ind. ?x:ind. (!y:ind. !z:ind. f y = f z ==> y = z) /\\ (!y:ind. ~(f y = x))"
    )
  }

  it should "state infinity in the form the construction uses, not the one upstream asserts" in {
    // HOL Light asserts `?f. ONE_ONE f /\ ~(ONTO f)` and derives this from it, through a step that
    // turns `~(!y. ?x. ...)` into `?y. ~(?x. ...)`, which is the excluded middle. This logic does
    // not have it, and the alternative is two axioms where this is one. The divergence is here
    // rather than only in the source, because it is a difference in what is believed.
    val infinity = force(naturals.axiom(Natural.Infinity))

    naturals.show(infinity.conclusion) should include("?f:ind -> ind. ?x:ind.")
    naturals.show(infinity.conclusion) should not include "ONTO"
  }

  "The successor and the point outside its image" should "be named, and carry what the axiom said" in {
    // The choice operator doing the one thing it was asserted for. What the axiom gives is that
    // some such pair exists; `Classical.witness` turns each existential into a term, which is what
    // `Kernel.defineType` needs, since a witness pulled out by eliminating an existential is a
    // variable and a type is defined by a closed predicate.
    val properties = force(naturals.fact(Natural.SuccessorProperties))

    properties.hypotheses shouldBe empty
    naturals.show(properties.conclusion) shouldBe
      "(!x:ind. !y:ind. IND_SUC x = IND_SUC y ==> x = y) /\\ (!x:ind. ~(IND_SUC x = IND_0))"
  }

  "The naturals" should "be a type, defined and not assumed" in {
    naturals.theory.typeOperators.get(Natural.TypeName) shouldBe Some(0)

    val abstraction = force(naturals.fact(Natural.AbstractionOfRepresentation))
    val characterisation = force(naturals.fact(Natural.Characterisation))

    naturals.show(abstraction.conclusion) shouldBe "mk_num (dest_num a) = a"
    naturals.show(characterisation.conclusion) shouldBe "NUM_REP r = (dest_num (mk_num r) = r)"

    abstraction.hypotheses shouldBe empty
    characterisation.hypotheses shouldBe empty
  }

  it should "cost no axiom beyond those it asserts, which is the whole reason for the rule" in {
    // `Kernel.defineType` is in the kernel exactly so that this line can be written. Every
    // alternative in `docs/adr/0006` reaches the same two theorems by asserting them, and the count
    // would then move by two for every type anyone defined.
    //
    // Three rather than two since 2026-09-10, and none of the difference is the type's: the
    // classical logic underneath went from one axiom to two when eta landed.
    naturals.theory.axioms.size shouldBe 3
  }

  "The predicate that carves them out" should "hold of zero, which is what makes the type inhabited" in {
    // The shortest derivation here and the one without which none of the rest is allowed: a type
    // defined over a predicate nothing satisfies would be a bijection with the empty.
    val represented = force(naturals.fact(Natural.ZeroIsRepresented))

    represented.hypotheses shouldBe empty
    naturals.show(represented.conclusion) shouldBe "NUM_REP IND_0"
  }

  it should "say that a natural is what every inductive predicate holds of" in {
    // Induction is not a further assumption here, it is this definition read back.
    val definition = force(naturals.definition(Natural.Representation))

    naturals.show(definition.conclusion) shouldBe
      "NUM_REP = (\\x:ind. !f:ind -> bool. f IND_0 /\\ (!y:ind. f y ==> f (IND_SUC y)) ==> f x)"
  }

  "Induction" should "be derived, and be the statement as it is written" in {
    // The theorem the naturals exist for. Nothing is left on the left of the turnstile, and it
    // reaches no axiom at all: it is the carving predicate read back, which the division over the
    // axioms below asserts with `Derivation.axiomsOf` rather than leaving to this sentence.
    val induction = force(naturals.fact(Natural.Induction))

    induction.hypotheses shouldBe empty
    naturals.show(induction.conclusion) shouldBe
      "!f:num -> bool. f ZERO /\\ (!n:num. f n ==> f (SUC n)) ==> (!n:num. f n)"

    // And it is the same proposition as the text the file states it by, compared as a term rather
    // than as printing: the letters above are the printer's, since a bound variable has no name.
    induction.conclusion shouldBe force(naturals.proposition(Natural.InductionStatement))
  }

  "Peano's other axioms" should "be derived too, so nothing about the naturals is assumed" in {
    // With induction these are Peano's, and not one of them is an axiom here: the type is defined,
    // induction is the definition read back, and these two are the pair the axiom of infinity gave,
    // carried across the bijection.
    val notZero = force(naturals.fact(Natural.SuccessorNotZero))
    val injective = force(naturals.fact(Natural.SuccessorInjective))
    val cases = force(naturals.fact(Natural.ZeroOrSuccessor))

    naturals.show(notZero.conclusion) shouldBe "!n:num. ~(SUC n = ZERO)"
    naturals.show(injective.conclusion) shouldBe "!n:num. !m:num. SUC n = SUC m ==> n = m"
    naturals.show(cases.conclusion) shouldBe "!n:num. n = ZERO \\/ (?m:num. n = SUC m)"

    Vector(notZero, injective, cases).foreach(_.hypotheses shouldBe empty)
  }

  it should "divide over its axioms exactly where the mathematics says it should" in {
    // The picture the proof record draws, and it is the right one. The two facts that tell the
    // naturals apart from a one-element type need infinity; the two that are structural do not.
    // If `ind` had a single element, `num` would be a singleton: induction and the case split would
    // still hold of it, and `SUC n = ZERO` would hold as well.
    Derivation.axiomsOf(force(naturals.fact(Natural.SuccessorNotZero))) should have size 2
    Derivation.axiomsOf(force(naturals.fact(Natural.SuccessorInjective))) should have size 2

    Derivation.axiomsOf(force(naturals.fact(Natural.ZeroOrSuccessor))) shouldBe empty
    Derivation.axiomsOf(force(naturals.fact(Natural.Induction))) shouldBe empty
  }

  it should "rest on two lemmas that are themselves derived" in {
    // Both halves of the bridge between the type and what it was carved out of, and neither is
    // assumed. The first is what makes the step of an induction go through and the second is how a
    // number reaches its representative at all.
    val closed = force(naturals.fact(Natural.RepresentationClosed))
    val represents = force(naturals.fact(Natural.RepresentationOfNumber))

    naturals.show(closed.conclusion) shouldBe "!x:ind. NUM_REP x ==> NUM_REP (IND_SUC x)"
    naturals.show(represents.conclusion) shouldBe "!n:num. NUM_REP (dest_num n)"

    closed.hypotheses shouldBe empty
    represents.hypotheses shouldBe empty
  }

  it should "be usable, which is the half a corpus of refusals would not catch" in {
    // A rule whose statement is right and which nothing can apply is one nobody finds out about
    // until later, so this applies it. `!n. n = n` by induction is the smallest claim that has to go
    // through both halves, and the point is the shape of the use rather than the theorem it reaches.
    val rules = naturals.logic.rules
    val induction = force(naturals.fact(Natural.Induction))
    val predicate = force(naturals.term("\\n:num. n = n"))

    val instance = force(rules.spec(predicate, induction))
    val opened = force(
      Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
    )

    val (premises, conclusion) = naturals.logic.destImp(opened.conclusion).get
    val (baseTerm, stepTerm) = naturals.logic.destConj(premises).get

    val base = Kernel.refl(force(naturals.term("ZERO")))
    base.conclusion shouldBe baseTerm

    val (variables, body) = force(Logic.stripForall(stepTerm))
    val (before, after) = naturals.logic.destImp(body).get
    val step = force(
      LogicError
        .lift(Kernel.assume(before))
        .flatMap(_ => rules.disch(before, Kernel.refl(force(Term.destEq(after).map(_._1).toRight(
          NotOfForm("an equation", after)
        )))))
        .flatMap(rules.gen(variables.head, _))
    )
    step.conclusion shouldBe stepTerm

    val proved = force(rules.conjIntro(base, step).flatMap(rules.mp(opened, _)))

    proved.hypotheses shouldBe empty
    proved.conclusion shouldBe conclusion
    naturals.show(proved.conclusion) shouldBe "!n:num. n = n"
  }

  "The two developments" should "compose into one signature when a caller asks for both" in {
    // What "siblings, not a chain" costs, and how a caller pays it instead. Neither standard
    // development can read the other's theorems, because neither theory holds the other's names, so
    // there is no signature in which a function from one to the other can even be stated. Measured
    // rather than argued, both ways round, and then built.
    Natural.standard.theory.checkTerm(force(Real.standard.axiom("ADD_SYM")).conclusion).isLeft shouldBe true
    Real.standard.theory.checkTerm(force(naturals.fact(Natural.Induction)).conclusion).isLeft shouldBe true

    val classical = Classical.standard
    val reals = force(Real.construct(classical.logic, classical.theory))
    // The notation comes with the theory: a chain through the reals reads `0 < x + 1`, which the
    // logic's own notation cannot. Passing the wrong one builds a theory that cannot read a
    // proposition in itself, which is how that became a parameter.
    val together = force(Natural.construct(classical, reals.theory, reals.notation))

    // One signature with both, and a statement neither of the two standard developments can make.
    together.theory.typeOperators.keySet should contain allOf ("real", "num", "ind")
    val bridged = force(
      LogicError.lift(
        together.theory.declareConstant("size", Type.fun(TyApp("num", Nil), TyApp("real", Nil)))
      )
    )
    val claim = force(
      Parser.proposition(bridged, together.notation, "!n:num. 0 < size n ==> 0 < size n + 1")
    )
    Show.show(together.notation, claim) shouldBe "!n:num. 0 < size n ==> 0 < size n + 1"

    // And the price of asking for both is stated: nineteen, not sixteen. It was eighteen until eta
    // landed in `Classical.scala` on 2026-09-10, and the ones that are not the field's are
    // `Classical.Axioms` and `Natural`'s infinity.
    together.theory.axioms.size shouldBe 19
  }

  "The reals" should "be untouched by any of this, since nothing here is built over them" in {
    // The two developments are siblings and not a chain: `Real.standard` is over `Logic.standard`,
    // which has no axioms, and this is over `Classical.standard`, which asserts `Classical.Axioms`.
    // A session that proves something about the reals is not asked to believe choice or eta.
    Real.standard.theory.axioms.size shouldBe 16
    Real.standard.theory.typeOperators.get(Natural.TypeName) shouldBe None
    Real.standard.theory.constants.get(Classical.Select) shouldBe None
  }
}
