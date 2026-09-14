package garden.xeno.symbolum.kernel

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The third theory extension, and everything it has to turn away. Not the eleventh inference
 * rule: it takes a theory and returns one, which is what `defineConstant` and `assertAxiom` do.
 *
 * `docs/adr/0006` argues the decision and lists these attacks; this is that table executed. The
 * must-accept case comes first on purpose: a rule whose refusals are all correct and whose product
 * is unusable passes every other assertion in the file.
 *
 * Two of the cases below were written wrongly the first time, and both mistakes are kept as
 * comments rather than tidied away, because each one is a thing about the rule that is easy to get
 * backwards.
 */
class TypeDefinitionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[KernelError, T]): T =
    result.fold(error => fail(s"expected success, got ${error.message}"), identity)

  private val ind: Type = TyApp("ind", Nil)

  /** A theory with a type, a predicate on it, and something that satisfies the predicate. */
  private def base: (Theory, Term, Term) = {
    val theory = force(
      for {
        withInd <- Theory.primitive.declareTypeOperator("ind", 0)
        withP <- withInd.declareConstant("P", Type.fun(ind, Type.Bool))
        withW <- withP.declareConstant("w", ind)
      } yield withW
    )

    (theory, force(theory.constant("P", Type.fun(ind, Type.Bool))), force(theory.constant("w", ind)))
  }

  /** `|- P w`, asserted here only to have a witness; a caller would prove one. */
  private def witnessed: (Theory, Kernel.Thm, Term, Term) = {
    val (theory, predicate, element) = base
    val applied = force(Term.app(predicate, element))
    val (extended, theorem) = force(Kernel.assertAxiom(theory, applied))
    (extended, theorem, predicate, element)
  }

  /* --------------------------------------------------------------- the must-accept half */

  "A predicate with a witness" should "define a type, and give the bijection both ways" in {
    val (theory, witness, _, _) = witnessed
    val (extended, (absOfRep, characterises)) = force(
      Kernel.defineType(theory, "sub", "abs", "rep", witness)
    )

    absOfRep.display shouldBe "|- ((abs (rep a)) = a)"
    characterises.display shouldBe "|- ((P r) = ((rep (abs r)) = r))"

    absOfRep.hypotheses shouldBe empty
    characterises.hypotheses shouldBe empty

    extended.typeOperators.get("sub") shouldBe Some(0)
    extended.constants.get("abs") shouldBe Some(Type.fun(ind, TyApp("sub", Nil)))
    extended.constants.get("rep") shouldBe Some(Type.fun(TyApp("sub", Nil), ind))

    // The invariant the signature check below exists to keep: what comes back is readable in the
    // theory that comes back with it. Asserted on the accepting side as well as the refusing one,
    // because a check that refuses everything would satisfy the refusal alone.
    force(extended.checkTerm(absOfRep.conclusion))
    force(extended.checkTerm(characterises.conclusion))
  }

  it should "add nothing to what has to be believed" in {
    // The whole reason this is a rule and not two asserted theorems. Every alternative in the record
    // reaches the same two theorems by putting them in `axioms`, where they would be believed rather
    // than derived, and the count would move by two for every type anybody defined.
    val (theory, witness, _, _) = witnessed
    val (extended, _) = force(Kernel.defineType(theory, "sub", "abs", "rep", witness))

    extended.axioms shouldBe theory.axioms
  }

  it should "take its arity from the predicate's type variables, not from the caller" in {
    // The caller does not get to choose it, which is a sharper edge than `declareTypeOperator` has
    // and belongs in a test rather than only in a comment. Sorted, so that two runs of the same
    // definition produce the same type rather than whichever order a set happened to iterate in.
    val alpha = TyVar("A")
    val predicateType = Type.fun(Type.fun(alpha, Type.Bool), Type.Bool)

    val theory = force(
      for {
        withQ <- Theory.primitive.declareConstant("Q", predicateType)
        withS <- withQ.declareConstant("s", Type.fun(alpha, Type.Bool))
      } yield withS
    )

    val predicate = force(theory.constant("Q", predicateType))
    val argument = force(theory.constant("s", Type.fun(alpha, Type.Bool)))
    val applied = force(Term.app(predicate, argument))
    val (asserted, witness) = force(Kernel.assertAxiom(theory, applied))

    val (extended, _) = force(Kernel.defineType(asserted, "poly", "absPoly", "repPoly", witness))

    Term.typeVariables(predicate) shouldBe Set("A")
    extended.typeOperators.get("poly") shouldBe Some(1)
  }

  /* ------------------------------------------------------------------- what it refuses */

  "A witness that holds only under an assumption" should "be refused" in {
    // The check that would be easiest to leave out, and the one that matters most: neither theorem
    // that comes back carries a hypothesis, so an assumption here would be discharged into silence
    // and an empty predicate could be given a bijection with a type.
    val (theory, _, predicate, element) = witnessed
    val applied = force(Term.app(predicate, element))

    Kernel.defineType(theory, "sub", "abs", "rep", force(Kernel.assume(applied))) match {
      case Left(TheoremHasHypotheses(hypotheses)) => hypotheses shouldBe List(applied)
      case other => fail(s"expected a refusal about hypotheses, got $other")
    }
  }

  "A conclusion that is not an application" should "be refused" in {
    // `|- w = w` is NOT this case, and getting that wrong is the first mistake worth keeping. It is
    // an application: `P w` with `P` the term `(= w)`, which is the predicate that holds of `w`
    // alone, and the type it defines is a singleton. HOL Light accepts it for the same reason.
    val (theory, _, _, element) = witnessed
    force(Kernel.defineType(theory, "one", "absOne", "repOne", Kernel.refl(element)))

    // What is really not an application is a proposition with no argument at all.
    val withFlag = force(theory.declareConstant("flag", Type.Bool))
    val flag = force(withFlag.constant("flag", Type.Bool))
    val (asserted, witness) = force(Kernel.assertAxiom(withFlag, flag))

    Kernel.defineType(asserted, "sub", "abs", "rep", witness) match {
      case Left(NotAnApplication(found)) => found shouldBe flag
      case other => fail(s"expected a refusal about the shape, got $other")
    }
  }

  "A predicate that is not closed" should "be refused" in {
    // It cannot arrive through `assertAxiom`, which refuses an open proposition, so it arrives
    // through reflexivity: `|- z w = z w` is `P (z w)` with `P` the term `(= (z w))`, which mentions
    // `z` freely and carries no hypothesis. That is the second mistake worth keeping: the obvious
    // route to this attack is closed off by another rule, and stopping there would have left the
    // check untested.
    val (theory, _, _, element) = witnessed
    val z = Term.variable("z", Type.fun(ind, ind))
    val applied = force(Term.app(z, element))

    Kernel.defineType(theory, "sub", "abs", "rep", Kernel.refl(applied)) match {
      case Left(DefinitionIsNotClosed(free)) => free shouldBe Set(z)
      case other => fail(s"expected a refusal about closedness, got $other")
    }
  }

  "A witness the theory cannot read" should "be refused" in {
    // Found by the second reading of the transcription, on 2026-09-10, and it is not a
    // mis-transcription: HOL Light has one global theory, so the constants of a theorem are in the
    // signature by construction and there is no analogue of this check to carry over. Here a
    // `Theory` is a value and a theorem can be built against one and handed to another, which is
    // what this rule accepted: the type came back characterised by a proposition that the theory
    // holding it then refused as an axiom.
    val (theory, _, _, _) = witnessed
    val away = force(theory.declareConstant("elsewhere", Type.Bool))
    val foreign = force(away.constant("elsewhere", Type.Bool))

    Kernel.defineType(theory, "sub", "abs", "rep", Kernel.refl(foreign)) match {
      case Left(UnknownConstant(name)) => name shouldBe "elsewhere"
      case other => fail(s"expected a refusal about the signature, got $other")
    }
  }

  "A name already in the theory" should "be refused, whichever of the three it is" in {
    val (theory, witness, _, _) = witnessed

    Kernel.defineType(theory, "ind", "abs", "rep", witness) match {
      case Left(AlreadyDeclared(name)) => name shouldBe "ind"
      case other => fail(s"expected a refusal about the type name, got $other")
    }

    Kernel.defineType(theory, "sub", "P", "rep", witness) match {
      case Left(AlreadyDeclared(name)) => name shouldBe "P"
      case other => fail(s"expected a refusal about the abstraction, got $other")
    }

    Kernel.defineType(theory, "sub", "abs", "w", witness) match {
      case Left(AlreadyDeclared(name)) => name shouldBe "w"
      case other => fail(s"expected a refusal about the representation, got $other")
    }
  }

  /* ------------------------------------------------- the attack that turns out not to be one */

  "A type variable the witness carries and the predicate does not" should "go nowhere" in {
    // The fourth attack the record lists, and the answer is that it is accepted and harmless. The
    // arity is read from the predicate, and the witness appears in **neither** theorem: it is used
    // to say the extension is not empty and for nothing else, so there is nowhere for a type
    // variable of its own to escape to.
    //
    // Built so the extra variable rides on a constant rather than a free variable, since a free one
    // would be caught by the closedness check instead and the case would not be tested.
    val beta = TyVar("B")
    val (start, predicate, _) = base

    val theory = force(
      for {
        withF <- start.declareConstant("f", Type.fun(beta, ind))
        withC <- withF.declareConstant("c", beta)
      } yield withC
    )

    val f = force(theory.constant("f", Type.fun(beta, ind)))
    val c = force(theory.constant("c", beta))
    val argument = force(Term.app(f, c))
    val applied = force(Term.app(predicate, argument))
    val (asserted, witness) = force(Kernel.assertAxiom(theory, applied))

    Term.typeVariables(argument) should contain("B")
    Term.typeVariables(predicate) shouldBe empty

    val (extended, (absOfRep, characterises)) =
      force(Kernel.defineType(asserted, "sub", "abs", "rep", witness))

    extended.typeOperators.get("sub") shouldBe Some(0)
    Term.typeVariables(absOfRep.conclusion) shouldBe empty
    Term.typeVariables(characterises.conclusion) shouldBe empty
  }
}
