package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Recursion where the step reads every earlier value, and what it cost to get there.
 *
 * Asserted here, in order: the theorem is the statement `Descent.StatementText` writes and not
 * something that follows from the same work; it reaches **no axiom the naturals did not already
 * reach**, which is the claim that would be worth the most and is the easiest to lose; and its
 * price is measured, because a derivation nobody priced is one nobody can tell has got slower.
 *
 * The assertion about the axioms is the one to read adversarially. It is written as an equality
 * against the two the naturals cost rather than as "no more than", because a count that only has to
 * stay under a bound passes when the derivation stops reaching one it should reach.
 */
class DescentSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val peano = chain.peano
  private val descent = force(Descent.construct(peano, chain.induct))

  "Definition by descent" should "be the statement it is written as" in {
    val theorem = force(descent.theorem)
    val statement = force(Parser.term(peano.theory, peano.notation, Descent.StatementText))

    theorem.conclusion shouldBe statement
    theorem.hypotheses shouldBe empty
  }

  it should "cost exactly what the naturals already cost, and no axiom of the reals" in {
    val theorem = force(descent.theorem)
    val recursion = force(peano.naturals.recursion)

    Derivation.axiomsOf(theorem) shouldBe Derivation.axiomsOf(recursion)
    Derivation.axiomsOf(theorem) should have size 2
  }

  /**
   * The assertion that keeps the rest of this file from being about nothing.
   *
   * Everything above is true of a theorem whose hypothesis nothing can satisfy, and such a theorem
   * would be worth nothing while passing every check here. So one step function is put to it end to
   * end. It reads the history at `ZERO`, which is the point: `Recursion` produces
   * `fn (SUC n) = f (fn n) n` and there is no way to write `fn ZERO` on the right of that at all,
   * so this recurrence is not a recurrence the simple theorem can state.
   */
  it should "define a function reading the history at an index simple recursion cannot name" in {
    val theorem = force(descent.theorem)
    val logic = peano.logic
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val classical = peano.naturals.classical
    // At `num`, and that is not a formality: both are stated at `'a`, `Rules.specAll` instantiates
    // terms and not types, and specialising them at a `num` argument refuses with a message about
    // an application rather than about a type.
    val condTrue = Kernel.instType(
      Map(Classical.TypeVariable -> numbers),
      force(classical.fact(Classical.CondTrue))
    )
    val condFalse = Kernel.instType(
      Map(Classical.TypeVariable -> numbers),
      force(classical.fact(Classical.CondFalse))
    )

    def read(text: String): Term = force(Parser.term(peano.theory, peano.notation, text))

    // `f n = COND (0 < n) (SUC (f 0)) 0`, whose right side names the value at zero and not the one
    // before `n`.
    val stepFunction = read("\\u:num -> num. \\n:num. COND (NUM_LT 0 n) (SUC (u 0)) 0")

    val atNumbers = Kernel.instType(Map(Classical.TypeVariable -> numbers), theorem)
    val applied = force(rules.spec(stepFunction, atNumbers))
    val instance = force(
      Conv
        .betaNormalise(applied.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, applied)))
    )

    val (admissible, existential) =
      logic.destImp(instance.conclusion).getOrElse(fail("an implication was expected"))

    // Admissibility, proved rather than assumed: two histories agreeing below `n` send this step to
    // the same answer, because the only value it reads is at `ZERO` and the guard puts `ZERO` below
    // `n` exactly when the value is read at all.
    val (binders, body) = force(Logic.stripForall(admissible))
    val Vector(first, second, bound) = binders
    val (agreement, equation) = logic.destImp(body).getOrElse(fail("an implication was expected"))
    val assumedAgreement = force(LogicError.lift(Kernel.assume(agreement)))
    val (leftSide, rightSide) = Term.destEq(equation).getOrElse(fail("an equation was expected"))

    def arms(conditional: Term): (Term, Term, Term) = conditional match {
      case App(App(App(_, test), here), otherwise) => (test, here, otherwise)
      case other => fail(s"an application of COND was expected: $other")
    }
    val (test, leftArm, otherwise) = arms(leftSide)
    val (_, rightArm, _) = arms(rightSide)

    val whenRead = force(for {
      assumed <- LogicError.lift(Kernel.assume(test))
      takenLeft <- rules.specAll(condTrue, List(test, leftArm, otherwise)).flatMap(rules.mp(_, assumed))
      takenRight <- rules.specAll(condTrue, List(test, rightArm, otherwise)).flatMap(rules.mp(_, assumed))
      zero <- LogicError.lift(peano.theory.constant(Natural.NumberZero, numbers))
      sameAtZero <- rules.spec(zero, assumedAgreement).flatMap(rules.mp(_, assumed))
      successor <- LogicError.lift(
        peano.theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      sameStepped <- Conv.apTerm(successor, sameAtZero)
      forward <- Conv.trans(takenLeft, sameStepped)
      back <- Conv.sym(takenRight)
      joined <- Conv.trans(forward, back)
    } yield joined)

    val whenNotRead = force(for {
      negation <- logic.mkNot(test)
      assumed <- LogicError.lift(Kernel.assume(negation))
      takenLeft <- rules.specAll(condFalse, List(test, leftArm, otherwise)).flatMap(rules.mp(_, assumed))
      takenRight <- rules.specAll(condFalse, List(test, rightArm, otherwise)).flatMap(rules.mp(_, assumed))
      back <- Conv.sym(takenRight)
      joined <- Conv.trans(takenLeft, back)
    } yield joined)

    val proved = force(for {
      settled <- classical.cases(test, whenRead, whenNotRead)
      implied <- rules.disch(agreement, settled)
      closed <- rules.genAll(implied, List(first, second, bound))
    } yield closed)

    // Before the modus ponens and not only after it. `Rules.mp` discharges the antecedent through
    // `proveHyp`, which leaves a hypothesis it cannot match in place rather than refusing, so an
    // admissibility proved in the wrong binder order comes back as a theorem that looks right and
    // carries the premise. Both halves are asserted for that reason.
    proved.conclusion shouldBe admissible

    val defined = force(rules.mp(instance, proved))
    defined.conclusion shouldBe existential
    defined.hypotheses shouldBe empty

    // And it still costs the two the naturals cost, which is what a definition by descent is for:
    // the recurrence is new and the trusted base is not.
    Derivation.axiomsOf(defined) should have size 2
    info(s"the recurrence reading the history at zero: ${Derivation.size(defined)} inferences")
  }

  it should "have a price somebody has read" in {
    val theorem = force(descent.theorem)
    info(s"definition by descent: ${Derivation.size(theorem)} inferences")
    Derivation.size(theorem) should be > 0
  }
}
