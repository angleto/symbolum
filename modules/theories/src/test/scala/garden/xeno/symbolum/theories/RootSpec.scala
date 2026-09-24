package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The square root: what it cost, what it rests on, and that what it says is not vacuous.
 *
 * **What it cost.** One defined constant and no axiom, asserted as a difference against the theory
 * below it rather than as a count.
 *
 * **What it rests on, and the split that is the point.** The existence of a root is a theorem about
 * the reals alone: it spends `COMPLETENESS`, which no ordered field short of the reals can pay, and
 * it reaches no axiom the chain adds. Everything about `sqrt` spends that and one choice more. The
 * two halves are asserted in one test, because a reading that answered the same for both would pass
 * either alone.
 *
 * **What keeps it from being a theorem about nothing.** A constant named by choice over a predicate
 * nothing satisfies is a term with no facts, and every conditional statement about it would still
 * derive. So the facts are detached at concrete numbers with nothing assumed, and the hypothesis
 * `0 <= x` is shown to be load-bearing by refuting the unconditional statement at minus one.
 */
class RootSpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val root = chain.root

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def fact(name: String): Kernel.Thm = force(root.fact(name))

  private val reals: Set[Term] = chain.reals.axioms.values.map(_.conclusion).toSet

  /* --------------------------------------------------------------- what it cost */

  "The square root" should "add one constant and no axiom to the theory below it" in {
    val below = chain.folding.theory
    root.theory.axioms shouldBe below.axioms
    (root.theory.constants.keySet -- below.constants.keySet) shouldBe Set(Root.SquareRoot)
    root.theory.typeOperators.keySet shouldBe below.typeOperators.keySet
  }

  it should "prove its existence from the reals alone, and name it with one choice more" in {
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion
    val exists = Derivation.axiomsOf(fact(Root.Exists))

    // The existence spends the sixteenth axiom, and nothing but the reals'.
    exists should contain(completeness)
    withClue(s"the existence reaches: ${(exists -- reals).map(root.show).mkString("; ")}\n") {
      (exists -- reals) shouldBe empty
    }

    // Every fact about the constant rests on that and on the choice in its definition, and on no
    // other foundational axiom: an equality rather than a ceiling, so a fact that quietly began to
    // spend infinity or eta would fail here rather than pass under a bound.
    val select = force(chain.classical.axiom("SELECT")).conclusion
    Root.Statements.map(_._1).filterNot(Set(Root.Exists, Root.TwoIrrational)).foreach { name =>
      val spent = Derivation.axiomsOf(fact(name))
      withClue(s"$name reaches: ${(spent -- reals).map(root.show).mkString("; ")}\n") {
        (spent -- reals) shouldBe Set(select)
        spent should contain(completeness)
      }
    }
  }

  it should "state the irrationality of the root of two by carrying the descent across" in {
    // The fact is the descent `Primes` holds, read on the reals: what it rests on is that and the
    // root, and the naturals' own two axioms come with the descent. Asserted by the facts it rests
    // on rather than by its size, because a derivation that reached the same statement without the
    // descent would be a different proof and the one this development claims to have.
    val theorem = fact(Root.TwoIrrational)
    val descent = force(chain.primes.fact(Primes.SquareNotDouble)).conclusion
    val squares = fact(Root.Squares).conclusion
    Derivation.restingOn(theorem, Set(descent, squares)) shouldBe Set(descent, squares)

    val select = force(chain.classical.axiom("SELECT")).conclusion
    val infinity = force(chain.naturals.axiom(Natural.Infinity)).conclusion
    val spent = Derivation.axiomsOf(theorem)
    withClue(s"it reaches: ${(spent -- reals).map(root.show).mkString("; ")}\n") {
      (spent -- reals) shouldBe Set(select, infinity)
    }
  }

  it should "detach at a denominator, so that its hypothesis is one something satisfies" in {
    // A negation under a hypothesis nothing satisfies is a theorem about nothing, and it would pass
    // every assertion above. `0 < SUC 0` is a fact of `num`, so the instance at one over one
    // detaches with nothing assumed.
    val one = force(root.term("SUC 0", TyApp(Natural.TypeName, Nil)))
    val atOne = force(logic.rules.specAll(fact(Root.TwoIrrational), List(one, one)))
    val zero = force(root.term("0", TyApp(Natural.TypeName, Nil)))
    val positive = force(logic.rules.spec(zero, force(chain.peano.fact(Peano.SuccessorPositive))))
    val detached = force(logic.rules.mp(atOne, positive))

    detached.hypotheses shouldBe empty
    root.show(detached.conclusion) shouldBe "~(sqrt 2 = real_of_num (SUC 0) / real_of_num (SUC 0))"
  }

  /* ------------------------------------------------------------- what it says */

  it should "state every fact as it is written, with nothing assumed" in {
    Root.Statements.foreach { case (name, text) =>
      val theorem = fact(name)
      withClue(s"$name: ") {
        theorem.conclusion shouldBe force(root.proposition(text))
        theorem.hypotheses shouldBe empty
        root.legible(theorem.conclusion) shouldBe defined
      }
    }
  }

  it should "say what the square of the square root of two is, with nothing assumed" in {
    // The detachment is the guard against vacuity: an implication nobody discharges reads exactly
    // like a fact. And it is the sentence this repository could not write before, which is what
    // `Primes.NUM_SQUARE_NOT_DOUBLE` is the arithmetic content of.
    val two = force(root.term("2:real"))
    val atTwo = force(logic.rules.spec(two, fact(Root.Squares)))
    val positive = force(Linarith.construct(chain.order).flatMap(_.prove("(0:real) <= 2")))
    val detached = force(logic.rules.mp(atTwo, positive))

    detached.hypotheses shouldBe empty
    root.show(detached.conclusion) shouldBe "0 <= sqrt 2 /\\ sqrt 2 * sqrt 2 = 2"
  }

  it should "need its hypothesis, which is shown by refuting the statement without it" in {
    // `0 <= x` is not decoration. Below zero the choice falls somewhere and nothing is provable
    // about where, and what IS provable is that no real squares to a negative number: so the
    // unconditional reading of `SQRT` is false at minus one, and this derives that it is.
    val noSquare = force(
      Linarith.construct(chain.order).flatMap(_.prove("!y:real. ~(y * y = 0 - 1)"))
    )
    val atRoot = force(logic.rules.spec(force(root.term("sqrt (0 - 1)")), noSquare))

    atRoot.hypotheses shouldBe empty
    root.show(atRoot.conclusion) shouldBe "~(sqrt (0 - 1) * sqrt (0 - 1) = 0 - 1)"
  }

  it should "be the chain's end, so that every development above the reals can name it" in {
    chain.widest shouldBe root
    chain.widest.theory.constants.keySet should contain(Root.SquareRoot)
  }

  private def logic: Logic = root.logic
}
