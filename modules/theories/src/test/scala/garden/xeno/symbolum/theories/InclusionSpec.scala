package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The bridge from `int` into `real`, and the two questions it exists to answer.
 *
 * == The accounting, which is asserted here and nowhere else ==
 *
 * `IntegerSpec` asserts that not one fact of that development reaches any of the sixteen axioms of
 * the reals, and the card that asked for the integers turns on it: a signed ring charging the reals
 * would be built on the thing it exists to avoid needing. Every fact of **this** development
 * reaches them, because every fact of this one is an equation between real numbers and `Ring`
 * decides those out of the field.
 *
 * The pair is the boundary between the two files, stated as a measurement rather than as prose, and
 * neither half means anything alone: a reading that returned the same set for every theorem would
 * pass the first, and one that returned everything would pass the second. So both are asserted
 * below, in one test, against a set of axioms read off `chain.reals` rather than named here.
 *
 * == That it does not collapse, which nothing else could notice ==
 *
 * Seven of the eight facts hold of the map sending every integer to `0`. So does the axiom reading,
 * so does the comparison against `Inclusion.Statements`, and so does every spelling check. Only
 * something that tells two values apart refutes that map. `docs/adr/0033` names the same hazard one
 * level down, where `IntegerSpec` answers it with a derived non-equality of two classes; the answer
 * here is `~(INT_ZERO = INT_ONE)` derived **through the bridge**, which uses the embedding as the
 * instrument rather than as the subject and so refutes the collapse of this map in particular.
 *
 * == What is deliberately not here ==
 *
 * That the embedding carries the order: `INT_LE a b = real_of_int a <= real_of_int b` is the fact
 * that would say so and it is the obvious next one. It is not in the card that asked for this file,
 * it wants an argument of its own rather than the rewriting route the eight share, and it is named
 * in that card as what is left instead of being left to be discovered here.
 */
class InclusionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val inclusion = chain.inclusion
  private val integers = chain.integers
  private val peano = chain.peano
  private val rules = inclusion.logic.rules

  private def fact(name: String): Kernel.Thm = force(inclusion.fact(name))

  /* ------------------------------------------------------------------ the constant exists */

  /**
   * An unknown constant is a **free variable** and not a parse error, which is what makes the
   * second half of this worth writing.
   *
   * `real_of_int a` read against the link below is well-typed and is a claim about an arbitrary
   * function of that name, so a successful parse there would say nothing. That is the trap
   * `ConcatenationSpec` records meeting for the third time. The question that separates the two
   * signatures is whether the name is a **constant of the theory**, and that is the one asked here.
   */
  "The chain" should "declare `real_of_int`, which the link under this one does not" in {
    inclusion.theory.constants.keySet should contain(Inclusion.Name)
    integers.theory.constants.keySet should not contain Inclusion.Name
  }

  it should "reach it through the widest signature, which is where a caller asks" in {
    // `Chain.widest` is the one place the name of the last link is written, and a goal reaching
    // `Ask` or `Find` goes through it. A link in the chain whose constant the widest signature
    // could not name would be unreachable from everything, which is the defect `ChainCoverageSpec`
    // and `Library.of` exist between them to fail on.
    chain.widest.theory.constants.keySet should contain(Inclusion.Name)
    chain.widest.term("real_of_int INT_ZERO", Real.realType) should be(Symbol("right"))
  }

  /* ------------------------------------------------------------------ the statements */

  it should "prove each of its facts with nothing assumed" in {
    Inclusion.Statements.foreach { case (name, _) =>
      withClue(s"$name: ")(fact(name).hypotheses shouldBe empty)
    }
  }

  it should "say what `Inclusion.Statements` says, read as a term" in {
    Inclusion.Statements.foreach { case (name, text) =>
      withClue(s"$name: ")(fact(name).conclusion shouldBe force(inclusion.proposition(text)))
    }
  }

  it should "hold a fact for every statement and a statement for every fact" in {
    // Both directions, because each catches a different mistake: a fact with no statement is one no
    // reader can check against the informal claim, and a statement with no fact is a name in a
    // table that nothing proves.
    inclusion.facts.keySet shouldBe Inclusion.Statements.map(_._1).toSet
  }

  /* ------------------------------------------------------------------ it does not collapse */

  /**
   * `~(INT_ZERO = INT_ONE)`, derived through the bridge.
   *
   * Assume the two integers equal, apply `real_of_int` as a congruence, and the two value facts
   * turn what comes out into `0 = 1`, which contradicts the one axiom of the reals that separates
   * the two numerals. The negation comes back with nothing assumed.
   *
   * It is the guard on everything above it. `Integer` has this separation already and proves it
   * through `Successor.distinct` in the carrier; what is refuted **here** is the map sending every
   * integer to zero, which satisfies all seven equations of this development and which no other
   * assertion in this file can see.
   */
  "The embedding" should "keep two integers apart, which is what says it did not collapse" in {
    val goal = force(inclusion.proposition("INT_ZERO = INT_ONE"))
    val assumed = force(LogicError.lift(Kernel.assume(goal)))

    val bridge = force(
      LogicError.lift(
        inclusion.theory.constant(Inclusion.Name, Type.fun(Integer.Classes, Real.realType))
      )
    )
    val applied = force(Conv.apTerm(bridge, assumed))

    val values = force(
      Rewrite.Rule.all(
        inclusion.logic,
        Vector(fact(Inclusion.EmbedsZero), fact(Inclusion.EmbedsOne))
      )
    )
    val overReals = force(Rewrite.inTheorem(values, applied))
    val reversed = force(Conv.sym(overReals))

    val distinct = force(chain.reals.axiom("ONE_NOT_ZERO"))
    val absurd = force(rules.notElim(distinct, reversed))
    val negation = force(rules.notIntro(goal, absurd))

    negation.hypotheses shouldBe empty
    negation.conclusion shouldBe force(inclusion.proposition("~(INT_ZERO = INT_ONE)"))
  }

  /**
   * And the injectivity detaches at a concrete pair, landing on a theorem proved without the reals.
   *
   * `real_of_int (INT_OF_NUM ZERO)` is `real_of_num ZERO` by the triangle and `0` by `NUM_REAL_ZERO`
   * below it, and `real_of_int INT_ZERO` is `0` by the value fact, so the two images are equal with
   * nothing assumed and `INT_REAL_INJECTIVE` gives `INT_OF_NUM ZERO = INT_ZERO`.
   *
   * What makes it worth running rather than merely deriving something: that conclusion is
   * `INT_OF_NUM_ZERO`, which `Integer` proves through the quotient and **without touching a real**.
   * So this is one theorem reached by two routes that share no step, and the assertion is that they
   * agree as terms.
   */
  it should "settle an integer equation through the reals that `Integer` settles without them" in {
    val embedded = force(inclusion.term("real_of_int (INT_OF_NUM ZERO)", Real.realType))

    val opening = force(
      Rewrite.Rule.all(
        inclusion.logic,
        Vector(fact(Inclusion.EmbedsNatural), force(peano.fact(Peano.EmbedsZero)))
      )
    )
    val leftValue = force(Rewrite.rewrite(opening, embedded))
    val rightValue = fact(Inclusion.EmbedsZero)

    val sameImage = force(Conv.trans(leftValue, force(Conv.sym(rightValue))))
    sameImage.hypotheses shouldBe empty

    val leftInteger = force(inclusion.term("INT_OF_NUM ZERO", Integer.Classes))
    val rightInteger = force(inclusion.term("INT_ZERO", Integer.Classes))
    val instance =
      force(rules.specAll(fact(Inclusion.EmbedsInjectively), List(leftInteger, rightInteger)))

    val settled = force(rules.mp(instance, sameImage))

    settled.hypotheses shouldBe empty
    settled.conclusion shouldBe force(integers.fact(Integer.OfNaturalZero)).conclusion
  }

  /* ------------------------------------------------------------------ what it costs */

  private lazy val eta: Term = force(chain.classical.axiom(Classical.Eta)).conclusion
  private lazy val choice: Term = force(chain.classical.axiom(Classical.Choice)).conclusion
  private lazy val infinity: Term = force(chain.naturals.axiom(Natural.Infinity)).conclusion

  /** The sixteen, read off the theory of the reals rather than listed again here. */
  private lazy val field: Set[Term] = chain.reals.axioms.values.map(_.conclusion).toSet

  "The link" should "assert no axiom of its own" in {
    // The size of the trusted base is a number rather than a matter of opinion, which is
    // `Theory.axioms`'s own sentence. A link that only defines a constant adds nothing to it.
    inclusion.theory.axioms.toSet shouldBe integers.theory.axioms.toSet
  }

  /**
   * It spends the reals, and the development it embeds spends none of them.
   *
   * The contrast is the assertion and neither side is one alone. Every fact here reaches at least
   * one of the sixteen, every fact here also reaches the carrier's own three, and nothing here
   * reaches anything outside those nineteen. `Integer.INT_EQ_PAIRS`, the fact that development is
   * built on, reaches none of the sixteen, which is what makes the first three sentences a boundary
   * rather than a reading that says the same thing everywhere.
   */
  it should "reach the axioms of the reals, where the development it embeds reaches none" in {
    val carrier = Set(choice, eta, infinity)

    Inclusion.Statements.foreach { case (name, _) =>
      withClue(s"$name: ") {
        val spent = Derivation.axiomsOf(fact(name))
        (spent intersect field) should not be empty
        (spent -- field) shouldBe carrier
        spent -- field -- carrier shouldBe empty
      }
    }

    Derivation.axiomsOf(force(integers.fact(Integer.Equal))) intersect field shouldBe empty
  }
}
