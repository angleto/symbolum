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
 * == That the facts say something together, which nothing else here could notice ==
 *
 * The other assertions in this file are about **form**: that each statement parses back to the
 * theorem, that nothing is assumed, that the facts and the statements cover each other, what each
 * derivation spent. Every one of them would pass over a development whose facts were individually
 * true and jointly empty, and none of them spends two facts against each other.
 *
 * The degenerate map to keep in mind is `real_of_int a := 0`, and it satisfies **four** of them,
 * the homomorphism equations for addition, multiplication, negation and zero, which are all
 * `0 = 0` under it. What refutes it is `INT_REAL_ONE`, which reads `0 = 1`. So the two value facts
 * are not a matched pair of which one would do. The order map does not refute it either, since
 * `INT_LE a b = (0 <= 0)` is true of every pair and false of some, which is the second guard
 * below.
 *
 * The test below spends exactly those two against each other and comes back with
 * `~(INT_ZERO = INT_ONE)`, nothing assumed, derived **through the bridge**: it uses the embedding
 * as the instrument rather than as the subject, and what it lands on is false in a one-point `int`.
 * `docs/adr/0033` names the same hazard one level down and `IntegerSpec` answers it there in the
 * carrier, through `Successor.distinct`; this answer shares no step with that one.
 *
 * == The order map, which arrived on 2026-09-18 and is the one fact of a different shape ==
 *
 * `INT_REAL_LE` says the embedding carries the order **both ways**, and it is an equation between
 * propositions where every other fact here is an equation between reals. It is the first statement
 * in this file that could have answered the accounting assertion differently, which is why that
 * assertion is read rather than only re-run below: measured on 2026-09-18 it reached fourteen of
 * the sixteen and the carrier's three and nothing else, so the boundary the section above describes
 * survives the new shape rather than being assumed to.
 *
 * What it is **not** is a way to `~(INT_DIVIDES 2 1)`, and since 2026-09-19 that is measured
 * rather than left open. `docs/adr/0033` predicted that statement wanted the discreteness of the
 * order and that this map might be the route to it. The statement is proved, as
 * `Integer.TwoDoesNotDivide`, and `IntegerSpec` walks its derivation and finds no fact of `INT_LE`
 * in it, with a positive control beside it so an empty answer cannot come from an instrument that
 * read nothing. That this map is not in it either needs no walk: `Integer` is built below this
 * development. So this map has no consumer yet.
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

  private def missing(theorem: Kernel.Thm): LogicError =
    NotOfForm("an equation between propositions", theorem.conclusion)

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(missing(theorem))

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

  /**
   * The re-basing refuses a theory that does not extend the one the quotient was built over.
   *
   * `Quotient.over` is what this development calls first, and the sentence in its docstring — that
   * a caller placing this link below the one it embeds is refused rather than quietly building a
   * second branch off the quotient — was a claim about a guard nothing exercised. It is asserted
   * here rather than in `QuotientSpec` because the refusal is about a real pair of theories and
   * that file's quotient is a toy over `NUM_CONG 2` with nothing below it to fail against.
   *
   * `product` is the link the construction of the integers extends, so its theory is genuinely
   * below the quotient's: it declares none of the constants the quotient introduced, and the
   * refusal names them. It was `forward` until phase 5 moved the integers below the reals, after
   * which `forward` holds the quotient and extends it.
   *
   * The positive control is the second half and is not decoration. A `Logic.over` that refused
   * everything would pass the first assertion, and this development would then not build at all —
   * which is true today and is exactly the kind of thing that stops being true when the check is
   * loosened rather than when it is removed.
   */
  "Re-basing the quotient" should "refuse a theory that does not extend the one it was built over" in {
    integers.quotient.over(chain.product.theory) match {
      case Left(error) => error.message should include(Integer.SameName)
      case Right(_) =>
        fail("a theory below the quotient's own was accepted as one extending it")
    }

    integers.quotient.over(integers.theory) should be(Symbol("right"))
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
   * It is the guard on everything above it, and what it guards against is not one wrong map but
   * the whole class of readings under which the facts are individually true and say nothing
   * jointly. `Integer` has this separation already and proves it through `Successor.distinct` in
   * the carrier, which shares no step with this: here it comes out of two **published** facts of
   * this development and one axiom of the reals.
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

    val distinct = force(chain.reals.law("ONE_NOT_ZERO"))
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

  /**
   * The order map refuses a pair, which is what says the biconditional is not trivially true.
   *
   * An `INT_LE` that held of every pair would satisfy the statement under an `INT_REAL_LE` that
   * held of every pair too, and every other assertion in this file would still pass: the form
   * assertions read the statement, and the accounting assertion reads the derivation. Neither
   * spends the fact on a claim that could come out false.
   *
   * So it is spent here, in both directions and at the same pair. Forward, `INT_ZERO <= INT_ONE`
   * comes out of `0 <= 1` on the reals; backward, the other order is **refused**, because `1 <= 0`
   * is not. The negative is the half that matters, and it lands on a claim about the carrier that
   * nothing in `Integer` proves: the order there is reflexive, transitive, antisymmetric and
   * total, and a one-point `int` satisfies all four.
   *
   * `LINARITH` over the chain's own order rather than a second one, for the reason
   * `Peano.construct` gives about paying for an order twice.
   */
  "The order map" should "settle an order at `int` both ways from one about the reals" in {
    val linarith = force(Linarith.construct(chain.order))

    val values = force(
      Rewrite.Rule.all(
        inclusion.logic,
        Vector(fact(Inclusion.EmbedsZero), fact(Inclusion.EmbedsOne))
      )
    )

    def atReals(left: String, right: String): Kernel.Thm = {
      val instance = force(
        rules.specAll(
          fact(Inclusion.EmbedsOrder),
          List(
            force(inclusion.term(left, Integer.Classes)),
            force(inclusion.term(right, Integer.Classes))
          )
        )
      )
      force(Rewrite.inTheorem(values, instance))
    }

    // Forward: the reals decide `0 <= 1` and the equation carries it to `int`.
    val upwards = atReals("INT_ZERO", "INT_ONE")
    val holds = force(linarith.prove(force(rightOf(upwards))))
    val ordered = force(LogicError.lift(Kernel.eqMp(force(Conv.sym(upwards)), holds)))

    ordered.hypotheses shouldBe empty
    ordered.conclusion shouldBe force(inclusion.proposition("INT_LE INT_ZERO INT_ONE"))

    // Backward, and this is the half a collapsed `int` fails: `1 <= 0` is refutable on the reals,
    // so the pair is refused rather than merely unproved.
    val downwards = atReals("INT_ONE", "INT_ZERO")
    val goal = force(Term.destEq(downwards.conclusion).map(_._1).toRight(missing(downwards)))
    val assumed = force(LogicError.lift(Kernel.assume(goal)))
    val overReals = force(LogicError.lift(Kernel.eqMp(downwards, assumed)))

    val refutation = force(
      linarith.prove(force(inclusion.proposition("(1:real) <= 0 ==> F")))
    )
    val absurd = force(rules.mp(refutation, overReals))
    val refused = force(rules.notIntro(goal, absurd))

    refused.hypotheses shouldBe empty
    refused.conclusion shouldBe force(inclusion.proposition("~(INT_LE INT_ONE INT_ZERO)"))
  }

  /* ------------------------------------------------------------------ what it costs */

  private lazy val eta: Term = force(chain.classical.axiom(Classical.Eta)).conclusion
  private lazy val choice: Term = force(chain.classical.axiom(Classical.Choice)).conclusion
  private lazy val infinity: Term = force(chain.naturals.axiom(Natural.Infinity)).conclusion

  /** The sixteen, read off the theory of the reals rather than listed again here. */
  private lazy val field: Set[Term] = chain.reals.laws.values.map(_.conclusion).toSet

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
        val spent = Real.spent(fact(name))
        (spent intersect field) should not be empty
        (spent -- field) shouldBe carrier
      }
    }

    Real.spent(force(integers.fact(Integer.Equal))) intersect field shouldBe empty
  }
}
