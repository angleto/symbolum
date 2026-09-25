package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The rationals' carrier and its type, which is as far as `docs/adr/0036` has been built.
 *
 * == What this file is for ==
 *
 * `QuotientSpec` says in as many words that the one guard it cannot carry is **non-collapse**, and
 * `IntegerSpec` carries it for `int` because `num` has a distinctness procedure. The same question
 * has to be asked of `rat` and it is the first assertion below: `0` and `1` are different
 * rationals, derived rather than assumed, and a quotient that had identified everything could not
 * produce it. Every other assertion here would pass over a one-point type.
 *
 * == And what it deliberately does not ask ==
 *
 * The operations exist since 2026-09-25, and the same day the rest of a commutative ring: the two
 * units, both associativities, the additive inverse and the distributive law, each compared below
 * with the text it is published as; and the order, `RAT_LE`, with the four laws of a total order and
 * the pair of facts that keeps it from being the trivial one. The inverse of a non-zero rational and the
 * two laws tying the order to the operations arrived the same day, and each is detached below at
 * the units, so none of them is an implication whose antecedent nobody can meet.
 */
class FractionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def lift[T](result: Either[KernelError, T]): T = force(LogicError.lift(result))

  private val chain = Chain.standard
  private val fractions = force(
    Fraction.construct(chain.classical, chain.integers, chain.product, chain.peano)
  )
  private val rules = fractions.logic.rules

  private def fact(name: String): Kernel.Thm = force(fractions.fact(name))

  /* ------------------------------------------------------------------ the statements */

  "Every fact of the development" should "prove the statement it is published as" in {
    Fraction.Statements.foreach { case (name, text) =>
      val proved = fact(name)
      withClue(s"$name: ") {
        proved.conclusion shouldBe force(fractions.proposition(text))
        proved.hypotheses shouldBe empty
      }
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    fractions.facts.keySet shouldBe Fraction.Statements.map(_._1).toSet
  }

  /* ------------------------------------------------------------------ the relation */

  "The relation" should "be the cross-multiplication over a denominator that is a successor" in {
    // The definition read back as the text a person checks against the informal claim, which is
    // the one thing in this file a reader compares with `docs/adr/0036` rather than with a
    // theorem. `(a, d)` denotes `a / (d + 1)`, so two pairs agree when `a * (d' + 1)` and
    // `a' * (d + 1)` do, and the successor is what makes the relation transitive at every pair
    // rather than at the ones with a non-zero denominator.
    val unfolded = force(
      for {
        definition <- fractions.definition(Fraction.SameName)
        left <- fractions.term("p:prod(int,num)", Fraction.Pairs)
        right <- fractions.term("q:prod(int,num)", Fraction.Pairs)
        applied <- Conv.unfold(definition, List(left, right))
      } yield applied
    )

    fractions.show(unfolded.conclusion) shouldBe
      "RAT_SAME p q = (INT_MUL (FST p) (INT_OF_NUM (SUC (SND q))) = " +
        "INT_MUL (FST q) (INT_OF_NUM (SUC (SND p))))"
  }

  /* ------------------------------------------------------------------ the type */

  "The type" should "not collapse, which is the one guard the builder cannot carry" in {
    // `0/1` and `1/1` are different rationals. The route is the quotient's central fact, which
    // turns the equality of two classes into the relation; the relation at these two pairs is
    // `INT_ZERO = INT_OF_NUM (SUC 0)` once the two products are taken, and that is `0 = SUC 0`
    // through the embedding's injectivity, which `NUM_SUC_NOT_ZERO` refuses. Without this, every
    // other assertion in this file holds of a one-point type.
    val nums = TyApp(Natural.TypeName, Nil)
    val ints = TyApp(Integer.TypeName, Nil)
    val zeroNum = force(fractions.term("0:num", nums))
    val successor = force(fractions.term("SUC (0:num)", nums))
    val embedded = force(fractions.term("INT_OF_NUM (SUC (0:num))", ints))
    val one = force(fractions.term("INT_ONE", ints))
    val integers = chain.integers

    val projections = force(
      Vector(chain.product.fact(Product.FirstOfPair), chain.product.fact(Product.SecondOfPair))
        .foldRight[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
          case (next, rest) => next.flatMap(one => rest.map(one +: _))
        }
        .flatMap(Rewrite.Rule.all(fractions.logic, _))
    )

    val refused = force(
      for {
        equal <- fractions.fact(Quotient.ProjectionEqual)
        zeroPair <- fractions.term("PAIR INT_ZERO (0:num)", Fraction.Pairs)
        onePair <- fractions.term("PAIR INT_ONE (0:num)", Fraction.Pairs)
        asRelation <- rules.specAll(equal, List(zeroPair, onePair))

        definition <- fractions.definition(Fraction.SameName)
        unfolded <- Conv.unfold(definition, List(zeroPair, onePair))
        reduced <- Rewrite.inTheorem(projections, unfolded)

        // `INT_ZERO * s = INT_ZERO` on the left, and `INT_ONE * s = s` on the right through
        // commutativity, which is what leaves a comparison between two embedded naturals.
        leftIsZero <- integers.fact(Integer.ZeroTimes).flatMap(rules.spec(embedded, _))
        commuted <- integers.fact(Integer.MulCommutative).flatMap(rules.specAll(_, List(one, embedded)))
        atOne <- integers.fact(Integer.MulAtOne).flatMap(rules.spec(embedded, _))
        rightIsSuccessor <- Conv.trans(commuted, atOne)
        collapsing <- Rewrite.Rule
          .all(fractions.logic, Vector(leftIsZero, rightIsSuccessor))
          .flatMap(Rewrite.inTheorem(_, reduced))

        // `INT_ZERO` written as an embedded natural, by a congruence on the LEFT ARGUMENT of the
        // equation and not by rewriting. The rewriting was tried first and is wrong here: it puts
        // `INT_OF_NUM ZERO` inside the pair on the other side of the chain as well, and the
        // transitivity then refuses against a relation about a pair nobody wrote.
        zeroBack <- integers.fact(Integer.OfNaturalZero).flatMap(Conv.sym)
        atEquality <- Conv
          .apTerm(Term.equalityAt(ints), zeroBack)
          .flatMap(Conv.apThm(_, embedded))
        asEmbedded <- Conv.trans(collapsing, atEquality)
        overNaturals <- integers
          .fact(Integer.OfNaturalInjective)
          .flatMap(rules.specAll(_, List(zeroNum, successor)))
        toNaturals <- Conv.trans(asEmbedded, overNaturals)
        classesEqual <- Conv.trans(asRelation, toNaturals)

        premise <- Term
          .destEq(classesEqual.conclusion)
          .map(_._1)
          .toRight(NotOfForm("an equation between propositions", classesEqual.conclusion))
        assumed <- LogicError.lift(Kernel.assume(premise))
        naturalsEqual <- LogicError.lift(Kernel.eqMp(classesEqual, assumed))
        flipped <- Conv.sym(naturalsEqual)
        never <- chain.peano.naturals
          .fact(Natural.SuccessorNotZero)
          .flatMap(rules.spec(zeroNum, _))
        clash <- rules.notElim(never, flipped)
        result <- rules.notIntro(premise, clash)
      } yield result
    )

    refused.hypotheses shouldBe empty
    fractions.show(refused.conclusion) shouldBe
      "~(RAT_OF_PAIR (PAIR INT_ZERO 0) = RAT_OF_PAIR (PAIR INT_ONE 0))"
  }

  it should "declare `rat`, the quotient's own constants, the operations, the two units, the order and the inverse, and nothing else" in {
    // The operations and the units since 2026-09-25, when the ring of `int` closed their
    // obligations; a constant arriving here beyond these would be a definition nobody listed,
    // which is what this reads for.
    val before = chain.integers.theory.constants.keySet
    (fractions.theory.constants.keySet -- before) shouldBe
      Set(Fraction.SameName, Fraction.Abstraction, Fraction.Representation, Fraction.Projection,
        Fraction.Names.representative, Fraction.Addition, Fraction.Negation, Fraction.Multiplication,
        Fraction.Zero, Fraction.One, Fraction.AtMost, Fraction.Inverse)
  }

  "The order" should "not be the trivial one, which every one of its four laws would also be" in {
    // Reflexivity, transitivity, antisymmetry and totality all hold of the relation that relates
    // everything, on a one-point type or on any other. What separates `RAT_LE` from it is one
    // comparison that holds and one that does not, both derived with nothing assumed.
    //
    // What this has and has not been seen catching, measured on 2026-09-25: with the definition
    // reversed, which is a total order too, the construction refused earlier, at the derivation of
    // `RAT_LE_PAIRS`, because that statement fixes the direction. So no perturbation of the
    // definition tried reaches this test; it holds the property against a change that keeps the
    // pair fact and moves the constants, which nothing has made yet.
    val upwards = fact(Fraction.ZeroAtMostOne)
    val downwards = fact(Fraction.OneNotAtMostZero)
    upwards.hypotheses shouldBe empty
    downwards.hypotheses shouldBe empty
    fractions.show(upwards.conclusion) shouldBe "RAT_LE RAT_ZERO RAT_ONE"
    fractions.show(downwards.conclusion) shouldBe "~(RAT_LE RAT_ONE RAT_ZERO)"
  }

  "The units" should "be different rationals, stated on the published constants" in {
    // The pair-level refusal above is what this repeats at the constants a consumer writes. It is
    // asserted as a theorem with nothing assumed rather than only as a statement, because a law
    // like `x + 0 = x` holds of a one-point type and this is the one fact here that does not.
    val distinct = fact(Fraction.UnitsDistinct)
    distinct.hypotheses shouldBe empty
    fractions.show(distinct.conclusion) shouldBe "~(RAT_ZERO = RAT_ONE)"
  }

  "The ring laws" should "rest on the ring of `int`, which is what decides each pair-level identity" in {
    // Each law is two rewritings to a pair and one relation between the pairs decided by
    // `Integer.ring`. A law whose derivation did not reach an integer law would have been decided
    // some other way, and the argument in `Fraction.Lifting.laws` would be describing a route
    // nothing took.
    val integerLaws = Set(Integer.MulCommutative, Integer.AddCommutative, Integer.MulAssociative)
      .map(name => force(chain.integers.fact(name)).conclusion)
    Vector(Fraction.AddAssociative, Fraction.MulAssociative, Fraction.Distributive, Fraction.MulAtOne)
      .foreach { name =>
        withClue(s"$name: ") {
          Derivation.restingOn(fact(name), integerLaws) should not be empty
        }
      }
  }

  "The inverse" should "be detached at a rational that is not zero, with nothing left assumed" in {
    // `RAT_MUL_INV` carries `~(x = RAT_ZERO)`, and an implication whose antecedent nobody can
    // discharge reads exactly like a fact. `RAT_ONE` is not zero by the units' distinctness, so
    // the antecedent is met at a published constant and the conclusion stands on its own.
    val one = force(fractions.term("RAT_ONE", Fraction.Classes))
    val nonZero = force(
      for {
        distinct <- Right(fact(Fraction.UnitsDistinct))
        held <- LogicError.lift(Kernel.assume(force(fractions.proposition("RAT_ONE = RAT_ZERO"))))
        flipped <- Conv.sym(held)
        absurd <- rules.notElim(distinct, flipped)
        result <- rules.notIntro(held.conclusion, absurd)
      } yield result
    )
    val detached = force(rules.spec(one, fact(Fraction.MulInverse)).flatMap(rules.mp(_, nonZero)))
    detached.hypotheses shouldBe empty
    fractions.show(detached.conclusion) shouldBe "RAT_MUL RAT_ONE (RAT_INV RAT_ONE) = RAT_ONE"
  }

  it should "be zero at zero, which the definition writes rather than assumes" in {
    // The convention a field's inverse has to take somewhere, and it is taken in the definition's
    // conditional: `RAT_INV_ZERO` costs no axiom beyond what the conditional costs, so a proof of
    // it that reached a fact about the order or the product would be a route nobody wrote.
    // The positive control is the product off zero, which does rest on it: without that line an
    // instrument that found nothing anywhere would pass the absence.
    val atZero = fact(Fraction.InverseAtZero)
    val product = Set(fact(Fraction.MulPairs).conclusion)
    atZero.hypotheses shouldBe empty
    Derivation.restingOn(fact(Fraction.MulInverse), product) should not be empty
    Derivation.restingOn(atZero, product) shouldBe empty
  }

  "The order" should "be carried by the sum and by the product, detached at the units" in {
    // The two laws that make an ordered field of an ordered ring, each spent with every antecedent
    // discharged by `RAT_ZERO_LE_ONE`, so neither is an implication nobody can use.
    val zero = force(fractions.term("RAT_ZERO", Fraction.Classes))
    val one = force(fractions.term("RAT_ONE", Fraction.Classes))
    val upwards = fact(Fraction.ZeroAtMostOne)

    val shifted = force(
      rules.specAll(fact(Fraction.AtMostAdd), List(zero, one, one)).flatMap(rules.mp(_, upwards))
    )
    shifted.hypotheses shouldBe empty
    fractions.show(shifted.conclusion) shouldBe "RAT_LE (RAT_ADD RAT_ZERO RAT_ONE) (RAT_ADD RAT_ONE RAT_ONE)"

    val product = force(
      rules.specAll(fact(Fraction.AtMostMul), List(one, one))
        .flatMap(rules.mp(_, upwards))
        .flatMap(rules.mp(_, upwards))
    )
    product.hypotheses shouldBe empty
    fractions.show(product.conclusion) shouldBe "RAT_LE RAT_ZERO (RAT_MUL RAT_ONE RAT_ONE)"
  }

  /* ------------------------------------------------------------------ what it costs */

  "Every fact of the carrier" should "cost at most the integers' foundation and no real axiom" in {
    // The reading `IntegerSpec` makes one level down, and it is about what a **fact** rests on and
    // not about the theory's axiom list. The list is the whole chain's and carries the sixteen
    // wherever it is taken, so an assertion over it would be about the chain rather than about
    // this development: the first version of this test made exactly that mistake and failed with
    // all sixteen in its hands.
    val eta = force(chain.classical.axiom(Classical.Eta)).conclusion
    val choice = force(chain.classical.axiom(Classical.Choice)).conclusion
    val infinity = force(chain.naturals.axiom(Natural.Infinity)).conclusion
    val foundation = Set(choice, eta, infinity)
    val realAxioms =
      Real.Axioms.map { case (name, _) => force(chain.reals.axiom(name)).conclusion }.toSet

    // Not empty, which is the guard against the guard: a reading that returned nothing for
    // everything would satisfy both lines below and say nothing at all.
    realAxioms should have size 16
    realAxioms should contain noElementsOf foundation

    Fraction.Statements.foreach { case (name, _) =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(fact(name)) should contain noElementsOf realAxioms
        Derivation.axiomsOf(fact(name)).diff(foundation) shouldBe empty
      }
    }
  }

  it should "spend the naturals on the transitivity and not on the other two" in {
    // Where the cost actually falls, which is the same split `IntegerSpec` draws for the relation
    // it quotients: reflexivity and symmetry are about equality and reach no axiom at all, and
    // transitivity is the one that cancels and therefore reaches the carrier's. A file where all
    // three cost the same would be a file where the cancellation had been assumed somewhere.
    Derivation.axiomsOf(fact(Fraction.SameReflexive)) shouldBe empty
    Derivation.axiomsOf(fact(Fraction.SameSymmetric)) shouldBe empty
    Derivation.axiomsOf(fact(Fraction.SameTransitive)) should not be empty
  }
}
