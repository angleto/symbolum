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
 * There is no arithmetic on `rat` yet, so there is nothing here about addition, multiplication or
 * the order. What decides when there will be is measured and is in `Fraction`'s own opening: the
 * carrier is pairs of **integers**, `Semiring` decides identities on `num` and `Ring` on the
 * reals, and nothing decides them on `int`, so each lifted operation's respectfulness is a hand
 * derivation until something does. That is a fact about the tools and not about the rationals.
 */
class FractionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def lift[T](result: Either[KernelError, T]): T = force(LogicError.lift(result))

  private val chain = Chain.standard
  private val fractions = force(
    Fraction.construct(chain.classical, chain.integers, chain.product)
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

  it should "declare `rat` and the quotient's own constants, and nothing else" in {
    val before = chain.integers.theory.constants.keySet
    (fractions.theory.constants.keySet -- before) shouldBe
      Set(Fraction.SameName, Fraction.Abstraction, Fraction.Representation, Fraction.Projection,
        Fraction.Names.representative)
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
