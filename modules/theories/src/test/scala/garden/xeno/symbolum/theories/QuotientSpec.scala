package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The quotient builder, put to a toy quotient before anything real is built through it.
 *
 * `docs/adr/0016` asks for exactly this and gives the reason in one line: a builder validated only
 * by its first real consumer is not validated, it is co-designed with it. The first real consumer
 * here is the integers, which are a quotient of pairs of naturals, and every choice this builder
 * makes would be bent towards them if they were the only thing it had ever run on.
 *
 * **The toy is `num` modulo two, and it is a real congruence rather than a relation invented for
 * the test.** `Modular.NUM_CONG` is the congruence this repository already has, with reflexivity,
 * symmetry, transitivity and the compatibility of addition and multiplication all derived. What
 * that buys is that three of the obligations the builder demands are discharged with a
 * specialisation and nothing else, so a failure here is the builder's and not the fixture's.
 *
 * `NUM_CONG 2` is a partial application of a ternary constant to a numeral. It is a **term** and
 * not a constant, it is closed, and `Kernel.defineType` asks for nothing more. That is the reason
 * `Quotient.Equivalence` takes a term: a builder that insisted on a constant would have forced this
 * test to define one, and defining one is how a fixture stops resembling the thing it stands in for.
 *
 * == The five questions ==
 *
 * **Whether it cost anything.** Asserted as an **equality** of axiom sets against what the carrier
 * already rested on, which is the form `CodingSpec` uses and is stronger than a ceiling: a fact that
 * quietly stopped spending the naturals' two would be as much a defect as one that started spending
 * a third. `docs/adr/0016` predicts the answer is nothing, having measured the mechanism against the
 * kernel and not against a build, so this is that prediction being run.
 *
 * **Whether the central fact is the central fact.** `proj x = proj y <=> R x y` in both directions,
 * against concrete numbers where the answer is known: two and four are congruent modulo two and
 * their classes are equal, two and three are not and theirs are not. The second of those is what
 * says the type is not the one-point type, and a builder that produced a one-point type would pass
 * every other assertion in this file.
 *
 * **Whether the three lifts lift.** One of each, against obligations that are `Modular`'s own facts
 * specialised at the modulus wherever they can be.
 *
 * **Whether a wrong obligation is refused rather than absorbed.** Three refusals, one per lift,
 * each handing the lift a theorem that is true and is about the wrong thing. This is the half that
 * is easy to leave out, and without it the three shape checks could be deleted and nothing here
 * would go red.
 *
 * **Whether the carrier check refuses.** A relation that is not two arguments of one type, and a
 * relation that is not closed, are the two ways a caller arrives at this builder wrongly.
 */
class QuotientSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val modular = chain.modular
  private val classical = chain.classical
  private val rules = modular.logic.rules

  /**
   * The two types this fixture names, spelled here rather than borrowed.
   *
   * `Modular` keeps its own as `private`, which is right: they are its internal spelling of `num`
   * and not an interface. Writing them again is two lines and the alternative is widening a
   * development's access for a test, which is the change that stops being noticed.
   */
  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val relation: Type = Type.fun(numbers, Type.fun(numbers, Type.Bool))
  private val ternary: Type = Type.fun(numbers, relation)

  /** `2:num`, which is the modulus and the only numeral this fixture needs. */
  private val two: Term = force(modular.term("2:num", numbers))

  /** `NUM_CONG 2`, the relation the classes are of. */
  private val congruence: Term = {
    val constant = force(LogicError.lift(modular.theory.constant(Modular.CongruenceName, ternary)))
    force(LogicError.lift(Term.app(constant, two)))
  }

  /** A fact of `Modular` with its leading modulus fixed at two. */
  private def atTwo(name: String): Kernel.Thm =
    force(modular.fact(name).flatMap(rules.spec(two, _)))

  private val equivalence = Quotient.Equivalence(
    congruence,
    reflexive = atTwo(Modular.CongRefl),
    symmetric = atTwo(Modular.CongSym),
    transitive = atTwo(Modular.CongTrans)
  )

  private val names = Quotient.Names(
    typeName = "parity",
    abstraction = "mk_parity",
    representation = "dest_parity",
    projection = "PARITY"
  )

  private lazy val parity: Quotient =
    force(
      Quotient.define(classical, modular.theory, modular.notation, names, equivalence)
    )

  private def numeral(text: String): Term = force(modular.term(text, numbers))

  /* ------------------------------------------- the two accessors a caller reaches for */

  /**
   * `definition` and `project`, which nothing had driven.
   *
   * Both are public and neither was exercised before 2026-09-17, which is a different thing from
   * being untested code: `fact` beside them is read throughout this file, so what was missing
   * is not the development but the two entry points a caller who holds an element rather than a
   * name goes through.
   *
   * The refusal is the half worth asserting. Asking for a name that is not there answers with
   * `MissingDefinition` carrying the name asked for, and the reason to pin that rather than the
   * success is the shape of the alternative: an accessor that answered with the wrong theorem, or
   * with a refusal naming nothing, would be found by a caller reading a proof rather than by a
   * test.
   */
  "The definition accessor" should "answer for a name it has and refuse one it has not, saying which" in {
    val defined = force(parity.definition(names.projection))
    parity.show(defined.conclusion) should include(names.projection)

    parity.definition("NO_SUCH_CONSTANT") match {
      case Left(MissingDefinition(name)) => name shouldBe "NO_SUCH_CONSTANT"
      case other => fail(s"a name this quotient never defined must be refused by name: $other")
    }
  }

  "Projecting an element" should "build the application a caller would otherwise spell by hand" in {
    // The point of the accessor is that the caller does not write the constant's name or its type:
    // both come from the quotient, so a caller cannot reach for `PARITY` at the wrong type and get
    // a term that parses and means nothing.
    val projected = force(parity.project(numeral("2:num")))

    parity.show(projected) should include(names.projection)
    Term.typeOf(projected) shouldBe TyApp(names.typeName, Nil)
  }

  /* ------------------------------------------------------------------ what it cost */

  /** The three the whole chain rests on, by name rather than by shape. */
  private lazy val eta: Term = force(classical.axiom(Classical.Eta)).conclusion
  private lazy val choice: Term = force(classical.axiom(Classical.Choice)).conclusion
  private lazy val infinity: Term =
    force(chain.naturals.axiom(Natural.Infinity)).conclusion

  /**
   * What the builder adds to what the carrier already spent, which is **eta and nothing else**.
   *
   * `docs/adr/0016` predicted this at the mechanism level and predicted it correctly: the fact the
   * type is defined for needs function extensionality in one direction, and
   * `Classical.FUNCTION_EXTENSIONALITY` is derived from eta rather than asserted. So the builder
   * adds no axiom the chain does not already hold, which is the record's claim, while adding one
   * the **carrier** was not spending, which is a different sentence and the one a reader needs.
   *
   * **The first version of this test asserted set equality with the carrier and was wrong**, in the
   * direction that would have made the file agree with a prediction instead of measuring. Equality
   * against `CodingSpec`'s model is right where the thing measured spends exactly what it inherits;
   * here it does not, and copying the form of a neighbouring assertion without checking that the
   * claim underneath is the same claim is how a test comes to encode an expectation.
   */
  it should "add exactly eta to what the carrier already spent" in {
    val central = force(parity.fact(Quotient.ProjectionEqual))
    val inherited = force(modular.fact(Modular.CongTrans))

    Derivation.axiomsOf(inherited) shouldBe Set(choice, infinity)
    Derivation.axiomsOf(central) shouldBe Set(choice, eta, infinity)
    Derivation.axiomsOf(central) -- Derivation.axiomsOf(inherited) shouldBe Set(eta)
  }

  /**
   * Everything the builder produces rests on the chain's three and on nothing else.
   *
   * The assertion that carries the record's actual claim, and the one that cannot go stale when the
   * carrier changes: `docs/adr/0016` says a quotient costs nothing beyond what the chain already
   * holds, and what the chain holds is choice, eta and infinity. Stated over **every** fact the
   * builder hands out rather than over one, because a builder that stayed clean in its central fact
   * and reached for something else in a lift would pass a one-fact assertion.
   *
   * The floor against vacuity is the count: six facts, not an empty map silently agreeing.
   */
  it should "rest on choice, eta and infinity and no others, in every fact it hands out" in {
    val names = Vector(
      Quotient.AbstractionOfRepresentation,
      Quotient.Characterisation,
      Quotient.ProjectionEqual,
      Quotient.ProjectionOnto,
      Quotient.ProjectionOfRepresentative,
      Quotient.RelatedToRepresentative
    )
    names should have size 6

    val spent = names.foldLeft(Set.empty[Term]) { (found, name) =>
      found ++ Derivation.axiomsOf(force(parity.fact(name)))
    }
    spent shouldBe Set(choice, eta, infinity)
  }

  /**
   * The chooser costs choice and **nothing else**, which is cheaper than the central fact.
   *
   * This assertion has now been wrong twice, both times in the same direction, and the shape of the
   * error is worth more than the number. I assumed the chooser sat **on top of** the central fact
   * and added choice to it, by analogy with `Product.FST`. It does not sit on it at all.
   *
   * `PROJ_REPR` comes from `PROJ_ONTO` and the choice axiom, and `PROJ_ONTO` comes from the two
   * theorems `Kernel.defineType` returned, which assert nothing. So the route never touches the
   * relation's own facts: no eta, because extensionality is only needed to turn a relation into an
   * equality of functions and this direction never does; and no infinity, because the carrier's
   * axioms are reached through `Modular`'s facts and this derivation reads none of them.
   *
   * The general statement, which is what a consumer needs: **the two halves of this builder are
   * independent.** `PROJ_EQ` costs the carrier's axioms plus eta; `PROJ_REPR` costs choice. Neither
   * is derived through the other, so a development that wants only one pays only for it.
   *
   * What produced two wrong guesses in a row was reasoning from a neighbouring construction's shape
   * (`Product`, where the projections genuinely are defined on top of the type's facts) instead of
   * from this derivation's own route. `Derivation.axiomsOf` answers it in one call and I twice
   * wrote down an expectation instead of making that call.
   */
  it should "pay choice for the chosen representative, and neither eta nor the carrier's axioms" in {
    val central = force(parity.fact(Quotient.ProjectionEqual))
    val onto = force(parity.fact(Quotient.ProjectionOnto))
    val chosen = force(parity.fact(Quotient.ProjectionOfRepresentative))

    // The bijection the kernel returned asserts nothing, which is what makes the rest of this
    // paragraph possible and is `docs/adr/0006`'s promise being spent.
    Derivation.axiomsOf(onto) shouldBe empty

    Derivation.axiomsOf(chosen) shouldBe Set(choice)
    Derivation.axiomsOf(chosen) should not contain eta
    Derivation.axiomsOf(chosen) should not contain infinity

    // And it really is cheaper, rather than equal by both being small: the central fact spends two
    // the chooser does not.
    Derivation.axiomsOf(central) -- Derivation.axiomsOf(chosen) shouldBe Set(eta, infinity)
  }

  /* ------------------------------------------------------------------ the central fact */

  /**
   * A number and that number plus the modulus have the same class.
   *
   * The direction that spends function extensionality, which is the one the builder exists for:
   * going from a relation between two numbers to an equality between two **functions** is not
   * something this logic does without eta.
   *
   * It is stated at `2` and `2 + 2` rather than at `2` and `4`, and the difference is not cosmetic.
   * `Modular.CongModulus` gives `NUM_CONG k (m + k) m` and nothing here computes, so `4` would have
   * to be reached from `2 + 2` by the arithmetic of `num`, which is a second development doing a
   * second thing. What this test is about is whether the quotient identifies two numbers the
   * relation relates; which two they are spelled as is the fixture's business and not the claim's.
   */
  it should "give a number and that number plus the modulus one class" in {
    val central = force(parity.fact(Quotient.ProjectionEqual))
    val sum = force(LogicError.lift(Term.appAll(addition, List(two, two))))

    val congruent = force(
      modular.fact(Modular.CongModulus).flatMap(rules.specAll(_, List(two, two)))
    )
    val instance = force(rules.specAll(central, List(sum, two)))
    val back = force(Conv.sym(instance))
    val equalClasses = force(LogicError.lift(Kernel.eqMp(back, congruent)))

    equalClasses.hypotheses shouldBe empty
    Term.destEq(equalClasses.conclusion) shouldBe defined
    parity.show(equalClasses.conclusion) should include(names.projection)

    // And it cost the carrier's two and nothing more, which is the assertion above seen at a
    // conclusion a reader can check by eye rather than at the general fact.
    Derivation.axiomsOf(equalClasses) shouldBe Set(choice, eta, infinity)
  }

  /**
   * The two sides of the central fact are different propositions, which is the non-collapse guard
   * this development can actually carry.
   *
   * **What it does not establish, said here rather than left to be assumed.** A quotient that
   * identified everything would satisfy every other assertion in this file, and refuting it means
   * deriving `~(NUM_CONG 2 2 3)`, which nothing in this repository can: `Modular` publishes no
   * negated congruence and there is no decision procedure over `num` to ask. So the honest guard is
   * structural. The biconditional really relates an equation between classes to the **caller's**
   * relation, rather than to truth: a builder that had collapsed the type would have produced a
   * central fact whose right side was not `NUM_CONG` at all, since the only way to make every class
   * equal is for the relation side to stop being read.
   *
   * The real non-collapse evidence in this file is the predicate lift further down, which carries a
   * property of a representative through to the class. That is what a collapsed quotient cannot do,
   * and it is why that test is not decoration.
   */
  it should "relate the equation between classes to the caller's own relation, not to truth" in {
    val central = force(parity.fact(Quotient.ProjectionEqual))
    val three = numeral("3:num")

    val instance = force(rules.specAll(central, List(two, three)))
    val (classesEqual, related) =
      Term.destEq(instance.conclusion).getOrElse(fail("the central fact is not an equation"))

    classesEqual should not be related
    parity.show(classesEqual) should include(names.projection)
    parity.show(related) should include(Modular.CongruenceName)
    parity.show(related) should not include names.projection
  }

  /* ------------------------------------------------------------------ the three lifts */

  private lazy val addition: Term =
    force(LogicError.lift(modular.theory.constant(Peano.Addition, Modular.binary)))

  private lazy val multiplication: Term =
    force(LogicError.lift(modular.theory.constant(Peano.Multiplication, Modular.binary)))

  /** `|- !x y u v. NUM_CONG 2 x u ==> NUM_CONG 2 y v ==> NUM_CONG 2 (x + y) (u + v)`. */
  private lazy val additionRespects: Kernel.Thm = reshape(atTwo(Modular.CongAdd))

  private lazy val multiplicationRespects: Kernel.Thm = reshape(atTwo(Modular.CongMul))

  /**
   * `Modular` states compatibility as `R m n ==> R p q ==> R (m # p) (n # q)` and the builder wants
   * `R x u ==> R y v ==> R (f x y) (f u v)`.
   *
   * The same theorem with the four binders in a different order, which is the difference between
   * pairing the arguments by **position in the operation** and pairing them by **which relation
   * they come from**.
   *
   * This specialises **positionally**, which `CLAUDE.md` warns about and which is safe here for a
   * reason worth stating rather than relying on: `Rules.specTo` finds the instantiation by matching
   * a body, and the body wanted here is the reordering itself, so there is no target to hand it
   * that is not the answer. What makes the positional call safe is that its correctness is asserted
   * immediately — the lift below refuses any theorem that is not exactly the obligation, so a
   * reordering that got the four the wrong way round fails this file rather than lifting the wrong
   * operation. The guard is the check inside the builder, not care taken here.
   */
  private def reshape(compatibility: Kernel.Thm): Kernel.Thm = {
    val x = Term.variable("x", numbers)
    val y = Term.variable("y", numbers)
    val u = Term.variable("u", numbers)
    val v = Term.variable("v", numbers)

    force(
      for {
        instance <- rules.specAll(compatibility, List(x, u, y, v))
        generalised <- rules.genAll(instance, List(x, y, u, v))
      } yield generalised
    )
  }

  it should "lift addition, and the lifted sum is the class of the sum" in {
    val (extended, fact) = force(parity.liftBinary("PARITY_ADD", addition, additionRespects))

    fact.hypotheses shouldBe empty
    extended.show(fact.conclusion) should include("PARITY_ADD")
    Derivation.axiomsOf(fact) should have size 3
  }

  it should "lift multiplication the same way" in {
    val (extended, fact) = force(parity.liftBinary("PARITY_MUL", multiplication, multiplicationRespects))

    fact.hypotheses shouldBe empty
    extended.show(fact.conclusion) should include("PARITY_MUL")
  }

  /**
   * Adding one, which on the classes is the parity flip.
   *
   * `NUM_ADD 1` is a partial application and therefore a term with no redex in it, which is the
   * reason this is the unary operation chosen: a lambda would exercise the builder's beta handling
   * as well, and that is a second question. The lambda case is the predicate below.
   */
  private lazy val successorRespects: Kernel.Thm = {
    val one = numeral("1:num")
    val x = Term.variable("x", numbers)
    val y = Term.variable("y", numbers)

    force(
      for {
        related <- parity.related(x, y)
        assumed <- LogicError.lift(Kernel.assume(related))
        reflexive <- modular.fact(Modular.CongRefl).flatMap(rules.specAll(_, List(two, one)))
        compatibility <- modular.fact(Modular.CongAdd).flatMap(rules.specAll(_, List(two, one, one, x, y)))
        once <- rules.mp(compatibility, reflexive)
        carried <- rules.mp(once, assumed)
        discharged <- rules.disch(related, carried)
        generalised <- rules.genAll(discharged, List(x, y))
      } yield generalised
    )
  }

  it should "lift adding one, which is the parity flip" in {
    val addOne = force(LogicError.lift(Term.app(addition, numeral("1:num"))))
    val (extended, fact) = force(parity.liftUnary("PARITY_FLIP", addOne, successorRespects))

    fact.hypotheses shouldBe empty
    extended.show(fact.conclusion) should include("PARITY_FLIP")
  }

  /**
   * Being even, as a predicate on the classes.
   *
   * Written as a lambda, so this is where the builder's normalisation is exercised: `p x` built by
   * hand is a redex and the same thing inside the respectfulness theorem below is reduced, and a
   * builder comparing the two without normalising would refuse a correct obligation over a
   * spelling.
   */
  private lazy val even: Term = {
    val m = Term.variable("m", numbers)
    val zero = numeral("0:num")
    force(
      for {
        applied <- parity.related(m, zero)
        lambda <- LogicError.lift(Term.abs(m, applied))
      } yield lambda
    )
  }

  /** `|- !x y. NUM_CONG 2 x y ==> (NUM_CONG 2 x 0 = NUM_CONG 2 y 0)`. */
  private lazy val evenRespects: Kernel.Thm = {
    val x = Term.variable("x", numbers)
    val y = Term.variable("y", numbers)
    val zero = numeral("0:num")

    force(
      for {
        related <- parity.related(x, y)
        assumed <- LogicError.lift(Kernel.assume(related))
        symmetric <- modular.fact(Modular.CongSym).flatMap(rules.specAll(_, List(two, x, y)))
        reversed <- rules.mp(symmetric, assumed)

        xEven <- parity.related(x, zero)
        yEven <- parity.related(y, zero)

        // `R x 0 |- R y 0`, by `R y x` and transitivity.
        assumedX <- LogicError.lift(Kernel.assume(xEven))
        throughX <- modular.fact(Modular.CongTrans).flatMap(rules.specAll(_, List(two, y, x, zero)))
        throughXOnce <- rules.mp(throughX, reversed)
        forward <- rules.mp(throughXOnce, assumedX)

        // `R y 0 |- R x 0`, by `R x y` and transitivity.
        assumedY <- LogicError.lift(Kernel.assume(yEven))
        throughY <- modular.fact(Modular.CongTrans).flatMap(rules.specAll(_, List(two, x, y, zero)))
        throughYOnce <- rules.mp(throughY, assumed)
        backward <- rules.mp(throughYOnce, assumedY)

        agreement = Kernel.deductAntisym(backward, forward)
        discharged <- rules.disch(related, agreement)
        generalised <- rules.genAll(discharged, List(x, y))
      } yield generalised
    )
  }

  it should "lift a predicate written as a lambda, normalising rather than refusing over a redex" in {
    val (extended, fact) = force(parity.liftPredicate("PARITY_EVEN", even, evenRespects))

    fact.hypotheses shouldBe empty
    extended.show(fact.conclusion) should include("PARITY_EVEN")
  }

  /* ------------------------------------------------------------------ what it refuses */

  /**
   * A true theorem about the wrong thing, handed to each lift in turn.
   *
   * The half that is easy to leave out. Without these three the shape checks inside the builder
   * could be deleted and every other assertion in this file would still pass, which is the test
   * `CLAUDE.md` asks for under "an assertion is only as good as the thought somebody gave to what
   * would make it empty": the input that makes the guard trivially true is a **correct** obligation,
   * and that is what the tests above supply.
   */
  it should "refuse a unary lift whose obligation is about something else" in {
    val addOne = force(LogicError.lift(Term.app(addition, numeral("1:num"))))
    val wrong = atTwo(Modular.CongRefl)

    val refusal = parity.liftUnary("PARITY_WRONG_UNARY", addOne, wrong)
    refusal.isLeft shouldBe true
    refusal.fold(_.message, _ => "") should include("respectfulness")
  }

  it should "refuse a binary lift given the uncurried or reordered obligation" in {
    // `Modular`'s own statement, at the modulus but with its binders in `Modular`'s order rather
    // than the builder's. True, about the same operation, and not the obligation.
    val refusal = parity.liftBinary("PARITY_WRONG_BINARY", addition, atTwo(Modular.CongAdd))
    refusal.isLeft shouldBe true
    refusal.fold(_.message, _ => "") should include("respectfulness")
  }

  it should "refuse a predicate lift given an implication where an equation is wanted" in {
    val x = Term.variable("x", numbers)
    val y = Term.variable("y", numbers)
    val zero = numeral("0:num")

    // `!x y. R x y ==> (R x 0 ==> R y 0)`: the implication in one direction, which is true and is
    // exactly the theorem that would let a predicate through that does not lift.
    val oneDirection = force(
      for {
        related <- parity.related(x, y)
        assumed <- LogicError.lift(Kernel.assume(related))
        symmetric <- modular.fact(Modular.CongSym).flatMap(rules.specAll(_, List(two, x, y)))
        reversed <- rules.mp(symmetric, assumed)
        xEven <- parity.related(x, zero)
        assumedX <- LogicError.lift(Kernel.assume(xEven))
        through <- modular.fact(Modular.CongTrans).flatMap(rules.specAll(_, List(two, y, x, zero)))
        once <- rules.mp(through, reversed)
        reached <- rules.mp(once, assumedX)
        inner <- rules.disch(xEven, reached)
        outer <- rules.disch(related, inner)
        generalised <- rules.genAll(outer, List(x, y))
      } yield generalised
    )

    val refusal = parity.liftPredicate("PARITY_WRONG_PREDICATE", even, oneDirection)
    refusal.isLeft shouldBe true
    refusal.fold(_.message, _ => "") should include("respectfulness")
  }

  /**
   * The two ways a caller arrives with something that is not an equivalence relation's shape.
   *
   * Refused at the carrier rather than several derivations later, which is the whole reason the
   * check is at the top of `define`: a relation of two different types produces a predicate whose
   * type is wrong, and the failure that would surface is a `Kernel.defineType` refusal naming a
   * term the caller never wrote.
   */
  it should "refuse a relation that is not two arguments of one type" in {
    val notARelation = force(
      LogicError.lift(modular.theory.constant(Modular.DividesName, relation))
    )
    // `NUM_DIVIDES` is two arguments of one type and **is** taken here, so the refusal has to be
    // shown on something that genuinely is not: `NUM_MOD : num -> num -> num` answers a number.
    val answersANumber = force(
      LogicError.lift(modular.theory.constant(Modular.ModName, Modular.binary))
    )

    val refusal = Quotient.define(
      classical,
      modular.theory,
      modular.notation,
      names.copy(typeName = "notaquotient", abstraction = "mk_notaquotient", representation = "dest_notaquotient", projection = "NOTAQUOTIENT"),
      equivalence.copy(relation = answersANumber)
    )

    refusal.isLeft shouldBe true
    refusal.fold(_.message, _ => "") should include("relation")
    notARelation should not be answersANumber
  }

  it should "refuse a relation that is not closed" in {
    val k = Term.variable("k", numbers)
    val congruenceConstant = force(
      LogicError.lift(modular.theory.constant(Modular.CongruenceName, ternary))
    )
    val atAVariable = force(LogicError.lift(Term.app(congruenceConstant, k)))

    val refusal = Quotient.define(
      classical,
      modular.theory,
      modular.notation,
      names.copy(typeName = "openquotient", abstraction = "mk_openquotient", representation = "dest_openquotient", projection = "OPENQUOTIENT"),
      equivalence.copy(relation = atAVariable)
    )

    refusal.isLeft shouldBe true
    refusal.fold(_.message, _ => "") should include("closed")
  }

}
