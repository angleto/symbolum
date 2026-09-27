package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The product type, and the four questions that decide whether it was worth defining.
 *
 * **The first is whether it cost anything.** `Kernel.defineType` is the part of the kernel with the
 * least mileage on it and `docs/adr/0006` says what it promises: the axiom count does not move. That
 * is asserted against the theory this one was built over rather than against a number written here,
 * because a number written here would have to be edited when the base moves for an unrelated reason,
 * and editing it is the moment the assertion exists to interrupt.
 *
 * **The second is whether it says what it means to say.** Each derived fact is compared with the
 * text `Product.Statements` holds, and compared as a **term**: a type variable is written
 * `'a` and printed `a`, so a printed polymorphic statement does not read back, and parsing the text
 * and comparing the parse is the stronger check of the two anyway.
 *
 * **The third is what each fact rests on.** Walked rather than read off the imports. The two
 * projections are defined by choice and reach `SELECT`; the case split, the injectivity and the
 * bridge to the representation reach nothing at all, which is the measurement that says the type
 * itself is free and only the naming of components is paid for. `ETA` is reached by nothing here.
 *
 * **The fourth is whether it can be used**, and the use at the end is the one the gap audit asked
 * for: a pair of naturals, stated in one signature, which is the thing its item A10 says could not
 * be written down. It is built over the chain rather than over the bare classical logic, because
 * two developments beside each other cannot read each other's theorems.
 */
class ProductSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val classical = Classical.standard
  private val product = Product.standard
  private val rules = product.logic.rules

  private def fact(name: String): Kernel.Thm = force(product.fact(name))

  private val Names: Vector[String] = Product.Statements.map(_._1)

  private val Derived: Vector[String] =
    Vector(Product.AbstractionOfRepresentation, Product.Characterisation) ++ Names

  /* ------------------------------------------------------ what the type definition cost */

  "The type and its constants" should "be defined rather than assumed" in {
    product.theory.axioms shouldBe classical.theory.axioms

    (product.theory.typeOperators.keySet -- classical.theory.typeOperators.keySet) shouldBe
      Set(Product.TypeName)
    (product.theory.constants.keySet -- classical.theory.constants.keySet) shouldBe Set(
      Product.PairFunction,
      Product.Abstraction,
      Product.RepresentationFunction,
      Product.Pairing,
      Product.First,
      Product.Second
    )

    // `mk_prod` and `dest_prod` are the type definition's, and it does not record a defining
    // equation for either: what they are is the pair of theorems below, not a body.
    product.theory.definitions.keySet should contain allOf (
      Product.PairFunction, Product.Pairing, Product.First, Product.Second
    )
    product.theory.definitions.keySet should not contain Product.Abstraction
    product.theory.definitions.keySet should not contain Product.RepresentationFunction
  }

  it should "give `prod` the arity the predicate's type variables decide, in their sorted order" in {
    // `docs/adr/0006` calls this the sharper edge the rule has over `declareTypeOperator`: the
    // arity is the count of the predicate's type variables and a caller cannot choose it. Pinned
    // here because the order is what decides whether `prod('a,'b)` is the pairs of `'a` and `'b` or
    // the other way round, and nothing in the signature of the rule says which.
    product.theory.typeOperators(Product.TypeName) shouldBe 2

    val schema = Type.fun(Product.Domain, Type.fun(Product.Codomain, Product.Pairs))
    val pairing = force(LogicError.lift(product.theory.constant(Product.Pairing, schema)))
    Term.typeOf(pairing) shouldBe schema
  }

  it should "carry no free variable of the witness into either theorem it returned" in {
    // The claim `docs/adr/0006` makes about the witness, measured. The witness proved here is
    // `P (mk_pair x y)` over two free variables, which the rule does not refuse and does not need
    // to: it is used to show the predicate's extension is not empty and for nothing else, so there
    // is nowhere for `x` and `y` to go. If either appeared, the type would be the pairs of one
    // particular pair of values.
    Derived.foreach { name =>
      withClue(s"$name: ")(Term.freeVariables(fact(name).conclusion).map(_.name) should
        contain noneOf ("x", "y"))
    }
  }

  it should "carry every fact without a hypothesis left standing" in {
    // Not a formality. `Rules.mp` leaves an antecedent that does not match standing as a hypothesis
    // rather than reporting it, so a derivation that specialised in the wrong order comes back as a
    // true sequent with an extra premise instead of as an error.
    Derived.foreach(name => withClue(s"$name: ")(fact(name).hypotheses shouldBe empty))
  }

  /* ------------------------------------------------------------------ the statements */

  "Every derived fact" should "read as the text this development is checked by" in {
    Product.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe force(product.proposition(text))
      }
    }
  }

  it should "hold the two halves of the bijection as the rule returned them" in {
    // Over the free variables `Kernel.defineType` names them with, which is why a use site
    // instantiates rather than specialises. Printed rather than parsed: neither is quantified, and
    // the second carries the predicate as a literal lambda, which is the honest reading of a type
    // defined without giving its predicate a name.
    product.show(fact(Product.AbstractionOfRepresentation).conclusion) shouldBe
      "mk_prod (dest_prod a) = a"
    product.show(fact(Product.Characterisation).conclusion) shouldBe
      "(\\f:'a -> 'b -> bool. ?x:'a. ?y:'b. f = mk_pair x y) r = (dest_prod (mk_prod r) = r)"
  }

  it should "name every fact the way the convention names one" in {
    // `LibrarySpec` checks this for the names in `docs/lemmas.md`, which has held this
    // development's since it joined the chain on 2026-09-12. Kept because this spec builds its own
    // `Product` over its own theory: what is checked there is the chain's copy.
    val shape = "[A-Z][A-Z0-9]*(_[A-Z0-9]+)*".r

    Derived.foreach(name => withClue(s"$name: ")(shape.matches(name) shouldBe true))

    // One spelling per concept, which is the rule with teeth: the corpus spells injectivity
    // `INJECTIVE` in `NUM_SUC_INJECTIVE`, so this development does not add `PAIR_EQ` beside it.
    Derived.filter(_.contains("_EQ")) shouldBe empty
  }

  /* ------------------------------------------------------------- what each fact rests on */

  "The type itself" should "cost no axiom at all" in {
    // The measurement `docs/adr/0006` predicts and the reason the rule is in the kernel: every
    // alternative reaches these two theorems by asserting them.
    Vector(
      Product.AbstractionOfRepresentation,
      Product.Characterisation,
      Product.RepresentationOfPair,
      Product.PairInjective,
      Product.Cases
    ).foreach(name => withClue(s"$name: ")(Real.spent(fact(name)) shouldBe empty))
  }

  "The two projections" should "rest on the choice axiom and on nothing else" in {
    // They are `select` of a predicate, which is the only route this logic has to a term denoting a
    // component: `PROD_CASES` says the components exist and names neither. So the split above and
    // below is not an accident of the derivations, it is what defining a projection costs.
    val choice = force(classical.axiom(Classical.Choice)).conclusion

    Vector(Product.FirstOfPair, Product.SecondOfPair, Product.Surjective).foreach { name =>
      withClue(s"$name: ")(Real.spent(fact(name)) shouldBe Set(choice))
    }
  }

  it should "reach eta nowhere, which is what says no extensionality was used" in {
    val eta = force(classical.axiom(Classical.Eta)).conclusion

    Derived.foreach(name => withClue(s"$name: ")(Real.spent(fact(name)) should not contain eta)
    )
  }

  "The cost of each fact" should "be the number of inferences measured, within an order" in {
    // Counted rather than timed, this machine's wall clock being worthless. The figures on
    // 2026-09-11 are 301 for each half of the bijection, 616 for the bridge, 736 for the case
    // split, 781 for injectivity, 1054 for each projection and 1832 for surjective pairing. They
    // are asserted as a band rather than exactly, because every one of them counts the shared
    // derivations of `Rules` underneath it: a cheaper `existsIntro` would move all eight and none
    // of those movements is about this file. What the band catches is the thing that would matter,
    // which is a derivation that started doing something quadratic.
    Derived.foreach { name =>
      withClue(s"$name: ") {
        Derivation.size(fact(name)) should be > 100
        Derivation.size(fact(name)) should be < 6000
      }
    }

    // And the ordering, which is about this file: surjective pairing is built from both
    // projections and the case split, so it cannot be the cheapest of the three.
    Derivation.size(fact(Product.Surjective)) should be >
      Derivation.size(fact(Product.FirstOfPair))
    Derivation.size(fact(Product.Cases)) should be <
      Derivation.size(fact(Product.FirstOfPair))
  }

  /* --------------------------------------------------------- what this development is not */

  "The comma" should "not be notation here, so `PAIR x y` is how a pair is written" in {
    // The absence read off the code rather than off a comment. `,` is the structural separator
    // inside a type application, and giving it a second meaning in terms changes the reader of
    // every existing statement rather than this file; nothing yet asks for it.
    product.notation.symbols should contain(",")
    Notation.Structural should contain(",")
    product.theory.constants.keySet should not contain ","
  }

  it should "hold no currying combinator, which is the step after this one" in {
    product.theory.constants.keySet should contain noneOf ("CURRY", "UNCURRY")
  }

  /* ---------------------------------------------------------------------- using it */

  "A pair" should "have the components it was built from, end to end" in {
    val x = Term.variable("x", Product.Domain)
    val y = Term.variable("y", Product.Codomain)

    product.show(force(rules.specAll(fact(Product.FirstOfPair), List(x, y))).conclusion) shouldBe
      "FST (PAIR x y) = x"
    product.show(force(rules.specAll(fact(Product.SecondOfPair), List(x, y))).conclusion) shouldBe
      "SND (PAIR x y) = y"
  }

  it should "nest, which is what says the type variables really are instantiated" in {
    // `prod('a,'b)` put in the first component of another pair. A type definition whose arity or
    // whose argument order were wrong would still give the two projection laws and would fail here.
    val nested = Kernel.instType(Map(Classical.TypeVariable -> Product.Pairs), fact(Product.FirstOfPair))
    val p = Term.variable("p", Product.Pairs)
    val y = Term.variable("y", Product.Codomain)

    product.show(force(rules.specAll(nested, List(p, y))).conclusion) shouldBe
      "FST (PAIR p y) = p"
    Term.typeOf(p) shouldBe TyApp(Product.TypeName, List(Product.Domain, Product.Codomain))
  }

  "A pair of naturals" should "be statable, which is the gap this development was asked for" in {
    // The audit's item A10 says index types and finite words are unstatable because there is no
    // product. This is the smallest execution of the claim that they now are: `prod(num, num)` in
    // the chain's own signature, with the projection law holding at that instance.
    val chain = Chain.standard
    // The chain's own pair, which is built below the reals over the naturals' arithmetic since
    // phase 5 of `docs/adr/0007`; building a second one over `chain.peano.theory` is refused, since
    // that theory holds this one.
    val naturals = chain.product

    naturals.theory.axioms shouldBe chain.peano.theory.axioms

    val numbers = TyApp(Natural.TypeName, Nil)
    val law = Kernel.instType(
      Map(Classical.TypeVariable -> numbers, Classical.CodomainVariable -> numbers),
      force(naturals.fact(Product.FirstOfPair))
    )
    val zero = force(LogicError.lift(naturals.theory.constant(Natural.NumberZero, numbers)))
    val one = force(naturals.term("SUC 0"))

    naturals.show(force(naturals.logic.rules.specAll(law, List(zero, one))).conclusion) shouldBe
      "FST (PAIR 0 (SUC 0)) = 0"

    // And the statement the audit wanted: a claim quantified over pairs of naturals, which the
    // chain could not write down at all before this.
    val statement = force(
      naturals.proposition("!p:prod(num,num). p = PAIR (FST p) (SND p)")
    )
    val surjective = Kernel.instType(
      Map(Classical.TypeVariable -> numbers, Classical.CodomainVariable -> numbers),
      force(naturals.fact(Product.Surjective))
    )
    surjective.conclusion shouldBe statement
  }
}
