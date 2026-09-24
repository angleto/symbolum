package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The fold over a list, and the three questions that decide whether it is worth anything.
 *
 * **What it cost.** One defined constant and no axiom, asserted as a difference against the theory
 * this link extends rather than against a number, which is `ListingSpec`'s argument and the same
 * one. And no type, for the same reason: `docs/adr/0038` decides that a list here is an orientation
 * on `word`, and a consumer that quietly carved one would show up here and nowhere else.
 *
 * **Whether the fold computes.** This is the one that could go vacuous. `LIST_FOLD` is defined
 * through `select`, so what its two equations pin down is exactly what they pin down and nothing
 * else: a development in which the constant answered the same thing at every list would satisfy
 * both of them at a start value that happened to be that thing, and every statement in
 * `Folding.Statements` would still read true. The test below runs the fold on a one-letter list and
 * reaches a number, then refuses the other number, so what is checked is a value rather than an
 * equation between two terms nobody evaluated.
 *
 * **Whether the split carries what the word-indexed one carries.** `Folding`'s docstring claims
 * that `LIST_FOLD_CONCAT` has no index correction in it where `Concatenation.Tally` does, and a
 * claim of that shape in prose is a claim nothing watches. The last test is that claim as a
 * measurement over the two statements: the one names `WORD_LENGTH` and `NUM_ADD` and the other
 * names neither.
 */
class FoldingSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val folding = Folding.standard
  private val logic = folding.logic
  private val rules = logic.rules

  private def fact(name: String): Kernel.Thm = force(folding.fact(name))

  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  /** The whole development at `num` for both type variables, which is what a concrete test needs. */
  private def atNumbers(theorem: Kernel.Thm): Kernel.Thm =
    Kernel.instType(
      Map(Classical.TypeVariable -> numbers, Classical.CodomainVariable -> numbers),
      theorem
    )

  private def term(text: String): Term =
    force(Parser.term(folding.theory, folding.notation, text))

  private def proposition(text: String): Term =
    force(Parser.proposition(folding.theory, folding.notation, text))

  /* --------------------------------------------------------------- what it cost */

  "The fold" should "be defined rather than assumed, and add no type" in {
    val below = Chain.standard.listing.theory

    folding.theory.axioms shouldBe below.axioms
    (folding.theory.constants.keySet -- below.constants.keySet) shouldBe Set(Folding.Fold)
    folding.theory.typeOperators.keySet shouldBe below.typeOperators.keySet
  }

  it should "cost the naturals' two axioms and no more" in {
    // An equality rather than a ceiling, which is `CodingSpec`'s discipline and `ListingSpec`'s: a
    // fact that quietly started spending a third axiom would pass a subset check. Choice is spent
    // twice over here, once inside `LIST_RECURSION` and once where the existence theorem becomes a
    // name, and twice is not a third axiom.
    val spent = Folding.Statements.flatMap { case (name, _) =>
      folding.facts.get(name).toVector.flatMap(theorem => Derivation.axiomsOf(theorem).toVector)
    }.toSet

    val naturals =
      (Chain.standard.naturals.axioms.values ++ Chain.standard.classical.axioms.values)
        .map(_.conclusion)
        .toSet
    withClue(s"what these facts rest on: ${spent.map(folding.show).mkString("; ")}\n") {
      (spent -- naturals) shouldBe empty
    }
  }

  it should "spend exactly choice, infinity and eta, measured as an equality" in {
    // Written by the verification of cards 5d59c308 and 708faa52 on 2026-09-24. The test above is
    // a ceiling: `(spent -- naturals) shouldBe empty` passes when `spent` is empty, and `naturals`
    // there holds both of the classical theory's axioms beside infinity, so it admits three. The
    // delivery said two, choice and infinity, "as an equality"; measured, the union is THREE, eta
    // being the third. This pins what was measured, so a derivation that starts or stops spending
    // any of them goes red, and the informer line names which of the three each fact reaches.
    val choice = Chain.standard.classical.axioms(Classical.Choice).conclusion
    val eta = Chain.standard.classical.axioms(Classical.Eta).conclusion
    val infinity = Chain.standard.naturals.axioms(Natural.Infinity).conclusion
    val named = Map(choice -> "SELECT", eta -> "ETA", infinity -> "INFINITY")
    val perFact = Folding.Statements.map { case (name, _) =>
      name -> folding.facts.get(name).toVector.flatMap(t => Derivation.axiomsOf(t).toVector).toSet
    }
    val report = perFact
      .map { case (name, axioms) =>
        val names = axioms.toVector.map(a => named.getOrElse(a, folding.show(a))).sorted
        s"$name: " + names.mkString(", ")
      }
      .mkString("; ")
    info(report)
    withClue(s"per fact: $report\n") {
      perFact.flatMap(_._2).toSet shouldBe Set(choice, infinity, eta)
    }
  }

  /* ------------------------------------------------------------- what it says */

  it should "prove every statement it publishes, owing nothing" in {
    Folding.Statements.foreach { case (name, text) =>
      val proved = fact(name)
      withClue(s"$name: ") {
        proved.hypotheses shouldBe empty
        proved.conclusion shouldBe proposition(text)
      }
    }
  }

  it should "publish a fact for every name in its statement list" in {
    Folding.Statements.map(_._1).toSet shouldBe folding.facts.keySet
  }

  /* ------------------------------ whether it is the recursion theorem that built it */

  it should "be built by the recursion theorem, which is the whole reason it is here" in {
    // The claim this development is FOR, as a measurement over the derivations rather than as a
    // sentence in a docstring. `LIST_FOLD` could have been introduced by any route that produced a
    // constant satisfying two equations -- an asserted axiom would satisfy every other test in this
    // file -- and what says it was not is that `LIST_RECURSION` is inside what its equations rest
    // on. If somebody replaced the construction with something that did not spend it, this goes red
    // and nothing else here would.
    val listing = Chain.standard.listing
    val recursion = force(listing.fact(Listing.RecursionTheorem)).conclusion

    withClue("the fold's own two equations do not spend `LIST_RECURSION`: ") {
      Derivation.restingOn(fact(Folding.FoldOfEmpty), Set(recursion)) shouldBe Set(recursion)
      Derivation.restingOn(fact(Folding.FoldOfCons), Set(recursion)) shouldBe Set(recursion)
    }

    // And the split spends the induction on top of it, which is the other half of what `Listing`
    // publishes and a different principle: the recursion supplies the constant and the induction is
    // what proves anything about every list it is applied to. Asserted separately so that a proof
    // that quietly stopped needing one of the two is visible.
    val induct = force(listing.fact(Listing.Induct)).conclusion
    withClue("the split over a concatenation does not spend both principles: ") {
      Derivation.restingOn(fact(Folding.FoldOfConcat), Set(recursion, induct)) shouldBe
        Set(recursion, induct)
    }

    // The control, without which the three assertions above are worth nothing: an instrument that
    // handed its own argument back would pass all of them. Associativity is inside the split's step
    // -- it is what turns `WORD_CONCAT (LIST_CONS x u) v` into `LIST_CONS x (WORD_CONCAT u v)` --
    // and it is nowhere near the fold's own two equations, so the same call has to answer both
    // ways on the same pair of derivations.
    val associative = force(
      Chain.standard.concatenation.fact(Concatenation.Associative)
    ).conclusion
    Derivation.restingOn(fact(Folding.FoldOfConcat), Set(associative)) shouldBe Set(associative)
    Derivation.restingOn(fact(Folding.FoldOfEmpty), Set(associative)) shouldBe empty
  }

  /* ------------------------------------------------------ whether it computes */

  it should "reach a number on a one-letter list, and not the other number" in {
    // The guard against the whole file being vacuous, and it has to be a VALUE. `LIST_FOLD` is
    // `select` applied to a predicate, so nothing about the constant is available except what its
    // two equations say; a fold answering `ZERO` everywhere satisfies both of them at
    // `a := ZERO` and would pass every test above this one.
    val plus = force(
      LogicError.lift(
        folding.theory.constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
    )
    val zero = term("ZERO:num")
    val one = term("SUC ZERO")
    val emptyWord = term("WORD_EMPTY:word(num)")

    val atCons = force(
      rules.specAll(atNumbers(fact(Folding.FoldOfCons)), List(plus, zero, one, emptyWord))
    )
    val atEmpty = force(rules.specAll(atNumbers(fact(Folding.FoldOfEmpty)), List(plus, zero)))
    val partial = force(LogicError.lift(Term.app(plus, one)))
    val inner = force(Conv.apTerm(partial, atEmpty))
    val collapsed = force(rules.spec(one, force(Chain.standard.peano.fact(Peano.AddAtZero))))

    val value = force(Conv.trans(atCons, inner).flatMap(Conv.trans(_, collapsed)))
    value.hypotheses shouldBe empty
    value.conclusion shouldBe proposition(
      "LIST_FOLD NUM_ADD ZERO (LIST_CONS (SUC ZERO) (WORD_EMPTY:word(num))) = SUC ZERO"
    )

    // And it is not the other number, which is what says the equations pin something down rather
    // than being satisfiable by a constant function.
    val notZero = force(
      rules.spec(zero, force(Chain.standard.naturals.fact(Natural.SuccessorNotZero)))
    )
    val folded = Term
      .destEq(value.conclusion)
      .map(_._1)
      .getOrElse(fail(s"the value is not an equation: ${value.conclusion}"))
    val claim = force(LogicError.lift(Term.eq(folded, zero)))
    val supposed = force(LogicError.lift(Kernel.assume(claim)))
    val absurd = force(
      Conv
        .sym(value)
        .flatMap(Conv.trans(_, supposed))
        .flatMap(rules.notElim(notZero, _))
    )
    val refused = force(rules.notIntro(claim, absurd))
    refused.hypotheses shouldBe empty
    refused.conclusion shouldBe proposition(
      "~(LIST_FOLD NUM_ADD ZERO (LIST_CONS (SUC ZERO) (WORD_EMPTY:word(num))) = ZERO)"
    )
  }

  /* ------------------------------------- whether the split carries a correction */

  "The split over a concatenation" should "carry no index correction, where the tally's does" in {
    // `Folding`'s own docstring rests on this and a docstring is watched by nothing. The tally
    // splits a sum over positions, so the right half's letters have to be re-read `WORD_LENGTH u`
    // further along and the statement says `NUM_ADD (WORD_LENGTH u) i`; the fold's split has no
    // index in it at all, so neither name can occur. What is compared is the two statements, by
    // the constants they name.
    def named(theorem: Kernel.Thm): Set[String] = {
      def walk(term: Term): Set[String] = term match {
        case Const(name, _) => Set(name)
        case App(operator, argument) => walk(operator) ++ walk(argument)
        case Abs(_, body) => walk(body)
        case _ => Set.empty
      }
      walk(theorem.conclusion)
    }

    val tally = named(force(Chain.standard.concatenation.fact(Concatenation.Tally)))
    val split = named(fact(Folding.FoldOfConcat))

    withClue("the tally is supposed to need both, and is the control for this measurement: ") {
      tally should contain(Peano.Addition)
      tally should contain(Word.Length)
    }
    withClue(s"the fold's split names: ${split.toVector.sorted.mkString(", ")}\n") {
      split should not contain Peano.Addition
      split should not contain Word.Length
    }

    // And both really are about a concatenation, so the comparison is between two answers to one
    // question rather than between two different questions.
    tally should contain(Concatenation.Name)
    split should contain(Concatenation.Name)
  }
}
