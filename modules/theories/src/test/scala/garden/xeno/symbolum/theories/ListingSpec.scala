package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The list interface over `word`, and the four questions that decide whether it is worth anything.
 *
 * **What it cost.** Three defined constants and no axiom, asserted as a difference against the
 * theory this link extends rather than against a number, which is `ConcatenationSpec`'s argument
 * and the same one. **And no type**: `docs/adr/0038` is the decision, so the assertion that the
 * type operators do not move is the one carrying it and not decoration.
 *
 * **What it says.** Each fact is compared against the text `Listing.Statements` holds, as a
 * **term**: a type variable is written `'a` and printed `a`, so a printed polymorphic statement
 * does not read back and parsing the text is the stronger check anyway.
 *
 * **Whether the two constructors are really two.** A development in which `LIST_CONS x w` could be
 * `WORD_EMPTY` would satisfy every equation below and would be useless, and so would one in which
 * two conses could be equal without their arguments being. Both are derived at a concrete pair
 * rather than left to the general statement, because a general statement about an empty case is
 * true.
 *
 * **Whether the induction can be SPENT.** This is the one that could go vacuous without anything
 * noticing: an induction principle is an implication, and a file that only ever asserts the
 * implication exists has not shown that its premises can be discharged. The last test discharges
 * both and reaches a conclusion, and the conclusion is a theorem this repository already holds by
 * another route -- `WORD_CONCAT_EMPTY_RIGHT` -- so what comes out is compared against it rather
 * than merely inspected. Re-deriving a known fact is the point: the subject of the test is the
 * principle, and the strongest available check on what the principle produced is a theorem proved
 * without it.
 */
class ListingSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val listing = Listing.standard
  private val logic = listing.logic
  private val rules = logic.rules

  private def fact(name: String): Kernel.Thm = force(listing.fact(name))

  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val element: Type = TyVar(Classical.TypeVariable)
  private val words: Type = TyApp(Word.TypeName, List(element))
  private val numberWords: Type = TyApp(Word.TypeName, List(numbers))

  /** The whole development at `num` as the element type, which is what a concrete test needs. */
  private def overNumbers(theorem: Kernel.Thm): Kernel.Thm =
    Kernel.instType(Map(Classical.TypeVariable -> numbers), theorem)

  private def term(text: String): Term =
    force(Parser.term(listing.theory, listing.notation, text))

  private def proposition(text: String): Term =
    force(Parser.proposition(listing.theory, listing.notation, text))

  /* --------------------------------------------------------------- what it cost */

  "The list interface" should "be defined rather than assumed, and add no type" in {
    // Against the theory it EXTENDS, which is `Inclusion`'s and not `Concatenation`'s. This
    // development needs the concatenation and sits on top of the chain's end, and the two are
    // different questions: a difference taken against `concatenation.theory` would come back
    // holding every constant of the five links between them and say nothing about what this added.
    val below = Chain.standard.inclusion.theory

    listing.theory.axioms shouldBe below.axioms
    (listing.theory.constants.keySet -- below.constants.keySet) shouldBe Set(
      Listing.Cons,
      Listing.Head,
      Listing.Tail
    )

    // The claim `docs/adr/0038` rests on, and the reason this line is here rather than in prose: a
    // list that carved a carrier would show up as a sixth type operator, and nothing else in this
    // file would notice.
    listing.theory.typeOperators.keySet shouldBe below.typeOperators.keySet

    Listing.Definitions.foreach { case (name, _) =>
      listing.theory.definitions.keySet should contain(name)
    }
  }

  it should "spend exactly choice, infinity and eta, measured as an equality" in {
    // Written by the verification of cards 5d59c308 and 708faa52 on 2026-09-24, and it replaced a
    // test titled "cost the naturals' two axioms and no more", which card 9084078b removed. That
    // one was a ceiling though its comment called it an equality: `(spent -- naturals) shouldBe
    // empty` passes when `spent` is empty, and `naturals` held both of the classical theory's
    // axioms beside infinity, so it admitted three. The delivery said two; measured, the union is
    // THREE, eta being the third. This pins what was measured, so a derivation that starts or
    // stops spending any of them goes red, and the informer line names which each fact reaches.
    val choice = Chain.standard.classical.axioms(Classical.Choice).conclusion
    val eta = Chain.standard.classical.axioms(Classical.Eta).conclusion
    val infinity = Chain.standard.naturals.axioms(Natural.Infinity).conclusion
    val named = Map(choice -> "SELECT", eta -> "ETA", infinity -> "INFINITY")
    val perFact = Listing.Statements.map { case (name, _) =>
      name -> listing.facts.get(name).toVector.flatMap(t => Derivation.axiomsOf(t).toVector).toSet
    }
    val report = perFact
      .map { case (name, axioms) =>
        val names = axioms.toVector.map(a => named.getOrElse(a, listing.show(a))).sorted
        s"$name: " + names.mkString(", ")
      }
      .mkString("; ")
    info(report)
    withClue(s"per fact: $report\n") {
      perFact.flatMap(_._2).toSet shouldBe Set(choice, infinity, eta)
    }
  }

  it should "spend eta exactly where it rests on the extensionality of words, and nowhere else" in {
    // Where the third axiom comes in, measured rather than read off the derivation. It is
    // `WORD_EXTENSIONALITY`, two words of one length agreeing below it being one word, which
    // `LIST_TAIL_CONS` closes on and every fact after it inherits; the four facts before it do not
    // reach it and do not spend eta. The equivalence per fact is what makes a fact that reached eta
    // by another road go red naming itself, and the two counts at the end say it is not vacuous in
    // either direction.
    //
    // **What it does not see**: `LIST_RECURSION_UNIQUE` pays for eta a second time, through
    // `Classical.ext` taken in this development's logic, which is a rule and not the published
    // `FUNCTION_EXTENSIONALITY`, so `restingOn` cannot find it. Card 9084078b's first version of
    // this test looked for that fact and found it under no list fact. The uniqueness rests on
    // `LIST_INDUCT` as well, so the equivalence holds for it and says nothing about the second
    // road; nothing here would notice that road closing.
    val eta = Chain.standard.classical.axioms(Classical.Eta).conclusion
    val ofWords = force(listing.concatenation.word.fact(Word.Extensionality))
    Derivation.axiomsOf(ofWords) should contain(eta)

    val readings = Listing.Statements.map { case (name, _) =>
      val theorem = fact(name)
      val through = Derivation.restingOn(theorem, Set(ofWords.conclusion)).nonEmpty
      (name, Derivation.axiomsOf(theorem).contains(eta), through)
    }
    info(readings.collect { case (name, _, true) => name }.mkString("through it: ", ", ", ""))

    readings.foreach { case (name, spendsEta, through) =>
      withClue(s"$name: ") { spendsEta shouldBe through }
    }
    readings.count(_._2) should be > 0
    readings.count(!_._2) should be > 0
  }

  /* ------------------------------------------------------------- what it says */

  it should "prove every statement it publishes, owing nothing" in {
    Listing.Statements.foreach { case (name, text) =>
      val proved = fact(name)
      withClue(s"$name: ") {
        proved.hypotheses shouldBe empty
        proved.conclusion shouldBe proposition(text)
      }
    }
  }

  it should "publish a fact for every name in its statement list" in {
    // The half that goes empty if the list and the map drift apart: a statement nobody derived
    // would be skipped by `construct`'s own check, which passes over a name it has no fact for so
    // that the surface can be written down before it is built out. This is what says the building
    // out finished.
    Listing.Statements.map(_._1).toSet shouldBe listing.facts.keySet
  }

  /* --------------------------------- whether the two constructors are really two */

  "A cons" should "be refused as the empty word at a concrete pair" in {
    // `LIST_CONS_NOT_EMPTY` is general, so it is true of an empty domain. This detaches it.
    val claim = proposition("~(LIST_CONS (ZERO:num) WORD_EMPTY = WORD_EMPTY)")
    val refused = force(
      rules.specAll(
        overNumbers(fact(Listing.ConsNotEmpty)),
        List(term("ZERO:num"), term("WORD_EMPTY:word(num)"))
      )
    )

    refused.hypotheses shouldBe empty
    refused.conclusion shouldBe claim
  }

  it should "give its two arguments back, at a concrete pair" in {
    val subject = term("LIST_CONS (ZERO:num) WORD_EMPTY")

    val head = force(
      rules.specAll(
        overNumbers(fact(Listing.HeadOfCons)),
        List(term("ZERO:num"), term("WORD_EMPTY:word(num)"))
      )
    )
    head.hypotheses shouldBe empty
    head.conclusion shouldBe proposition("LIST_HEAD (LIST_CONS (ZERO:num) WORD_EMPTY) = ZERO")

    val tail = force(
      rules.specAll(
        overNumbers(fact(Listing.TailOfCons)),
        List(term("ZERO:num"), term("WORD_EMPTY:word(num)"))
      )
    )
    tail.hypotheses shouldBe empty
    tail.conclusion shouldBe
      proposition("LIST_TAIL (LIST_CONS (ZERO:num) WORD_EMPTY) = WORD_EMPTY")
  }

  "The cases" should "be exhaustive and, at the empty word, decided by the left one" in {
    // A disjunction is not a decision. This spends `LIST_CONS_NOT_EMPTY` against the right disjunct
    // at the empty word, which is what makes the split a split rather than two overlapping cases.
    val atEmpty = force(
      rules.spec(term("WORD_EMPTY:word(num)"), overNumbers(fact(Listing.Cases)))
    )
    atEmpty.hypotheses shouldBe empty

    val halves = logic
      .destDisj(atEmpty.conclusion)
      .getOrElse(fail(s"the cases are not a disjunction: ${atEmpty.conclusion}"))
    halves._1 shouldBe proposition("(WORD_EMPTY:word(num)) = WORD_EMPTY")
  }

  /* ------------------------------ whether the induction can be spent */

  "The cons induction" should "reach a conclusion this repository proves another way" in {
    // The guard against the whole file being vacuous. `LIST_INDUCT` is an implication, and nothing
    // above discharges its premises: a development whose induction principle could never be used
    // would pass every test before this one.
    //
    // The claim is `!w. WORD_CONCAT w WORD_EMPTY = w`, which is `Concatenation.EmptyRight` and is
    // already a theorem by a different route. That is deliberate and is the strongest check
    // available here: what the principle produces is compared against a theorem proved without it,
    // rather than read and approved.
    //
    // The step is where the induction is really spent. `WORD_CONCAT (LIST_CONS x w) WORD_EMPTY` is
    // `WORD_CONCAT (WORD_CONCAT (WORD_SINGLETON x) w) WORD_EMPTY`, which associativity moves to
    // `WORD_CONCAT (WORD_SINGLETON x) (WORD_CONCAT w WORD_EMPTY)`, and **there** the hypothesis
    // rewrites the inner concatenation to `w`. Without the hypothesis the step does not close.
    val concatenation = Chain.standard.concatenation
    val emptyRight = force(concatenation.fact(Concatenation.EmptyRight))
    val emptyLeft = force(concatenation.fact(Concatenation.EmptyLeft))
    val associative = force(concatenation.fact(Concatenation.Associative))

    val w = Term.variable("w", words)
    val emptyWord = term("WORD_EMPTY:word('a)")
    val concat = force(
      LogicError.lift(listing.theory.constant(Concatenation.Name, Type.fun(words, Type.fun(words, words))))
    )

    // `\w. WORD_CONCAT w WORD_EMPTY = w`
    val applied = force(LogicError.lift(Term.appAll(concat, List(w, emptyWord))))
    val body = force(LogicError.lift(Term.eq(applied, w)))
    val predicate = force(LogicError.lift(Term.abs(w, body)))

    val instance = force(rules.spec(predicate, fact(Listing.Induct)))
    val opened = force(
      Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
    )
    val premises = logic
      .destImp(opened.conclusion)
      .getOrElse(fail(s"the induction is not an implication: ${opened.conclusion}"))
    val pair = logic
      .destConj(premises._1)
      .getOrElse(fail(s"its premise is not a conjunction: ${premises._1}"))

    // The base: `WORD_CONCAT WORD_EMPTY WORD_EMPTY = WORD_EMPTY`, which is the left unit at the
    // empty word and not a second argument about it.
    val base = force(rules.spec(emptyWord, emptyLeft))
    base.conclusion shouldBe pair._1

    // The step, as the induction states it. **Its two variables are read off it and not chosen
    // here**, which is what the first attempt at this test got wrong: specialising the principle at
    // a predicate whose own body binds `w` renames the step's word variable away from it, so a step
    // rebuilt with the name written here is a proof about a different word and `Conv.trans` refuses
    // it two lines later. The refusal named both terms, which is how it was found.
    val stepStripped = force(Logic.stripForall(pair._2))
    val letterVariable = stepStripped._1.headOption
      .getOrElse(fail(s"the step binds no letter: ${pair._2}"))
    val wordVariable = stepStripped._1.drop(1).headOption
      .getOrElse(fail(s"the step binds no word: ${pair._2}"))
    val stepParts = logic
      .destImp(stepStripped._2)
      .getOrElse(fail(s"the step is not an implication: ${stepStripped._2}"))
    val hypothesis = force(LogicError.lift(Kernel.assume(stepParts._1)))

    val singleton = force(
      LogicError.lift(listing.theory.constant(Concatenation.Singleton, Type.fun(element, words)))
    )
    val letter = force(LogicError.lift(Term.app(singleton, letterVariable)))

    // `WORD_CONCAT (LIST_CONS x w) WORD_EMPTY` is `WORD_CONCAT (WORD_CONCAT (WORD_SINGLETON x) w)
    // WORD_EMPTY`; associativity moves the empty word inside, and **there** the hypothesis rewrites
    // it away. Without the hypothesis the step does not close, which is what makes this a use of
    // the induction rather than a demonstration beside it.
    val consOpened = force(
      Conv.unfold(force(listing.definition(Listing.Cons)), List(letterVariable, wordVariable))
    )
    val carried = force(Conv.apTerm(concat, consOpened).flatMap(Conv.apThm(_, emptyWord)))
    val moved = force(rules.specAll(associative, List(letter, wordVariable, emptyWord)))
    val inner = force(
      Conv.apTerm(force(LogicError.lift(Term.app(concat, letter))), hypothesis)
    )
    val reached = force(
      Conv.trans(carried, moved).flatMap(Conv.trans(_, inner)).flatMap { step =>
        Conv.sym(consOpened).flatMap(Conv.trans(step, _))
      }
    )
    reached.conclusion shouldBe stepParts._2

    val step = force(
      rules.disch(stepParts._1, reached).flatMap(rules.genAll(_, stepStripped._1.toList))
    )
    val everywhere = force(rules.conjIntro(base, step).flatMap(rules.mp(opened, _)))

    everywhere.hypotheses shouldBe empty
    everywhere.conclusion shouldBe emptyRight.conclusion
  }

  /* --------------------------- whether the recursion can be spent */

  "The structural recursion" should "produce a function this repository already has" in {
    // The same guard as the one above, for the two theorems above it, and it has to be a different
    // test because the danger is a different one: `LIST_RECURSION` is an EXISTENTIAL, so a file
    // that only ever asserts a function exists has not shown that one can be got out, and
    // `LIST_RECURSION_UNIQUE` is an implication whose premises nobody may be able to discharge.
    // Both are spent here, in one derivation, and what comes out is compared against a constant
    // this repository defined long before either of them: `WORD_LENGTH`.
    //
    // The step is `\x. \w. \r. SUC r` and the start is `ZERO`, so what the recursion produces is
    // the function counting a list's letters. `WORD_LENGTH` satisfies those two equations already
    // -- `WORD_EMPTY_LENGTH` is the first and `LIST_CONS_LENGTH` is the second -- so uniqueness
    // says the two are one function. Neither half of that is available without both theorems: the
    // recursion supplies the function and nothing else says it is the one already here.
    val classical = Chain.standard.classical
    val concatenation = Chain.standard.concatenation
    val emptyLength = force(concatenation.fact(Concatenation.EmptyLength))
    val consLength = fact(Listing.ConsLength)

    def atNumbers(theorem: Kernel.Thm): Kernel.Thm =
      Kernel.instType(
        Map(Classical.TypeVariable -> numbers, Classical.CodomainVariable -> numbers),
        theorem
      )

    val zero = term("ZERO:num")
    val step = term("\\x:num. \\w:word(num). \\r:num. SUC r")
    val lengthConstant = force(
      LogicError.lift(listing.theory.constant(Word.Length, Type.fun(numberWords, numbers)))
    )

    // The function, out of the existential. `Classical.witness` is what turns "there is one" into
    // a term, and it is the only thing that can: the theorem names no function.
    val instance = force(rules.specAll(atNumbers(fact(Listing.RecursionTheorem)), List(zero, step)))
    val opened = force(
      Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
    )
    val chosen = force(classical.witness(opened))
    val reduced = force(
      Conv
        .betaNormalise(chosen.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chosen)))
    )
    val selected = chosen.conclusion match {
      case App(_, function) => function
      case other => fail(s"the witness is not a predicate applied to a term: $other")
    }

    // What `WORD_LENGTH` has to satisfy for uniqueness to reach it, and both are already proved.
    val lengthAtEmpty = Kernel.instType(Map(Classical.TypeVariable -> numbers), emptyLength)
    val lengthAtCons = Kernel.instType(Map(Classical.TypeVariable -> numbers), consLength)

    val unique = force(
      rules.specAll(
        atNumbers(fact(Listing.RecursionUnique)),
        List(zero, step, selected, lengthConstant)
      )
    )
    val stated = force(
      Conv
        .betaNormalise(unique.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, unique)))
    )
    val wanted = logic
      .destImp(stated.conclusion)
      .getOrElse(fail(s"the uniqueness is not an implication: ${stated.conclusion}"))
    val halves = logic
      .destConj(wanted._1)
      .getOrElse(fail(s"its premise is not a conjunction: ${wanted._1}"))

    val fromLength = force(rules.conjIntro(lengthAtEmpty, lengthAtCons))
    withClue("the length's own two equations are not the ones uniqueness asks for: ") {
      fromLength.conclusion shouldBe halves._2
    }

    val both = force(rules.conjIntro(reduced, fromLength))
    val equal = force(rules.mp(stated, both))

    // The function the recursion produced IS `WORD_LENGTH`, owing nothing.
    equal.hypotheses shouldBe empty
    equal.conclusion shouldBe force(LogicError.lift(Term.eq(selected, lengthConstant)))
  }
}
