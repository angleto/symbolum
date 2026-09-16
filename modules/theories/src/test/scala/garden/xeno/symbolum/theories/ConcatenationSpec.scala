package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Concatenating words, and the five questions that decide whether the development was worth it.
 *
 * **What it cost.** Nothing: six defined constants and no axiom, asserted against the theory it was
 * built over rather than against a number, which is `ProductSpec`'s argument and the same one.
 *
 * **What it says.** Each fact is compared against the text `Concatenation.Statements` holds, and
 * compared as a **term**: a type variable is written `'a` and printed `a`, so a printed polymorphic
 * statement does not read back and parsing the text is the stronger check anyway.
 *
 * **Whether the predicate ever says no.** `WORD_FACTOR` is an existential over all words, so a
 * definition alone proves nothing about it: the constant-true relation satisfies every test that
 * only ever asks it to hold. The test below derives `~(WORD_FACTOR u w)` for a **concrete** pair,
 * with every premise discharged, which is what says the relation discriminates.
 *
 * **Whether it can be used.** `WORD_FACTOR_LENGTH` is the first statement in the file that uses the
 * predicate rather than defining it, and the caller below spends it.
 *
 * **Whether the gap the card named is closed.** The last test is the acceptance criterion the card
 * for this work wrote down: the induction of Collatz 05 section 3.1.30 B, **stated** in symbolum.
 * It is checked by parsing it against the chain's widest signature and by putting the same text to
 * the signature one link down, which refuses it. The second half is what makes the first half worth
 * anything: a proposition that parses everywhere says nothing about what this development added.
 */
class ConcatenationSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val concatenation = Concatenation.standard
  private val rules = concatenation.logic.rules

  private def fact(name: String): Kernel.Thm = force(concatenation.fact(name))

  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val words: Type = TyApp(Word.TypeName, List(TyVar("a")))

  /** The whole development at `num` as the element type, which is what a concrete test needs. */
  private def overNumbers(theorem: Kernel.Thm): Kernel.Thm =
    Kernel.instType(Map(Classical.TypeVariable -> numbers), theorem)

  /* --------------------------------------------------------------- what it cost */

  "The concatenation" should "be defined rather than assumed" in {
    // Against the theory it actually EXTENDS, which is `Transcendental`'s and not `Word`'s. This
    // development needs `Word` and sits on top of the chain's end, and the two are different
    // questions: a difference taken against `word.theory` would come back holding every constant of
    // nine links and say nothing about what the concatenation added.
    val below = Chain.standard.transcendental.theory

    concatenation.theory.axioms shouldBe below.axioms
    (concatenation.theory.constants.keySet -- below.constants.keySet) shouldBe Set(
      Concatenation.Empty,
      Concatenation.Singleton,
      Concatenation.Name,
      Concatenation.Prefix,
      Concatenation.Suffix,
      Concatenation.Factor
    )
    Concatenation.Definitions.foreach { case (name, _) =>
      concatenation.theory.definitions.keySet should contain(name)
    }

    // And what it needs, as opposed to what it extends. All four were already in `Word.standard`'s
    // own signature, which is why this file's docstring says the split from `Word` is a decision
    // rather than the constraint `Rotation` was under.
    val narrow = Word.standard.theory.constants.keySet
    narrow should contain(Peano.Addition)
    narrow should contain(Peano.Subtraction)
    narrow should contain(Peano.StrictOrder)
    narrow should contain(Classical.Conditional)
    narrow should not contain Modular.ModName
  }

  it should "carry every fact without a hypothesis left standing" in {
    Concatenation.Statements.foreach { case (name, _) =>
      fact(name).hypotheses shouldBe empty
    }
  }

  it should "say what `Concatenation.Statements` says, read as a term" in {
    Concatenation.Statements.foreach { case (name, text) =>
      fact(name).conclusion shouldBe force(concatenation.proposition(text))
    }
  }

  it should "reach `docs/lemmas.md` through the chain's own library" in {
    // The check that would have caught `Magnitude` and `Coding`, each of which was proved, green and
    // in no document for a few hours. `ChainCoverageSpec` asks whether somebody classified the file;
    // this asks whether the facts are collected.
    val library = Library.of(Chain.standard)
    Concatenation.Statements.foreach { case (name, _) =>
      library.named(name) should not be empty
    }
  }

  /* ------------------------------------------------------- the three algebraic laws */

  "The two units" should "hold on the empty word from both sides" in {
    val w = Term.variable("w", words)

    force(rules.spec(w, fact(Concatenation.EmptyLeft))).hypotheses shouldBe empty
    force(rules.spec(w, fact(Concatenation.EmptyRight))).hypotheses shouldBe empty
  }

  "Associativity" should "be an equation between two words rather than an implication" in {
    // Read off the term rather than off the text: a version that had quietly acquired a side
    // condition on the lengths would still be a theorem and would still print plausibly.
    val opened = force(
      rules.specAll(
        fact(Concatenation.Associative),
        List(Term.variable("u", words), Term.variable("v", words), Term.variable("w", words))
      )
    )

    concatenation.logic.destImp(opened.conclusion) shouldBe None
    Term.destEq(opened.conclusion) should not be None
  }

  /* -------------------------------------------------- the predicate, and it saying no */

  "A factor" should "be no longer than the word it is a factor of" in {
    val opened = force(
      rules.specAll(
        fact(Concatenation.FactorLength),
        List(Term.variable("u", words), Term.variable("w", words))
      )
    )

    // An implication and not an equation: the premise is the predicate, which is the whole point of
    // the lemma. A version with the premise lost would be false.
    concatenation.logic.destImp(opened.conclusion) should not be None
    opened.hypotheses shouldBe empty
  }

  it should "be refused outright when it is longer, with nothing left assumed" in {
    // The negative control the card asked for by name, at a concrete pair rather than schematically:
    // a one-letter word is not a factor of the empty one. Every premise is discharged, so what comes
    // out is `|- ~(WORD_FACTOR (WORD_SINGLETON x) WORD_EMPTY)` with no hypotheses at all.
    val letter = Term.variable("x", numbers)
    // Not named `empty`: ScalaTest's `shouldBe empty` takes the nearest `empty` in scope, so a val
    // of that name turns the hypothesis assertion below into a comparison against a word. It did,
    // and the failure read "List() was not equal to WORD_EMPTY". `RotationSpec` carries the same
    // note about the same trap, which is how this one was recognised rather than debugged.
    val nothing = force(concatenation.term("WORD_EMPTY:word(num)"))
    val single = force(
      LogicError.lift(
        Term.app(
          force(
            LogicError.lift(
              concatenation.theory.constant(
                Concatenation.Singleton,
                Type.fun(numbers, TyApp(Word.TypeName, List(numbers)))
              )
            )
          ),
          letter
        )
      )
    )

    // `|WORD_EMPTY| < |WORD_SINGLETON x|`, which is `0 < SUC 0`.
    val emptyLength = overNumbers(fact(Concatenation.EmptyLength))
    val singleLength = force(rules.spec(letter, overNumbers(fact(Concatenation.SingletonLength))))
    val zero = force(concatenation.term("ZERO:num"))
    val positive = force(
      rules.spec(zero, force(concatenation.peano.fact(Peano.SuccessorPositive)))
    )

    val order = force(
      LogicError.lift(
        concatenation.theory
          .constant(Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
    )
    val atZero = force(
      Conv
        .sym(singleLength)
        .flatMap(equation => LogicError.lift(Term.app(order, zero)).flatMap(Conv.apTerm(_, equation)))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, positive)))
    )
    val shorter = force(
      Conv
        .sym(emptyLength)
        .flatMap(Conv.apTerm(order, _))
        .flatMap(Conv.apThm(_, force(rightOf(Conv.sym(singleLength)))))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atZero)))
    )

    val refused = force(
      rules
        .specAll(overNumbers(fact(Concatenation.FactorRefused)), List(single, nothing))
        .flatMap(rules.mp(_, shorter))
    )

    refused.hypotheses shouldBe empty
    concatenation.logic.destNot(refused.conclusion) should not be None
    concatenation.show(refused.conclusion) should include(Concatenation.Factor)
  }

  "A prefix and a suffix" should "each be a factor, through the empty word" in {
    val u = Term.variable("u", words)
    val w = Term.variable("w", words)

    force(rules.specAll(fact(Concatenation.PrefixIsFactor), List(u, w))).hypotheses shouldBe empty
    force(rules.specAll(fact(Concatenation.SuffixIsFactor), List(u, w))).hypotheses shouldBe empty
  }

  /* ------------------------------------------------------------------ the induction */

  "The induction" should "be usable by a caller that supplies a predicate of its own" in {
    // A caller, with the predicate instantiated. `\w. WORD_LENGTH w = WORD_LENGTH w` is a predicate
    // nothing could fail, which is the point: what is being checked is that the principle
    // specialises and detaches, not that it proves anything interesting.
    val trivial = force(concatenation.term("\\w:word(num). WORD_LENGTH w = WORD_LENGTH w"))
    val instance = force(rules.spec(trivial, overNumbers(fact(Concatenation.Induction))))

    instance.hypotheses shouldBe empty
    concatenation.logic.destImp(instance.conclusion) should not be None
  }

  it should "extend on the right rather than on the length, which is what the card asked for" in {
    // Read off the term: the step has to be about `WORD_CONCAT w (WORD_SINGLETON x)` and not about
    // `SUC (WORD_LENGTH w)`. A principle stated on the length alone would pass every other test in
    // this file and would be useless to the consumer, who extends a word at its end.
    val opened = force(
      rules.spec(
        Term.variable("P", Type.fun(words, Type.Bool)),
        fact(Concatenation.Induction)
      )
    )
    val premises = concatenation.logic
      .destImp(opened.conclusion)
      .getOrElse(fail("the induction is not an implication"))
    val halves = concatenation.logic
      .destConj(premises._1)
      .getOrElse(fail("its premise is not a conjunction"))

    concatenation.show(halves._2) should include(Concatenation.Name)
    concatenation.show(halves._2) should include(Concatenation.Singleton)
  }

  /* ------------------------------------------------- the criterion the card wrote down */

  /**
   * The induction of Collatz 05 section 3.1.30 B, written in symbolum.
   *
   * That argument puts `/f0^i f` in `RFC(S2)` by right extension: rule A2 carries `/f0^i f` to
   * `/f0^i 0f`, which is `/f0^(i+1) f`, and the family follows by induction on `i`. The card for
   * this work named the **statement** of that induction as the acceptance criterion and named its
   * proof as depending on the inductive-sets card, which is a different piece of work.
   *
   * So `RFC` is a free predicate here and deliberately: this development has nothing that defines a
   * set by closure, and writing one would be pretending. What is not free is everything else. The
   * block `/f0^i f` is four concatenations, three one-letter words and one `WORD_MAKE` of `i`
   * copies of a letter, and **none of the four operations existed in this repository yesterday**.
   *
   * Note that `0^i` needs no seventh constant: a word with one letter repeated is what `WORD_MAKE`
   * already builds, and that was worth measuring rather than assuming, because a repetition operator
   * would have been a second definition and a second set of laws.
   */
  private val theBlock: String =
    "WORD_CONCAT (WORD_CONCAT (WORD_CONCAT (WORD_SINGLETON (slash:num)) (WORD_SINGLETON f)) " +
      "(WORD_MAKE i (\\k:num. COND (NUM_LT k i) d (WORD_PAD:num)))) (WORD_SINGLETON f)"

  private val theInduction: String =
    "!i:num. RFC (" + theBlock + ") ==> RFC (" +
      theBlock.replace("(WORD_MAKE i ", "(WORD_MAKE (SUC i) ").replace("(NUM_LT k i)", "(NUM_LT k (SUC i))") +
      ")"

  "The induction of Collatz 05 section 3.1.30 B" should "be a proposition of the chain's signature" in {
    val stated = force(Chain.standard.widest.proposition(theInduction))

    // It is a claim about every `i`, and the two sides of the implication are different terms: a
    // text that had quietly collapsed to `RFC x ==> RFC x` would parse and would say nothing.
    val stripped = force(Logic.stripForall(stated))
    val parts = Chain.standard.widest.logic
      .destImp(stripped._2)
      .getOrElse(fail("the induction is not an implication"))
    parts._1 should not be parts._2
  }

  it should "read as a claim about nothing in the signature one link down" in {
    // The half that makes the half above worth having, and it is **not** a refusal. That is what
    // this test asserted first and it was wrong: an unknown letter-initial name parses as a FREE
    // VARIABLE, so the same text against `Transcendental` is well-typed and is a claim about an
    // arbitrary function that happens to be spelled `WORD_CONCAT`. It is the trap `Chain.peano`'s
    // docstring records for `NUM_LE ZERO n` and `ChainSpec` records for `zork`, met a third time,
    // and it is why "does it parse" is the wrong question to ask of a new constant.
    //
    // The right question is whether the name is a constant of the theory, and the two answers
    // differ: below the link the four names are free variables and the statement is about nothing.
    val statedNow = force(Chain.standard.widest.proposition(theInduction))
    val statedBefore = force(Chain.standard.transcendental.proposition(theInduction))

    val declared = Vector(
      Concatenation.Name,
      Concatenation.Singleton
    )

    declared.foreach { name =>
      withClue(s"$name should be a constant of the widest signature:\n")(
        constantsIn(statedNow) should contain(name)
      )
      withClue(s"$name should not be a free variable of the widest signature:\n")(
        Term.freeVariables(statedNow).map(_.name) should not contain name
      )
      withClue(s"$name should be a free variable one link down:\n")(
        Term.freeVariables(statedBefore).map(_.name) should contain(name)
      )
    }

    statedNow should not be statedBefore
  }

  /** Every constant name occurring in a term. */
  private def constantsIn(term: Term): Set[String] = term match {
    case Const(name, _) => Set(name)
    case App(operator, argument) => constantsIn(operator) ++ constantsIn(argument)
    case Abs(_, body) => constantsIn(body)
    case _ => Set.empty
  }

  private def rightOf(result: Either[LogicError, Kernel.Thm]): Either[LogicError, Term] =
    result.flatMap(theorem =>
      Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
    )
}
