package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The system $S_2$: that the eleven rules are the source's eleven, that they constrain, and that
 * the marked words are closed under them.
 *
 * This development is `BesideTheChain`, so nothing else builds it and this file is the only thing
 * that does. That is the obligation the standing carries rather than an accident of where the test
 * went.
 *
 * == What each of the three guards here is against ==
 *
 * A relation that held of every pair would make `WORD_RFC S2` the set of all words, and every
 * statement downstream of it true and empty. [[Collatz.Refused]] is what says the eleven are a
 * constraint, and it is derived rather than observed.
 *
 * A relation whose eleven clauses had collapsed into fewer would be a different rewriting system
 * that still proved theorems. The count of disjuncts says how many clauses were **written**; the
 * fifty-five separations say how many pairs the relation actually holds of, and only the second
 * would notice a table in which two rules had become one.
 *
 * And [[Collatz.MarkedClosed]] over an empty class of marked words would be a theorem about
 * nothing. The closure is therefore detached here rather than asserted to exist: `/0.` is marked,
 * `B1` steps it, and what comes back out is a marked word.
 *
 * == The fourth, which arrived with the digit family ==
 *
 * A membership in `WORD_RFC S2` is worth exactly what the non-memberships are worth, and there
 * were none until 2026-09-18: a closure that held of every word would make [[Collatz.FamilyWithF]]
 * and [[Collatz.FamilyWithTail]] theorems about nothing, and neither they nor anything proved
 * after them would notice. [[Collatz.ClosureRefused]] is the guard, and it is a theorem of the
 * development rather than an assertion here because the induction it runs on is
 * [[Forward.Induction]] rather than anything a test can reach.
 *
 * The family itself is detached here, for [[Collatz.MarkedInhabited]]'s reason: the statement
 * quantifies over an index and names a run of digits, so what says it is about words is
 * specialising it and reading the letters that come out.
 */
class CollatzSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard

  private lazy val system: Collatz =
    Collatz
      .construct(
        chain.forward,
        chain.reaching,
        chain.numbering,
        chain.naturals,
        chain.peano,
        chain.successor,
        chain.forward.theory,
        chain.forward.notation)
      .fold(error => fail(s"the system does not build: ${error.message}"), identity)

  private def fact(name: String): Kernel.Thm =
    system.fact(name).fold(error => fail(error.message), identity)

  private def rules: Rules = system.logic.rules

  /** A term of this signature, read the way a person writing one in this file reads it. */
  private def parse(text: String): Term =
    Parser
      .term(system.theory, system.notation, text)
      .fold(error => fail(s"$text does not read: ${error.message}"), identity)

  /** The body of a nest of lambdas: both definitions here are `\l. \r. <the disjunction>`. */
  private def under(term: Term): Term = term match {
    case Abs(_, body) => under(body)
    case other => other
  }

  private def disjuncts(term: Term): Int = system.logic.destDisj(term) match {
    case Some((left, right)) => disjuncts(left) + disjuncts(right)
    case None => 1
  }

  private def bodyOf(name: String): Term = {
    val definition = system.definition(name).fold(error => fail(error.message), identity)
    under(Term.destEq(definition.conclusion).map(_._2).getOrElse(fail("not an equation")))
  }

  "The system" should "declare the alphabet, the four relations and the marker-free words" in {
    system.definitions.keySet shouldBe Set(
      Collatz.F, Collatz.T, Collatz.Head, Collatz.Tail,
      Collatz.Name, Collatz.Counted, Collatz.Potential, Collatz.Marked, Collatz.TailFree,
      Collatz.HeadFree, Collatz.Anchored,
      Collatz.Run, Collatz.RunCounted,
      Collatz.Zeros
    )
  }

  it should "hold exactly eleven rules, which is the number the source has" in {
    // Counted off the definition rather than off the table that generated it, so that a
    // generation which dropped or doubled a clause is caught here rather than believed.
    withClue(s"${system.show(bodyOf(Collatz.Name))}\n") {
      disjuncts(bodyOf(Collatz.Name)) shouldBe 11
    }
    Collatz.Rules.size shouldBe 11
  }

  it should "say the same thing its published statements do" in {
    for ((name, text) <- Collatz.Statements) {
      val expected = Parser
        .proposition(system.theory, system.notation, text)
        .fold(error => fail(s"$name does not parse: ${error.message}"), identity)

      withClue(s"$name\n  text:    ${system.show(expected)}\n  theorem: ${system.show(fact(name).conclusion)}\n") {
        fact(name).conclusion shouldBe expected
      }
    }
  }

  "The relation" should "hold of something, so that nothing downstream of it is vacuous" in {
    // `WORD_RFC S2` of an empty relation is empty and every non-membership about it is trivially
    // true. This is the guard `InductiveSpec` puts on the even numbers, at this system.
    fact(Collatz.Inhabited).hypotheses shouldBe empty
  }

  it should "refuse a pair, which is what makes it a constraint rather than a relation" in {
    // The half that cannot be got by looking: a search over the rules answers a membership and
    // never a non-membership. Here the one-letter word is refuted against all eleven clauses on
    // the lengths, which is a derivation the kernel checked.
    val refused = fact(Collatz.Refused)
    refused.hypotheses shouldBe empty

    withClue(s"${system.show(refused.conclusion)}\n") {
      system.logic.destNot(refused.conclusion) shouldBe defined
    }
  }

  it should "have eleven rules that are pairwise different, derived rather than counted" in {
    // The count above says eleven clauses were written. This says the eleven left-hand sides are
    // eleven different words, which is what a table with a rule duplicated would fail: the count
    // would still be eleven and this would go red on the pair that had become one.
    val separations = system.separations
      .fold(error => fail(s"the rules are not separated: ${error.message}"), identity)

    separations.size shouldBe 55

    for ((first, second, apart) <- separations) {
      withClue(s"$first against $second: ${system.show(apart.conclusion)}\n") {
        apart.hypotheses shouldBe empty
        system.logic.destNot(apart.conclusion) shouldBe defined
      }
    }

    // And the population is the one it claims to be: every rule appears, and no pair twice.
    separations.map(entry => (entry._1, entry._2)).distinct.size shouldBe 55
    separations.flatMap(entry => List(entry._1, entry._2)).distinct.size shouldBe 11
  }

  "Every rule" should "carry each marker the same number of times on both sides" in {
    // The combinatorial half of a closure lemma nobody has proved yet, pinned where facts about
    // the encoding live. That `REACH_POTENTIAL` cannot be read on `S2_MARKED` alone is a theorem
    // since 2026-09-21 and is no longer a witness quoted in a comment: `Collatz.PlainStepHolds`
    // with the three facts beside it is the instance, at the bottom of this file. So the class the
    // potential argument wants is the marked words **and** one head marker, in front, and what
    // makes that class closed under a step is that no rule of this table introduces or removes
    // either marker, which is this, counted.
    //
    // **It reads the table and not the definition**, which is weaker than the two tests above it
    // and is said rather than left to be noticed: `disjuncts` counts clauses off the definition and
    // the fifty-five separations are derived from it, where this is a property of the Scala vector
    // the definition is generated from. What it is for is that the next piece of work has the fact
    // written down at all, at the place a change to the table breaks it.
    for (rule <- Collatz.Rules) {
      withClue(s"${rule.label}: ${rule.left.mkString} -> ${rule.right.mkString}\n") {
        rule.left.count(_ == Collatz.Head) shouldBe rule.right.count(_ == Collatz.Head)
        rule.left.count(_ == Collatz.Tail) shouldBe rule.right.count(_ == Collatz.Tail)
      }
    }

    // And the head marker, where a rule holds one at all, is the first letter on both sides. That
    // is what says a `B` rule fires at the front of a well-formed word and nowhere else, which is
    // the other half of the same argument.
    val atTheHead = Collatz.Rules.filter(_.left.contains(Collatz.Head))
    atTheHead.map(_.label) shouldBe Vector("B1", "B2", "B3")
    for (rule <- atTheHead) {
      withClue(s"${rule.label}: ${rule.left.mkString} -> ${rule.right.mkString}\n") {
        rule.left.head shouldBe Collatz.Head
        rule.right.head shouldBe Collatz.Head
      }
    }
  }

  "The counted sub-relation" should "be six of the eleven, and every one of them a rule" in {
    disjuncts(bodyOf(Collatz.Counted)) shouldBe 6
    Collatz.CountedRules.size shouldBe 6

    // And they really are rules of the system, which is the fact a potential argument needs
    // before it can call `A` a sub-relation of `R` at all.
    fact(Collatz.CountedIsRule).hypotheses shouldBe empty
  }

  "The marked words" should "be closed under a step, and the closure detached rather than admired" in {
    // A closure statement over an empty class is a theorem about nothing, and so is one over a
    // relation that steps nothing. Neither would fail any other assertion in this file. So the
    // implication is spent here: `/0.` is marked, `B1` steps it to `/t.`, and modus ponens gives
    // a marked word back.
    val marked = fact(Collatz.MarkedInhabited)
    val stepped = fact(Collatz.StepInhabited)

    val subject = argumentOf(marked.conclusion)
    val result = argumentOf(stepped.conclusion)

    withClue(s"${system.show(subject)} against ${system.show(result)}\n") {
      result should not be subject
    }

    val closed = rules
      .conjIntro(marked, stepped)
      .flatMap(premise =>
        rules
          .specAll(fact(Collatz.MarkedClosed), List(subject, result))
          .flatMap(rules.mp(_, premise)))
      .fold(error => fail(s"the closure does not apply: ${error.message}"), identity)

    closed.hypotheses shouldBe empty

    val predicate = headOf(marked.conclusion)
    val expected = Term
      .app(predicate, result)
      .fold(error => fail(s"the predicate does not apply: ${error.message}"), identity)

    withClue(s"${system.show(closed.conclusion)}\n") {
      closed.conclusion shouldBe expected
    }
  }

  "The anchored words" should "be closed under a step, and the closure detached rather than admired" in {
    // [[Collatz.MarkedClosed]]'s guard at the other marker, and it is needed for the same reason:
    // a closure over an empty class is a theorem about nothing. `/0.` has its head marker where an
    // anchored word has one, `B1` steps it, and what comes back is anchored.
    //
    // The two classes are what the potential argument is stated on together. Marked alone leaves
    // the head marker free to sit anywhere in the word, and then a `B` rule fires at a digit that
    // is not the first and `S2_PHI` falls across a step nothing counted: `0/0.` steps to `0/t.`.
    val anchored = fact(Collatz.AnchoredInhabited)
    val stepped = fact(Collatz.StepInhabited)

    val subject = argumentOf(anchored.conclusion)
    val result = argumentOf(stepped.conclusion)

    val closed = rules
      .conjIntro(anchored, stepped)
      .flatMap(premise =>
        rules
          .specAll(fact(Collatz.AnchoredClosed), List(subject, result))
          .flatMap(rules.mp(_, premise)))
      .fold(error => fail(s"the closure does not apply: ${error.message}"), identity)

    closed.hypotheses shouldBe empty

    val predicate = headOf(anchored.conclusion)
    val expected = Term
      .app(predicate, result)
      .fold(error => fail(s"the predicate does not apply: ${error.message}"), identity)

    withClue(s"${system.show(closed.conclusion)}\n") {
      closed.conclusion shouldBe expected
    }
  }

  it should "be a class the two markers agree on, which is what the step witness shows" in {
    // The witness is one word, `/0.`, and both classes hold of it: the head marker is its first
    // letter and the tail marker is its last. A reader who took `S2_ANCHORED` for a restatement of
    // `S2_MARKED` would find nothing here to correct them, so what says the two are different
    // claims is that each refuses what the other takes. `/0` has no tail marker and `0.` has no
    // head marker, and neither is a word this file had to build: they are the rule sides of `B1`
    // and of `R2`, which the table already spells.
    val anchoredWitness = argumentOf(fact(Collatz.AnchoredInhabited).conclusion)
    val markedWitness = argumentOf(fact(Collatz.MarkedInhabited).conclusion)

    anchoredWitness shouldBe markedWitness
  }

  private def argumentOf(term: Term): Term = term match {
    case App(_, argument) => argument
    case other => fail(s"not an application: ${system.show(other)}")
  }

  private def headOf(term: Term): Term = term match {
    case App(head, _) => head
    case other => fail(s"not an application: ${system.show(other)}")
  }

  it should "need the tail to be non-empty, which the empty word is what says" in {
    // `S2_MARKED_CONCAT` carries `0 < WORD_LENGTH v` and the condition is not decoration: at the
    // empty tail the left-hand side is `S2_MARKED u` and the right-hand side asks for a last
    // letter of a word with none. This derives the half that makes the equation false there.
    val emptyWord = system.theory
      .constant(Concatenation.Empty, TyApp(Word.TypeName, List(TyApp(Natural.TypeName, Nil))))
      .fold(error => fail(error.message), identity)

    val definition = system.definition(Collatz.Marked).fold(error => fail(error.message), identity)
    val opened = Conv.unfold(definition, List(emptyWord)).fold(error => fail(error.message), identity)
    val claim = Term.destEq(opened.conclusion).map(_._1).getOrElse(fail("not an equation"))

    val refused = for {
      assumed <- LogicError.lift(Kernel.assume(claim))
      held <- LogicError.lift(Kernel.eqMp(opened, assumed))
      positive <- rules.conjElim1(held)
      emptyLength <- chain.concatenation
        .fact(Concatenation.EmptyLength)
        .map(Kernel.instType(Map(Classical.TypeVariable -> TyApp(Natural.TypeName, Nil)), _))
      order <- LogicError.lift(
        system.theory.constant(
          Peano.StrictOrder,
          Type.fun(TyApp(Natural.TypeName, Nil), Type.fun(TyApp(Natural.TypeName, Nil), Type.Bool))))
      zero <- LogicError.lift(
        system.theory.constant(Natural.NumberZero, TyApp(Natural.TypeName, Nil)))
      partial <- LogicError.lift(Term.app(order, zero))
      moved <- Conv.apTerm(partial, emptyLength)
      atZero <- LogicError.lift(Kernel.eqMp(moved, positive))
      nothing <- chain.peano.fact(Peano.NotBelowZero).flatMap(rules.spec(zero, _))
      absurd <- rules.notElim(nothing, atZero)
      result <- rules.notIntro(claim, absurd)
    } yield result

    val theorem = refused.fold(error => fail(s"the empty word is not refused: ${error.message}"), identity)
    theorem.hypotheses shouldBe empty
    system.logic.destNot(theorem.conclusion) shouldBe defined
  }

  "The digit family" should "detach at an index and come back a word with letters in it" in {
    // `05` section 3.1.30 B at `j = 1`, which is the smallest index the family has and the first
    // one the source's backward search settles. The published statement quantifies over the index
    // and names the run `S2_ZEROS` rather than any letter, so what says it is a claim about words
    // is this: specialise it at zero, rewrite the run away with the recursion's own two equations,
    // and read what is left. `/f0.` is what comes out, written out letter by letter.
    //
    // Source for the word: `collatz@8b991e5`, `code/referee/checks_rewriting.py:726`, where
    // `_in_rfc('/f' + '0' * j + '.')` is asserted True for `j` from 1 to 10 by a search that knows
    // nothing of the induction this repository proves.
    val numbers = TyApp(Natural.TypeName, Nil)
    val zero = parse("(ZERO:num)")
    val emptyLeft = Kernel.instType(
      Map(Classical.TypeVariable -> numbers),
      chain.forward.concatenation
        .fact(Concatenation.EmptyLeft)
        .fold(error => fail(error.message), identity)
    )

    val equations = Vector(
      fact(Collatz.ZerosAtSuccessor),
      fact(Collatz.ZerosAtZero),
      emptyLeft
    ).map(equation =>
      Rewrite.Rule.of(system.logic, equation).fold(error => fail(error.message), identity))

    // Both indices and not one. At `j = 1` the run's own base case is what is read, so a
    // `S2_ZEROS` that was the empty word at every index would pass; `j = 2` is where the recursion
    // has to fire twice, and it is the smallest index that says the run grows.
    val cases = Vector(
      zero ->
        ("WORD_RFC S2 (WORD_CONCAT (WORD_CONCAT (WORD_CONCAT " +
          "(WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (S2_F:num))) " +
          "(WORD_SINGLETON (0:num))) (WORD_SINGLETON (S2_TAIL:num)))"),
      // The run stays a block of its own here, where at `j = 1` it collapsed to one letter and the
      // word came out flat. That is the shape of the statement rather than an accident of the
      // rewriting: the family is written `WORD_CONCAT (WORD_CONCAT /f 0^j) .`, so the letters of
      // the run are inside their own concatenation and nothing above flattens them. A reader
      // comparing this with `/f00.` is reading the same word at a different nesting.
      parse("(SUC ZERO)") ->
        ("WORD_RFC S2 (WORD_CONCAT (WORD_CONCAT (WORD_CONCAT " +
          "(WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (S2_F:num))) " +
          "(WORD_CONCAT (WORD_SINGLETON (0:num)) (WORD_SINGLETON (0:num)))) " +
          "(WORD_SINGLETON (S2_TAIL:num)))")
    )

    for ((index, text) <- cases) {
      val instance = rules
        .spec(index, fact(Collatz.FamilyWithTail))
        .fold(error => fail(error.message), identity)
      val simplified = Rewrite
        .rewrite(equations, instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
        .fold(error => fail(error.message), identity)

      val expected = Parser
        .proposition(system.theory, system.notation, text)
        .fold(error => fail(error.message), identity)

      withClue(s"at ${system.show(index)}: ${system.show(simplified.conclusion)}\n") {
        simplified.conclusion shouldBe expected
      }
      simplified.hypotheses shouldBe empty
    }
  }

  it should "be one induction and one extension, not two inductions" in {
    // The shape of the pair rather than its content, and it is worth asserting because the cheap
    // mistake here is to prove the family twice. `S2_FAMILY_TAIL` is `S2_FAMILY_F` with one right
    // extension on the end, so the second rests on the first: what the first reaches, and nothing
    // else, is what the second can be about.
    //
    // Read off the proof record rather than off the source, so a rewrite of either derivation that
    // separated them goes red here.
    val familyWithF = fact(Collatz.FamilyWithF)
    val familyWithTail = fact(Collatz.FamilyWithTail)

    Derivation.restingOn(familyWithTail, Set(familyWithF.conclusion)) should
      contain(familyWithF.conclusion)
    Derivation.restingOn(familyWithF, Set(familyWithTail.conclusion)) shouldBe empty
  }

  "What the facts cost" should "split three ways, and the third way was a prediction this test refuted" in {
    // The two that are equations between words and closed under the definition reach no
    // foundational axiom at all.
    Derivation.axiomsOf(fact(Collatz.CountedIsRule)) shouldBe empty
    Derivation.axiomsOf(fact(Collatz.Inhabited)) shouldBe empty

    // Everything that reasons about LENGTHS or POSITIONS pays what anything about `num` pays
    // here and no more: `SELECT` and `INFINITY`.
    val aboutNumbers = List(
      Collatz.Refused,
      Collatz.TailFreeConcat,
      Collatz.MarkedConcat,
      Collatz.RuleNotEmpty,
      Collatz.MarkedStep,
      Collatz.TailFreeStep,
      Collatz.MarkedInhabited
    )

    for (name <- aboutNumbers) {
      val rests = Derivation.axiomsOf(fact(name))
      withClue(s"$name rests on: ${rests.map(system.show).toVector.sorted.mkString(", ")}\n") {
        rests.size shouldBe 2
      }
    }

    // **And two pay a third, which is `ETA_AX`, and this file predicted two for them.** The
    // prediction was that "everything that reads a length costs two"; the run said three for
    // these, and the probe that found out why is worth the two lines it takes to record.
    //
    // It is not something the closure does. `WORD_CONCAT_EMPTY_RIGHT` and
    // `WORD_LENGTH_ZERO` **each cost three by themselves**, eta among them, because both are
    // `WORD_EXTENSIONALITY` at a word rebuilt from `WORD_EMPTY` and the extensionality of a
    // defined type goes through its abstraction. Measured, not reasoned: `NUM_CASES` costs
    // zero, `NUM_ZERO_LT_SUC` costs two, and `WORD_STEP`'s defining equation costs zero, so
    // none of those is where it enters.
    //
    // So the line is not lengths against words. It is whether a proof has to turn a word back
    // into `WORD_EMPTY`: the closure's empty-tail branch does, the step witness does through
    // `WORD_CONCAT_EMPTY_LEFT`, and nothing else here does.
    val throughTheEmptyWord = List(Collatz.MarkedClosed, Collatz.StepInhabited)

    for (name <- throughTheEmptyWord) {
      val rests = Derivation.axiomsOf(fact(name))
      withClue(s"$name rests on: ${rests.map(system.show).toVector.sorted.mkString(", ")}\n") {
        rests.size shouldBe 3
      }
    }

    // The digit family, measured on 2026-09-18 when it landed, and it falls on **both** sides of
    // the line the two paragraphs above draw rather than on one. The run's own equations and the
    // guard that the closure is not every word cost the naturals' two; the two facts about the
    // family cost three, and the third is `ETA_AX` again.
    //
    // That is the same criterion as above and not a coincidence: the family's base case is
    // `WORD_CONCAT (/f) (S2_ZEROS ZERO)`, which is a word rebuilt from `WORD_EMPTY` through
    // `WORD_CONCAT_EMPTY_RIGHT`, and that lemma carries eta by itself. `S2_RFC_REFUSED` mentions
    // `WORD_EMPTY` in its own statement and costs two, which is what says the criterion is about
    // turning a word back into the empty word rather than about naming it: that proof only ever
    // refutes being it, through `WORD_EMPTY_LENGTH`.
    for (name <- List(Collatz.ZerosAtZero, Collatz.ZerosAtSuccessor, Collatz.ClosureRefused)) {
      val rests = Derivation.axiomsOf(fact(name))
      withClue(s"$name rests on: ${rests.map(system.show).toVector.sorted.mkString(", ")}\n") {
        rests.size shouldBe 2
      }
    }

    for (name <- List(Collatz.FamilyWithF, Collatz.FamilyWithTail)) {
      val rests = Derivation.axiomsOf(fact(name))
      withClue(s"$name rests on: ${rests.map(system.show).toVector.sorted.mkString(", ")}\n") {
        rests.size shouldBe 3
      }
    }

    // The guard against that third being a fact about this file rather than about the two
    // lemmas: they carry it before anything here touches them.
    for (name <- List(Concatenation.EmptyRight, Concatenation.LengthZero)) {
      val rests = chain.concatenation
        .fact(name)
        .fold(error => fail(error.message), theorem => Derivation.axiomsOf(theorem))
      withClue(s"$name rests on: ${rests.map(system.show).toVector.sorted.mkString(", ")}\n") {
        rests.size shouldBe 3
      }
    }
  }

  // Part C's nineteen facts, which had no cost asserted anywhere until 2026-09-20 while the two
  // paragraphs above covered sixteen of the development's others. That gap is what the card's own
  // test plan asked for and is the reason this test exists rather than a second reading of the one
  // above: the anchored class, the measure and the run were written after it, and a proof that
  // quietly started spending a fourth axiom would have been invisible at exactly the facts the
  // investigation rests on.
  //
  // THE PARTITION IS THE ASSERTION AND THE NAMES ARE NOT SORTED BY HAND INTO IT. Every fact is
  // measured, the two groups come out of the measurement, and the clue prints the whole table, so
  // a fact that moves between them says which one it is and what it now rests on.
  "What part C costs" should "be the naturals' two, and a third where the proof rebuilds the empty word" in {
    val partC = List(
      Collatz.HeadFreeConcat,
      Collatz.AnchoredConcat,
      Collatz.HeadFreeStep,
      Collatz.AnchoredStep,
      Collatz.AnchoredClosed,
      Collatz.AnchoredInhabited,
      Collatz.PotentialConcat,
      Collatz.PotentialAtAWord,
      Collatz.PotentialBlocks,
      Collatz.PotentialCountedStep,
      Collatz.PotentialPlainStep,
      Collatz.RunPotential,
      Collatz.RunInhabited,
      Collatz.ZerosLength,
      Collatz.StemLength,
      Collatz.PotentialOfStem,
      Collatz.PotentialOfFamily,
      Collatz.FamilyBounded,
      Collatz.FamilyAtOne
    )

    val measured = partC.map(name => name -> Derivation.axiomsOf(fact(name))).toMap
    val table = measured.toVector
      .sortBy(_._1)
      .map { case (name, rests) => s"$name: ${rests.map(system.show).toVector.sorted.mkString(", ")}" }
      .mkString("\n")

    withClue(s"what part C rests on, measured:\n$table\n") {
      // Nothing here reaches a fourth axiom, and that is the half of this test that would still
      // mean something if the split below were rewritten: the reals are not among them, and no
      // fact of this development spends anything the naturals do not.
      measured.values.foreach(rests => rests.size should (be(2) or be(3)))

      // THE PREDICTION WAS THREE FOR EVERYTHING BUT THE TWO LENGTH LEMMAS, AND THE RUN SAID TEN
      // OF THE NINETEEN COST TWO. It came from a probe a verifying session ran on 2026-09-18 over
      // ten of these facts, and what was wrong with it was the population rather than the
      // arithmetic: the anchored and head-free lemmas were not in that ten and they cost two.
      //
      // What the run says instead is that the criterion two paragraphs up carries here unchanged,
      // and this is the third group it has been checked against. A proof costs the third axiom,
      // `ETA_AX`, exactly when it has to turn a word back into `WORD_EMPTY`:
      //
      //   - the closure over the anchored class does, at the empty-tail branch, which is why it
      //     sits with `S2_MARKED_CLOSED` and not with the other anchored lemmas;
      //   - the measure's two step theorems do, and everything resting on them does, which is the
      //     whole of the run and the family;
      //   - the family's base case is `WORD_CONCAT (/f) (S2_ZEROS ZERO)`, which is
      //     `WORD_CONCAT_EMPTY_RIGHT`, and that lemma carries eta by itself.
      //
      // And what does NOT: everything that only reads positions and lengths, which is the ten
      // below. `S2_PHI_CONCAT`, `S2_PHI_AT_A_WORD` and `S2_PHI_BLOCKS` are about the measure and
      // are in that ten, so the line is not the measure against the class either.
      val two = measured.collect { case (name, rests) if rests.size == 2 => name }.toSet
      two shouldBe Set(
        Collatz.HeadFreeConcat,
        Collatz.AnchoredConcat,
        Collatz.HeadFreeStep,
        Collatz.AnchoredStep,
        Collatz.AnchoredInhabited,
        Collatz.PotentialConcat,
        Collatz.PotentialAtAWord,
        Collatz.PotentialBlocks,
        Collatz.ZerosLength,
        Collatz.StemLength
      )
    }
  }

  "The bound on a run" should "detach, which is REACH_POTENTIAL arriving at this measure" in {
    // What this shows and what it does not. `REACH_START` inhabits the closure whatever the
    // relation does, so detaching here says the instantiation's two hypotheses were discharged
    // and the conclusion reads at this system -- not that any run gets anywhere. What says the
    // relation steps something at all is `S2_RUN_INHABITED`, derived beside it; what would say a
    // run of positive length exists is a refusal of the counted step at a concrete pair, and
    // nothing in this repository proves one of those yet.
    val rules = system.logic.rules
    val (run, before) = fact(Collatz.RunInhabited).conclusion match {
      case App(App(relation, left), _) => (relation, left)
      case other => fail(s"not a step of the run: ${system.show(other)}")
    }
    val counted = system.theory
      .constant(Collatz.RunCounted, Term.typeOf(run))
      .fold(error => fail(s"no such constant: $error"), identity)
    val start = chain.reaching
      .fact(Reaching.Start)
      .fold(error => fail(error.message), theorem =>
        Kernel.instType(Map(Classical.TypeVariable -> Term.typeOf(before)), theorem))

    val atStart = rules
      .specAll(start, List(run, counted, before))
      .fold(error => fail(error.message), identity)
    val reached = atStart.conclusion match {
      case App(_, argument) => argument
      case other => fail(s"not a reachability: ${system.show(other)}")
    }
    val bound = rules
      .specAll(fact(Collatz.RunPotential), List(before, reached))
      .flatMap(rules.mp(_, atStart))
      .fold(error => fail(error.message), identity)

    // The measure is read off a fact that already names it rather than fetched by name and type,
    // which keeps this test from having to spell a type it has no other reason to know.
    val measure = Term.destEq(fact(Collatz.PotentialAtAWord).conclusion) match {
      case Some((App(head, _), _)) => head
      case other => fail(s"not the measure at a word: $other")
    }
    val wanted = Term
      .app(measure, before)
      .fold(error => fail(s"the measure does not apply: $error"), identity)

    bound.hypotheses shouldBe empty
    withClue(s"${system.show(bound.conclusion)}\n") {
      bound.conclusion match {
        case App(App(_, left), _) => left shouldBe wanted
        case other => fail(s"not an order statement: ${system.show(other)}")
      }
    }
  }

  /* ---------------------------------- the anchored class, and why it is not the marked one */

  private lazy val witnesses: Collatz.ClassWitnesses =
    system.classWitnesses
      .fold(error => fail(s"the witnesses do not build: ${error.message}"), identity)

  "The anchored class" should "have nine witnesses that say what they are written down as saying" in {
    // The same comparison `Statements` gets one section up, at the facts this development does
    // not publish. A derivation that reached a theorem about another word, or about `S2` where
    // the claim is about `S2_COUNTED`, is true and is not the counterexample, and nothing in the
    // shape assertions below would notice: they read which relation and which pair, off the
    // theorem itself. This reads the text.
    val derived = witnesses.named.toMap
    derived.keySet shouldBe Collatz.WitnessStatements.map(_._1).toSet

    for ((name, text) <- Collatz.WitnessStatements) {
      val expected = Parser
        .proposition(system.theory, system.notation, text)
        .fold(error => fail(s"$name does not parse: ${error.message}"), identity)
      val held = derived.getOrElse(name, fail(s"no witness named $name"))

      withClue(s"$name\n  text:    ${system.show(expected)}\n  theorem: ${system.show(held.conclusion)}\n") {
        held.conclusion shouldBe expected
        held.hypotheses shouldBe empty
      }
    }
  }

  it should "be what the counted step's drop needs, refuted on a marked word" in {
    // `S2_PHI_COUNTED_STEP` asks `S2_ANCHORED u` and nothing else. What says that hypothesis is
    // load-bearing is this instance: `f0.` satisfies every other antecedent, is NOT anchored, and
    // the conclusion is false at it. A theorem does not refuse, so this is the only form the
    // control can take, and it is the one `ReachingSpec` uses on the lemma being instantiated.
    //
    // Until 2026-09-21 what stood in this place was six figures in prose, counted by a Python
    // mirror over every word of at most seven letters and read by no test. A figure of that kind
    // is a property of the enumeration's bound as much as of the system; this is a derivation.
    val witness = witnesses.counted

    for (held <- List(witness.marked, witness.notAnchored, witness.stepped, witness.measureStands))
      withClue(s"${system.show(held.conclusion)}\n") {
        held.hypotheses shouldBe empty
      }

    // Marked, and not anchored: the pair is what says the weakening under test is a real one.
    system.logic.destNot(witness.notAnchored.conclusion) shouldBe defined
    system.logic.destNot(witness.marked.conclusion) shouldBe empty

    // The step is a COUNTED one, so the lemma's second antecedent holds as written.
    witness.stepped.conclusion match {
      case App(App(App(_, relation), _), _) =>
        relation shouldBe system.theory
          .constant(Collatz.Counted, Term.typeOf(relation))
          .fold(error => fail(s"no such constant: $error"), identity)
      case other => fail(s"not a step: ${system.show(other)}")
    }

    // And the conclusion is refuted: what the lemma would give is `S2_PHI u = SUC (S2_PHI v)`,
    // and both measures are nothing, because a digit at position zero and one at position one
    // both weigh `i - 1` over a truncated subtraction.
    withClue(s"${system.show(witness.measureStands.conclusion)}\n") {
      system.logic.destNot(witness.measureStands.conclusion) shouldBe defined
    }
  }

  it should "be what the uncounted step's bound needs, refuted on another marked word" in {
    // `S2_PHI_PLAIN_STEP` asks `S2_ANCHORED u /\ S2_MARKED u /\ ...`, and this refutes dropping
    // the first of the two. `0/0.` is marked, is not anchored, `B1` steps it to `0/t.`, nothing
    // counts that step, and the measure FALLS across it, which is the second hypothesis of
    // `REACH_POTENTIAL` failing at a pair the weakened lemma would admit.
    //
    // The antecedent that costs something is the third. Naming `B1` says the rule that fired is
    // not a commutation and says nothing about a different factorisation of the same pair;
    // `Collatz.noCountedStepFrom` is what derives the negative about the relation.
    val witness = witnesses.plain

    val everything = List(
      witness.marked,
      witness.notAnchored,
      witness.stepped,
      witness.notCounted,
      witness.measureFalls)

    for (held <- everything)
      withClue(s"${system.show(held.conclusion)}\n") {
        held.hypotheses shouldBe empty
      }

    system.logic.destNot(witness.notAnchored.conclusion) shouldBe defined
    system.logic.destNot(witness.marked.conclusion) shouldBe empty

    // The step is a step of the SYSTEM, and it is not a step of the counted sub-relation. The
    // second is a negative, and a negative about a relation is the half a witness cannot exhibit.
    witness.stepped.conclusion match {
      case App(App(App(_, relation), _), _) =>
        relation shouldBe system.theory
          .constant(Collatz.Name, Term.typeOf(relation))
          .fold(error => fail(s"no such constant: $error"), identity)
      case other => fail(s"not a step: ${system.show(other)}")
    }

    val refused = system.logic
      .destNot(witness.notCounted.conclusion)
      .getOrElse(fail(s"not a refusal: ${system.show(witness.notCounted.conclusion)}"))
    refused match {
      case App(App(App(_, relation), _), _) =>
        relation shouldBe system.theory
          .constant(Collatz.Counted, Term.typeOf(relation))
          .fold(error => fail(s"no such constant: $error"), identity)
      case other => fail(s"not a step: ${system.show(other)}")
    }

    // The two steps are about the same pair, which is what makes the four antecedents one
    // instance rather than four facts that happen to be true.
    (witness.stepped.conclusion, refused) match {
      case (App(App(_, beforeStep), afterStep), App(App(_, beforeRefusal), afterRefusal)) =>
        beforeStep shouldBe beforeRefusal
        afterStep shouldBe afterRefusal
      case other => fail(s"not two steps: $other")
    }

    withClue(s"${system.show(witness.measureFalls.conclusion)}\n") {
      system.logic.destNot(witness.measureFalls.conclusion) shouldBe defined
    }
  }
}
