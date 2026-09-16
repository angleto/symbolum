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
 */
class CollatzSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard

  private lazy val system: Collatz =
    Collatz
      .construct(
        chain.forward,
        chain.naturals,
        chain.peano,
        chain.successor,
        chain.forward.theory,
        chain.forward.notation)
      .fold(error => fail(s"the system does not build: ${error.message}"), identity)

  private def fact(name: String): Kernel.Thm =
    system.fact(name).fold(error => fail(error.message), identity)

  private def rules: Rules = system.logic.rules

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
      Collatz.Name, Collatz.Counted, Collatz.Potential, Collatz.Marked, Collatz.TailFree
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
}
