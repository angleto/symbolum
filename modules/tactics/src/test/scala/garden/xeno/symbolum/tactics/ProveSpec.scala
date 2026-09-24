package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.Real

/**
 * The dispatcher, and the rule that decides which refusal a caller receives.
 *
 * Most of this file is one regression test written five ways, and the five ways are the five goals
 * that the frozen corpus of 2026-09-07 reported as refused with the wrong obstacle named. Those
 * goals are not invented for the test: they are claims from `~/data/WORK/thinktank/incendi` and
 * from the Collatz development, and the note `e5de06b0` holds them with the prediction that was
 * written before they were first run.
 *
 * The measurement they come from is the reason to have them here. Before this dispatcher existed,
 * five goals were refused and none of the five messages named the actual obstacle, while every one
 * of them arrived as a well-formed `RestateTheProblem`. A taxonomy that is right and a content that
 * is wrong is the failure mode hardest to see from inside, because the types all look correct.
 */
class ProveSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val prove = Prove.standard
  private val reals = prove.reals

  /* ------------------------------------------- the corpus cases, by their own ids */

  "A claim written as one ratio against another" should "be decided without being cross-multiplied" in {
    // E02 and E05 of the frozen set: the same claims as E01 and E04, written as the author writes
    // them rather than cross-multiplied. They were refused for most of two days, first with
    // "restate it as an equation" (RING complaining that a strict inequality is not an equation)
    // and then, correctly, by naming the division.
    //
    // What changed on 2026-09-09 is not the message. LINARITH reads a numeral denominator as a
    // rational coefficient now, so a ratio against a ratio is a comparison between two constants
    // and the procedure decides it. Cross-multiplying by hand was the workaround, and a claim
    // checked in a form nobody wrote is a claim checked at one remove from the source.
    val ratios = Vector(
      "3967 / 285489 < 14 / 1000",
      "2 * (249415 / 22049) < 384552 / 14805"
    )

    ratios.foreach { text =>
      withClue(s"$text: ") {
        val theorem = force(prove(text)).theorem

        theorem.hypotheses shouldBe empty
        theorem.conclusion shouldBe force(reals.proposition(text))
      }
    }
  }

  it should "still name the division where the denominator is one nothing here can invert" in {
    // The refusal this file was written for, on a goal that still needs it. `inv 0` is an atom
    // rather than a denominator, which is the rule RING keeps too, so `x / 0` is an unknown and
    // naming that is what a caller can act on.
    prove("!x. 0 < x ==> 0 < x / 0") match {
      case Left(error) => Remedy.of(reals, error).message should include("divides by zero")
      case Right(outcome) => fail(s"expected a refusal, got ${outcome.theorem.conclusion}")
    }
  }

  "An equation that holds off one point" should "be refused by naming what a proof would cost" in {
    // M02 used to be the witness here and is proved since 2026-09-09, because a numeral denominator
    // is a coefficient now. What is left is a SYMBOLIC denominator, and it is the case that
    // separates a refusal a caller can act on from one it cannot: this is not a theorem as written,
    // `Field` proves it by assuming the denominator is not zero, and what comes back here is that
    // condition. Naming the quotient, which is what this refusal used to do, is true of the goal
    // and says nothing about what to do with it.
    //
    // The condition names `x` and the goal was written with `y`, and that is not a defect: a bound
    // variable has no name in a term, so `Field` opened `!y` into a fresh one and `Printer` names
    // it by depth. The proposition is what is asserted here; the letter is the printer's.
    val text = "!y. (2 * y) / y = 2"

    prove(text) match {
      case Left(error) =>
        Remedy.of(reals, error) match {
          case AcceptTheConditions(conditions) => conditions shouldBe Vector("~(x = 0)")
          case other => fail(s"expected the condition to be named, got $other")
        }
      case Right(outcome) => fail(s"expected a refusal, got ${outcome.theorem.conclusion}")
    }
  }

  it should "not be answered with the conditional theorem itself" in {
    // The decision this dispatcher records rather than the message it produces. `Field` settles the
    // goal and `Prove` still refuses, because a caller reading a `Right` as "proved" would carry a
    // hypothesis it never looked at. The theorem is available, one call away, where the sequent
    // shows what it rests on.
    val goal = force(reals.proposition("!y. (2 * y) / y = 2"))

    prove(goal) shouldBe a[Left[?, ?]]
    prove.field.conditions(force(prove.field.prove(goal))).map(reals.show) shouldBe
      List("~(x = 0)")
  }

  "A conjunctive conclusion" should "be proved, conjunct by conjunct" in {
    // E07 and E08: the two goals of the frozen set predicted provable and refused. They are the
    // shape an article writes a measurement in, "above one in 2023 and in 2024", and both were
    // refused because LINARITH opened conjunctive hypotheses and had no route for a conjunctive
    // conclusion.
    val conjunctions = Vector("100 < 120 /\\ 100 < 152", "265 < 331 /\\ 331 < 902")

    conjunctions.foreach { text =>
      withClue(s"$text: ") {
        val theorem = force(prove(text)).theorem

        theorem.hypotheses shouldBe empty
        theorem.conclusion shouldBe force(reals.proposition(text))
      }
    }
  }

  it should "carry hypotheses through to each conjunct" in {
    val text = "!x y. x < y /\\ 0 < x ==> x < y /\\ 0 < y"

    force(prove(text)).theorem.conclusion shouldBe force(reals.proposition(text))
  }

  it should "be refused by naming the conjunct that failed, not the conjunction" in {
    // The repair the conjunctive route must not undo: a caller told that `a /\ b` failed learns
    // nothing, and the two conjuncts usually fail for different reasons or not at all. The ratio
    // this used to pair with the first conjunct is proved since 2026-09-09, so the failing half is
    // now the one denominator nothing here inverts.
    prove("100 < 120 /\\ 0 < 1 / 0") match {
      case Left(error) => Remedy.of(reals, error).message should include("divides by zero")
      case Right(outcome) => fail(s"expected a refusal, got ${outcome.theorem.conclusion}")
    }
  }

  /* --------------------------------------------------------------- the address rule */

  "The address of a goal" should "follow its conclusion, under quantifiers and through hypotheses" in {
    prove.addressOf(force(reals.proposition("!x y. x < y ==> x + 1 < y + 1"))) shouldBe
      Prove.Address.Order

    prove.addressOf(force(reals.proposition("!x. x + x = 2 * x"))) shouldBe
      Prove.Address.Equation

    prove.addressOf(force(reals.proposition("100 < 120 /\\ 100 < 152"))) shouldBe
      Prove.Address.Order
  }

  it should "be nobody's when the shape belongs to no procedure, and say what it would have to be" in {
    // This example has moved twice rather than being rewritten, and both moves were capabilities
    // arriving. It was `!x. ~(x < x)` until 2026-09-10, when a denial became LINARITH's. It was
    // `!p:bool. p ==> p` until 2026-09-11, when the negation-free propositional fragment got an
    // address and that goal became a theorem costing no axiom.
    //
    // What is still nobody's is an equation between things that are not reals and that carries no
    // connective: there is nothing for the arithmetic to normalise and nothing for the fragment to
    // take apart.
    val goal = force(reals.proposition("!p:bool. p = p"))

    prove.addressOf(goal) match {
      case Prove.Address.Nobody(why) => why should include("equation between reals")
      case other => fail(s"expected no address, got $other")
    }
  }

  "The prover a chain deserves" should "reach what the chain holds and the standard one cannot" in {
    // Three things at once, and each was separately unreachable from `Prove.standard`: a goal
    // mentioning `num` cannot even be STATED there, the naturals' lemmas are not in the library an
    // `Order` can reach, and a caller assembling the three pieces by hand gets the second wrong
    // because the obvious call takes that library.
    val chain = garden.xeno.symbolum.theories.Chain.standard
    val wider = force(Prove.construct(chain))

    val goal = force(wider.reals.proposition("!n:num. NUM_LE ZERO n"))

    force(wider(goal)).theorem.hypotheses shouldBe empty
    Prove.standard.reals.proposition("!n:num. NUM_LE ZERO n").isLeft shouldBe true
  }

  it should "reach a POLYMORPHIC lemma at the instance a goal asks for" in {
    // The second half of the same argument, and it needed a change to the matcher rather than to
    // the prover. `FST_PAIR` is `!x:'a. !y:'b. FST (PAIR x y) = x`, which is the goal below at
    // `num`; until 2026-09-12 the library lookup compared `Const("FST", prod('a,'b) -> 'a)` with
    // `Const("FST", prod(num,num) -> num)` by identity and the match failed on the head, so this
    // came back `Unsettled` from a prover holding the lemma that IS it.
    //
    // What the theorem rests on is asserted with it, because "proved" and "proved on nothing
    // assumed" are different claims: the projections are defined by choice, so this one is believed
    // on the choice axiom and on no statement about a number.
    val chain = garden.xeno.symbolum.theories.Chain.standard
    val wider = force(Prove.construct(chain))

    val goal = force(wider.reals.proposition("!x:num. !y:num. FST (PAIR x y) = x"))
    val theorem = force(wider(goal)).theorem

    theorem.conclusion shouldBe goal
    theorem.hypotheses shouldBe empty
    Derivation.axiomsOf(theorem).size shouldBe 1

    // Reported rather than asserted. The count is what the card asked for and it is a fact about
    // how the pair is constructed, not a budget anybody has chosen; a number asserted here goes red
    // on a change to `Product` that is an improvement.
    info(s"proved in ${Derivation.size(theorem)} inferences")
  }

  it should "address a propositional goal to the fragment that costs no axiom" in {
    // The other side of the line above, added the day it moved: `p ==> p` is not nobody's any more.
    val goal = force(reals.proposition("!p:bool. p ==> p"))

    prove.addressOf(goal) shouldBe Prove.Address.Propositional
    force(prove(goal)).theorem.hypotheses shouldBe empty
  }

  it should "reach the rest of the classical fragment where a chain supplies the axioms for it" in {
    // The gap this file named when `Propositional` landed and did not close: the procedure existed
    // and the prover did not route to it, so "proved" and "reachable by asking the prover" were two
    // claims and only the first was true.
    //
    // Peirce's law is the witness because it is exactly the difference. It has no negation in it, so
    // the free fragment reads it; it is not intuitionistically provable, so the free fragment
    // refuses it; and `MinimalSpec` asserts that refusal from the other side.
    val chain = garden.xeno.symbolum.theories.Chain.standard
    val wider = force(Prove.construct(chain))
    val goal = force(wider.reals.proposition("!p:bool. !q:bool. ((p ==> q) ==> p) ==> p"))

    wider.addressOf(goal) shouldBe Prove.Address.Propositional
    val theorem = force(wider(goal)).theorem
    theorem.conclusion shouldBe goal
    theorem.hypotheses shouldBe empty

    // What it costs, asserted rather than described: one axiom, the choice operator, spent at the
    // single classical step of a replay that is otherwise intuitionistic.
    Derivation.axiomsOf(theorem).size shouldBe 1

    // And the prover without a chain behind it still refuses, which is what makes the `Option` a
    // real configuration rather than a degraded one: `Order.standard` has never heard of the
    // classical axioms and a second `Classical` must not be built to fill the gap.
    Prove.standard(force(Prove.standard.reals.proposition("!p:bool. !q:bool. ((p ==> q) ==> p) ==> p"))).isLeft shouldBe true
  }

  it should "address a propositional goal with a negation in it, which used to be nobody's" in {
    // The other half of the widening. `p \\/ ~p` is bare propositional atoms and a negation, so the
    // free fragment turns it away by naming the negation — the right answer while that fragment was
    // the only propositional procedure there was, and a goal being told to remove a negation by a
    // system that can settle it once it is not.
    val chain = garden.xeno.symbolum.theories.Chain.standard
    val wider = force(Prove.construct(chain))
    val goal = force(wider.reals.proposition("!p:bool. p \\/ ~p"))

    wider.addressOf(goal) shouldBe Prove.Address.Propositional
    force(wider(goal)).theorem.hypotheses shouldBe empty
  }

  it should "prove a negated goal the intuitionistic calculus reaches, at no axiom at all" in {
    // The capability the routing of 2026-09-18 exists for, and the one the two tests above do not
    // cover between them: `p \\/ ~p` needs the classical axiom and Peirce's law has no negation, so
    // both of them are answered by `Propositional` and neither says what a goal with a negation in
    // it that is intuitionistically provable costs.
    //
    // It used to cost one. `Minimal` refused this by naming the negation, the goal fell through to
    // the classical procedure, and the theorem came back resting on `SELECT` — the same term, at a
    // price the argument does not need. Over every propositional formula on two atoms within the
    // node bound `PropositionalRouteSpec` enumerates, the goals in exactly this position are the
    // ones that spec counts as gained and pins.
    //
    // **Seen failing against the tree that carries it**, which is what makes it a guard rather than
    // a description: run on 2026-09-18 with `Prove.scala` reverted to `6554615` and this file left
    // as it is, the assertion below reported the axiom set as
    // `Set(! \x. ! \y. x y ==> x (select x))` where it wanted none — the choice axiom, named by the
    // failure rather than by this comment. The two cases in `RefusalSpec` went red in the same run.
    val chain = garden.xeno.symbolum.theories.Chain.standard
    val wider = force(Prove.construct(chain))
    val goal = force(wider.reals.proposition("!p:bool. ~(p /\\ ~p)"))

    wider.addressOf(goal) shouldBe Prove.Address.Propositional

    val theorem = force(wider(goal)).theorem
    theorem.conclusion shouldBe goal
    theorem.hypotheses shouldBe empty
    Derivation.axiomsOf(theorem) shouldBe empty

    // And the same goal through the procedure it used to reach, so that the zero above is read as a
    // price and not as an absence: the classical route proves it too, and charges for it.
    val classically = force(Propositional(chain.classical).prove(goal))
    classically.conclusion shouldBe goal
    Derivation.axiomsOf(classically).size shouldBe 1
  }

  it should "keep an arithmetic denial with the procedure whose message is worth more" in {
    // The narrowness that makes the widening safe, asserted so it cannot drift. `~(x = 0)` has an
    // arithmetic atom, so it is not the propositional address however propositional its shape looks,
    // and the refusal a caller gets is still the one that names what a proof would cost.
    val chain = garden.xeno.symbolum.theories.Chain.standard
    val wider = force(Prove.construct(chain))

    wider.addressOf(force(wider.reals.proposition("!x:real. ~(x = 0)"))) should not be Prove.Address.Propositional
  }

  "A defined constant at numerals" should "be evaluated by the prover, which is what `Ask` asks" in {
    // Step 5 of the card `Value` was built for, and the half that was separately missing. `Value`
    // has proved `NUM_DIV 17 5 = 3` since 2026-09-18 and **nothing routed a goal to it**: asked of
    // the prover, that theorem came back "restate it as an equation between reals; this one is
    // between something else", which is true of the shape and is advice to rewrite a claim with
    // nothing wrong with it. Measured before the address existed, on all five constants.
    //
    // All five are here rather than a witness, because the address is one test and the table is
    // five rows: a route that worked for the quotient and not for the floor would be an address
    // that reads `Value.Routes` and a reading that does not, which is exactly what `Value.reads`
    // exists to prevent.
    val chain = garden.xeno.symbolum.theories.Chain.standard
    val wider = force(Prove.construct(chain))

    val values = Vector(
      "NUM_DIV 17 5 = 3" -> 2,
      "NUM_MOD 17 5 = 2" -> 2,
      "NUM_GCD 12 18 = 6" -> 2,
      // A floor takes a real, so its bounds are settled over the ordered field and it carries the
      // reals' fifteen and the sixteenth through the Archimedean property. `ValueSpec` asserts that
      // split per row; what it means here is that the address is one thing and the price is the
      // constant's, not the address's.
      "NUM_FLOOR (7 / 2) = 3" -> 18,
      "NUM_CEIL (7 / 2) = 4" -> 18
    )

    values.foreach { case (text, axioms) =>
      withClue(s"$text: ") {
        val goal = force(wider.reals.proposition(text))
        wider.addressOf(goal) shouldBe Prove.Address.Evaluation

        val theorem = force(wider(goal)).theorem
        theorem.conclusion shouldBe goal
        theorem.hypotheses shouldBe empty
        Derivation.axiomsOf(theorem).size shouldBe axioms
      }
    }
  }

  it should "answer a wrong value with the value, which is a fact about the claim" in {
    // What the refusal is worth, and it is worth more than a refusal usually is. Every other
    // refusal on this surface names a fragment; this one names the number. An author who wrote
    // `= 4` learns the quotient is 3, which settles their claim rather than redirecting them.
    val chain = garden.xeno.symbolum.theories.Chain.standard
    val wider = force(Prove.construct(chain))

    wider("NUM_DIV 17 5 = 4") match {
      case Right(outcome) => fail(s"expected a refusal, got ${wider.reals.show(outcome.theorem.conclusion)}")
      case Left(error) =>
        val message = Remedy.of(wider.reals, error).message
        message should include("NUM_DIV 17 5 = 3")
        message should include("what this evaluates to")
    }
  }

  it should "leave a general claim about the same constant where it was" in {
    // The narrowness that makes the address safe, asserted so it cannot drift. What decides the
    // address is that the left side is an application this table can READ, not that its head is a
    // constant the table knows: `NUM_DIV (m * n) n = m` names `NUM_DIV` and has nothing to
    // evaluate, so it keeps whatever refusal it had. Without this line the address would swallow
    // every lemma about the quotient and answer each one "not a numeral".
    val chain = garden.xeno.symbolum.theories.Chain.standard
    val wider = force(Prove.construct(chain))
    val general = force(wider.reals.proposition("!m:num. !n:num. NUM_DIV (m * n) n = m"))

    wider.addressOf(general) should not be Prove.Address.Evaluation
  }

  it should "refuse an unaddressed goal as itself, not as a procedure's complaint" in {
    // The point of the whole file: a goal nobody can take is told so, rather than being handed
    // whichever procedure was asked last and reporting that procedure's shape requirement.
    prove("!p:bool. p = p") match {
      case Left(error) => Remedy.of(reals, error) shouldBe a[RestateTheProblem]
      case Right(outcome) => fail(s"expected a refusal, got ${outcome.theorem.conclusion}")
    }
  }

  it should "address a denial to the procedure that has a route for one" in {
    // The capability the two examples above moved for. `!x. ~(x < x)` is `LT_IRREFLEXIVE`, an axiom
    // of this theory, and it was refused by the reader before the procedure that decides it was
    // ever asked.
    prove.addressOf(force(reals.proposition("!x. ~(x < x)"))) shouldBe Prove.Address.Order
    prove("!x:real. 0 < x ==> ~(x = 0)").isRight shouldBe true
  }

  /* ------------------------------------------------------------------- the text path */

  "Text that does not read" should "be a repair of the text, never a procedure's refusal" in {
    prove("!x. x <") match {
      case Left(error) => Remedy.of(reals, error) shouldBe a[RepairTheText]
      case Right(outcome) => fail(s"expected a refusal, got ${outcome.theorem.conclusion}")
    }
  }

  /* ------------------------------------------ what the theory-aware rendering buys */

  "A refusal rendered with the theory" should "print arithmetic the way the reader wrote it" in {
    // The same refusal twice, once with the theory and once without. The second is what every
    // caller got before, and it is correct and unreadable: the kernel's printer knows the
    // connectives and not the arithmetic, so a numeral arrives as its binary encoding.
    //
    // The goal is a false identity rather than the quotient above, and deliberately: a refusal that
    // names an obstacle renders the term through the theory on the way in, so it prints the same
    // either way and this assertion would hold without the theory doing anything. This one carries
    // two normal forms and nothing else, which is the case the theory-aware mapping exists for.
    val goal = force(reals.proposition("!n. 2 * n + 1 = 3 * n"))
    val refusal = prove(goal).left.getOrElse(fail("expected a refusal"))

    Remedy.of(reals, refusal).message should not include "BIT"
    Remedy.of(refusal).message should include("BIT")
  }
}
