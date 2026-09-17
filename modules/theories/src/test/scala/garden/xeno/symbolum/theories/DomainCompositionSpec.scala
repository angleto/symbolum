package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Two domains that are not mathematics, composed, and a claim across both accounted for.
 *
 * Two files already show that **one** domain theory can be stated and proved against, and they are
 * worth naming because this is the third and does something neither does. `DomainTheorySpec` has a
 * release gate and measures what a conclusion spends against what was asserted; `DomainSpec` has a
 * consignment rule, costs zero axioms, and lets `Minimal` do the case split, which is automation on
 * a domain rather than bookkeeping.
 *
 * What neither has is the half `23045598` lists fourth: **there was no composition**. Nothing took
 * two independent domain theories and made one, and nothing said what happens when they collide on
 * a name. `Domain.compose` is that, and this file is what says it refuses.
 *
 * == The domain, and why a precondition and an invariant ==
 *
 * A rule about writing software, chosen because it is the shelf Angelo actually works from. Two of
 * them, so that composing is a real operation rather than a ceremony:
 *
 *  - **Calls**, a precondition rule: a caller may invoke an operation only where the operation's
 *    precondition holds at the state it is invoked in, and an operation establishes its
 *    postcondition only where it was invoked legally.
 *  - **States**, an invariant rule: a state reached by a legal step from a state satisfying the
 *    invariant satisfies it too, and the initial state satisfies it.
 *
 * They share the type `state` and nothing else, which is the case composition exists for: two
 * vocabularies written apart, meant to be read together, agreeing on exactly one name.
 *
 * == What the accounting says, which is the whole point ==
 *
 * The claim proved below is that an operation invoked from a reachable state leaves the invariant
 * standing. It is the sentence a person writes in a design document and then never checks. Six
 * axioms are asserted across the two domains and the conclusion spends **three**; the three it does
 * not spend are the ones a reader would most expect it to need, and that is the finding rather than
 * the theorem.
 */
class DomainCompositionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val classical = Classical.standard
  private val foundation = classical.theory

  private val state: Type = TyApp("state", Nil)
  private val operation: Type = TyApp("operation", Nil)

  private def onState(n: Int): Type =
    if (n == 1) Type.fun(state, Type.Bool) else Type.fun(state, Type.fun(state, Type.Bool))

  /* ------------------------------------------------------------------ the two domains */

  /**
   * The precondition rule, as four sentences.
   *
   * `Legal o s` is "invoking `o` in state `s` is allowed"; `Pre o s` is the operation's own
   * precondition at that state; `Steps o s t` is "invoking `o` in `s` reaches `t`". The fourth is
   * the direction that makes it a **rule** rather than an observation, exactly as the release
   * gate's fourth sentence is in `DomainTheorySpec`.
   */
  private val calls: Domain = Domain(
    name = "Calls",
    typeOperators = Vector("state" -> 0, "operation" -> 0),
    constants = Vector(
      "Pre" -> Type.fun(operation, onState(1)),
      "Legal" -> Type.fun(operation, onState(1)),
      "Steps" -> Type.fun(operation, onState(2))
    ),
    axioms = Vector(
      "legal-needs-pre" -> "!o:operation. !s:state. Legal o s ==> Pre o s",
      "pre-permits" -> "!o:operation. !s:state. Pre o s ==> Legal o s",
      "illegal-does-not-step" ->
        "!o:operation. !s:state. !t:state. Steps o s t ==> Legal o s"
    )
  )

  /**
   * The invariant rule, as three sentences, over the same `state` and nothing else of `Calls`.
   *
   * `Inv s` is the invariant; `Reachable s` says the state is reached by some run. The third is
   * what makes an invariant an invariant rather than a property somebody hopes for.
   */
  private val states: Domain = Domain(
    name = "States",
    typeOperators = Vector("state" -> 0),
    constants = Vector(
      "Inv" -> onState(1),
      "Reachable" -> onState(1)
    ),
    axioms = Vector(
      "reachable-holds" -> "!s:state. Reachable s ==> Inv s",
      "initial-reachable" -> "!s:state. Inv s ==> Reachable s",
      "steps-preserve" ->
        "!o:operation. !s:state. !t:state. Inv s /\\ Legal o s /\\ Steps o s t ==> Inv t"
    )
  )

  /* --------------------------------------------------------------- composing them */

  "Two domains sharing one type" should "compose when the sharing is declared" in {
    // `state` is shared on purpose and `operation` is `Calls`' alone. Composing without saying so
    // is refused, which is the next test; saying so is a line in this file rather than an accident
    // of the two agreeing on a word.
    val both = Domain.composeSharing(calls, states, Set("state"))

    both.isRight shouldBe true
    val composed = both.getOrElse(fail("composition refused"))
    composed.constants.map(_._1) should contain allOf ("Pre", "Legal", "Steps", "Inv", "Reachable")
    composed.typeOperators.count(_._1 == "state") shouldBe 1
    composed.axioms should have size 6
  }

  it should "be refused when the sharing is not declared, naming what collided" in {
    // The refusal this file exists for. `docs/adr/0008` leaves a declared constant with no origin
    // and `docs/adr/0019` measured that and let it stand, so two domains declaring one name really
    // are declaring one thing. A silent merge would mean something neither domain said.
    val refused = Domain.compose(calls, states)

    refused.isLeft shouldBe true
    val clash = refused.swap.getOrElse(fail("the collision was not refused"))
    clash.kind shouldBe Domain.Clash.Kind.TypeOperator
    clash.names shouldBe Vector("state")
    clash.message should include("Calls")
    clash.message should include("States")
  }

  it should "refuse a declared sharing the two do not actually agree on" in {
    // Saying two domains share a name does not make it true. `Other` declares `Inv` over an
    // operation rather than a state, so the sharing is a collision wearing a permission slip.
    val other = Domain(
      name = "Other",
      typeOperators = Vector.empty,
      constants = Vector("Inv" -> Type.fun(operation, Type.Bool)),
      axioms = Vector.empty
    )
    val refused = Domain.composeSharing(states, other, Set("Inv"))

    refused.isLeft shouldBe true
    refused.swap.getOrElse(fail("not refused")).kind shouldBe Domain.Clash.Kind.Schema
  }

  /* ------------------------------------------- the refusal a caller actually reads */

  /**
   * Each kind of clash, rendered.
   *
   * The tests above read `kind`, which is what a program branches on, and until 2026-09-17 nothing
   * read `message`, which is what a person is shown. Three of its four branches had therefore never
   * been rendered at all, and the fourth only in the singular: a sentence built by string
   * concatenation that nothing ever builds is a sentence that can name the wrong domain, ask for
   * the wrong remedy, or not compile into prose at all, and every one of those passes a test that
   * stops at `kind`.
   *
   * The pair is the point rather than either half. `kind` decides what a caller can do next and
   * `message` says it in words; a clash whose kind is right and whose words tell the reader to
   * rename a constant that is really a type operator is worse than one that says nothing.
   */
  "A clash on a constant" should "say that a declared constant has no origin, and what to do" in {
    val left = Domain(
      name = "Ledger",
      typeOperators = Vector("entry" -> 0),
      constants = Vector("Cost" -> Type.fun(TyApp("entry", Nil), Type.Bool)),
      axioms = Vector.empty
    )
    val right = Domain(
      name = "Roster",
      typeOperators = Vector("agent" -> 0),
      constants = Vector("Cost" -> Type.fun(TyApp("agent", Nil), Type.Bool)),
      axioms = Vector.empty
    )

    val clash = Domain.compose(left, right).swap.getOrElse(fail("the collision was not refused"))

    clash.kind shouldBe Domain.Clash.Kind.Constant
    clash.names shouldBe Vector("Cost")
    clash.message should include("Ledger")
    clash.message should include("Roster")
    clash.message should include("constant Cost")
    // The remedy, which is the half of the sentence a reader acts on.
    clash.message should include("composeSharing")
  }

  it should "count the names it found, so one collision does not read as several" in {
    // `plural` is the only arithmetic in that sentence and it has one boundary. Two names at once
    // is also the case that says `names` is a list rather than the first thing found.
    val left = Domain(
      name = "Ledger",
      typeOperators = Vector.empty,
      constants = Vector("Cost" -> Type.Bool, "Paid" -> Type.Bool),
      axioms = Vector.empty
    )
    val right = Domain(
      name = "Roster",
      typeOperators = Vector.empty,
      constants = Vector("Cost" -> Type.Bool, "Paid" -> Type.Bool),
      axioms = Vector.empty
    )

    val clash = Domain.compose(left, right).swap.getOrElse(fail("the collision was not refused"))

    clash.names shouldBe Vector("Cost", "Paid")
    clash.message should include("constants Cost, Paid")
    clash.message should not include "constant Cost,"
  }

  "A sharing the two disagree about" should "say which of the two disagreements it is" in {
    // Arity and schema are different refusals with one shape, and the words are where they differ:
    // a type operator shared at two arities, and a constant shared at two types. Both are a caller
    // asserting a sharing that is not there, and a reader has to be told which.
    val states = Domain(
      name = "States",
      typeOperators = Vector("state" -> 0),
      constants = Vector("Inv" -> Type.fun(TyApp("state", Nil), Type.Bool)),
      axioms = Vector.empty
    )
    val indexed = Domain(
      name = "Indexed",
      typeOperators = Vector("state" -> 1),
      constants = Vector.empty,
      axioms = Vector.empty
    )

    val arity = Domain
      .composeSharing(states, indexed, Set("state"))
      .swap
      .getOrElse(fail("the arity disagreement was not refused"))

    arity.kind shouldBe Domain.Clash.Kind.Arity
    arity.message should include("disagree about arity")
    arity.message should include("States")
    arity.message should include("Indexed")

    val other = Domain(
      name = "Other",
      typeOperators = Vector.empty,
      constants = Vector("Inv" -> Type.fun(operation, Type.Bool)),
      axioms = Vector.empty
    )
    val schema = Domain
      .composeSharing(states, other, Set("Inv"))
      .swap
      .getOrElse(fail("the schema disagreement was not refused"))

    schema.kind shouldBe Domain.Clash.Kind.Schema
    schema.message should include("disagree about type")
    schema.message should not include "arity"
  }

  /* ------------------------------------------------------------------ building it */

  private lazy val built: Domain.Built = {
    val composed = Domain
      .composeSharing(calls, states, Set("state"))
      .getOrElse(fail("composition refused"))
    force(Domain.build(foundation, classical.notation, composed))
  }

  private lazy val logic: Logic = force(classical.logic.over(built.theory))
  private lazy val rules: Rules = logic.rules

  private def proposition(text: String): Term =
    force(Parser.proposition(built.theory, classical.notation, text))

  "The composed domain" should "be a theory like any other, beside the chain and not in it" in {
    built.theory.typeOperators.keySet should contain("state")
    built.theory.typeOperators.keySet should contain("operation")
    built.theory.constants.keySet should contain allOf ("Pre", "Legal", "Steps", "Inv", "Reachable")
    built.axioms should have size 6

    // Beside the chain and it must stay there: `docs/adr/0019` decided that two theories
    // axiomatising one name still produce constants that compare equal, so a domain surface keeps
    // domains apart by construction. This one extends the classical foundation and nothing else.
    built.theory.axioms.size shouldBe (foundation.axioms.size + 6)
    Chain.standard.widest.theory.constants.keySet should not contain "Legal"
  }

  /**
   * A claim that does not read at all, which is a third answer and not either of the other two.
   *
   * `settle` over text has two failures before it has a verdict: the text may not parse, and the
   * parsed term may not be a proposition. Both come back as `Refused`, which is the same case a
   * claim that the method could not decide comes back as, so the message is the only thing telling
   * a reader which of the three happened. That is why it is asserted here by its words and not by
   * its case.
   */
  "A claim that does not parse" should "be refused before anything is specialised" in {
    built.settle(classical, "Reachable (s:state) /\\") match {
      case Domain.Verdict.Refused(why) => why should not be empty
      case other => fail(s"text that does not parse must not reach a verdict: $other")
    }
  }

  /* ---------------------------------------------------- the claim, and what it spends */

  /**
   * The claim: an operation that steps from a reachable state leaves the invariant standing.
   *
   * Derived by hand, because nothing here can be asked to find it: `Ring` and `Linarith` decide
   * fragments of the reals and have nothing to say about an arbitrary axiom.
   */
  private lazy val derived: Kernel.Thm = {
    val o = Term.variable("o", operation)
    val s = Term.variable("s", state)
    val t = Term.variable("t", state)

    val antecedent = proposition(
      "Reachable (s:state) /\\ Steps (o:operation) s (t:state)"
    )

    force(for {
      assumed <- LogicError.lift(Kernel.assume(antecedent))
      reachable <- rules.conjElim1(assumed)
      stepped <- rules.conjElim2(assumed)

      // `Reachable s` gives `Inv s`.
      holds <- built
        .axiom("reachable-holds")
        .flatMap(rules.specAll(_, List(s)))
        .flatMap(rules.mp(_, reachable))

      // The step was taken, so it was legal.
      legal <- built
        .axiom("illegal-does-not-step")
        .flatMap(rules.specAll(_, List(o, s, t)))
        .flatMap(rules.mp(_, stepped))

      // And a legal step out of a state satisfying the invariant lands in one that does.
      // `/\` is right-associative, so the axiom's antecedent is `Inv s /\ (Legal o s /\ Steps o s t)`
      // and not `(Inv s /\ Legal o s) /\ Steps o s t`. `Rules.mp` compares antecedents by equality
      // rather than up to associativity, so the wrong nesting comes back as a refusal naming both
      // shapes -- which is the failure this line was written with and is why it is worth a comment.
      tail <- rules.conjIntro(legal, stepped)
      together <- rules.conjIntro(holds, tail)
      preserved <- built
        .axiom("steps-preserve")
        .flatMap(rules.specAll(_, List(o, s, t)))
        .flatMap(rules.mp(_, together))

      result <- rules.disch(antecedent, preserved).flatMap(rules.genAll(_, List(o, s, t)))
    } yield result)
  }

  "A claim across both domains" should "be derivable with nothing left assumed" in {
    derived.hypotheses shouldBe empty
    Show.show(classical.notation, derived.conclusion) should include("Inv")
  }

  it should "spend three of the six axioms, and not the three a reader would expect" in {
    val spending = built.spends(derived)

    spending.ofTheDomain shouldBe Set(
      "reachable-holds",
      "illegal-does-not-step",
      "steps-preserve"
    )

    // The three it does NOT spend are the converses, and that is the finding. `pre-permits` and
    // `legal-needs-pre` tie legality to the precondition and are the pair a reader would assume
    // any claim about a legal call must go through; this one never asks what the precondition
    // says, only that the step happened. `initial-reachable` is the converse of the one axiom it
    // does use.
    spending.unspent shouldBe Set("pre-permits", "legal-needs-pre", "initial-reachable")
  }

  it should "cost no foundational axiom at all, which is what a reader must be told" in {
    // The reasoning is propositional over the domain's own assumptions: no choice, no infinity,
    // none of the reals. A conclusion that had reached outside the domain to get there would be a
    // different kind of claim and a reader should learn which before being asked to believe it.
    built.spends(derived).foundational shouldBe empty
  }

  it should "report what it cost in one line" in {
    val summary = built.spends(derived).summary

    summary should include("3 of 6")
    summary should include("no foundational axiom at all")
  }

  /* --------------------------------------------------- the guard against a vacuous report */

  "The accounting" should "name a foundational axiom when one is actually spent" in {
    // What makes the report above worth anything is that it can say the other thing. A theorem
    // reaching the classical axioms has to come back with them named; a report that always said
    // "no foundational axiom" would pass the test above and mean nothing.
    val excluded = force(classical.excludedMiddleAt(proposition("Inv (s:state)")))
    val spending = built.spends(excluded)

    spending.foundational should not be empty
    spending.ofTheDomain shouldBe empty
    spending.summary should include("foundational")
  }
}
