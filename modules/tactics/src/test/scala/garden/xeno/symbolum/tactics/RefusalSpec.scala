package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.Derivation
import garden.xeno.symbolum.logic.LogicError

/**
 * What a caller is told when nothing proves the goal, over the shapes a caller actually writes.
 *
 * The card this comes from is about a refusal that named the last tactic's complaint rather than
 * the first obstacle, and closing it once was not enough: a refusal goes stale when the procedure
 * gets better, and two of the messages here were wrong on 2026-09-10 for exactly that reason. A
 * message that says "rewrite the product" about a product the form now reads sends an author to
 * rewrite it and be refused again.
 *
 * So this is not a test of any one message. It is the assertion that every refusal on this list
 * names something a reader can act on, and it is written out per goal so that a message going stale
 * fails here rather than in somebody's afternoon.
 */
class RefusalSpec extends AnyFlatSpec with Matchers {

  private val prove = Prove.standard
  private val reals = prove.reals

  private def refusalFor(text: String): String = remedyFor(text).message

  private def remedyFor(text: String): Remedy =
    prove(text) match {
      case Right(outcome) => fail(s"$text was proved: ${reals.show(outcome.theorem.conclusion)}")
      case Left(error) => Remedy.of(reals, error)
    }

  "A false ring identity" should "be told apart from one the prover cannot see" in {
    // Both are possible and the message says so rather than choosing. What it must not do is print
    // the two sides in the kernel's notation, which is what it did until 2026-09-08.
    val message = refusalFor("!x:real. x = x + 1")

    message should include("both reached a normal form and the forms differ")
    message should include("1 + x")
    message should not include "BIT1"
  }

  "An identity that needs a denominator" should "name the price rather than the shape" in {
    val message = refusalFor("!x:real. inv x * x = 1")

    message should include("~(x = 0)")
    message should include("Field")
  }

  "A goal with a symbolic denominator" should "name the denominator, in either position" in {
    // The obstacle is looked for in the sides of the relation and not in the proposition, which is
    // what stopped the message being "an inequality is not a variable, a numeral or a sum of
    // those": true of every inequality ever written, and therefore saying nothing.
    //
    // **The witness lost its hypothesis on 2026-09-18 and that is the interesting part.** It was
    // `!x. 0 < x ==> 0 < inv x`, which is `INV_POSITIVE` written out, and the surface refused it:
    // a lemma that IS the goal owes its own antecedent, because `Apply` reads the specialised
    // implication's antecedents as obligations. Since the goal's premises became facts
    // (`docs/adr/0025`) that one is proved, so the goal here is the same claim with nothing
    // assumed, which no premise can reach and which still has the denominator in it.
    refusalFor("!x:real. 0 < inv x") should include("inv x divides by x")

    // Asserted to the end of the sentence, because the end is the half worth having. Naming the
    // denominator says which subterm stopped the read; the clause after it says what would let the
    // goal through and whose price that is, and a message cut back to its first half would leave
    // this suite green while telling a caller nothing to do next.
    val message = refusalFor("!x:real. x / y:real = 1")

    message should include("x / y divides by y")
    message should include(
      "cancelling a symbolic denominator needs it to be non-zero, which is Field's to assume"
    )
  }

  "A goal past the degree the products reach" should "say so, and say how far past" in {
    // Added on 2026-09-10, when the products started reaching degree three and this goal's refusal
    // still said "restate it as a non-negative combination of the hypotheses". True, and an
    // instruction to do something nobody can do: there is no combination of four positives that is
    // their product.
    val message = refusalFor(
      "!w:real x:real y:real. 0 < w /\\ 0 < x /\\ 0 < y /\\ 0 < z:real ==> 0 < w * x * y * z"
    )

    message should include("is a product of 4 unknowns")
    message should include("reach three")
  }

  it should "not fire on an atom that is not a product, which a better message already covers" in {
    // `inv x` is out of reach too, and it is out of reach for a reason that has a name. A degree
    // message there would be both wrong and a step back from one that was right. The hypothesis is
    // gone for the reason the test above gives.
    refusalFor("!x:real. 0 < inv x") should not include "is a product of"
  }

  "A classically valid propositional goal" should "be told what stopped it, not that it is hard" in {
    // Out, not hard, and the two send an author to different places. `p \/ ~p` is a theorem here,
    // by way of the choice operator, and this prover does not reach it: it was built over
    // `Order.standard`, which has never heard of the classical axioms, so the widest propositional
    // procedure it holds is the intuitionistic one and that one refuses the excluded middle.
    //
    // **The message this asserted until 2026-09-18 was "negation", and it stopped being true that
    // day rather than going stale.** While the free procedure was `Minimal` the boundary really was
    // the negation, so naming it was the actionable fact; since the routing moved, `~(p /\ ~p)` is
    // proved here with two negations in it and `p \/ ~p` is refused, so a message about the
    // negation would send an author to remove the one thing that is not the obstacle. What is the
    // obstacle is the caller's configuration, which is why the sentence names it.
    val message = refusalFor("!p:bool. p \\/ ~p")

    message should include("classically valid")
    message should include("this prover has no classical axioms")
    message should not include "negation"
  }

  "A propositional goal with a negation that is intuitionistically provable" should "be proved, at no axiom" in {
    // The other side of the line above and the reason it moved. This is the shape a criterion about
    // the world is made of, and the prover with no classical extension reaches it: the theorem is
    // the same one `Propositional` would produce and it rests on nothing, where that one rests on
    // the choice operator.
    val theorem = prove("!p:bool. ~(p /\\ ~p)").fold(error => fail(error.message), _.theorem)

    theorem.hypotheses shouldBe empty
    Derivation.axiomsOf(theorem) shouldBe empty
  }

  "A propositional goal inside the fragment" should "be proved rather than refused" in {
    // The other side of the same line, here because a refusal test that never checks the accepting
    // case passes just as well against a procedure that refuses everything.
    prove("!p:bool q:bool. p /\\ q ==> p").isRight shouldBe true
  }

  "A claim that is simply false" should "get the plain answer, which is the honest one" in {
    // The default is not a failure of this list. When a goal is inside the fragment, is readable,
    // and does not follow, there is nothing more specific to say and inventing something would be
    // the failure this file is about arriving from the other side.
    //
    // What changed is the move, not the sentence: this was `RestateTheProblem` while the answer was
    // a `NotOfForm`, and restating a goal the procedure has already decided is advice nobody can
    // act on. It is `Settled` now, which is the remedy whose own documentation named "a decision
    // over the linear fragment" before anything could reach it that way.
    refusalFor("!x:real y:real. 0 < x /\\ 0 < y ==> 1 < x * y") should
      include("non-negative combination")
    refusalFor("!x:real. x <= y:real ==> x < y") should include("non-negative combination")

    remedyFor("!x:real. x <= y:real ==> x < y") shouldBe a[Settled]
  }

  /* --------------------------------------- the three a negative check has to tell apart */

  /**
   * Nine hypotheses and a product of two, which the pair round settles at eight and not at nine.
   *
   * The goal is provable and the procedure stops before proving it, which is the only way to reach
   * an exhausted search from this surface. `LinarithLimitsSpec` is where the crossing is measured;
   * here it is a fixture, and it is the shape the consumer this card came from actually met.
   *
   * **The bound moved from zero to one on 2026-09-18**, and the reason is the one the two goals
   * above carry: with `0 < x1 … 0 < x9` the conclusion `0 < x1 * x2` is now **proved**, out of two
   * of the goal's own premises and one library lemma about a product of positives, so it stopped
   * being a search that exhausts and became a proof. At `1 <` the library has no such lemma, the
   * pair round is still what would settle it, and it still runs out: measured the same day,
   * `Linarith.Facts` reached at 76 against 48.
   */
  private val exhausting: String = {
    val variables = (1 to 9).map(index => s"x$index:real").mkString(" ")
    val hypotheses = (1 to 9).map(index => s"1 < x$index").mkString(" /\\ ")
    s"!$variables. $hypotheses ==> 1 < x1 * x2"
  }

  private def standingFor(text: String): Option[LogicError.Standing] =
    prove(text) match {
      case Right(outcome) => fail(s"$text was proved: ${reals.show(outcome.theorem.conclusion)}")
      case Left(error) => TacticError.standing(error)
    }

  "The three refusals" should "be three answers in the type, not three sentences in one" in {
    // The card: a consumer's harness counted every failure as a refutation, so an exhausted search
    // was published as one. It was careful, and being careful was not enough, because what told the
    // two apart was English inside a constructor both of them used.
    //
    // Asserted on the standing rather than on the wording, which is the opposite of the rest of
    // this file and is the point: everywhere above, a message is what a reader acts on; here, a
    // message is what a caller must NOT have to parse.
    standingFor("!x:real. x <= y:real ==> x < y") shouldBe Some(LogicError.Standing.Decided)
    standingFor(exhausting) shouldBe Some(LogicError.Standing.Exhausted)
    standingFor("!x:real. x / y:real = 1") shouldBe Some(LogicError.Standing.Unread)
  }

  it should "be reachable by naming the decision and by nothing else" in {
    // The half that makes it indestructible. Every one of the three is a `Left`, so `isLeft`,
    // `.toOption`, a `Try` and a `catch` all give the same weak and honest answer; only the caller
    // that names the decision gets one. Inattention buying the safe reading is the property the
    // old spelling did not have.
    val answers = Vector("!x:real. x <= y:real ==> x < y", exhausting, "!x:real. x / y:real = 1")
      .map(prove(_))

    answers.foreach(_.isLeft shouldBe true)
    answers.map(TacticError.decided) shouldBe Vector(true, false, false)

    // And a proof is not a decision that something does not follow, which is the outcome a
    // predicate over an `Either` is easiest to get wrong.
    TacticError.decided(prove("!x:real y:real. x < y ==> x <= y")) shouldBe false
  }

  it should "reach RING without RING changing, which is the argument for the case living here" in {
    // `Rewrite.proveEquation` already kept all three apart: `NotEqualTo` where both sides reached a
    // fixed point and differ, `NotNormalised` where the rewriting stopped, `NotOfForm` where it
    // never read the goal. Classifying them is the whole of what RING needed, and it is why the
    // decided case is a `LogicError` rather than a three-way result belonging to `Linarith`.
    standingFor("!x:real. x = x + 1") shouldBe Some(LogicError.Standing.Decided)
  }

  /* ----------------------------------------- a claim that reaches no procedure at all */

  "A claim about the naturals written with the reals' symbols" should "no longer be a refusal" in {
    // **This entry asserted a refusal until `docs/adr/0018` and now asserts a proof, and it is kept
    // rather than deleted because the reversal is the thing worth pinning.** `!n:num. n + 0 = n` is
    // the first claim anybody makes about the naturals. Until 2026-09-12 the whole of the answer
    // was "real and num cannot be the same type": true, naming neither the owner of `+` nor
    // `NUM_ADD`. The repair then was to improve the refusal, on the ground `Peano` wrote down, that
    // a `Notation` maps a symbol to one constant and the reals already own `+`.
    //
    // That ground is gone. A symbol stands for more than one constant and the elaborator picks by
    // the type unification settles, so the claim reads as written and the prover settles it. A
    // reader following `CLAUDE.md`'s sentence about a claim over `num` being one `Ask` now gets
    // what that sentence promises.
    //
    // The list this entry is on is about the shapes a caller actually writes, and this shape is
    // still the first one written; what it demonstrates is no longer a refusal worth improving but
    // a refusal that was removed at its cause. `Counterpart` kept the row for `-`, whose two
    // readings really are different operations, and `CounterpartSpec` is where the surviving half
    // is asserted.
    val page = Ask.of("!n:num. n + 0 = n")

    // `!x:num.` and not `!n:num.` in the first line: a bound name is not part of a term, so the
    // page prints the printer's name and says so on its last line. The claim as the reader wrote it
    // is echoed there, which is what this asserts rather than reaching for the printer's spelling.
    page should startWith("Proved: !x:num. x + 0 = x")
    page should include("as asked: !n:num. n + 0 = n")
    page should not include "real and num cannot be the same type"
  }

  it should "say nothing of the sort about a claim that mentions no natural number" in {
    // The other side of the line, and what keeps the sentence above worth reading when it appears: a
    // type error over the reals gets the reader's own message and nothing invented on top of it.
    val page = Ask.of("!x:real. x + T = x")

    page should startWith("unreadable:")
    page should not include "NUM_ADD"
  }
}
