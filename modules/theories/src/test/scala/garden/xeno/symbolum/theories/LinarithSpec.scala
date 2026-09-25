package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Linear arithmetic: what it decides, and where it stops.
 *
 * The goals below are grouped by what they need, because the procedure changed shape on
 * 2026-09-05 and the groups are what the change was for. The first group needs a plain sum of the
 * hypotheses and was decided before it; the second needs a multiplier, a constant, or both, and
 * was refused; the third is the fragment's edge and is refused still.
 *
 * The two sections after those are the later widenings and their own edges: the products of the
 * hypotheses, which reach an atom no combination of the originals reaches, and the denominators the
 * linear form reads, which are the constant ones and no others.
 */
class LinarithSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val linarith = Linarith.standard
  private val reals = linarith.reals

  private def proves(text: String): Kernel.Thm = {
    val theorem = force(linarith.prove(text))
    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe force(reals.proposition(text))
    theorem
  }

  /** What a caller is told about a goal this refuses, which is asserted rather than only its kind. */
  private def refusalFor(text: String): String =
    linarith
      .prove(text)
      .fold(_.message, theorem => fail(s"expected a refusal, got ${reals.show(theorem.conclusion)}"))

  "Linear arithmetic" should "prove that adding one preserves an inequality" in {
    proves("!x:real y:real. x < y ==> x + 1 < y + 1")
  }

  it should "prove transitivity, which is also an axiom" in {
    proves("!x:real y:real z:real. x < y /\\ y < z ==> x < z")
  }

  it should "add two inequalities" in {
    proves("!x:real y:real z:real w:real. x < y /\\ z < w ==> x + z < y + w")
  }

  it should "add the same term to both sides" in {
    proves("!x:real y:real z:real. x < y ==> x + z < y + z")
  }

  it should "prove a goal where the hypotheses need rearranging to match" in {
    proves("!x:real y:real. x < y ==> x - y < 0")
  }

  it should "use only the hypotheses it needs" in {
    proves("!x:real y:real z:real w:real. x < y /\\ z < w ==> x + 1 < y + 1")
  }

  it should "prove a goal whose hypotheses are nested the other way" in {
    // The antecedent is assumed as written and taken apart along its own conjunctions. A version
    // of this file flattened it, rebuilt it right-nested, and returned a theorem about that other
    // conjunction as a success; `proves` compares the conclusion with the goal, and this is the
    // goal that comparison needed to see.
    proves("!x:real y:real z:real w:real. (x < y /\\ y < z) /\\ z < w ==> x < w")
  }

  "Linear arithmetic" should "refuse a goal that does not follow" in {
    // `DoesNotFollow` and not `NotOfForm`, which is what all three of these were until the case
    // existed. `NotOfForm` is also what a goal this procedure cannot READ comes back as, so the
    // two were one constructor with a different sentence inside, and a caller could tell them
    // apart only by parsing English.
    linarith.prove("!x:real y:real. x < y ==> y < x").left.map(_.getClass) shouldBe
      Left(classOf[DoesNotFollow])
  }

  it should "refuse a goal that is false however the hypotheses are weighed" in {
    // No non-negative combination of `y - x` is `x - y`, and one hypothesis cannot contradict
    // itself, so both halves of the search decline.
    linarith.prove("!x:real y:real. y < x ==> x < y").left.map(_.getClass) shouldBe
      Left(classOf[DoesNotFollow])
  }

  it should "refuse a goal whose difference is nothing at all" in {
    // `x < x` has the zero difference, and the empty combination adds up to zero, so a search
    // that took the goal as a target without this case would certify it.
    linarith.prove("!x:real. x < x").left.map(_.getClass) shouldBe Left(classOf[DoesNotFollow])
  }

  it should "not call it decided when it never read the statement" in {
    // The guard that makes the case above worth having. `LinearFact.of` cannot fail: a hypothesis
    // it does not recognise becomes a strict fact over an atom nobody else mentions, which is right
    // for a procedure that ends in a theorem and wrong for one that ends in an answer, and its own
    // documentation says so. `p ==> p` therefore reaches the certificate search as a question about
    // an unknown, finds no combination, and would report a DECISION that a tautology does not
    // follow. It is the one way this case could mislead and it is the reason the standing is earned
    // by the reading rather than by the search.
    val tautology = linarith.prove("!p:bool. p ==> p")

    tautology.isLeft shouldBe true
    LogicError.decided(tautology) shouldBe false
    tautology.left.map(_.standing) shouldBe Left(LogicError.Standing.Unread)

    // And the same on the other side of the turnstile: hypotheses it reads, a conclusion it does
    // not. Nothing was asked about `q`, so nothing was decided about it.
    val unreadable = linarith.prove("!x:real q:bool. 0 < x ==> q")

    unreadable.isLeft shouldBe true
    LogicError.decided(unreadable) shouldBe false
  }

  it should "say in the type which standing it ended in" in {
    // Read together rather than one by one, because what the card is about is that they were one
    // answer. A caller that takes `isLeft` for "does not follow" gets the same `true` from all
    // three, which is the weak and honest reading; the decision is reachable only by naming it.
    val decided = linarith.prove("!x:real. x < x")
    val unread = linarith.prove("!p:bool. p ==> p")

    Vector(decided, unread).foreach(_.isLeft shouldBe true)

    decided.left.map(_.standing) shouldBe Left(LogicError.Standing.Decided)
    unread.left.map(_.standing) shouldBe Left(LogicError.Standing.Unread)
    LogicError.decided(decided) shouldBe true
    LogicError.decided(unread) shouldBe false

    // A proof is not a decision that something does not follow, which is the fourth outcome and the
    // one a predicate over an `Either` is easiest to get wrong.
    LogicError.decided(linarith.prove("!x:real y:real. x < y ==> x < y")) shouldBe false
  }

  it should "decide a denial it cannot force, and say so about the denial" in {
    // `byDenial` assumes `x = 0` and asks the search for falsity, so a decision arrives naming
    // falsity as its goal, and falsity is a term the caller never wrote. What finished is a search
    // about the denial.
    linarith.prove("!x:real. ~(x = 0)") match {
      case Left(DoesNotFollow(goal, _)) =>
        goal should not be reals.logic.falsity
        reals.show(goal) should include("~")
      case other => fail(s"expected a decision about the denial, got $other")
    }
  }

  /* --------------------------------------------- which signature the text is read in */

  "A name the signature does not hold" should "become a variable rather than a refusal" in {
    // What a caller meets when it hands the `String` entry point a text written in its OWN
    // development's notation. The text is parsed against `reals.theory`, which for a link in the
    // chain is below the development doing the calling: `Limit.construct` builds its Linarith over
    // `magnitude.order`, before `converges` and `lim` exist. A letter-initial name that signature
    // does not hold is well-typed as a free variable, so the text does not fail, and what is
    // proved is a claim about a variable.
    val text = "!x:real. selectivity < x ==> selectivity < x + 1"

    // The line that keeps the rest of this from being vacuous, and the only one that separates the
    // two readings. If anything ever declares this name into the standard theory, the case below
    // stops being the case it is named for, and this is what says so rather than a silent pass.
    reals.theory.constants.exists { case (name, _) => name == "selectivity" } shouldBe false

    val theorem = force(linarith.prove(text))
    theorem.hypotheses shouldBe empty

    // And it comes back printing as the text that was written, because a variable is printed no
    // differently from a constant. `proves` above compares the conclusion against
    // `reals.proposition(text)`, which reads the name the same way, so neither the printer nor
    // that comparison can catch this; only the constant check can.
    reals.show(theorem.conclusion) shouldBe text
  }

  "A multiplier" should "close a goal that a plain sum cannot" in {
    // The goal that named the limitation in three documents. The certificate is one half, cleared
    // to a multiplier of one on the hypothesis and a scale of two on the goal, and the scale comes
    // off through `Order.cancelPositive`.
    proves("!x:real y:real. 2 * x < 2 * y ==> x < y")
  }

  it should "work at a coefficient that is not a small one" in {
    proves("!x:real y:real. 1000 * x < 1000 * y ==> x < y")
    proves("!x:real y:real. x < y ==> 7 * x < 7 * y")
  }

  it should "combine with a constant when the goal needs both" in {
    proves("!x:real y:real. 2 * x < 2 * y ==> x < y + 1")
  }

  "A constant" should "close a goal that has no hypothesis to lean on" in {
    // `0 < 1` reaching the search at last: the goal is a positive constant, and the combination
    // that makes it uses no hypothesis at all.
    proves("!x:real. x < x + 1")
    proves("!x:real y:real. x < y ==> x < y + 1")
  }

  "Hypotheses that cannot all hold" should "prove whatever they are asked" in {
    // An implication with impossible premises is true whatever it concludes, and the combination
    // that shows the premises impossible is the same kind of certificate aimed elsewhere. This is
    // the half of the decision procedure that has nothing to do with the goal.
    proves("!x:real y:real. x < y /\\ y < x ==> x < x")
    proves("!x:real y:real z:real w:real. x < y /\\ y < x ==> z < w")
  }

  "The non-strict order" should "be read on both sides of the goal" in {
    proves("!x:real. x <= x")
    proves("!x:real y:real. x <= y ==> x <= y + 1")
    proves("!x:real y:real z:real. x <= y /\\ y <= z ==> x <= z")
    proves("!x:real y:real. x <= y ==> x < y + 1")
    proves("!x:real y:real. 2 * x <= 2 * y ==> x <= y")
    proves("!x:real y:real. 0 <= x /\\ 0 <= y ==> 0 <= x + y")
  }

  it should "mix with the strict order in either direction" in {
    proves("!x:real y:real z:real. x <= y /\\ y < z ==> x < z")
    proves("!x:real y:real z:real. x < y /\\ y <= z ==> x < z")
    proves("!x:real y:real. x < y ==> x <= y")
  }

  it should "not make a strict conclusion out of hypotheses that are not" in {
    // The one thing the certificate has to get right about strictness, and it is what the second
    // phase of the search is for: a combination that weighs only non-strict facts proves the
    // non-strict goal and nothing more. `x <= y ==> x < y` is false at `x = y`.
    //
    // `DoesNotFollow`, because all three have premises and a conclusion this procedure reads and
    // all three were searched to the end. What a caller is told is that they do not follow, which
    // is the answer; the near miss is that the second phase could have manufactured strictness and
    // did not, and a refusal saying only "wrong shape" would have hidden which of the two happened.
    linarith.prove("!x:real y:real. x <= y ==> x < y").left.map(_.getClass) shouldBe
      Left(classOf[DoesNotFollow])
    linarith.prove("!x:real y:real. x = y ==> x < y").left.map(_.getClass) shouldBe
      Left(classOf[DoesNotFollow])
    linarith.prove("!x:real y:real. 0 <= x /\\ 0 <= y ==> 0 < x + y").left.map(_.getClass) shouldBe
      Left(classOf[DoesNotFollow])
  }

  "An equality hypothesis" should "be weighed with either sign" in {
    // What the multiplier multiplies is zero, so the sign is free. The second and third need it
    // negative, which is the case a search over non-negative multipliers has to be told about.
    proves("!x:real y:real. x = y ==> x <= y")
    proves("!x:real y:real. x = y ==> y <= x")
    proves("!x:real y:real. 2 * x = y ==> y < 2 * x + 1")
    proves("!x:real y:real z:real. x = y /\\ y < z ==> x < z")
    proves("!x:real y:real z:real. x <= y /\\ y = z ==> x <= z")
  }

  it should "be the shape a corpus of measurements is made of" in {
    // The article this was built for says things like: the index is this ratio, the ratio is at
    // least this and at most that, so the quantity is bounded. Nothing here is deep; what matters
    // is that a definition and a bound can appear as premises at all.
    proves("!a:real b:real. a = 53 * b /\\ 0 < b ==> a <= 60 * b")
    proves("!v:real i:real j:real. 0 < v - i - j ==> j < v - i")
  }

  it should "be weighed when its left side occurs inside its right" in {
    // Found on 2026-09-25 by the work on deciding a series, and not by reading: `x = c * x` was
    // weighed by rewriting with it, and a rewrite put `c * x` for the `x` inside `c * x` as well,
    // so the product it handed `RING` was not zero and the refusal named neither the goal nor the
    // equation. The content is linear in the atoms `x` and `c * x`, which the last line shows by
    // naming the right side: that one was proved all along.
    proves("!c:real x:real. x = c * x ==> ~(0 < x - c * x)")
    proves("!c:real x:real. 0 < (1 - c) * x ==> x = c * x ==> 0 < 0")
    proves("!c:real x:real. 0 < (1 - c) * x ==> ~(x = c * x)")
    proves("!c:real x:real y:real. y = c * x ==> x = y ==> ~(0 < (1 - c) * x)")
  }

  it should "reach a product with the negated goal when its left side occurs inside its right" in {
    // The second case the same card named: `x = c * x` with `c < 1` makes `x` zero, which needs
    // `(1 - c) * x` and so a product of the hypothesis `c < 1` with the negated goal `0 < x`.
    proves("!c:real x:real. c < 1 ==> 0 <= x ==> x = c * x ==> x <= 0")
  }

  /* ------------------------------------------------- the products of the hypotheses */

  "A product of two unknowns" should "be reached by multiplying the hypotheses" in {
    // The border of the fragment until 2026-09-09, and it was an axiom the whole time: the linear
    // form reads `x * y` as an atom, and no combination of forms over `x` and `y` reaches an atom
    // neither mentions. Multiplying the pair puts it into a hypothesis.
    proves("!x:real y:real. 0 < x /\\ 0 < y ==> 0 < x * y")
    proves("!x:real y:real. 0 < x /\\ 0 <= y ==> 0 <= x * y")
  }

  it should "be reached whichever way round the goal writes it" in {
    // A form's atoms are keys in an untrusted search and never reach the kernel, so the factors of
    // a manufactured product are sorted and `x * y` and `y * x` are one key. Without that the move
    // would work or not according to how the goal happened to be typed.
    proves("!x:real y:real. 0 < x /\\ 0 < y ==> 0 < y * x")
  }

  it should "include a hypothesis multiplied by itself" in {
    // One hypothesis has no pair, and a square is the case this move exists for as much as any.
    proves("!x:real. 0 < x ==> 0 < x * x")
  }

  it should "reach a conclusion the pair does not state, not only the pair itself" in {
    // The point of handing the products to the ordinary search rather than matching the goal
    // against them: `(x - 1) * (y - 1) > 0` gives `x * y > x + y - 1`, and the rest is linear.
    proves("!x:real y:real. 1 < x /\\ 1 < y ==> 1 < x * y")
    proves("!x:real y:real z:real. x < y /\\ 0 < z ==> x * z < y * z")
  }

  it should "be reached between two non-strict facts, since 2026-09-10" in {
    // This assertion read the other way round until the lemma it was waiting for arrived. `LT_MUL`
    // multiplies two strict facts and `Order.MUL_NONNEG` a strict by a non-strict; the pair of
    // non-strict ones was refused because `0 <= x ==> 0 <= y ==> 0 <= x * y` was not among the
    // order facts, which is `Order.MUL_NONNEG_BOTH` now. Nothing in the procedure moved for it.
    proves("!x:real y:real. 0 <= x /\\ 0 <= y ==> 0 <= x * y")

    // The square, which is the shape with one hypothesis, and the mixed pair, which has to keep
    // working: the lemma is chosen by the kind of the first side and choosing it wrongly would be
    // invisible here without both.
    proves("!x:real. 0 <= x ==> 0 <= x * x")
    proves("!x:real y:real. 0 < x /\\ 0 <= y ==> 0 <= x * y")
  }

  it should "still not turn two non-strict facts into a strict conclusion" in {
    // The boundary the new lemma must not cross. Both goals are false at the point where the
    // hypotheses are tight, and a lemma stated one character out would prove both.
    linarith.prove("!x:real y:real. 0 <= x /\\ 0 <= y ==> 0 < x * y").isLeft shouldBe true
    linarith.prove("!x:real. 0 <= x ==> 0 < x * x").isLeft shouldBe true
  }

  it should "prove nothing false, since a manufactured fact is still checked" in {
    // The assertion that makes the whole move safe to have. A product is a theorem like any other
    // and the ring step still checks the combination against the goal, so the worst a useless or
    // wrong product can do is fail to help. Both of these are false at some point of the region
    // their hypotheses allow.
    linarith.prove("!x:real y:real. 0 < x /\\ 0 < y ==> 1 < x * y").isLeft shouldBe true
    linarith.prove("!x:real. 0 < x ==> x < x * x").isLeft shouldBe true
  }

  /* ------------------------------------------------- the denominators the form reads */

  "A quotient by a numeral" should "be a coefficient when a hypothesis is what carries it" in {
    // The invariant: a fact's coefficients are rational, and a rational fact is weighed by a whole
    // multiplier like any other. Here the multiplier is two, the sum it builds is
    // `2 * (y / 2 - x / 2)`, and what shows the denominator to the kernel is the ring step that
    // checks that sum against `y - x`. Reading `x / 2` as an atom instead would leave the goal's
    // `x` in a column nothing reaches, so this is the assertion that the widening reached the
    // hypothesis side and not only the goal side.
    proves("!x:real y:real. x / 2 < y / 2 ==> x < y")
  }

  it should "be a coefficient in the conclusion, where the scale comes back off" in {
    // The same widening from the other side, and it needs the cancellation rather than the
    // multiplier: the certificate here wants one half, which is cleared to a whole multiplier and
    // a scale of two on the goal, and `Order.cancelPositive` takes the scale off. Nothing in the
    // procedure divides and nothing in it writes `inv`.
    proves("!x:real y:real. x < y ==> x / 2 < y / 2")
    proves("!x:real. 0 < x ==> 0 < x / 2")
  }

  "A symbolic denominator" should "be refused by name, with the condition it would cost" in {
    // What the linear form reads as a denominator is a constant, and `y` does not become one by
    // anything looking harder: whether `inv y` is anything at all needs `~(y = 0)`, which is
    // `Field`'s to charge for. The refusal has to say that and has to describe the denominators
    // the reader does take, since a caller told only that the divisor is not a numeral would read
    // `x / (2 / 3)`, whose divisor the reader takes, as refused too.
    val message = refusalFor("!x:real y:real. 0 < x ==> 0 < x / y")

    message should include("x / y divides by y")
    message should include("an inverse of a non-zero numeral or a quotient of two of those")
    message should include("cancelling a symbolic denominator needs it to be non-zero")
    message should include("Field")
  }

  it should "be told apart from a division by zero, which no hypothesis repairs" in {
    // Two refusals rather than one, because the two repairs are different: a symbolic denominator
    // is a condition somebody can assume, and `x / 0` is not. `inv 0` is an atom this theory says
    // nothing about, so `x / 0` is an unknown rather than a scaled `x`, and a message offering
    // `~(0 = 0)` would send a caller after a hypothesis that is false.
    val message = refusalFor("!x:real. 0 < x ==> 0 < x / 0")

    message should include("x / 0 divides by zero")
    message should include("inv 0 is an atom rather than a denominator")
  }

  "The search" should "be untrusted, so a wrong linear form only loses a proof" in {
    // The form of a term nobody taught it about is an atom, which is why an opaque subterm does
    // not break anything: it cancels with itself or the ring step refuses.
    proves("!x:real y:real. inv x < inv y ==> inv x + 1 < inv y + 1")
  }

  it should "report a certificate it found and could not rebuild as that, and never as a decision" in {
    // A true goal whose certificate needs the product of `c < 1` with the goal's denial, so it is
    // found by an escalation, and at `57a2276d` the kernel refused the rebuilding of the
    // contradiction it rests on. The escalation then reported the refusal from before it:
    // `DoesNotFollow`, a decision against a goal whose proof the search had just found. Seen red
    // that way on 2026-09-25 with the repair taken away at that one site, which is perturbation 1
    // of `tools/verify/perturb-certificate-not-rebuilt.sh`, and recorded in `LogicError.NotRebuilt`.
    //
    // Either answer below is right, and which one arrives depends on whether the rebuilding has
    // been repaired, which is a separate change: a theorem, or the refusal that says the search
    // found one and names the goal. What must never arrive is a refusal carrying `Decided`.
    val goal = "!c:real x:real. c < 1 ==> 0 <= x ==> x = c * x ==> x <= 0"
    linarith.prove(goal) match {
      case Right(theorem) => theorem.conclusion shouldBe force(reals.proposition(goal))
      case Left(refusal) =>
        withClue(s"${refusal.message}\n") {
          LogicError.decided(Left(refusal)) shouldBe false
          refusal match {
            case NotRebuilt(named, procedure, _) =>
              procedure shouldBe "LINARITH"
              reals.show(named) should endWith("<= 0")
            case other => fail(s"expected the certificate's refusal, got $other")
          }
        }
    }
  }

  "A proof" should "say which premises it rests on" in {
    // The upper bound a sequent carries becomes exact here, because the certificate names its own
    // support. Told that four premises give a conclusion, the useful answer is which two did.
    // Written with free variables rather than quantified, which is the shape a claim about named
    // quantities has, and which is also what lets the premises come back in their own words: a
    // bound variable has no name in a term, so a quantified goal comes back with the ones the
    // procedure opened it into.
    val support = force(
      linarith.support("x:real < y:real /\\ z:real < w:real /\\ y:real < z:real ==> x < z")
    )

    support.hypotheses.map { case (hypothesis, weight) => (reals.show(hypothesis), weight) } shouldBe
      Vector(("x < y", BigInt(1)), ("y < z", BigInt(1)))

    support.squares shouldBe empty
  }

  it should "name the multiplier, not only the premise" in {
    val support = force(linarith.support("2 * x:real < 2 * y:real ==> x < y"))

    support.hypotheses.map { case (hypothesis, weight) => (reals.show(hypothesis), weight) } shouldBe
      Vector(("2 * x < 2 * y", BigInt(1)))
  }

  it should "refuse to name a support for a goal it cannot prove" in {
    linarith.support("x:real < y:real ==> y < x").isLeft shouldBe true
  }

  /**
   * A proof that spent a square reports it beside the premises, which is `docs/adr/0032` point 4.
   *
   * Three things are asserted and each is a different way the design could have failed, which is
   * why they are one test rather than three: this file's other support tests are all over goals
   * that spend no square, so every one of them would pass over a `support` that dropped squares
   * on the floor or refused any goal that used one.
   *
   * **It does not refuse.** The certificate is rebuilt over the hypotheses, and a goal proved by
   * a square has none over those alone; before the squares were carried into the rebuild this
   * refused a goal `prove` had just proved, with the message saying exactly that.
   *
   * **The square is reported.** Dropped, the answer here would be an empty `hypotheses` and
   * nothing else, which is also the honest answer for a goal that needed none of its premises.
   * The two readings are "nothing was needed" and "something was needed and is not shown", and
   * the second field is the whole of what tells them apart.
   *
   * **And it is not among the premises.** The goal has one hypothesis and it is genuinely spent,
   * so this is the case that separates "beside" from "among": a `support` that appended the
   * square to the same vector would come back with two entries here and the caller would have no
   * way to tell which of them it wrote.
   */
  it should "report a completed square beside the premises rather than among them" in {
    // `0 <= y` is a real premise and is needed: without it the claim is false at `y = -1, x = 0`.
    // The square is over the atom `x * x`, which nothing in the goal's hypotheses gives and which
    // no restatement of them would. It comes back as `0 <= x * x` and not `0 <= (x + 0) * (x + 0)`
    // because the completion's shift is zero here and `squares` specialises `SQUARE_NONNEG` at the
    // bare base when it is, which is the shape a reader checks the lemma against.
    val support = force(linarith.support("0 <= y:real ==> 0 <= x:real * x + y"))

    support.hypotheses.map { case (hypothesis, weight) => (reals.show(hypothesis), weight) } shouldBe
      Vector(("0 <= y", BigInt(1)))

    support.squares should have length 1
    support.squares.map { case (square, weight) => (reals.show(square), weight) } shouldBe
      Vector(("0 <= x * x", BigInt(1)))
  }

  /* ---------------------------------------------------------------- how far a form goes */

  private def facts(texts: Vector[String]): Vector[LinearFact] =
    texts.map(text => force(LinearFact.relation(reals, force(reals.proposition(text)))))

  private def form(text: String): LinearForm =
    force(LinearForm.of(reals, force(reals.term(text))))

  "The largest a form can be" should "be the supremum, exactly, and not a value nearby" in {
    // The question that turns proposing a premise into solving for one. Each of these is checked by
    // hand: the region is small enough to see, and a rational answer that is right to the last part
    // is what the caller needs, because the bound it offers an author is that number.
    val region = facts(Vector("0 < x:real", "x:real + y:real <= 2"))

    Region.largest(region, form("y:real")) shouldBe Farkas.Extreme.At(Rational.of(2))
    Region.largest(region, form("x:real + y:real")) shouldBe Farkas.Extreme.At(Rational.of(2))

    // The one the fractional case exists for: `0 < x`, `3y < 2` and `x <= y` bound `x` by two
    // thirds, which is not a numeral anybody wrote and is exactly the threshold a missing premise
    // has to name.
    val thirds = facts(Vector("0 < x:real", "3 * y:real < 2", "x:real <= y:real"))
    Region.largest(thirds, form("x:real")) shouldBe Farkas.Extreme.At(Rational.of(2, 3))
    Region.largest(thirds, form("3 * x:real")) shouldBe Farkas.Extreme.At(Rational.of(2))
  }

  it should "say when there is no largest value, rather than returning one" in {
    // A form that grows without limit on the region is the case where no bound of that shape can be
    // imposed at all, and folding it into an answer would make a caller propose a premise that
    // closes nothing.
    val region = facts(Vector("0 < x:real", "x:real + y:real <= 2"))

    Region.largest(region, form("x:real")) shouldBe Farkas.Extreme.Unbounded
    Region.largest(region, form("0 - y:real")) shouldBe Farkas.Extreme.Unbounded
  }

  it should "answer about the closure, which is narrower than it sounds" in {
    // `{0 < x, x < 0}` has no point at all, and this says the largest `x` is nought rather than
    // `Infeasible`: the encoding weakens a strict inequality to a margin the search may set to
    // zero, so what is maximised over is the closure. The one caller only asks about a region it
    // has already established is non-empty, and `satisfying` is the reader for the open question.
    val empty = facts(Vector("0 < x:real", "x:real < 0"))

    Region.largest(empty, form("x:real")) shouldBe Farkas.Extreme.At(Rational.zero)
    Region.satisfying(empty) shouldBe None

    // And a region empty without any strictness in it does come back infeasible.
    val closed = facts(Vector("1 <= x:real", "x:real <= 0"))
    Region.largest(closed, form("x:real")) shouldBe Farkas.Extreme.Infeasible
  }

  "A goal with no hypotheses at all" should "be settled by completing its own square" in {
    // The acceptance criterion of Mycelium card `bacfaba5`, and the two statements are
    // `algebra_sqineq_at2malt1` and `mathd_algebra_113` of miniF2F, which `docs/adr/0029` names as
    // the two the corpus was waiting on. Both are one square of a linear form and NEITHER HAS A
    // HYPOTHESIS, which is why no degree of products ever reached them: the fact pool is built from
    // the hypotheses, and an empty pool has no products at any degree. `docs/adr/0032` is the
    // record, and `Linarith.squares` is what it decided.
    linarith.prove("!a:real. a * (2 - a) <= 1").isRight shouldBe true
    linarith.prove("!x:real. x * x - 14 * x + 3 >= 7 * 7 - 14 * 7 + 3").isRight shouldBe true
  }

  it should "still refuse those same statements made false, which is what the square is not" in {
    // The control the assertion above needs and would pass without. A source that manufactured
    // facts carelessly would prove these too, and a reader shown only the two successes cannot
    // tell a procedure that completed a square from one that stopped checking. Both are the
    // statements above moved by one, so the only difference is the truth.
    linarith.prove("!a:real. a * (2 - a) <= 0").isLeft shouldBe true
    linarith.prove("!x:real. x * x + 1 <= 0").isLeft shouldBe true
  }

  it should "cost no axiom the reals do not already carry" in {
    // What the square is worth depends on it being free: `Order.SQUARE_NONNEG` is derived, so a
    // goal settled through it rests on the reals and on nothing else. Asserted as a subset of the
    // theory's own axioms rather than as a count, because a count moves when the library does and
    // says nothing about WHICH.
    val theorem = linarith
      .prove("!a:real. a * (2 - a) <= 1")
      .fold(error => fail(error.message), identity)

    Derivation.axiomsOf(theorem).subsetOf(reals.theory.axioms.toSet) shouldBe true
  }

  "The theory" should "still assert only the axioms `Real.Axioms` lists" in {
    reals.theory.axioms.length shouldBe Real.Axioms.length
  }
}
