package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Linarith, Order, Real}

/**
 * The text a session is shown, and the guarantee that it is the term that was proved.
 *
 * What is asserted here is the guarantee rather than the rendering: that what comes back reads as
 * the same term, and that a term which would not survive the round trip is refused instead of
 * shown. The rendering itself is `Show`'s and is pinned where the notation is.
 */
class ReadbackSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val order = Order.standard
  private val reals = order.reals
  private val linarith = Linarith.standard

  "A term" should "come back as text that reads as the same term" in {
    val term = force(reals.term("x + 2 * y"))
    val text = force(Readback.of(reals, term))

    text shouldBe "x + 2 * y"
    force(reals.term(text)) shouldBe term
  }

  it should "survive the shapes the notation makes ambiguous" in {
    // `-` is infix subtraction and prefix negation at once. These are the two readings, and each
    // has to come back as itself rather than as the other.
    Vector("-x * y", "-(x * y)", "x - y", "x + -y", "-(x - y)").foreach { source =>
      val term = force(reals.term(source))

      force(reals.term(force(Readback.of(reals, term)))) shouldBe term
    }
  }

  "A theorem" should "be shown with every part read back" in {
    val theorem = force(order.zeroLessOne)
    val shown = force(Readback.of(reals, theorem))

    shown shouldBe "|- 0 < 1"
  }

  it should "put its hypotheses on the left of the turnstile" in {
    val assumed = force(LogicError.lift(Kernel.assume(force(reals.proposition("0 < x")))))
    val shown = force(Readback.of(reals, assumed))

    shown shouldBe "0 < x |- 0 < x"
    // Every part carries the guarantee separately, which is what taking the theorem apart buys:
    // the parser reads propositions and no reader here reads a sequent.
    shown.split(" \\|- ").foreach { part =>
      force(reals.proposition(part)) shouldBe force(reals.proposition(part))
    }
  }

  "A report" should "put the formalisation before the verdict" in {
    // A reader who stops after the second line has read the thing that can be wrong. A verdict
    // above the formalisation would be a claim about a statement nobody has checked.
    val goal = force(reals.proposition("!x y. x < y ==> x < y + 1"))
    val proved = TacticError.lift(linarith.prove(goal))
    val report = force(Readback.report(reals, "y is above x, so it is below x plus one", goal, proved))

    val lines = report.split("\n").toVector
    lines(0) should startWith("source:")
    lines(1) should startWith("formalised:")
    lines(2) should startWith("proved:")
  }

  it should "carry a next step when the goal was not proved" in {
    val goal = force(reals.proposition("!x y. x <= y ==> x < y"))
    val refused = TacticError.lift(linarith.prove(goal))
    val report = force(Readback.report(reals, "x is at most y, so it is below y", goal, refused))

    refused.isLeft shouldBe true
    report should include("not proved:")
    report should include("next:")
  }

  it should "still show the formalisation when the goal was not proved" in {
    // The case that matters for a session: a refusal is when a person most needs to see what was
    // actually asked, because the likeliest cause is that it was not what they meant.
    val goal = force(reals.proposition("!x. 0 < x * x"))
    val refused = TacticError.lift(linarith.prove(goal))
    val report = force(Readback.report(reals, "a square is positive", goal, refused))

    report should include(s"formalised: ${reals.show(goal)}")
  }

  "A term the reader cannot read back" should "be refused rather than shown" in {
    // A variable whose NAME the lexer cannot read, which is the case that is left. The point is the
    // shape of the answer: a refusal that `Remedy` reports as a defect here, never a string handed
    // over with the disagreement inside it.
    //
    // It was `TyVar("a")` until 2026-09-12 and that stopped being an example of anything: a type
    // variable prints as `'a` now, the parser reads it, and `Theory.checkType` accepts it, because
    // naming a type variable asserts nothing about a theory. A type **operator** nobody declared is
    // no example either, and finding that out is worth the line: the parser checks a constant's
    // type against the theory and nothing checks a free variable's, so `x:widget` reads back as
    // itself. `%0` is not contrived; `Matching` names the variables it opens binders with that way,
    // and `%` starts no name the lexer accepts, which is exactly why it chose that prefix.
    val foreign: Term = Term.variable("%0", Real.realType)

    Readback.of(reals, foreign) match {
      case Left(error: NotLegible) => Remedy.of(error) shouldBe a[ReportADefect]
      case Left(other) => fail(s"expected an illegible term, got $other")
      case Right(text) => fail(s"expected a refusal, got $text")
    }
  }
}
