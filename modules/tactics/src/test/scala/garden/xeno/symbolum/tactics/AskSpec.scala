package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.theories.Chain

/**
 * The command line, which is the smallest thing that removes a compilation from a question.
 *
 * Every measurement in the session that built this began by writing a file into `scratch/`,
 * compiling it against the build's classpath and running it, to ask something `Cost` answers in one
 * call. The card that asked for a request surface said the useful version was small: take a
 * statement, give back the report as data, without the caller compiling.
 */
class AskSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  "A claim the theory can state" should "come back as the page Cost renders" in {
    val page = Ask.of("!x:real. x + 0 = x")

    page should startWith("Proved: !x:real. x + 0 = x")
    page should include("inferences over 1 axioms")
    page should include("believed on: !x:real. x + 0 = x")
  }

  it should "reach the naturals, which is what asking over the chain buys" in {
    // `Cost.standard` decides over the reals alone and cannot state this at all. What the command
    // line holds is `Cost.construct(chain)`, so a claim about `num` is a claim it can take.
    val page = Ask.of("!x:num. !y:num. NUM_ADD x y = NUM_ADD y x")

    page should startWith("Proved:")
    page should include("inferences over 2 axioms")
  }

  "A claim already read" should "be answered from the term, without going through the text" in {
    // The overload a caller holding a `Term` wants, which nothing reached. Asserted against the
    // text route rather than against a fixed page, so it stays true when the printer changes.
    val claim = force(Chain.standard.widest.proposition("!x:real. x + 0 = x"))

    Ask.page(claim) shouldBe Ask.of("!x:real. x + 0 = x")
  }

  it should "answer a term that is not a claim rather than throwing at it" in {
    // Written first as `should startWith("refused:")`, on the reading that a term of type `real` is
    // not a claim and `Cost` refuses it. The run said otherwise: it comes back `Unsettled`, with
    // the reader's own "restate it as an inequality, an equation between reals, a denial of one, or
    // a conjunction". So `cost.of` and `cost.render` both succeed on it and the `refused:` branch
    // under the `fold` is not what a non-proposition reaches.
    //
    // **What does reach that branch is not known**, and saying so is the record rather than
    // contriving an input until something matches: `page` takes a term that has already been read,
    // which is what removes most of the ways a report fails to build. It is the one statement in
    // this file nothing here exercises, and a reader looking for the gap should look there.
    val notAClaim = force(Chain.standard.widest.term("x:real + 0"))
    val page = Ask.page(notAClaim)

    page should startWith("Unsettled:")
    page should include("restate it as")
  }

  "The command line itself" should "answer an empty invocation with how to use it" in {
    // `main` is what `sbt "tactics/runMain ... Ask"` reaches and nothing exercised it. Both arms:
    // no claim at all, and a claim that is answered.
    Ask.claimsIn(Vector.empty) shouldBe empty
    noException should be thrownBy Ask.main(Array.empty)
    noException should be thrownBy Ask.main(Array("!x:real.", "x", "+", "0", "=", "x"))
  }

  "A claim the theory cannot state" should "say so in its place, and not stop the others" in {
    // A caller asking three things wants the two that read.
    val report = Ask.report(Vector("!x:real. x + 0 = x", "nonsense here", "!x:real. x * 1 = x"))
    val lines = report.linesIterator.toVector

    lines.count(_.startsWith("Proved:")) shouldBe 2
    lines.count(_.startsWith("unreadable:")) shouldBe 1
    report should include("unreadable: nonsense here")
  }

  "A command line" should "be put back together and split where the caller meant" in {
    // `sbt` hands the arguments over already split on whitespace and with the shell's quotes gone,
    // so a quoted claim arrives as `'!x:real.` and a parse error about a type variable. The pieces
    // are joined and `|` separates one claim from the next; `;` is unavailable because `sbt` reads
    // it as the end of a command.
    Ask.claimsIn(Vector("!x:real.", "x", "+", "0", "=", "x")) shouldBe Vector("!x:real. x + 0 = x")

    Ask.claimsIn(Vector("!x:real.", "x", "+", "0", "=", "x", "|", "!x:real.", "x", "*", "1", "=", "x")) shouldBe
      Vector("!x:real. x + 0 = x", "!x:real. x * 1 = x")

    Ask.claimsIn(Vector.empty) shouldBe empty
    Ask.claimsIn(Vector("|", " ", "|")) shouldBe empty
  }

  "A claim whose binders the caller named" should "come back beside the caller's own text" in {
    // `docs/adr/0002` puts no name in `Term.Abs`, so a report answers under the printer's names:
    // somebody who asks about `budget` is told about `x`. That is not a printing defect and the
    // printer cannot repair it, and it matters because a formal statement has to be checkable
    // against the informal claim it translates by a reader who did not write it. The repair is a
    // string this object already held and used to discard.
    val page = Ask.of("!budget:real. 0 < budget ==> budget < 2 * budget")

    page should startWith("Proved: !x:real. 0 < x ==> x < 2 * x")
    page should include("as asked: !budget:real. 0 < budget ==> budget < 2 * budget")
  }

  it should "say nothing where the report already prints the claim as it was written" in {
    // The other side of it. A line printed under every report is a line nobody reads, and the case
    // this one exists for is exactly the case where the two texts differ.
    Ask.of("!x:real. x + 0 = x") should not include "as asked:"
  }

  "The axioms a claim is believed on" should "be shown read back, now that they read back" in {
    // This was the other way round until 2026-09-12 and the history is the assertion. `Cost.render`
    // reads every proposition back through `Readback`; the choice axiom quantifies over a type
    // variable, the printer wrote one as a bare name, and the reader refused it, so this page said
    // "believed on, and it does not read back" for an axiom every development holding the naturals
    // carries. Reading it leniently was the repair for the page and not for the cause.
    //
    // The cause is repaired: a type variable prints as `'a`, which is what the parser reads. The
    // lenient branch in `Cost.page` stays, because "shown and named" is still the right answer for a
    // statement that cannot be read, and `CostSpec` exercises it on a term that cannot.
    val page = Ask.of("!x:num. !y:num. NUM_ADD x y = NUM_ADD y x")

    page should include("believed on: !x:'a -> bool. !y:'a. x y ==> x (select x)")
    page should not include "does not read back"
    page should include("rests on:")
  }
}
