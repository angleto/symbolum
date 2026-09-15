package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The search a session runs from a command line, against the library it actually has.
 *
 * The assertions are about what comes back and never about the wording of a heading. What is worth
 * pinning is that each of the three questions is asked and answered separately, because the reason
 * this exists rather than a single clever reader is that a query cannot be classified without a
 * rule and every available rule is wrong somewhere.
 */
class FindSpec extends AnyFlatSpec with Matchers {

  "A name fragment" should "find the lemmas whose names contain it" in {
    val page = Find.of("TELESCOPES")

    page should include("SUM_TELESCOPES")
    page should include("by name")
  }

  it should "ignore case, because a caller half remembering a name does not remember its case" in {
    Find.of("telescopes") should include("SUM_TELESCOPES")
  }

  "A constant's name" should "find what the library holds about it, which is a different question" in {
    // `Sum` is a constant and not a name fragment of anything: no lemma is called `Sum`. The two
    // headings answer differently and that is the point of having both.
    val page = Find.of("Sum")

    page should include("about the constant")
    page should include("SUM_ZERO")
  }

  "A shape" should "find the lemma whose conclusion matches it under the pattern's own variables" in {
    val page = Find.of("x:real + y:real = y + x")

    page should include("by shape")
    page should include("ADD_SYM")
  }

  it should "find nothing for an instance rather than a shape, which is the useful way round" in {
    // A caller looking for a lemma writes the shape, not an instance. `0 + 1 = 1 + 0` is a true
    // claim and is not a lemma anybody holds, and matching it against commutativity would be the
    // wrong answer to the question that was asked.
    //
    // Annotated since `docs/adr/0018`, and the annotation is carrying weight rather than decorating:
    // `+` stands for two constants and every leaf here is a digit string, so the bare text is
    // refused for an undetermined type and the shape question is never asked. That refusal is
    // correct and is asserted two tests below; what this one is about is what the shape search
    // says when it DOES run, so the query has to be one it can run on.
    val page = Find.of("(0:real) + 1 = 1 + 0")

    page should include("by shape, matching")
    page should include("nothing")
  }

  "A query that is not a proposition" should "say so where the shape answer would have been" in {
    // Not a silent empty section. A reader who asked three questions and is shown two answers
    // cannot tell which of the three was empty and which was never asked, and that distinction is
    // the one this repository is built around.
    val page = Find.of("x:real +")

    page should include("by shape: not a proposition of this theory, so nothing was asked")
  }

  "A query that is a bare identifier" should "be refused by shape rather than matched against everything" in {
    // The defect the first version of this file had, and the reason `byShape` is a branch. A
    // proposition has to be boolean, so `SUM_TELESCOPES` reads as a boolean VARIABLE, and a pattern
    // that is a variable matches every lemma there is: the answer was 126, the whole library,
    // printed where an answer to a question belongs. Nothing was wrong with the matching. What was
    // wrong is that a reader would have read it as a result.
    val page = Find.of("SUM_TELESCOPES")

    page should include("by shape: that reads as a bare variable")
    page should not include "by shape, matching"
    // and the name question still answers, which is the one the caller meant
    page should include("Series.SUM_TELESCOPES")
  }

  "Every heading" should "be printed even when it is empty" in {
    val page = Find.of("ZZZ_NOTHING_IS_CALLED_THIS")

    page should include("by name")
    page should include("about the constant")
    page should include("by shape")
    page.linesIterator.count(_.contains("nothing")) should be >= 2
  }

  "The library the search runs over" should "be the whole chain and not the reals alone" in {
    // The trap the card names: the obvious call takes the library an `Order` can reach, and an
    // `Order` has never heard of `num`. A search that could not find a lemma about the naturals
    // would be a search over a library the caller does not have.
    Find.of("NUM_ADD_SYM") should include("NUM_ADD_SYM")
  }
}
