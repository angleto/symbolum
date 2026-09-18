package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The one condition four renderers share, checked where it is written rather than four times over.
 *
 * `EssaySpec`, `CostSpec`, `LedgerSpec` and `ArgumentSpec` each take both directions through their
 * own page, which is the assertion that the page reaches this and is not a copy of it. What is left
 * over for here is the part none of them can exercise: the cases the docstring makes a claim about
 * and no caller happens to produce.
 */
class ProseSpec extends AnyFlatSpec with Matchers {

  "A count of one" should "take the noun as it was given" in {
    Prose.count(1, "axiom") shouldBe "1 axiom"
    Prose.count(1, "named fact") shouldBe "1 named fact"
    Prose.count(1, "idle citation") shouldBe "1 idle citation"
  }

  // The case a reader of the condition does not picture, and the one no page above reliably
  // produces: `if (howMany == 1)` is read as "the singular where there is one" and zero is not one.
  // English pluralises it, and a renderer that took the other reading would print "0 axiom".
  "A count of zero" should "take the plural, which is what English does" in {
    Prose.count(0, "axiom") shouldBe "0 axioms"
    Prose.count(0, "point") shouldBe "0 points"
  }

  "Any other count" should "take the plural" in {
    Prose.count(2, "inference") shouldBe "2 inferences"
    Prose.count(77, "inference") shouldBe "77 inferences"
  }

  // The limit the docstring states, asserted rather than only described, so that a caller reading
  // the test knows the shape of what this refuses to do before routing an irregular noun through
  // it. It is a fact about the helper and not a defect: a noun with an irregular plural wants its
  // two forms written out at the call site.
  "A noun whose plural is not an appended s" should "come out wrong, and none is sent here" in {
    Prose.count(2, "hypothesis") shouldBe "2 hypothesiss"
  }

  // Negative counts have no caller and are not refused: every number this is reached with is a
  // `size`, a `length` or a `count`. Pinned so that the behaviour is a reading rather than a
  // discovery if one ever arrives.
  "A negative count" should "take the plural rather than being refused" in {
    Prose.count(-1, "axiom") shouldBe "-1 axioms"
  }
}
