package garden.xeno.symbolum.lsp

import garden.xeno.symbolum.tactics.Elaborate
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * What the server says about a document, asserted as a function of the text.
 *
 * Each answer is asserted beside the input that would make it vacuous: a hover that always answered
 * would pass a test asking for one, so a line no declaration spans is asked too, and a diagnostic
 * list is asserted empty only on a text where a sibling assertion shows it is not empty for a
 * small change.
 */
class AnalysisSpec extends AnyFlatSpec with Matchers {

  private lazy val elaborate: Elaborate = Elaborate.standard

  private val proved =
    """theorem ZERO_RIGHT : !n:num. n + 0 = n
      |proof
      |  fix n
      |  show n + 0 = n by arith
      |qed""".stripMargin

  private val wrong = proved.replace("ZERO_RIGHT", "WRONG").replace("n + 0 = n", "n + 1 = n")

  private def check(text: String, beside: Map[String, String] = Map.empty, published: Map[String, String] = Map.empty) =
    Analysis.check(elaborate, "Mine", text, published.get, beside.get)

  "A document that checks" should "have no diagnostic, where the same proof of a false claim has one" in {
    Analysis.diagnostics(check(proved)) shouldBe empty
    val found = Analysis.diagnostics(check(wrong))
    found should have size 1
    found.head.line shouldBe 4
    found.head.severity shouldBe Analysis.Severity.Error
    // The refusal, then the goal at that point, as the checker prints them.
    found.head.message should include("n : num")
    found.head.message should include("|- n + 1 = n")
  }

  it should "show the goal of the line under the cursor, and the price on the declaration's line" in {
    val checked = check(proved)
    val head = Analysis.hover(checked, 1).getOrElse(fail("no hover on the theorem's line"))
    head should startWith("theorem ZERO_RIGHT: proved")
    head should include("inferences: ")
    val step = Analysis.hover(checked, 4).getOrElse(fail("no hover on the `show` line"))
    step should include("n : num")
    step should include("|- n + 0 = n")
    step should not include "inferences: "
    // `fix n` is given the goal before n is fixed, which the line after it is not.
    Analysis.hover(checked, 3).getOrElse("") should not include "n : num"
    Analysis.hover(checked, 5) shouldBe Analysis.hover(checked, 4)
  }

  it should "answer nothing on a line no declaration spans" in {
    val checked = check(s"$proved\n\n-- between the two\n\ndefine TWICE := \\n:num. n + n")
    Analysis.hover(checked, 2) should not be empty
    Analysis.hover(checked, 7) shouldBe empty
    Analysis.hover(checked, 9).getOrElse("") should startWith("define TWICE: defined")
  }

  it should "show the goal at a line of a proof that did not check, where its problem is" in {
    val hover = Analysis.hover(check(wrong), 4).getOrElse(fail("no hover on the failing line"))
    hover should startWith("theorem WRONG: incomplete")
    hover should include("|- n + 1 = n")
  }

  "The outline" should "span each declaration over its lines, a proof to its qed" in {
    val outline = Analysis.outline(check(s"$proved\n\ndefine TWICE := \\n:num. n + n"))
    outline.map(o => (o.name, o.from, o.to)) shouldBe Vector(("ZERO_RIGHT", 1, 5), ("TWICE", 7, 7))
    outline.map(_.status) shouldBe Vector(Elaborate.Status.Proved, Elaborate.Status.Defined)
  }

  "A line that does not read" should "be a diagnostic on that line" in {
    val found = Analysis.diagnostics(check("theorem T : 0 + 0 = 0:num by arith\nnonsense here"))
    found.map(_.line) shouldBe Vector(2)
  }

  "An import" should "read the document beside, and say so on its line when it names none" in {
    val twice = "define TWICE := \\n:num. n + n\ntheorem TWICE_ZERO : TWICE 0 = 0\nproof\n  rewrite TWICE\n  by arith\nqed"
    val importing = "import A\ntheorem AGAIN : TWICE 0 = 0 by exact TWICE_ZERO"
    Analysis.diagnostics(check(importing, beside = Map("A" -> twice))) shouldBe empty
    val alone = Analysis.diagnostics(check(importing))
    alone.map(_.line) should contain(1)
  }

  it should "read a published document before a file of that name beside it, with a warning on the line" in {
    val twice = "define TWICE := \\n:num. n + n\ntheorem TWICE_ZERO : TWICE 0 = 0\nproof\n  rewrite TWICE\n  by arith\nqed"
    val importing = "import A\ntheorem AGAIN : TWICE 0 = 0 by exact TWICE_ZERO"
    val both = Analysis.diagnostics(check(importing, beside = Map("A" -> "theorem OTHER : 0 = 0:num by arith"), published = Map("A" -> twice)))
    both.map(d => (d.line, d.severity)) shouldBe Vector((1, Analysis.Severity.Warning))
    both.head.message should include("A is a published document")
    Analysis.diagnostics(check(importing, published = Map("A" -> twice))) shouldBe empty
  }

  "A datatype and a function by recursion" should "span their lines in the outline, and show what they are on a hover" in {
    val text = "datatype tree = LEAF\n  | NODE tree num tree\n\ndefine SIZE : tree -> num\n  SIZE LEAF = 0\n  SIZE (NODE l x r) = SIZE l + 1 + SIZE r\nend"
    val checked = check(text)
    Analysis.diagnostics(checked) shouldBe empty
    Analysis.outline(checked).map(o => (o.name, o.kind, o.from, o.to)) shouldBe
      Vector(("tree", Elaborate.Kind.Datatype, 1, 2), ("SIZE", Elaborate.Kind.Definition, 4, 7))
    val datatype = Analysis.hover(checked, 2).getOrElse(fail("no hover on the constructors' line"))
    datatype should startWith("datatype tree: defined")
    datatype should include("tree = LEAF | NODE tree num tree")
    datatype should not include "|- "
    Analysis.hover(checked, 6).getOrElse("") should startWith("define SIZE: defined")
    Analysis.hover(checked, 3) shouldBe empty
  }
}
