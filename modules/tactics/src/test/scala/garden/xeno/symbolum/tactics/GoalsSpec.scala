package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The goal at every line of a proof, which the elaborator records for an editor to show
 * (`docs/adr/0076`), for a proof that checked as much as for one that did not.
 *
 * Each goal is asserted against the one before or after it, because a recorder that wrote the same
 * goal at every line would pass any test asking only that a goal is there.
 */
class GoalsSpec extends AnyFlatSpec with Matchers {

  private lazy val elaborate: Elaborate = Elaborate.standard

  private val induction =
    """theorem ADD_ZERO_LEFT : !n:num. 0 + n = n
      |proof
      |  fix n
      |  induction n
      |  case zero:
      |    by rewrite NUM_ADD_ZERO
      |  case succ m ih:
      |    calc 0 + SUC m = SUC (0 + m) by rewrite NUM_ADD_SUC
      |         _ = SUC m by rewrite ih
      |  end
      |qed""".stripMargin

  private def entry(text: String): Elaborate.Entry = {
    val report = elaborate.check(text)
    report.entries should have size 1
    report.entries.head
  }

  "A proof that checked" should "carry the goal each line was given, the line before it acts" in {
    val proved = entry(induction)
    proved.status shouldBe Elaborate.Status.Proved
    def at(line: Int): String = proved.goalAt(line).map(_.text).getOrElse(fail(s"no goal at line $line"))

    // `proof` and `fix n` are given the claim; `induction n` is given it with n fixed.
    at(2) should include("|- !n")
    at(3) shouldBe at(2)
    at(4) should startWith("n : num")
    at(4) should include("|- 0 + n = n")
    // Each branch header shows its own case, with what the header introduced.
    at(5) should include("|- 0 + 0 = 0")
    at(7) should include("m : num")
    at(7) should include("ih : 0 + m = m")
    // A link of a `calc` is given its own claim, the first link's line keeping the step's goal.
    at(8) should include("|- 0 + SUC m = SUC m")
    at(9) should include("|- SUC (0 + m) = SUC m")
    // A line no step starts on shows the step above it.
    at(10) shouldBe at(9)
    at(11) shouldBe at(9)
  }

  it should "have nothing above its first recorded line, and nothing for a definition" in {
    entry(induction).goalAt(1) shouldBe empty
    entry("define TWICE := \\n:num. n + n").goals shouldBe empty
  }

  "A proof that did not check" should "carry its goals too, up to and past the step that failed" in {
    val failed = entry(
      """theorem WRONG : !n:num. n + 1 = n
        |proof
        |  fix n
        |  by arith
        |qed""".stripMargin)
    failed.status shouldBe Elaborate.Status.Incomplete
    failed.goalAt(4).map(_.text) shouldBe failed.problems.head.goal
    failed.goalAt(4).map(_.text).getOrElse("") should include("n : num")
  }

  "The checker's JSON" should "carry the goals of each declaration, and omit them where there are none" in {
    val json = elaborate.check(induction + "\ndefine TWICE := \\n:num. n + n").json
    json should include(""""goals":[{"line":2,"goal":""")
    json.split("\"goals\"").length shouldBe 2
  }
}
