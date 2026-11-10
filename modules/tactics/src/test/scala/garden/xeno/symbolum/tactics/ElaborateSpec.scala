package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * What checking a proof document guarantees, each property stated with the input that would make it vacuous.
 *
 * The properties are the ones `docs/adr/0070` puts the language under:
 *
 *  - **nothing false is proved**, through any route the elaborator offers, and in particular not
 *    through the assumption a failed `have` leaves behind so the steps after it can be checked;
 *  - **a failure is local**: it marks its own declaration and leaves every other one checked, and a
 *    declaration that cites a failed one is told so by name;
 *  - **every refusal says where and what**: the line, the reason, and the goal at that step.
 *
 * The positive cases are not decoration. A checker that refused everything would pass every
 * assertion here that something is refused, so each refusal sits beside a proof of the same shape
 * that goes through.
 */
class ElaborateSpec extends AnyFlatSpec with Matchers {
  import Elaborate.{Status, Report}

  private lazy val elaborate: Elaborate = Elaborate.standard

  private def check(text: String): Report = elaborate.check(text.stripMargin)

  private def status(report: Report, name: String): Status =
    report.entries.find(_.name == name).map(_.status).getOrElse(fail(s"no declaration $name in ${report.render}"))

  private def messages(report: Report, name: String): Vector[String] =
    report.entries.find(_.name == name).toVector.flatMap(_.problems.map(_.reason))

  /* ------------------------------------------------------------------ nothing false */

  "A failed have" should "not let the assumption it leaves behind prove the claim" in {
    val report = check(
      """theorem FALSE_VIA_HOLE : !x:real. x = x + 1
        |proof
        |  fix x
        |  have h : x = x + 1 by ring
        |  by exact h
        |qed
        |theorem TRUE_VIA_HAVE : !x:real. x + 0 = x
        |proof
        |  fix x
        |  have h : x + 0 = x by ring
        |  by exact h
        |qed""")

    status(report, "FALSE_VIA_HOLE") shouldBe Status.Incomplete
    // One problem, the one at the `have`: the assumption the steps after it were checked against is
    // not reported again as a hypothesis left over, which is the cascade this guards.
    messages(report, "FALSE_VIA_HOLE") should have size 1
    report.entries.head.problems.head.line shouldBe 4
    // The control: the same shape over a true claim is proved, so the refusal is about the claim.
    status(report, "TRUE_VIA_HAVE") shouldBe Status.Proved
  }

  it should "still have the steps after it checked" in {
    val report = check(
      """theorem TWO_PROBLEMS : !x:real. x = x
        |proof
        |  fix x
        |  have h : x = x + 1 by ring
        |  have k : x = x + 2 by ring
        |  by ring
        |qed""")
    report.entries.head.problems.map(_.line) shouldBe Vector(4, 5)
  }

  "A proved theorem" should "be exactly the claim as written, and rest on no hypothesis" in {
    val report = check("""theorem SQ : !x:real. 0 <= x * x by auto""")
    val entry = report.entries.head
    entry.status shouldBe Status.Proved
    val theorem = entry.theorem.getOrElse(fail("no theorem on a proved entry"))
    theorem.hypotheses shouldBe empty
    entry.statement shouldBe "!x:real. 0 <= x * x"
    report.ok shouldBe true
  }

  /* ------------------------------------------------------------------ local failures */

  "A failure" should "leave the declarations after it checked, and a citation of it told why" in {
    val report = check(
      """theorem BROKEN : !x:real. x = x + 1 by ring
        |theorem CITES : !x:real. x = x + 1 by exact BROKEN
        |theorem UNRELATED : !x:real. x + 0 = x by ring""")
    status(report, "BROKEN") shouldBe Status.Incomplete
    messages(report, "CITES").head should include("BROKEN is declared on line 1 and its proof did not check")
    status(report, "UNRELATED") shouldBe Status.Proved
    report.ok shouldBe false
  }

  it should "be reported with the goal as it stood at that step" in {
    val report = check(
      """theorem WRONG_SHOW : !x:real. x + 0 = x
        |proof
        |  fix x
        |  show x = x + 0 by ring
        |qed""")
    val problem = report.entries.head.problems.head
    problem.line shouldBe 4
    problem.reason should include("`show` names x = x + 0, and the goal is x + 0 = x")
    problem.goal shouldBe Some("x : real\n|- x + 0 = x")
  }

  it should "report steps written after the goal is closed rather than drop them" in {
    val report = check(
      """theorem AFTER : !x:real. x + 0 = x
        |proof
        |  fix x
        |  by ring
        |  by ring
        |qed""")
    report.entries.head.problems.map(_.line) shouldBe Vector(5)
  }

  "A name" should "be looked up in the proof, then the document, then the library, and its absence named" in {
    val report = check(
      """theorem LOCAL : !n:num. n + 0 = n by exact NUM_ADD_ZERO
        |theorem MISSING : !n:num. n + 0 = n by exact NO_SUCH_LEMMA""")
    status(report, "LOCAL") shouldBe Status.Proved
    messages(report, "MISSING").head should include("no fact named NO_SUCH_LEMMA")
  }

  it should "be declared once in a document" in {
    val report = check(
      """theorem T : !x:real. x = x by ring
        |theorem T : !x:real. x + 0 = x by ring""")
    report.entries.map(_.status) shouldBe Vector(Status.Proved, Status.Refused)
  }

  /* ------------------------------------------------------------------ the steps */

  "Induction" should "name its cases and refuse a case the principle does not have" in {
    val report = check(
      """theorem GOOD : !n:num. 0 + n = n
        |proof
        |  fix n
        |  induction n
        |  case zero:
        |    by rewrite NUM_ADD_ZERO
        |  case succ m ih:
        |    calc 0 + SUC m = SUC (0 + m) by rewrite NUM_ADD_SUC
        |         _ = SUC m by rewrite ih
        |  end
        |qed
        |theorem BAD : !n:num. n + 0 = n
        |proof
        |  fix n
        |  induction n
        |  case zero:
        |    by arith
        |  case step m ih:
        |    by arith from ih
        |  end
        |qed""")
    status(report, "GOOD") shouldBe Status.Proved
    messages(report, "BAD").head should include("no case `step` here; the cases are zero (or 1), succ (or 2)")
  }

  it should "refuse a variable a fact of the proof mentions, and say how to carry it" in {
    val report = check(
      """theorem MENTIONED : !n:num. n = n ==> n + 0 = n
        |proof
        |  fix n
        |  assume h
        |  induction n
        |  case zero:
        |    by arith
        |  case succ m ih:
        |    by arith
        |  end
        |qed""")
    messages(report, "MENTIONED").head should include("the facts h mention n")
  }

  it should "take a principle named with `using`, with numbered cases" in {
    val report = check(
      """theorem STRONG : !n:num. 0 <= n
        |proof
        |  fix n
        |  induction n using NUM_STRONG_INDUCTION
        |  case 1 k hk:
        |    by arith
        |  end
        |qed""")
    status(report, "STRONG") shouldBe Status.Proved
  }

  "A fixed variable" should "keep the type it was fixed at, with no annotation in the text" in {
    val report = check(
      """theorem TYPED : !n:num. n <= n + 1
        |proof
        |  fix n
        |  have h : n + 0 = n by exact NUM_ADD_ZERO
        |  by arith
        |qed""")
    status(report, "TYPED") shouldBe Status.Proved
  }

  "The other steps" should "each prove what they are for" in {
    val report = check(
      """theorem WITNESS : ?n:num. n + 1 = 1
        |proof
        |  witness 0
        |  by arith
        |qed
        |theorem OBTAIN : (?n:num. n + 1 = 1) ==> (?m:num. m = 0)
        |proof
        |  assume e
        |  obtain k hk from e
        |  witness k
        |  by arith from hk
        |qed
        |theorem SPLIT : !x:real. x + 0 = x /\ 0 + x = x
        |proof
        |  fix x
        |  split
        |  case left:
        |    by ring
        |  case right:
        |    by ring
        |  end
        |qed
        |theorem EXCLUDED : !p:bool. p \/ ~p
        |proof
        |  fix p
        |  cases h : p
        |  case pos:
        |    left
        |    by exact h
        |  case neg:
        |    right
        |    by exact h
        |  end
        |qed
        |theorem APPLIED : !n:num. !m:num. !k:num. m <= k ==> n + m <= n + k
        |proof
        |  fix n m k
        |  assume h
        |  apply NUM_ADD_MONOTONE
        |  by exact h
        |qed
        |define twice := \x:real. x + x
        |theorem TWICE : !x:real. twice x = 2 * x
        |proof
        |  fix x
        |  rewrite twice
        |  by ring
        |qed
        |theorem CHAIN : !x:real. !y:real. 0 <= x /\ x <= y ==> x <= y + y
        |proof
        |  fix x y
        |  assume h
        |  calc x <= y by linarith from h
        |       _ <= y + y by linarith from h
        |qed""")
    withClue(report.render) { report.ok shouldBe true }
    report.entries.map(_.name) shouldBe Vector("WITNESS", "OBTAIN", "SPLIT", "EXCLUDED", "APPLIED", "twice", "TWICE", "CHAIN")
  }

  "A calc" should "refuse a chain whose ends are not the goal" in {
    val report = check(
      """theorem ENDS : !x:real. x <= x + 2
        |proof
        |  fix x
        |  calc x <= x + 1 by linarith
        |       _ <= x + 3 by linarith
        |qed""")
    messages(report, "ENDS").head should include("the chain proves x <= x + 3, and the goal is x <= x + 2")
  }

  /* ------------------------------------------------------------------ increment 2 */

  "A method that refused" should "carry whether its goal is false, with the answers kept apart" in {
    val report = check(
      """theorem FALSE_LINEAR : !x:real. !y:real. x < y ==> y < x
        |proof
        |  fix x y
        |  assume h
        |  by linarith from h
        |qed
        |theorem FALSE_SAMPLED : !x:real. x * x <= x
        |proof
        |  fix x
        |  by auto
        |qed
        |theorem CONTRADICTORY : !x:real. x < 0 /\ 0 < x ==> x = 7
        |proof
        |  fix x
        |  assume h
        |  by ring
        |qed
        |theorem UNREACHED : !x:real. 0 <= x * x * x * x
        |proof
        |  fix x
        |  by ring
        |qed""")
    def kind(name: String): Option[String] =
      report.entries.find(_.name == name).flatMap(_.problems.headOption).flatMap(_.refuted).map(_.kind)
    kind("FALSE_LINEAR") shouldBe Some("solved")
    kind("FALSE_SAMPLED") shouldBe Some("found")
    // `{x < 0, 0 < x}` came back as a hundred points survived before `Refutation` asked whether the
    // premises can hold at all; the proof language is what printed it.
    kind("CONTRADICTORY") shouldBe Some("contradictory")
    // The control: a true claim the method cannot reach is evidence, never reported false.
    kind("UNREACHED") shouldBe Some("survived")
    report.entries.find(_.name == "UNREACHED").flatMap(_.problems.head.refuted).exists(_.refutes) shouldBe false
  }

  "A proved theorem's price" should "name its axioms, the lemmas it cites, and the document's own theorems" in {
    val report = check(
      """theorem BASE : !x:real. x + 0 = x by ring
        |theorem USES_BASE : !y:real. y + 0 = y by exact BASE
        |theorem ZERO_LEFT : !n:num. 0 + n = n
        |proof
        |  fix n
        |  induction n
        |  case zero:
        |    by rewrite NUM_ADD_ZERO
        |  case succ m ih:
        |    calc 0 + SUC m = SUC (0 + m) by rewrite NUM_ADD_SUC
        |         _ = SUC m by rewrite ih
        |  end
        |qed""")
    def price(name: String): Elaborate.Price =
      report.entries.find(_.name == name).flatMap(_.price).getOrElse(fail(s"no price for $name in ${report.render}"))
    price("USES_BASE").document shouldBe Vector("BASE")
    price("BASE").document shouldBe empty
    // The lemmas cited, and not the construction of `num` under them, which a transitive walk lists.
    price("ZERO_LEFT").facts should contain allOf ("NUM_ADD_SUC", "NUM_ADD_ZERO", "NUM_INDUCTION")
    price("ZERO_LEFT").facts should not contain "NUM_REP_0"
    // Axioms by name: a statement printed in place of a name would carry a binder.
    price("ZERO_LEFT").axioms should not be empty
    price("ZERO_LEFT").axioms.foreach(axiom => axiom should not include "!")
    price("ZERO_LEFT").inferences should be > 0
  }

  "A rewrite" should "be refused when its walk did not finish, rather than carried on from a waypoint" in {
    val report = check(
      """theorem LOOP : !x:real. !y:real. x + y + 0 = y + x
        |proof
        |  fix x y
        |  rewrite ADD_SYM
        |  by ring
        |qed""")
    messages(report, "LOOP").head should include("did not finish: the step limit ran out")
  }

  "The branches of a split" should "all be checked when one fails" in {
    val report = check(
      """theorem TWO : !x:real. x = x + 1 /\ x + 1 = x
        |proof
        |  fix x
        |  split
        |  case left:
        |    by ring
        |  case right:
        |    by ring
        |  end
        |qed""")
    report.entries.head.problems.map(_.line) shouldBe Vector(6, 8)
  }

  "The report" should "be valid structured data a program can read" in {
    val report = check(
      """theorem OK : !x:real. x + 0 = x by ring
        |theorem NOT : !x:real. x = x + 1 by ring""")
    val json = report.json
    json should startWith("""{"ok":false,""")
    // A field with nothing in it is left out, so the word the gates ban appears nowhere.
    json should not include "null"
    json should include(""""name":"OK","line":1,"kind":"theorem","status":"proved"""")
    json should include(""""name":"NOT","line":2,"kind":"theorem","status":"incomplete"""")
    // Braces and brackets balance outside strings, which is the cheapest test that it parses.
    val outside = json.replaceAll("\"(\\\\.|[^\"\\\\])*\"", "\"\"")
    outside.count(_ == '{') shouldBe outside.count(_ == '}')
    outside.count(_ == '[') shouldBe outside.count(_ == ']')
  }
}
