package garden.xeno.symbolum.tactics

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Every refusal the elaborator can give, and every route through a step or a method that
 * `ElaborateSpec` does not take, each by the smallest document that reaches it.
 *
 * `ElaborateSpec` states the properties the language is under; this suite is the census beside it.
 * A refusal is part of the language a writer meets, and one nobody has seen fire is a message
 * nobody has read: of the refusals below, the reader's half of this census found one that named the
 * wrong keyword (`DocumentSpec`). Each refusal is asserted by its message and its line, and the
 * routes that prove something are asserted proved, so a checker that refused everything fails the
 * second half of this suite and a checker that proved everything fails the first.
 */
class ElaborateRoutesSpec extends AnyFlatSpec with Matchers {
  import Elaborate.{Report, Status}

  private lazy val elaborate: Elaborate = Elaborate.standard

  private def check(text: String): Report = elaborate.check(text.stripMargin)

  /** A one-theorem document whose proof is `body`, over `claim`. */
  private def theorem(claim: String, body: String): String = s"theorem T : $claim\nproof\n$body\nqed"

  "A refusal" should "be given for every step and method used where it does not apply, on its line" in {
    val cases: Vector[(String, String, Status, Int, String)] = Vector(
      ("a definition whose body does not read", "define bad := x +", Status.Refused, 1, "expected a name or '(', at character 3"),
      ("a definition of a name the theory has", "define SUC := \\x:num. x", Status.Refused, 1, "SUC is already declared in this theory"),
      ("a claim that does not read", "theorem T : !x:real. x + by ring", Status.Refused, 1, "expected a name or '(', at character 12"),
      ("a block that ends open", theorem("!x:real. x = x", "  fix x"), Status.Incomplete, 4, "the block ends with the goal still open"),
      ("assume on a goal that is no implication", theorem("!x:real. x = x", "  assume h"), Status.Incomplete, 3,
        "`assume h` wants a goal of the form A ==> B"),
      ("fix on a goal that is no universal", theorem("(1:real) = 1", "  fix x"), Status.Incomplete, 3, "`fix x` wants a goal of the form !x. P x"),
      ("fix at a constant's name", theorem("!x:real. x = x", "  fix SUC"), Status.Incomplete, 3, "SUC is a constant of the theory"),
      ("fix at a name used twice", theorem("!x:real. !y:real. x = y ==> x = y", "  fix x x"), Status.Incomplete, 3,
        "x already names something in this proof"),
      ("show naming another claim", theorem("!x:real. x = x", "  fix x\n  show x = x + 0 by ring"), Status.Incomplete, 4,
        "`show` names x = x + 0, and the goal is x = x"),
      ("obtain from no existential", theorem("!x:real. x = x ==> x = x", "  fix x\n  assume h\n  obtain y k from h"), Status.Incomplete, 5,
        "h is x = x, which is not an existential"),
      ("split on no conjunction", theorem("!x:real. x = x", "  fix x\n  split\n  case left:\n    by ring\n  case right:\n    by ring\n  end"),
        Status.Incomplete, 4, "`split` wants a goal of the form A /\\ B"),
      ("left on no disjunction", theorem("!x:real. x = x", "  fix x\n  left\n  by ring"), Status.Incomplete, 4,
        "`left` wants a goal of the form A \\/ B"),
      ("right on no disjunction", theorem("!x:real. x = x", "  fix x\n  right\n  by ring"), Status.Incomplete, 4,
        "`right` wants a goal of the form A \\/ B"),
      ("witness on no existential", theorem("!x:real. x = x", "  fix x\n  witness 1"), Status.Incomplete, 4,
        "`witness` wants a goal of the form ?x. P x"),
      ("a case written twice", theorem("!x:real. x = x /\\ x = x",
        "  fix x\n  split\n  case left:\n    by ring\n  case left:\n    by ring\n  end"), Status.Incomplete, 4, "the case `left` is written twice"),
      ("a case missing", theorem("!x:real. x = x /\\ x = x", "  fix x\n  split\n  case left:\n    by ring\n  end"), Status.Incomplete, 4,
        "the case `right` is missing; the cases are left (or 1), right (or 2)"),
      ("a case naming more than it binds", theorem("!x:real. x = x /\\ x = x",
        "  fix x\n  split\n  case left extra:\n    by ring\n  case right:\n    by ring\n  end"), Status.Incomplete, 5,
        "`case left` names extra, and its goal binds nothing more"),
      ("induction over a variable not fixed", theorem("!n:num. n + 0 = n", "  induction n\n  case zero:\n    by arith\n  end"),
        Status.Incomplete, 3, "induction is over a fixed variable, and n is not one"),
      ("induction over a type with no default", theorem("!x:real. x = x", "  fix x\n  induction x\n  case 1:\n    by ring\n  end"),
        Status.Incomplete, 4, "no default induction principle for real"),
      ("induction by a lemma that is no principle", theorem("!n:num. n + 0 = n",
        "  fix n\n  induction n using NUM_ADD_ZERO\n  case 1:\n    by arith\n  end"), Status.Incomplete, 4,
        "NUM_ADD_ZERO is not an induction principle over this variable's type"),
      ("apply with cases where nothing is owed", theorem("!x:real. !y:real. x + y = y + x",
        "  fix x y\n  apply ADD_SYM\n  case 1:\n    by ring\n  end"), Status.Incomplete, 4, "ADD_SYM owes nothing here, so it has no cases"),
      ("a fact cited from a proof holding others", theorem("!x:real. x = x ==> x = x", "  fix x\n  assume h\n  by exact nowhere"),
        Status.Incomplete, 5, "no fact named nowhere: this proof holds h"),
      ("a rewrite with something not an equation", theorem("!x:real. 0 <= x ==> x = x", "  fix x\n  assume h\n  rewrite h\n  by ring"),
        Status.Incomplete, 5, "expected an equation, found 0 <= x"),
      ("a rewrite that changes nothing", theorem("!x:real. x = x", "  fix x\n  rewrite NUM_ADD_ZERO\n  by ring"), Status.Incomplete, 4,
        "rewriting with NUM_ADD_ZERO changes nothing in the goal"),
      ("a rewrite method that leaves something", "define twice := \\x:real. x + x\n" +
        "theorem T : !x:real. twice x = 2 * x\nproof\n  fix x\n  by rewrite twice\nqed", Status.Incomplete, 5,
        "rewriting with twice leaves"),
      ("an apply method that leaves obligations", theorem("!n:num. !m:num. !k:num. m <= k ==> n + m <= n + k",
        "  fix n m k\n  assume h\n  by apply NUM_ADD_MONOTONE"), Status.Incomplete, 5, "NUM_ADD_MONOTONE leaves m <= k to prove"),
      ("then after a method that closes", theorem("!x:real. x = x", "  fix x\n  by ring then ring"), Status.Incomplete, 4,
        "only `rewrite` changes a goal and leaves something for `then`"),
      ("first where nothing settles", theorem("!x:real. x = x + 1", "  fix x\n  by first ring | linarith"), Status.Incomplete, 4,
        "none of the alternatives settled the goal: "),
      ("a method proving something else", theorem("!x:real. !y:real. x + y = y + x", "  fix x y\n  by exact NUM_ADD_SYM"), Status.Incomplete, 4,
        // Only the half of the message that is printed through the notation: the lemma's half is
        // printed as a raw term by `Rules.specTo`, which is a defect of that message and not pinned here.
        "found x + y = y + x")
    )
    val wrong = cases.flatMap { case (what, text, status, line, message) =>
      val report = elaborate.check(text)
      val entry = report.entries.lastOption
      val problems = entry.toVector.flatMap(_.problems)
      val matched = problems.exists(p => p.line == line && p.reason.contains(message))
      if (entry.exists(_.status == status) && matched) None
      else Some(s"$what: expected $status with line $line naming \"$message\", got\n${report.render}")
    }
    withClue(wrong.mkString("\n\n")) { wrong shouldBe empty }
  }

  "The routes ElaborateSpec does not take" should "each prove what they are for" in {
    val report = check(
      """theorem EXACT_SPECIALISED : !x:real. !y:real. x + y = y + x
        |proof
        |  fix x y
        |  by exact ADD_SYM
        |qed
        |theorem APPLY_METHOD : !x:real. !y:real. x + y = y + x
        |proof
        |  fix x y
        |  by apply ADD_SYM
        |qed
        |theorem APPLY_CASES : !x:real. !y:real. !z:real. !u:real. x <= y ==> z <= u ==> x + z <= y + u
        |proof
        |  fix x y z u
        |  assume a b
        |  apply ADD_LE
        |  case 1:
        |    by exact a
        |  case 2:
        |    by exact b
        |  end
        |qed
        |define twice := \x:real. x + x
        |theorem THEN : !x:real. twice x = 2 * x
        |proof
        |  fix x
        |  by rewrite twice then ring
        |qed
        |theorem FIRST : !x:real. x + 0 = x
        |proof
        |  fix x
        |  by first linarith | ring
        |qed
        |theorem AUTO_FROM : !x:real. 0 <= x ==> 0 <= x + x
        |proof
        |  fix x
        |  assume h
        |  by auto from h
        |qed
        |theorem STRICT_CHAIN : !x:real. !y:real. x < y ==> x < y + 1
        |proof
        |  fix x y
        |  assume h
        |  calc x < y by linarith from h
        |       _ = y + 0 by ring
        |       _ <= y + 1 by linarith
        |qed
        |theorem NUM_CHAIN : !n:num. !m:num. n <= m ==> n < m + 1
        |proof
        |  fix n m
        |  assume h
        |  calc n <= m by arith from h
        |       _ < m + 1 by arith
        |qed
        |theorem CASES_BY_NUMBER : !x:real. x = x /\ x = x
        |proof
        |  fix x
        |  split
        |  case 2:
        |    by ring
        |  case 1:
        |    by ring
        |  end
        |qed""")
    withClue(report.render) { report.ok shouldBe true }
    report.entries.map(_.name) shouldBe
      Vector("EXACT_SPECIALISED", "APPLY_METHOD", "APPLY_CASES", "twice", "THEN", "FIRST", "AUTO_FROM", "STRICT_CHAIN", "NUM_CHAIN",
        "CASES_BY_NUMBER")
  }

  it should "warn about the steps after an apply that closed the goal, and still prove it" in {
    val report = check(theorem("!x:real. !y:real. x + y = y + x", "  fix x y\n  apply ADD_SYM\n  by ring"))
    report.entries.head.status shouldBe Status.Incomplete
    report.entries.head.problems.map(p => (p.line, p.reason)) shouldBe
      Vector((5, "the goal is closed on line 4, so this step and the ones after it have nothing to prove"))
  }

  "A refusal's refutation" should "name which of the kinds it is, for the kinds ElaborateSpec does not reach" in {
    def kind(text: String): Option[String] =
      check(text).entries.lastOption.toVector.flatMap(_.problems).flatMap(_.refuted).headOption.map(_.kind)
    // A true linear claim that `ring` cannot settle: the linear question is decided, and nothing refutes it.
    kind(theorem("!x:real. x <= x + 1", "  fix x\n  by ring")) shouldBe Some("no-counterexample")
    // A claim over a constant this document defined, which the model has no reading of.
    kind("define twice := \\x:real. x + x\n" + theorem("!x:real. twice x = x + x", "  fix x\n  by ring")) shouldBe Some("never-asked")
    // The control, a false linear claim refused by the same method: solved, so the two above are
    // not a refutation that answers nothing.
    kind(theorem("!x:real. x + 1 <= x", "  fix x\n  by ring")) shouldBe Some("solved")
  }

  "The report" should "print the price, the problems and the syntax errors a reader needs" in {
    val report = check(
      """theorem LEMMA : !x:real. x + 0 = x by ring
        |theorem USES : !x:real. x + 0 = x
        |proof
        |  fix x
        |  by exact LEMMA
        |qed
        |theorem WRONG : !x:real. x = x + 1
        |proof
        |  fix x
        |  by ring
        |qed
        |nonsense""")
    val rendered = report.render
    rendered should include("from this document: LEMMA")
    rendered should include("axioms: ")
    rendered should include("line 10: ")
    rendered should include("    try: ")
    rendered should include("    false: ")
    rendered should include("    |- x = x + 1")
    rendered should include("line 12: syntax: ")
    rendered should endWith("3 declarations: 2 proved, 0 defined, 1 not proved, 1 syntax errors")
    report.json should include("\"syntax\":[{\"line\":12,")
  }

  it should "escape every character JSON needs escaped" in {
    val report = check("theorem T : !x:real. x = \"a\\b\tc\u0001\" by ring")
    val json = report.json
    json should include("\\\"a\\\\b\\tc\\u0001\\\"")
    json should not include "\t"
    json should not include "\u0001"
  }

  "The command line" should "answer a usage error and a missing file without building anything" in {
    Check.run(Vector.empty, fail("the chain was built for a usage error")) shouldBe
      Check.Outcome(2, Vector.empty, Vector("usage: Check [--json] FILE..."))
    Check.run(Vector("--yaml", "x.sym"), fail("the chain was built for a usage error")).err shouldBe
      Vector("usage: Check [--json] FILE...", "unknown flag: --yaml")
    Check.run(Vector("no/such/file.sym"), fail("the chain was built for a missing file")) shouldBe
      Check.Outcome(2, Vector.empty, Vector("no such file: no/such/file.sym"))
  }

  it should "exit 0 on a document that checks and 1 on one that does not, in both forms" in {
    val good = Files.createTempFile("good", ".sym")
    val bad = Files.createTempFile("bad", ".sym")
    try {
      Files.write(good, "theorem T : !x:real. x + 0 = x by ring".getBytes(StandardCharsets.UTF_8))
      Files.write(bad, "theorem T : !x:real. x = x + 1 by ring".getBytes(StandardCharsets.UTF_8))
      val text = Check.run(Vector(good.toString), elaborate)
      text.status shouldBe 0
      text.out.head shouldBe s"== $good"
      text.out(1) should include("T: proved")
      val json = Check.run(Vector("--json", good.toString, bad.toString), elaborate)
      json.status shouldBe 1
      json.out should have size 2
      json.out.head should startWith(s"""{"file":"$good","report":{"ok":true""")
      json.out(1) should include(""""ok":false""")
    } finally {
      Files.deleteIfExists(good)
      Files.deleteIfExists(bad)
    }
  }
}
