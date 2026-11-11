package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The syntax of a proof document, read without a chain.
 *
 * What is asserted is the shape the elaborator receives and the one property of reading that a long
 * document depends on: a syntax error ends its own declaration and nothing else. Each assertion that
 * something was read is paired with the input that would make it vacuous, since a reader that drops
 * a declaration it cannot parse would pass every "the good ones are there" check on its own.
 */
class DocumentSpec extends AnyFlatSpec with Matchers {
  import Document.*

  "A document" should "read a structured proof into steps that carry their lines" in {
    val parsed = read(
      """theorem T : !n:num. 0 + n = n
        |proof
        |  fix n
        |  induction n
        |  case zero:
        |    by arith
        |  case succ m ih:
        |    by arith from ih
        |  end
        |qed""".stripMargin)

    parsed.errors shouldBe empty
    parsed.declarations should have size 1
    val Declaration.Theorem(line, name, claim, Justification.Block(_, steps, closed)) = parsed.declarations.head: @unchecked
    (line, name, claim, closed) shouldBe ((1, "T", "!n:num. 0 + n = n", 10))
    steps.map(_.line) shouldBe Vector(3, 4)
    val Step.Induction(_, variable, using, branches) = steps(1): @unchecked
    (variable, using) shouldBe (("n", None))
    branches.map(b => (b.line, b.label, b.names)) shouldBe Vector((5, "zero", Vector()), (7, "succ", Vector("m", "ih")))
    branches(1).steps.head shouldBe Step.Show(8, None, Justification.By(8, Method.Arith(Vector("ih"))))
  }

  it should "end only the declaration a syntax error is in" in {
    val parsed = read(
      """theorem A : !x:real. x = x
        |proof
        |  frobnicate x
        |qed
        |theorem B : !x:real. x = x by ring
        |define c := \x:real. x""".stripMargin)

    parsed.errors.map(_.line) shouldBe Vector(3)
    parsed.errors.head.reason should include("no step `frobnicate`")
    // The declarations after the error are read, and the one with the error is not half-read.
    parsed.declarations.collect { case d: Declaration.Theorem => d.name; case d: Declaration.Define => d.name } shouldBe Vector("B", "c")
  }

  it should "take the claim before the last ` by ` and the method after it" in {
    val parsed = read("theorem T : !x:real. 0 <= x * x by auto from h, k")
    val Declaration.Theorem(_, _, claim, Justification.By(_, method)) = parsed.declarations.head: @unchecked
    claim shouldBe "!x:real. 0 <= x * x"
    method shouldBe Method.Auto(Vector("h", "k"))
  }

  it should "read `then` and `first` as methods over methods" in {
    val parsed = read("theorem T : !x:real. x = x by first rewrite A then ring | auto")
    val Declaration.Theorem(_, _, _, Justification.By(_, method)) = parsed.declarations.head: @unchecked
    method shouldBe Method.First(Vector(Method.Then(Method.Rewrite(Vector("A")), Method.Ring), Method.Auto(Vector.empty)))
  }

  it should "substitute where the last link ended for the `_` of a calc" in {
    val parsed = read(
      """theorem T : !x:real. x <= x + 1
        |proof
        |  fix x
        |  calc x = x + 0 by ring
        |       _ <= x + 1 by linarith
        |qed""".stripMargin)
    val Declaration.Theorem(_, _, _, Justification.Block(_, steps, _)) = parsed.declarations.head: @unchecked
    val Step.Calc(_, links) = steps(1): @unchecked
    links.map(_.claim) shouldBe Vector("x = x + 0", "(x + 0) <= x + 1")
  }

  it should "find a relation at the top level of a link, never inside parentheses or an implication" in {
    val parsed = read(
      """theorem T : !p:bool. p ==> p
        |proof
        |  calc (p ==> p) = (p ==> p) by auto
        |       _ = T by auto
        |qed""".stripMargin)
    val Declaration.Theorem(_, _, _, Justification.Block(_, steps, _)) = parsed.declarations.head: @unchecked
    val Step.Calc(_, links) = steps.head: @unchecked
    links(1).claim shouldBe "((p ==> p)) = T"
  }

  it should "strip a comment only where `--` opens the line or follows a space" in {
    val parsed = read(
      """-- a comment line
        |theorem T : !x:real. x = x by ring -- a trailing comment""".stripMargin)
    parsed.errors shouldBe empty
    val Declaration.Theorem(_, _, claim, Justification.By(_, method)) = parsed.declarations.head: @unchecked
    (claim, method) shouldBe (("!x:real. x = x", Method.Ring))
  }

  it should "refuse a group of branches with no `end`, naming the line that opened it" in {
    val parsed = read(
      """theorem T : !x:real. x = x /\ x = x
        |proof
        |  fix x
        |  split
        |  case left:
        |    by ring
        |  case right:
        |    by ring
        |qed""".stripMargin)
    parsed.declarations shouldBe empty
    parsed.errors.head.reason should include("opened on line 4 end with `end`")
  }

  it should "refuse a proof with no `qed`, and a theorem with neither `by` nor `proof`" in {
    read("theorem T : !x:real. x = x\nproof\n  fix x").errors.head.reason should include("has no `qed`")
    read("theorem T : !x:real. x = x\ntheorem U : !x:real. x = x by ring").errors.head.reason should include("write `proof`")
  }

  /**
   * Every refusal of the reader, each by the smallest input that reaches it, with the line it names.
   *
   * The line is asserted as well as the message because a refusal on the wrong line sends the writer
   * to a line that is fine. Each input is one theorem whose proof is otherwise well formed, so the
   * message is the only thing that can be wrong; the control is the first test of this suite, which
   * reads the same constructs written correctly.
   */
  it should "refuse every malformed construct with its own message, on the line it is on" in {
    def proof(body: String): String = s"theorem T : !x:real. x = x\nproof\n$body\nqed"
    val cases: Vector[(String, String, Int, String)] = Vector(
      ("a top-level line that is not a declaration", "lemma T : x", 1, "this line starts with `lemma`"),
      ("a definition without :=", "define twice \\x:real. x", 1, "`define` is written `define NAME := TERM`"),
      ("a theorem without a claim", "theorem T :", 1, "`theorem` is written `theorem NAME : CLAIM`"),
      ("a theorem at the end with no proof", "theorem T : !x:real. x = x", 1, "the document ends"),
      ("a proof closed by something else", "theorem T : !x:real. x = x\nproof\n  by ring\nend", 4, "`end` belongs to the branches"),
      ("fix with no names", proof("  fix"), 3, "`fix` wants the names of the variables it fixes"),
      ("fix with a number", proof("  fix 1x"), 3, "`1x` is not a name"),
      ("have with a bad name", proof("  have 2h : x = x by ring"), 3, "`2h` is not a name"),
      ("have without a colon", proof("  have h x = x by ring"), 3, "`have` is written `have NAME : CLAIM by METHOD`"),
      ("show with only a method", proof("  show by ring"), 3, "`show` wants the claim it closes"),
      ("by with nothing after it", proof("  by"), 3, "`by` wants a method"),
      ("obtain without from", proof("  obtain y h e"), 3, "`obtain` is written `obtain x h from FACT`"),
      ("obtain with three names", proof("  obtain y h k from e"), 3, "names exactly one variable and one hypothesis"),
      ("obtain from something not a name", proof("  obtain y h from 3e"), 3, "`3e` is not a name"),
      ("cases with a bad name", proof("  cases 1 : x = x\n  end"), 3, "`1` is not a name"),
      ("induction with two variables", proof("  induction x y\n  end"), 3, "`induction` is written `induction x` or `induction x using LEMMA`"),
      ("split with something after it", proof("  split now\n  end"), 3, "`split` takes nothing after it"),
      ("left with something after it", proof("  left now"), 3, "`left` takes nothing after it"),
      ("witness with no term", proof("  witness"), 3, "`witness` wants the term"),
      ("rewrite with no equations", proof("  rewrite"), 3, "`rewrite` wants the equations it rewrites with"),
      ("rewrite with a bad equation", proof("  rewrite A, 2B"), 3, "`2B` is not a name"),
      ("apply with no lemma", proof("  apply"), 3, "`apply` wants the lemma it applies"),
      ("a stray case", proof("  case left:"), 3, "`case` belongs to the branches"),
      ("a stray qed inside branches", proof("  split\n  case left:\n    by ring\n  qed now"), 6, "end with `end`"),
      ("a step that is not one", proof("  simp"), 3, "no step `simp`; a step is one of"),
      ("a branch with no colon", proof("  split\n  case left\n  end"), 4, "ending with a colon"),
      ("a branch with no label", proof("  split\n  case :\n  end"), 4, "a branch wants its label"),
      ("a branch with a bad name", proof("  split\n  case left 9:\n  end"), 4, "`9` is not a name"),
      ("a branch group the document ends inside", "theorem T : !x:real. x = x\nproof\n  split\n  case left:", 4, "have no `end`"),
      ("a calc link with no method", proof("  calc x = x"), 3, "every link of a `calc` ends with `by METHOD`"),
      ("a calc link after the first without _", proof("  calc x = x by ring\n  _ = x by ring\n  x = x by ring"), 5, "no step `x`"),
      ("a calc link that is not a relation", proof("  calc f x by ring"), 3, "a link of a `calc` is a relation"),
      ("a method that is not one", proof("  by simp"), 3, "no method `simp`; a method is one of"),
      ("first with one alternative", proof("  by first ring"), 3, "with at least two methods"),
      ("first written as a bare word", proof("  by first"), 3, "with at least two methods"),
      ("ring with an argument", proof("  by ring h"), 3, "`ring` takes nothing after it"),
      ("auto with something other than from", proof("  by auto using h"), 3, "`auto` is written `auto` or `auto from F, G`"),
      // The message names the method and not the step it is written in: it said "`by` wants the fact"
      // until this table was written, which is what reading the keyword off the line gives.
      ("exact with no fact", proof("  by exact"), 3, "`exact` wants the fact"),
      ("rewrite as a method with no equations", proof("  by rewrite"), 3, "`rewrite` wants the equations"),
      ("from with no facts", proof("  by linarith from  ,"), 3, "`linarith` wants the facts it uses"),
      ("apply as a method with a bad name", proof("  by apply 3"), 3, "`3` is not a name"),
      ("a bad name inside then", proof("  by rewrite A then exact 4"), 3, "`4` is not a name")
    )
    val wrong = cases.flatMap { case (what, text, line, message) =>
      read(text).errors.headOption match {
        case Some(error) if error.line == line && error.reason.contains(message) => None
        case other => Some(s"$what: expected line $line with \"$message\", got $other")
      }
    }
    withClue(wrong.mkString("\n")) { wrong shouldBe empty }
  }

  it should "read the methods and steps the first test does not, into the shape the elaborator receives" in {
    val parsed = read(
      """theorem T : !x:real. x = x
        |proof
        |  fix x
        |  have h : x = x
        |  proof
        |    by first ring | auto
        |  qed
        |  apply LEMMA
        |  case 1:
        |    by exact h
        |  end
        |  right
        |  witness x + 1
        |  by linarith from h, k
        |qed
        |theorem U : !x:real. x = x by apply LEMMA""".stripMargin)
    withClue(parsed.errors) { parsed.errors shouldBe empty }
    val Declaration.Theorem(_, _, _, Justification.Block(_, steps, _)) = parsed.declarations.head: @unchecked
    val Step.Have(_, "h", "x = x", Justification.Block(_, inner, _)) = steps(1): @unchecked
    inner.head shouldBe Step.Show(6, None, Justification.By(6, Method.First(Vector(Method.Ring, Method.Auto(Vector.empty)))))
    steps(2) shouldBe Step.Apply(8, "LEMMA", Vector(Branch(9, "1", Vector.empty, Vector(Step.Show(10, None, Justification.By(10, Method.Exact("h")))))))
    steps(3) shouldBe Step.Choose(12, false)
    steps(4) shouldBe Step.Witness(13, "x + 1")
    steps(5) shouldBe Step.Show(14, None, Justification.By(14, Method.Linarith(Vector("h", "k"))))
    parsed.declarations(1) shouldBe Declaration.Theorem(16, "U", "!x:real. x = x", Justification.By(16, Method.Apply("LEMMA")))
  }

  "An import" should "be read at the top of a document, apart from the declarations" in {
    val parsed = read(
      """-- what this builds on
        |import Doubling
        |import Parity_2
        |define d := \x:num. x + x
        |theorem T : d 0 = 0 by auto""".stripMargin)

    parsed.errors shouldBe empty
    parsed.imports shouldBe Vector(Import(2, "Doubling"), Import(3, "Parity_2"))
    parsed.declarations.map(_.line) shouldBe Vector(4, 5)
    // The input that would make the first assertion vacuous: a document with no import line.
    read("define d := \\x:num. x").imports shouldBe empty
  }

  it should "be refused after a declaration, twice, without a name, or with a name that is a path" in {
    val parsed = read(
      """import A
        |import A
        |import
        |import ../secret
        |import B C
        |define d := \x:num. x
        |import Late
        |theorem T : d 0 = 0 by auto""".stripMargin)

    parsed.imports shouldBe Vector(Import(1, "A"))
    parsed.errors shouldBe Vector(
      Malformed(2, "A is already imported on line 1"),
      Malformed(3, "`import` wants the name of a document"),
      Malformed(4, "`../secret` is not the name of a document: one word of letters, digits and `_`, starting with a letter"),
      Malformed(5, "`B C` is not the name of a document: one word of letters, digits and `_`, starting with a letter"),
      Malformed(7, "`import` comes before every `define` and `theorem`: move it to the top of the document"))
    // An error on an import line ends nothing: both declarations are read.
    parsed.declarations.map(_.line) shouldBe Vector(6, 8)
  }

  it should "be refused after a declaration that failed to read, which is still a declaration" in {
    val parsed = read(
      """theorem BROKEN
        |import Late""".stripMargin)
    parsed.imports shouldBe empty
    parsed.errors.map(_.line) shouldBe Vector(1, 2)
    parsed.errors(1).reason should include("comes before every")
  }

  "`cases NAME from FACT`" should "read as a split of a fact, apart from `cases NAME : CLAIM`" in {
    val parsed = read(
      """theorem T : !p:bool. !q:bool. p \/ q ==> q \/ p
        |proof
        |  fix p q
        |  assume h
        |  cases k from h
        |  case left:
        |    right
        |    by exact k
        |  case right:
        |    left
        |    by exact k
        |  end
        |  cases c : p from q
        |  case pos:
        |    by auto
        |  case neg:
        |    by auto
        |  end
        |qed""".stripMargin)

    parsed.errors shouldBe empty
    val Declaration.Theorem(_, _, _, Justification.Block(_, steps, _)) = parsed.declarations.head: @unchecked
    val Step.CasesFrom(line, name, from, branches) = steps(2): @unchecked
    (line, name, from, branches.map(_.label)) shouldBe ((5, "k", "h", Vector("left", "right")))
    // With a colon it is the claim form, whatever follows: `from` inside a claim is not this step.
    val Step.Cases(_, named, claim, _) = steps(3): @unchecked
    (named, claim) shouldBe (("c", "p from q"))
  }

  it should "refuse a fact or a name that is not a name" in {
    val parsed = read(
      """theorem T : T
        |proof
        |  cases k from 1h
        |  case left:
        |    by auto
        |  case right:
        |    by auto
        |  end
        |qed""".stripMargin)
    parsed.errors shouldBe Vector(Malformed(3, "`1h` is not a name"))
  }
}
