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
}
