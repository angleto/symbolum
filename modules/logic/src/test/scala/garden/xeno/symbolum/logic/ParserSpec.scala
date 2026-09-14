package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * Reading terms from text.
 *
 * The assertions compare against terms built with the kernel's constructors rather than against
 * printed output, because the point of the parser is that the term it produces is the one the
 * reader thinks the text denotes. Comparing two pieces of text would only show that the parser and
 * the printer agree with each other.
 */
class ParserSpec extends AnyFlatSpec with Matchers {


  /**
   * Abstraction, forced.
   *
   * `Term.abs` refuses a body that is not locally closed, since 2026-09-10, so it returns a
   * refusal like `app` and `eq` do. Every body below is built out of variables and constants a
   * line or two above and none of them can be open, so forcing here is reading the signature and
   * not ignoring it. A test that meant to hand it an open body says so by calling `Term.abs`
   * directly and looking at the `Left`.
   */
  private def lam(variable: FVar, body: Term): Term =
    Term.abs(variable, body).fold(error => fail(s"unexpected refusal: $error"), identity)

  private val logic = Logic.standard
  private val theory = logic.theory

  private val p = Term.variable("p", Type.Bool)
  private val q = Term.variable("q", Type.Bool)
  private val r = Term.variable("r", Type.Bool)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private def parse(text: String): Term = force(Parser.proposition(theory, text))

  /** A theory with two ground types and one operator over them, which is all the case below needs. */
  private lazy val arithmetic: Theory = {
    val real = TyApp("real", Nil)
    val numbers = TyApp("num", Nil)
    force(
      theory
        .declareTypeOperator("real", 0)
        .flatMap(_.declareTypeOperator("num", 0))
        .flatMap(_.declareConstant("Power", Type.fun(real, Type.fun(numbers, real))))
    )
  }


  "The parser" should "read a conjunction" in {
    parse("p /\\ q") shouldBe force(logic.mkConj(p, q))
  }

  it should "associate implication to the right" in {
    val expected = force(logic.mkImp(p, force(logic.mkImp(q, r))))

    parse("p ==> q ==> r") shouldBe expected
  }

  it should "bind conjunction tighter than implication" in {
    val expected = force(logic.mkImp(force(logic.mkConj(p, q)), force(logic.mkConj(q, p))))

    parse("p /\\ q ==> q /\\ p") shouldBe expected
  }

  it should "bind negation tighter than disjunction" in {
    val expected = force(logic.mkDisj(force(logic.mkNot(p)), q))

    parse("~p \\/ q") shouldBe expected
  }

  it should "read <=> as equality" in {
    parse("p <=> q") shouldBe force(Term.eq(p, q))
  }

  it should "read a universal quantifier" in {
    val x = Term.variable("x", TyVar("a"))
    val expected = force(logic.mkForall(x, force(Term.eq(x, x))))

    force(Parser.proposition(theory, "!x:'a. x = x")) shouldBe expected
  }

  it should "read several variables under one binder" in {
    val x = Term.variable("x", Type.Bool)
    val y = Term.variable("y", Type.Bool)
    val expected = force(logic.mkForall(x, force(logic.mkForall(y, force(Term.eq(x, y))))))

    parse("!x:bool y:bool. x = y") shouldBe expected
  }

  it should "read a lambda" in {
    val x = Term.variable("x", Type.Bool)

    force(Parser.term(theory, "\\x:bool. x")) shouldBe lam(x, x)
  }

  it should "apply to the left" in {
    val f = Term.variable("f", Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool)))
    val expected = force(Term.appAll(f, List(p, q)))

    force(Parser.proposition(theory, "f:bool->bool->bool p q")) shouldBe expected
  }

  it should "not let a binder capture a free variable of the same name" in {
    val x = Term.variable("x", Type.Bool)
    val identity = lam(x, x)
    val expected = force(logic.mkConj(x, force(Term.app(identity, x))))

    force(Parser.proposition(theory, "x /\\ ((\\x:bool. x) x)")) shouldBe expected
    Term.freeVariables(expected) shouldBe Set(x)
  }

  it should "infer the type of a variable from how it is used" in {
    val result = force(Parser.proposition(theory, "p /\\ q"))

    Term.freeVariables(result) shouldBe Set(p, q)
  }

  "A type" should "be read with the arrow to the right" in {
    val expected = Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool))

    force(Parser.parseType(theory, "bool -> bool -> bool")) shouldBe expected
  }

  it should "be refused when it names an operator the theory does not have" in {
    Parser.parseType(theory, "real").left.map(_.getClass) shouldBe Left(classOf[FromKernel])
  }

  "The parser" should "refuse a term whose type it cannot determine" in {
    Parser.proposition(theory, "x = y").left.map(_.getClass) shouldBe Left(classOf[TypeError])
  }

  it should "refuse a term that is not well typed" in {
    Parser.proposition(theory, "p /\\ (\\x:bool. x)").left.map(_.getClass) shouldBe
      Left(classOf[TypeError])
  }

  it should "refuse a proposition that is not of type bool" in {
    Parser.proposition(theory, "\\x:bool. x").left.map(_.getClass) shouldBe Left(classOf[TypeError])
  }

  it should "refuse an unclosed parenthesis" in {
    Parser.proposition(theory, "(p /\\ q").left.map(_.getClass) shouldBe Left(classOf[SyntaxError])
  }

  it should "refuse text left over after the term" in {
    Parser.proposition(theory, "p q)").left.map(_.getClass) shouldBe Left(classOf[SyntaxError])
  }

  it should "refuse a character it cannot read" in {
    Parser.proposition(theory, "p # q").left.map(_.getClass) shouldBe Left(classOf[SyntaxError])
  }

  "A parsed formula" should "print back as it was written" in {
    val text = "p /\\ q ==> q \\/ ~p"

    Show.show(parse(text)) shouldBe text
  }

  it should "survive being proved about" in {
    val statement = parse("p /\\ q ==> q /\\ p")
    val conjunction = force(logic.mkConj(p, q))
    val assumed = force(Kernel.assume(conjunction))

    val theorem = force(
      for {
        left <- logic.rules.conjElim1(assumed)
        right <- logic.rules.conjElim2(assumed)
        swapped <- logic.rules.conjIntro(right, left)
        discharged <- logic.rules.disch(conjunction, swapped)
      } yield discharged
    )

    theorem.conclusion shouldBe statement
  }

  "A term whose type did not close" should "name the free variables that left it open" in {
    // **The case this message was pointed at before it was written**, and it is a consumer's
    // rather than an invention: `Odd` is one of ITS constants and not one of this theory's, so it
    // is read as a free variable, the term is perfectly well formed, and its type simply never
    // closes. The message used to say "Undetermined: 1 type" and the actual mistake -- a constant
    // that is not here -- appeared nowhere in it.
    val real = TyApp("real", Nil)
    val numbers = TyApp("num", Nil)

    val refusal = Parser.term(
      arithmetic,
      Notation.standard,
      "\\i:num. Power (z:real) (Odd t i)",
      Type.fun(numbers, real)
    )

    val message = refusal.fold(_.message, term => fail(s"expected a refusal, got $term"))

    // Printed, because the whole claim of this test is that a person can read the message, and a
    // green run that does not show it asserts substrings about text nobody saw.
    info(message)

    // The list points, and `Odd` is what it has to point at.
    message should include("Odd")

    // **And the sentence is what makes the list a diagnosis rather than a second clue**, which is
    // the consumer's finding and not mine: `Odd, t` alone is two names, one of which the writer
    // meant as a variable, and nothing says which is which. Asserted separately from the list so
    // that deleting it fails here rather than quietly leaving the weaker message.
    message should include("read as a free variable")

    // **And the remedy follows the diagnosis**, which is the consumer's second correction and the
    // defect in the first version of this message: it opened with "annotate it" in every case, and
    // where the open name is a constant the theory has not got, annotating is precisely what does
    // not help. A reader acts on the first thing they read.
    message should include("parse against the theory that declares it")
    message should not include "annotate it"
  }

  it should "ask for an annotation where an annotation is what would help" in {
    // The other half of the pairing, and the case had to be chosen rather than assumed: an
    // undetermined type with NO open free name. `\\x. x` is it -- the binder's type is a
    // metavariable and `x` is bound, so there is no name to go looking for a theory for, and the
    // remedy that was wrong above is the right one here. Without this test, the one above is
    // satisfied by a message that never mentions annotating at all.
    val refusal = Parser.term(arithmetic, Notation.standard, "\\x. x")
    val message = refusal.fold(_.message, term => fail(s"expected a refusal, got $term"))

    info(message)
    message should include("annotate it")
    message should not include "The names whose type is still open"
  }

}
