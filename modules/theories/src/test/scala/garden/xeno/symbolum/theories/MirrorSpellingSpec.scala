package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * `>` and `>=` are read and never written.
 *
 * The assertion that carries the whole design is the first one: the two spellings produce the
 * *same term*, not two terms that happen to be provably equivalent. A `>` that built its own
 * constant would be a second relation, and the theory would owe an axiom tying it to `<` and a
 * second copy of every order lemma. Reading it as the mirror of `<` costs nothing and adds
 * nothing to the trusted base.
 *
 * What this fixes, 2026-09-09: a session checking a corpus wrote `30 > 10` and was told
 * "cannot read the character '>'". True, and no help: what it needed was that the relation is
 * spelled the other way round. A refusal that names a character where it could name a remedy is
 * the same defect as a tactic that says the forms differ where it could name the obstacle.
 */
class MirrorSpellingSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val linarith = Linarith.standard
  private val reals = linarith.reals

  private def read(text: String): Term = force(reals.proposition(text))

  "A mirror spelling" should "build the very same term, not an equivalent one" in {
    // On the nose. Anything weaker would let the two drift apart later.
    read("30 > 10") shouldBe read("10 < 30")
    read("30 >= 10") shouldBe read("10 <= 30")
    read("!x:real. x + 1 > x") shouldBe read("!x:real. x < x + 1")
  }

  it should "never be what a term prints as" in {
    // The discipline the surface work rests on: the printed form is the one form that reads back
    // to the term it came from. Two spellings in, one spelling out.
    reals.show(read("30 > 10")) shouldBe "10 < 30"
    reals.show(read("!x:real. x + 1 >= x")) shouldBe "!x:real. x <= x + 1"
  }

  it should "round-trip through the printer" in {
    val written = reals.show(read("!x:real y:real. x * y > x + y"))
    force(reals.proposition(written)) shouldBe read("!x:real y:real. x * y > x + y")
  }

  it should "carry the theory's precedence, not a new one" in {
    // `>` sits where `<` sits, so arithmetic binds tighter on both sides exactly as it does for
    // `<`. Asserted by the term identity rather than by reading the precedence table.
    read("2 * 3 > 1 + 1") shouldBe read("1 + 1 < 2 * 3")
  }

  "A goal written with the mirror spelling" should "be proved like any other" in {
    // LINARITH rather than the dispatcher, because `theories` cannot see `tactics` and the
    // direction of that dependency is the correctness argument, not tidiness.
    linarith.prove("30 > 10") should matchPattern { case Right(_) => }
    linarith.prove("!x:real. x + 1 > x") should matchPattern { case Right(_) => }
  }

  it should "still be refused when it is false, and not for its spelling" in {
    // The refusal has to come from the procedure, not the reader: the text parsed fine.
    linarith.prove("10 > 30").left.map(_.getClass) should not be Left(classOf[SyntaxError])
    linarith.prove("10 > 30") should matchPattern { case Left(_) => }
  }

  "The lexer" should "still refuse a character the notation has no operator for" in {
    // The fix is two spellings, not a lexer that shrugs. `$` is nobody's.
    reals.proposition("3 $ 4").left.map(_.getClass) shouldBe Left(classOf[SyntaxError])
  }

  "The theory it reads in" should "still assert only the reals' axioms" in {
    // A spelling is not a constant: nothing about the trusted base moves.
    reals.theory.axioms.length shouldBe Real.Axioms.length
    reals.theory.constants.keySet should not contain ">"
  }
}
