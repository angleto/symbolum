package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The completed square attacked at its edges, for the verification of Mycelium card `bacfaba5` on
 * 2026-09-26.
 *
 * `LinarithSpec` holds the two miniF2F statements and each moved by one. This file adds the near
 * misses a source that manufactured facts carelessly would get wrong, the square the completion does
 * not reach, and the quartic on both sides of its truth: each true claim either proved or refused
 * by name, each false one refused, and every proof resting on the reals' axioms alone.
 */
class LinarithSquareBoundarySpec extends AnyFlatSpec with Matchers {

  private val linarith = Linarith.standard
  private val believed: Set[Term] = linarith.reals.theory.axioms.toSet

  private def proved(text: String): Kernel.Thm = {
    val theorem = linarith.prove(text).fold(error => fail(s"$text: ${error.message}"), identity)
    withClue(s"$text: ") {
      theorem.hypotheses shouldBe empty
      Derivation.axiomsOf(theorem).diff(believed) shouldBe empty
    }
    theorem
  }

  private def refused(text: String): LogicError =
    linarith.prove(text).fold(identity, theorem => fail(s"$text was proved: ${theorem.conclusion}"))

  "A square that is true" should "be proved without a hypothesis" in {
    Vector(
      "!x:real. x * x - 2 * x + 1 >= 0",
      "!x:real. 0 - x * x <= 0",
      "!x:real. x * x + 1 > 0",
      "!a:real. 4 * (a * a) - 4 * a + 1 >= 0"
    ).foreach(proved)
  }

  "A square one step past its truth" should "be refused" in {
    // Each is false at one point: `x = 1` for the first three, `a = 1/2` for the fourth. A source
    // that produced a fact it had not justified would prove at least one of them.
    Vector(
      "!x:real. x * x - 2 * x + 1 > 0",
      "!a:real. a * (2 - a) < 1",
      "!x:real. x * x >= 2 * x",
      "!a:real. 4 * (a * a) - 4 * a + 1 > 0"
    ).foreach(refused)
  }

  "A quartic without hypotheses" should "be refused naming the empty pool, on either side of its truth" in {
    // `(x * x) * (x * x) >= 0` is true and `> 0` is false at zero; both are an atom of four factors
    // that is not one unknown times itself, so neither the schedule nor the completion reaches it,
    // and the refusal must say which obstacle it met rather than answer.
    Vector("!x:real. (x * x) * (x * x) >= 0", "!x:real. (x * x) * (x * x) > 0").foreach { text =>
      val error = refused(text)
      withClue(s"$text: ${error.message}\n") {
        error.message should include("pool")
        error.message should not include "multiplied reach three"
      }
    }
  }

  "The same quartic under hypotheses" should "still hear about the degree" in {
    val error = refused("!w:real x:real y:real z:real. 0 < w /\\ 0 < x /\\ 0 < y /\\ 0 < z ==> 0 < w * x * y * z")
    error.message should include("multiplied reach three")
  }

  "A square the completion does not reach" should "be refused rather than guessed" in {
    // `(x - y)^2 >= 0` needs the cross term `x * y`, which is a product of two different unknowns
    // and not one unknown times itself. It is true; what is asserted is that the procedure does not
    // answer it by guessing: a refusal, whatever its sentence, printed so the verdict can quote it.
    val error = refused("!x:real y:real. x * x + y * y >= 2 * (x * y)")
    info(s"${error.standing}: ${error.message}")
  }

  it should "name the cross term as the obstacle, not a square it completed" in {
    // Found by this file on 2026-09-26 at `1bcad72b`. The refusal names `x * x` as the product out
    // of reach and ends "an atom that is one unknown times itself, and this goal has none", while
    // `x * x` and `y * y` are exactly such atoms and the one out of reach is `x * y`. `naming`
    // picks the first goal atom outside the products by term order and does not leave out the
    // atoms a square covers. It was held pending until the message named the obstacle it met, which
    // is the acceptance criterion of card `bacfaba5` that says the refusal keeps naming it, and the
    // wrapper came off in the change to `naming` that made it pass.
    val message = refused("!x:real y:real. x * x + y * y >= 2 * (x * y)").message
    message should include("x * y")
    message should not include "this goal has none"
  }

  // Second round of the verification of card `bacfaba5`, 2026-09-27, over `f62925b6` and `45e5fdcc`.
  // The assertion above passes on `include("x * y")`, which a message naming `x * x` and quoting
  // the goal could also satisfy; these read the atom the refusal names, which is what sits before
  // "is a product of", and ask of it what the completion cannot cover: that it is not one unknown
  // times itself whenever the goal holds an atom that is not.
  private val Named = """:\s([^:]+?) is a product of""".r

  private def named(text: String): Option[String] = {
    val error = refused(text)
    info(s"$text\n    ${error.standing}: ${error.message}")
    Named.findFirstMatchIn(error.message).map(_.group(1))
  }

  private val Square = """^\(?(\w+) \* (\w+)\)?$""".r

  private def isSquare(atom: String): Boolean = atom match {
    case Square(left, right) => left == right
    case _ => false
  }

  "The atom a refusal names" should "be one no square covers, whenever the goal holds such an atom" in {
    Vector(
      "!x:real y:real z:real. x * x + y * y + z * z >= x * y + y * z + z * x" -> Set("x * y", "y * z", "x * z", "z * x", "y * x", "z * y"),
      "!x:real y:real. 3 * (x * x) + y * y >= x * y" -> Set("x * y", "y * x"),
      // The binders are renamed by the reader before LINARITH sees them, so the cross term of this
      // one is printed `x * y`, which the first run of this test on 2026-09-27 found and this set
      // now says: the order of the letters in the text is what is varied, not the atom.
      "!b:real a:real. b * b + a * a >= 2 * (a * b)" -> Set("x * y", "y * x"),
      "!x:real y:real. x * x + y * y >= x * x * y" -> Set("x * x * y", "y * x * x", "x * y * x"),
      "!x:real y:real. 0 < y ==> x * x + y * y >= 2 * (x * y)" -> Set("x * y", "y * x"),
      "!x:real y:real. 0 < y ==> x * x * y * y >= 0" -> Set("x * x * y * y", "y * y * x * x")
    ).flatMap { case (text, expected) =>
      // Every case is asked before anything is asserted, so a red names all the misses at once
      // rather than hiding the ones after the first.
      named(text) match {
        case Some(atom) if !isSquare(atom) && expected.contains(atom) => None
        case other => Some(s"$text named $other, expected one of $expected")
      }
    } shouldBe empty
  }

  "A goal whose only products are squares" should "be refused, and the verdict reads what it names" in {
    // No atom out of reach is anything but a square here, so the fallback names one. Recorded rather
    // than asserted, because whether that sentence is right is the question the verdict answers.
    Vector("!x:real. x * x >= 1", "!x:real y:real. x * x + y * y >= 1").foreach { text =>
      info(s"named: ${named(text)}")
    }
  }
}
