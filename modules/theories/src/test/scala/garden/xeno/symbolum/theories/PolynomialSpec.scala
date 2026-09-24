package garden.xeno.symbolum.theories

import org.scalacheck.{Gen, Shrink}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The collecting normal form: what it produces, and the one way it can be wrong.
 *
 * Every step it takes is a kernel theorem, so it cannot produce a false one. What it can do is send
 * two terms of the same value to two different terms, and then `Ring` refuses an identity that
 * holds. That is what the property in the middle of this file looks for, and it looks for it the
 * only way worth looking: by writing the same value two ways and demanding one answer.
 *
 * The examples at the top are the degenerate cases, which are where a normal form usually breaks:
 * the empty polynomial, the empty product, a coefficient of one, a coefficient of minus one, and a
 * monomial that cancels itself.
 */
class PolynomialSpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {

  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 100)

  /**
   * No shrinking, because what this generator produces is source text.
   *
   * ScalaCheck's shrinker for a pair of strings takes characters off them, and a term with
   * characters missing does not parse, so a genuine counterexample was reported as
   * `("", "")` and a syntax error. The failure it was hiding was real. A shrunk case that cannot
   * be read is worse than an unshrunk one that can.
   */
  implicit private val doNotShrink: Shrink[(String, String)] = Shrink.shrinkAny

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val arithmetic = Arithmetic.standard
  private val reals = arithmetic.reals
  private val collecting = force(Polynomial.construct(Coefficient.standard)).normalisation
  private val expanding = arithmetic.normalisation

  private def read(text: String): Term = force(reals.term(text))

  /** The normal form of a term, as the term. */
  private def formOf(conversion: Rewrite.Conversion, text: String): Term =
    force(Term.destEq(force(conversion(read(text))).conclusion).toRight("not an equation"))._2

  private def normalises(text: String, expected: String): Unit =
    reals.show(formOf(collecting, text)) shouldBe expected

  "The collecting form" should "build over the standard arithmetic" in {
    Polynomial.construct(Coefficient.standard) should matchPattern { case Right(_) => }
  }

  it should "keep a coefficient as a number" in {
    // The whole difference from the expanding form, in one line: this is where `2 * x` used to
    // become `x + x`.
    normalises("2 * x:real", "2 * x")
    normalises("1000 * x:real", "1000 * x")
  }

  it should "collect a coefficient that was written as a repeated sum" in {
    normalises("x:real + x", "2 * x")
    normalises("x:real + x + x", "3 * x")
  }

  it should "compute a product of numerals rather than expanding it" in {
    normalises("12 * 12", "144")
  }

  it should "put the empty polynomial as zero and drop nothing else" in {
    normalises("x:real - x", "0")
    normalises("0", "0")
    normalises("x:real * 0", "0")
  }

  it should "absorb a coefficient of one and of minus one" in {
    normalises("1 * x:real", "x")
    normalises("-x:real", "-x")
    normalises("0 - x:real", "-x")
  }

  it should "order the monomials by degree and then by their atoms" in {
    normalises("(x:real + 1) * (x + 1)", "1 + (2 * x + x * x)")
    normalises("3 * (x:real + 1)", "3 + 3 * x")
  }

  it should "collect over an atom it cannot take apart" in {
    // The case that decides the architecture, and the middle monomial is what makes it one.
    // `inv x` is opaque to this theory and its head constant sorts after `BIT0`, so under
    // `Arithmetic.ringOrder` the coefficient leads and a monomial is compared by its coefficient
    // first. `4 * inv y` therefore sorts between the two `inv x` monomials, they are not
    // neighbours, and no rule between neighbours could ever bring them together. Collecting by a
    // merge rather than by rewriting is what makes this one work.
    normalises("2 * inv x:real + 4 * inv y:real + 8 * inv x", "10 * inv x + 4 * inv y")
    normalises("2 * inv x:real + 3 * inv x", "5 * inv x")
  }

  it should "not have needed that architecture for a monomial made of variables" in {
    // The other half of the sentence above, and it is here because a first version of the comment
    // in `Polynomial` used `{2 * inv x, 3 * y, 5 * inv x}` as its witness and that one separates
    // nothing: the ordered product rules settle `3 * y` as `y * 3`, since a variable sorts below a
    // numeral, and `y * 3` then sorts below both. Pinned so that the claim cannot rot back.
    val settled = Vector("3 * y:real", "y:real * 3").map(read).min(Arithmetic.ringOrder)
    reals.show(settled) shouldBe "y * 3"

    val separator = Vector("4 * inv y:real", "inv y:real * 4").map(read).min(Arithmetic.ringOrder)
    reals.show(separator) shouldBe "4 * inv y"
  }

  it should "reach inside a term it treats as opaque" in {
    // Neither normal form has a rule for `inv` or `div`, but the expanding one reaches inside them
    // anyway, because `Rewrite.depthConv` rewrites a subterm whatever its parent is. So
    // `inv (x + x)` and `inv (2 * x)` are one term there and the identity between them is proved.
    // A recursion that stopped at the atom would make them two atoms and refuse it, which is the
    // one failure this design can have: two terms of equal value reaching two different terms.
    normalises("inv (x:real + x)", "inv (2 * x)")
    normalises("x:real / (y:real + y)", "x * inv (2 * y)")
    normalises("inv (x:real * 1 + 0)", "inv x")

    Ring.standard.prove("!x:real. inv (x + x) = inv (2 * x)") should matchPattern { case Right(_) => }
  }

  it should "contract a redex rather than take it for an atom" in {
    // `Rewrite.betaConv` sits in the expanding form's rule vector, so a redex of type real is an
    // ordinary ring expression there. Without the same case here it would become an atom, and an
    // identity across it would stop being provable.
    normalises("(\\y:real. y + y) x:real", "2 * x")
  }

  it should "still unfold a bit applied to something that is not a numeral" in {
    // `BIT0 x` is an ordinary ring expression, and the expanding form could always handle it.
    // Recognising a numeral before taking a term apart is what keeps both true at once.
    normalises("BIT0 x:real", "2 * x")
  }

  "A term this procedure does not interpret" should "come through unchanged" in {
    normalises("inv x:real", "inv x")
  }

  it should "not include a quotient, which is interpreted after all" in {
    // `div` is an abbreviation and unfolding it needs nothing, so a quotient is a product with an
    // opaque factor rather than an opaque term. `inv y` is where the interpretation stops, and it
    // stops there because cancelling it would need `~(y = 0)`, which no normal form can assume on
    // its own. Two spellings of one quotient are one term from here.
    normalises("x:real / y:real", "x * inv y")
    // The example the field task names, and the whole denominator stays one atom: `inv (2 * y)`
    // is not `inv 2 * inv y`, because splitting it is a step this normal form does not take and
    // does not need to take for the two spellings to meet.
    normalises("(z:real * x:real) / (2 * y:real)", "x * (z * inv (2 * y))")
  }

  /* ------------------------------------------------------------------ the property */

  /**
   * An atom, and a second spelling of the same atom.
   *
   * The compound ones are the point. An atom is a term the procedure decided not to interpret, and
   * it still has to interpret what that term is applied to, or `inv (x + x)` and `inv (2 * x)`
   * become two atoms and the identity between them is refused. A generator whose atoms were all
   * `inv x` could not see that, and the first version of this one could not: the case was found by
   * a second reader of the file instead.
   *
   * Every compound spelling is parenthesised, and that is not tidiness. `*` and `/` share a
   * precedence, so an unbracketed `x / (y + y)` dropped into a product re-associates: `z * x / (y +
   * y)` reads as `(z * x) / (y + y)`, one atom, while `x / (2 * y) * z` reads as `(x / (2 * y)) * z`,
   * a product of two. Those are different terms, both normal forms refuse the identity between them
   * because nothing unfolds `div`, and the property below reported it as a disagreement. It was
   * right to: the two strings did not denote the same value, which is the generator's job to
   * guarantee and was its bug rather than the procedure's.
   */
  private val atoms: Gen[(String, String)] = Gen.oneOf(
    ("x:real", "x:real"),
    ("y:real", "y:real"),
    ("z:real", "z:real"),
    ("(inv x:real)", "(inv x:real)"),
    ("(inv (x:real + y:real))", "(inv (y:real + x:real))"),
    ("(inv (x:real + x))", "(inv (2 * x:real))"),
    ("(x:real / (y:real + y))", "(x:real / (2 * y:real))")
  )

  /**
   * A leaf, three times out of four an atom.
   *
   * Numerals are the rarer leaf and they stop at four on purpose: eight of them multiplied together
   * is the deepest this generator goes, and the coefficient arithmetic is the one part of the
   * procedure whose cost grows with the value rather than with the size of the term. Measured warm
   * on 2026-09-04, a product of two numerals costs 7 ms at three digits and 104 ms at six, so a
   * generator that reached six digits would put a tenth of a second into a draw to test nothing
   * new. Read that as the warm figure: the same call was 459 ms on the first invocation of the day.
   */
  private val leaf: Gen[(String, String)] =
    Gen.frequency((3, atoms), (1, Gen.choose(0, 4).map(value => (value.toString, value.toString))))

  /**
   * An expression, and the same expression written differently.
   *
   * The variant commutes every sum and product it passes and writes a subtraction as an addition of
   * a negation, both of which the axioms justify, so the two terms denote the same value however
   * the generator chose. Anything else would be testing the generator.
   */
  private def expression(depth: Int): Gen[(String, String)] =
    if (depth == 0) leaf
    else
      Gen.oneOf(
        for {
          left <- expression(depth - 1)
          right <- expression(depth - 1)
          swap <- Gen.oneOf(true, false)
        } yield (
          s"(${left._1} + ${right._1})",
          if (swap) s"(${right._2} + ${left._2})" else s"(${left._2} + ${right._2})"
        ),
        for {
          left <- expression(depth - 1)
          right <- expression(depth - 1)
          swap <- Gen.oneOf(true, false)
        } yield (
          s"(${left._1} * ${right._1})",
          if (swap) s"(${right._2} * ${left._2})" else s"(${left._2} * ${right._2})"
        ),
        for {
          left <- expression(depth - 1)
          right <- expression(depth - 1)
          unfold <- Gen.oneOf(true, false)
        } yield (
          s"(${left._1} - ${right._1})",
          if (unfold) s"(${left._2} + -(${right._2}))" else s"(${left._2} - ${right._2})"
        ),
        expression(depth - 1).map { case (one, other) => (s"-($one)", s"-($other)") }
      )

  "Two ways of writing one value" should "reach the same term" in {
    // A hundred samples at depth three, which is the count `ArithmeticSpec` settled on and the
    // depth at which the generator starts producing coefficients the expanding form could not
    // afford: measured while writing this, no later than 2026-09-14, a depth-three sample reached
    // a coefficient above forty about one time in twenty.
    forAll(expression(3)) { case (one, other) =>
      formOf(collecting, one) shouldBe formOf(collecting, other)
    }
  }

  it should "reach a term the procedure then leaves alone" in {
    // Idempotence, and it is not decoration: `Rewrite.proveWith` asks whether a form is at a fixed
    // point in order to tell an unfinished rewriting from a false identity, and a normal form that
    // moved under a second pass would make that diagnostic lie.
    forAll(expression(3)) { case (one, _) =>
      val form = formOf(collecting, one)
      force(collecting(form)).conclusion shouldBe force(Term.eq(form, form))
    }
  }

  "Values that differ" should "not be sent to one term" in {
    // A procedure that sent every term to `0` would satisfy both properties above and be useless.
    // This is the one it fails, and it belongs here rather than among the examples because what it
    // asserts is about the whole list and not about any entry in it.
    val forms = Vector(
      "0", "1", "2", "x:real", "-x:real", "2 * x:real", "x:real + 1", "x:real * x",
      "x:real * y:real", "2 * x:real + 1", "inv x:real", "y:real"
    ).map(text => formOf(collecting, text))

    forms.distinct.length shouldBe forms.length
  }

  /* ------------------------------------------------------- against the other form */

  "The two normal forms" should "decide the same identities" in {
    // Where the expanding form can still afford an answer, it is the second opinion: it reaches a
    // different normal form by a different procedure, so agreement between them is evidence about
    // the fragment rather than about one implementation.
    val corpus = Vector(
      "(x:real + y:real) * (x + y)",
      "(x:real - y:real) * (x + y)",
      "x:real * (y:real + 1) + -(x * y)",
      "-(x:real + y:real) + x",
      "(x:real + 1) * (x + 1) * (x + 1)",
      "3 * (x:real * y:real) - y * x",
      "(x:real - 1) * (x + 1) + 1"
    )

    corpus.foreach { text =>
      val collected = formOf(collecting, text)
      val expandedFromCollected = force(expanding(collected))
      val expandedFromSource = force(expanding(read(text)))

      withClue(s"$text: ") {
        force(Term.destEq(expandedFromCollected.conclusion).toRight("not an equation"))._2 shouldBe
          force(Term.destEq(expandedFromSource.conclusion).toRight("not an equation"))._2
      }
    }
  }

  /* ------------------------------------------------------------------- refusals */

  "The tactic over this form" should "refuse an equation that is not an identity" in {
    val ring = Ring.standard
    // `NotEqualTo` rather than `NotOfForm` since 2026-09-08: both sides reached a normal form and
    // the forms differ, which is a different finding from "this was not the shape I needed" and now
    // has its own case carrying both terms.
    ring.prove("!x:real. x + x = 3 * x").left.map(_.getClass) shouldBe Left(classOf[NotEqualTo])
    ring.prove("!x:real. x * inv x = 1").left.map(_.getClass) shouldBe Left(classOf[NotEqualTo])
  }

  "The theory it works in" should "still assert only the reals' axioms" in {
    reals.theory.axioms.length shouldBe Real.Axioms.length
  }
}
