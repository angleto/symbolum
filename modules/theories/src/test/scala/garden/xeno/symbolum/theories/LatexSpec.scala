package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Whether every statement this repository holds can be set in print, and what that does not say.
 *
 * The table in `Spellings` is a claim about how constants are written in the literature, and no
 * test can hold that claim: `\gcd` written against `NUM_LCM` renders beautifully and wrongly, and
 * finding it is a reading, which `docs/reading-register.md` is the place for. What a test can hold
 * is the three properties that make the claim checkable by the reader who does the reading, and
 * those are what is here.
 *
 * **Coverage in both directions**, which is the drift guard. A constant of the signature with no
 * row prints as its own name in roman and nothing would say so; a row for a constant the signature
 * does not have is a spelling nobody reads, and it survives a rename that a compiler cannot catch
 * because the key is a string. Both fail here.
 *
 * **The pairing**, which is the discipline: the printed form is published only beside the form that
 * reads back. That is asserted over the whole library rather than by example, and the population is
 * printed, because a check of this shape passes vacuously the day the library is empty.
 *
 * **Two worked statements**, compared against text written by hand here. Golden output is the one
 * thing that catches a template whose braces are wrong, and it is deliberately two rather than
 * two hundred: the assertion that scales is the coverage above, and a suite that pinned every
 * statement would fail on every spelling improved.
 */
class LatexSpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val signature = chain.widest
  private val library = Library.of(chain)

  private def constantsIn(term: Term): Set[String] = term match {
    case Const(name, _) => Set(name)
    case App(fn, argument) => constantsIn(fn) ++ constantsIn(argument)
    case Abs(_, body) => constantsIn(body)
    case _ => Set.empty
  }

  private val used: Set[String] =
    library.entries
      .flatMap(entry => constantsIn(entry.theorem.conclusion) ++ entry.theorem.hypotheses.flatMap(constantsIn))
      .toSet

  /** The constants the notation already spells, which need no row of their own. */
  private val spelledByNotation: Set[String] = {
    val notation = signature.notation
    (notation.infix.map(_.constant) ++
      notation.prefix.map(_.constant) ++
      notation.binders.flatMap(_.constant) ++
      notation.numerals.flatMap(entry => Vector(entry.zero, entry.one, entry.bit0, entry.bit1))).toSet
  }

  "The table" should "spell every constant of the signature that the notation does not" in {
    val missing = signature.theory.constants.keySet -- spelledByNotation -- Spellings.standard.spelled
    info(s"${signature.theory.constants.size} constants, ${spelledByNotation.size} spelled by the notation, ${Spellings.standard.spelled.size} spelled here")

    withClue("constants with no spelling: ") { missing shouldBe empty }
  }

  it should "keep every delimited template's promise, which is that it delimits" in {
    // The guard a peer session proposed after finding two of these by reading the output, and it
    // belongs beside the coverage checks rather than among the readings: `delimited` promises that
    // the result is an atom and that the arguments sit inside marks of the template's own, and a
    // template whose placeholder is at either end carries no such mark there. `inv` spelled
    // `#1^{-1}` set the inverse of a sum as a sum with an inverse in it, and every coverage check
    // stayed green, because the row existed and the constant existed.
    //
    // What a template promises is a property of the template, so unlike the spelling itself this
    // is mechanical. Five rows failed it the day it was written, of which a reader had found two.
    val leading = """^\s*#[0-9b]""".r
    val trailing = """#[0-9b]\s*$""".r

    Spellings.standard.spellings.foreach { case (constant, spelling) =>
      if (spelling.result == Latex.Atom) {
        withClue(s"$constant is delimited and its template begins with a place: ") {
          leading.findFirstIn(spelling.template) shouldBe empty
        }
        withClue(s"$constant is delimited and its template ends with a place: ") {
          trailing.findFirstIn(spelling.template) shouldBe empty
        }
      }
    }
  }

  it should "spell nothing the signature does not have" in {
    // Stale rows are what a rename leaves behind: the key is a string, so the compiler says
    // nothing, and a spelling nobody reads is indistinguishable from one that is right.
    val stale = Spellings.standard.spelled -- signature.theory.constants.keySet
    withClue("spellings for constants nobody declares: ") { stale shouldBe empty }
  }

  it should "cover the constants the library's statements actually name" in {
    // The assertion above is about the signature; this is about what is written with it, and it is
    // the one that would go quietly empty if `Library.of` ever stopped collecting. So the
    // population is asserted before it is used.
    used.size should be > 70
    (used -- spelledByNotation -- Spellings.standard.spelled) shouldBe empty
  }

  "Every statement in the library" should "have both forms, or neither" in {
    val entries = library.entries
    entries.size should be > 200

    val unreadable = entries.filterNot(entry => signature.readable(entry.theorem.conclusion).isDefined)
    info(s"${entries.size} statements, ${entries.size - unreadable.size} with both forms")

    withClue(s"statements with no readable pair: ${unreadable.map(_.name).take(5)}") {
      unreadable shouldBe empty
    }
  }

  it should "keep the printed form out of the legible one" in {
    // The pair exists so that the two are not confused, so the cheap check that they are two
    // different texts is worth making: a `readable` that returned the ASCII twice would satisfy
    // every other assertion here.
    val differing = library.entries.count { entry =>
      signature.readable(entry.theorem.conclusion).exists(pair => pair.printed != pair.legible)
    }

    differing should be > 250
  }

  private def printed(name: String): String =
    signature.readable(library.named(name).head.theorem.conclusion).get.printed

  private def legible(name: String): String =
    signature.readable(library.named(name).head.theorem.conclusion).get.legible

  "The triangle inequality" should "be set with the bars and the quantifiers" in {
    legible(Magnitude.Triangle) shouldBe "!x:real. !y:real. abs (x + y) <= abs x + abs y"
    printed(Magnitude.Triangle) shouldBe
      """\forall x \colon \mathbb{R}.\ \forall y \colon \mathbb{R}.\ """ +
        """\lvert x + y \rvert \le \lvert x \rvert + \lvert y \rvert"""
  }

  "Addition on the naturals" should "be set as addition, and say which type it is over" in {
    // The two forms carry different halves of what a reader needs: the printed one says `+` where
    // the legible one says `NUM_ADD`, and the legible one is the text that reads back. Neither is
    // the other's improvement.
    legible("NUM_ADD_SYM") shouldBe "!x:num. !y:num. x + y = y + x"
    printed("NUM_ADD_SYM") shouldBe
      """\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ x + y = y + x"""
  }

  "The congruence" should "put the modulus where the reader expects it" in {
    // Pinned because this row was wrong first: `NUM_CONG k m n` takes the modulus **first**, and a
    // template reading `#1 \equiv #2 \pmod{#3}` set every congruence in the library beautifully
    // and about the wrong pair. No coverage check can see that, so the one reading that caught it
    // is written down here.
    printed("NUM_CONG_ADD") shouldBe
      """\forall x \colon \mathbb{N}.\ \forall y \colon \mathbb{N}.\ \forall z \colon \mathbb{N}.\ """ +
        """\forall u \colon \mathbb{N}.\ \forall v \colon \mathbb{N}.\ """ +
        """y \equiv z \pmod{x} \Rightarrow u \equiv v \pmod{x} \Rightarrow """ +
        """y + u \equiv z + v \pmod{x}"""
  }

  "A matrix type" should "keep the brackets that say it is a pair of pairs" in {
    // The other rendering defect found by reading the output: set flat, the type of a two by two
    // matrix is four reals in a row, which is a different type.
    printed("MAT_DET_MUL") should include(
      """(\mathbb{R} \times \mathbb{R}) \times (\mathbb{R} \times \mathbb{R})"""
    )
  }
}
