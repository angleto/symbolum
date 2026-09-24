package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.{Type, TyApp}

/**
 * The table that answers a claim about `num` written with the reals' symbols.
 *
 * Two questions, and the second is the one worth the file. The first is whether the table's pairs
 * name constants that exist, which is what stops a refusal advising a reader to write something the
 * reader would refuse. The second is whether the constants it **leaves out** are the ones nothing
 * on `num` corresponds to: a table that silently stopped covering `-` would go on being right about
 * every entry it kept, and a reader who wrote `-` would be back where this started.
 */
class CounterpartSpec extends AnyFlatSpec with Matchers {

  private val widest = Chain.standard.widest
  private val notation = widest.notation

  "Every name the table pairs" should "be a constant the widest signature declares" in {
    Counterpart.onNum.foreach { case (real, num) =>
      withClue(s"the reals' `$real`: ") {
        widest.theory.constants.keySet should contain(real)
      }
      withClue(s"its counterpart `$num`: ") {
        widest.theory.constants.keySet should contain(num)
      }
    }
  }

  /** The type a binary operator takes on its left, when it has one. */
  private def leftOf(name: String): Option[Type] =
    widest.theory.constants.get(name).flatMap(Type.destFun).map(_._1)

  "The constants it leaves out" should "be the ones a reader needs no help with, and division" in {
    // The partition this asserts changed shape with `docs/adr/0018` and the assertion is stronger
    // for it, because there are now two reasons to be absent and they must not be confused.
    //
    // A real operator whose symbol `num` shares needs no row: the claim reads as written, and a row
    // would send a reader to rewrite a text that works. A real operator whose symbol `num` does NOT
    // share needs one, because the claim refuses and the reader is owed the constant that does the
    // job. So the two sets below are asserted separately rather than as one difference: a single
    // `diff` would pass if a symbol quietly stopped being overloaded AND its row were removed at
    // the same time, which is the one combination that leaves a reader with a refusal and no help.
    val realOwned = notation.infix
      .map(_.constant)
      .distinct
      .filter(name => leftOf(name).contains(Real.realType))
      .toSet

    val sharedWithNum = realOwned.filter(name =>
      notation
        .infixesFor(notation.infixOf(name).map(_.symbol).getOrElse(""))
        .exists(other => leftOf(other.constant).contains(TyApp(Natural.TypeName, Nil)))
    )

    // Four, and they are the four the record admits.
    sharedWithNum shouldBe Set(Real.Addition, Real.Multiplication, Real.Order, Real.NonStrictOrder)

    // What is left needs a row, or is division. `NUM_DIV` is not a spelling of `/`: it truncates,
    // it is total, and it comes with `NUM_MOD` beside it, so naming it here would be a refusal
    // proposing a different claim.
    realOwned.diff(sharedWithNum).diff(Counterpart.onNum.map(_._1).toSet) shouldBe Set(Real.Division)

    // And the table holds nothing a symbol already covers, which is the direction that catches a
    // row left behind rather than one never written.
    Counterpart.onNum.map(_._1).toSet.intersect(sharedWithNum) shouldBe Set.empty
  }

  "A claim about the naturals spelled with `+`" should "need no answer at all" in {
    // This asserted the opposite until `docs/adr/0018`, and the reversal is the record's whole
    // return measured at the one place a reader meets it. `!n:num. n + 0 = n` is the first claim
    // anybody writes about the naturals; it used to be refused with "real and num cannot be the
    // same type" and this table was how a reader got from there to `NUM_ADD n ZERO`. It reads now.
    //
    // Asserted in both halves, because the empty half alone would pass on a table that had stopped
    // working: the claim parses, AND nothing here proposes a rewrite of it.
    widest.proposition("!n:num. n + 0 = n").isRight shouldBe true
    Counterpart.spellings(notation, "!n:num. n + 0 = n").map(_.constant) shouldBe
      Vector(Natural.NumberZero)
  }

  it should "name the numerals too, which is what stops a second refusal" in {
    // Measured on the claim above rather than argued, and the second refusal it guards against
    // changed shape on 2026-09-12 while the guard went on being needed. It used to be that `0` was
    // the reals' numeral full stop, so a reader who took the advice about `NUM_ADD` and wrote
    // `NUM_ADD n 0` was refused again with the same message, and the advice was to spell the
    // number out with `SUC`. `NUM_ADD n 0` reads now. What can still send somebody back to the
    // start is a numeral nothing determines, so the instruction has to name the annotation rather
    // than the successor, and this asserts the new one instead of being deleted with the old.
    val found = Counterpart.spellings(notation, "!n:num. n + 0 = n")

    found.last.constant shouldBe Natural.NumberZero
    found.last.instruction should include(s"2:${Natural.TypeName}")
    found.last.instruction should include(s"2:${Real.TypeName}")
  }

  it should "say it once however many digits the claim carries" in {
    Counterpart.spellings(notation, "!n:num. n + 1 + 1 = n + 2")
      .count(_.constant == Natural.NumberZero) shouldBe 1
  }

  it should "not be needed for the mirror spellings either, which is why they were declared" in {
    // `>` and `>=` used to reach this table through `<` and `le`, since they are those two read
    // from the other end rather than constants of their own. Overloading `<` and `<=` at `num`
    // took the rows away, and that on its own would have left `!n:num. n < n` reading while
    // `!n:num. n > n` refused with nothing to say -- an asymmetry a reader meets on their second
    // line and which `docs/adr/0018` would have INTRODUCED rather than found. `Peano` declares
    // both mirrors for that reason, at no constant and no axiom.
    widest.proposition("!n:num. n > n").isRight shouldBe true
    widest.proposition("!n:num. n >= n").isRight shouldBe true
    Counterpart.spellings(notation, "!n:num. n > n") shouldBe empty
    Counterpart.spellings(notation, "!n:num. n >= n") shouldBe empty
  }

  it should "reverse the arguments where the spelling is flipped" in {
    // The half that makes the sentence worth printing, kept alive by the one row that is left.
    // `a > b` builds the term `b < a`, to the node, so a reader told to write `NUM_LT a b` would
    // state a claim about the other end of the order: worse than the type error it replaces, and
    // not something the reader could see. Nothing flipped reaches the table today, so this asserts
    // the mechanism on the row that does, and the assertion that keeps it honest is the first
    // line: a table with no flipped entry at all must not read as this test passing.
    notation.infix.filter(_.flipped).map(_.constant).toSet should contain(Real.Order)
    Counterpart.spellings(notation, "!n:num. n - 1 = n").head.instruction should
      include(s"`${Peano.Subtraction} a b`")
  }

  it should "tell one symbol from another it occurs inside" in {
    // The reason the scan is a scan and not a `contains` per symbol: `<` occurs inside `<=` and
    // inside `<=>`, so a claim about the non-strict order would have been answered about the strict
    // one, which is a different relation and a worse answer than the type error.
    //
    // Both orders were overloaded by `docs/adr/0018` and neither reaches this table any more, so
    // the property is asserted where it can still be seen: `-` occurs inside `->`, and a claim
    // whose only `-` is the arrow of a function type must not be answered about subtraction.
    Counterpart.spellings(notation, "!n:num. n - 1 = n").map(_.constant) should
      contain(Peano.Subtraction)
    Counterpart.spellings(notation, "!f:num -> num. f 0 = 0").map(_.constant) should
      not contain Peano.Subtraction
  }

  it should "warn where the counterpart is not the same function" in {
    // `NUM_SUB` truncates at zero and `-` does not, so this is the one entry whose advice changes
    // what the claim says. It is in the table because `Peano` declares it the only subtraction
    // `num` can have, and it carries the warning because a refusal must not quietly propose a
    // different claim.
    Counterpart.spellings(notation, "!m:num. m - m = m").head.instruction should include("truncates")
  }

  "A claim that names no natural number" should "get nothing from this table" in {
    // The condition that keeps it from firing on every type error a claim about the reals produces.
    Counterpart.spellings(notation, "!x:real. x + T = x") shouldBe empty
  }

  it should "not read `num` out of a longer name" in {
    Counterpart.spellings(notation, "!x:real. numerator x + 0 = x") shouldBe empty
  }
}
