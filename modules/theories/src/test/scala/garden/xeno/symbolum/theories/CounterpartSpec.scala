package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.Type

/**
 * The table that answers a claim about `num` written with the reals' symbols.
 *
 * Two questions, and the second is the one worth the file. The first is whether the five pairs name
 * constants that exist, which is what stops a refusal advising a reader to write something the
 * reader would refuse. The second is whether the constants it **leaves out** are the ones nothing
 * on `num` corresponds to: a table that silently stopped covering `<=` would go on being right about
 * every entry it kept, and a reader who wrote `<=` would be back where this started.
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

  "The constants it leaves out" should "be exactly the ones `num` has no counterpart for" in {
    // Division, and division only. `NUM_DIV` is not a spelling of `/`: it truncates, it is total,
    // and it comes with `NUM_MOD` beside it, so naming it here would be a refusal proposing a
    // different claim. Everything else the reals spell infix over their own type is in the table,
    // and an operator added to the notation later fails here until somebody decides which it is.
    val realOwned = notation.infix
      .map(_.constant)
      .distinct
      .filter(name => leftOf(name).contains(Real.realType))
      .toSet

    realOwned.diff(Counterpart.onNum.map(_._1).toSet) shouldBe Set(Real.Division)
  }

  "A claim about the naturals spelled with `+`" should "be answered with NUM_ADD" in {
    val found = Counterpart.spellings(notation, "!n:num. n + 0 = n")

    found.map(_.constant) shouldBe Vector(Peano.Addition, Natural.NumberZero)
    found.head.instruction should include(Peano.Addition)
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

  it should "reach the flipped spellings, which is why the table is keyed by constant" in {
    // `>` and `>=` are `<` and `le` read from the other end and are not constants of their own, so
    // a table of symbols would have carried four entries for two relations and would have gone
    // stale the day a third spelling arrived.
    Counterpart.spellings(notation, "!n:num. n > n").map(_.constant) shouldBe
      Vector(Peano.StrictOrder)
    Counterpart.spellings(notation, "!n:num. n >= n").map(_.constant) shouldBe
      Vector(Peano.NonStrictOrder)
  }

  it should "reverse the arguments where the spelling is flipped" in {
    // The half that makes the sentence worth printing. `a > b` builds the term `b < a`, to the node,
    // so a reader told to write `NUM_LT a b` would state a claim about the other end of the order:
    // worse than the type error it replaces, and not something the reader could see.
    Counterpart.spellings(notation, "!n:num. n > n").head.instruction should
      include(s"`${Peano.StrictOrder} b a`")
    Counterpart.spellings(notation, "!n:num. n < n").head.instruction should
      include(s"`${Peano.StrictOrder} a b`")
  }

  it should "tell `<=` from the `<` inside it" in {
    // The reason the scan is a scan and not a `contains` per symbol: `<` occurs inside `<=` and
    // inside `<=>`, so a claim about the non-strict order would have been answered about the strict
    // one, which is a different relation and a worse answer than the type error.
    Counterpart.spellings(notation, "!n:num. n <= n").map(_.constant) shouldBe
      Vector(Peano.NonStrictOrder)
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
