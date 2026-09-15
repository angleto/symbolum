package garden.xeno.symbolum.theories

import scala.annotation.tailrec
import garden.xeno.symbolum.logic.Notation

/**
 * What a claim about `num` has to be written with, for a reader who wrote the reals' symbols.
 *
 * **This file was written for a decision that has since been reversed, and what is left of it is
 * the part that decision never covered.** Until `docs/adr/0018` a `Notation` mapped a symbol to one
 * constant and the reals owned `+`, `*`, `<` and `<=`, so `!n:num. n + 0 = n`, which is the first
 * claim anybody writes about the naturals, was answered in full with
 *
 * {{{
 *   unreadable: !n:num. n + 0 = n
 *     real and num cannot be the same type
 * }}}
 *
 * true, everything the reader knew, and naming neither the owner of `+` nor the constant that does
 * the same job one type over. This table was how a reader got from that to
 * `!x:num. NUM_ADD x ZERO = x`. Today the claim reads as written, and the four rows that carried a
 * reader across are gone: see [[onNum]] for why keeping them would be worse than useless rather
 * than merely unnecessary.
 *
 * What survives is the case overloading refuses. `-` and `/` are **different operations** over
 * `num`, truncated and floor, so no symbol is going to stand for both and a reader who writes one
 * still arrives here. That is one row and one gap, and it is the whole of what this file is now
 * for. It is smaller than it was and it is not empty, which is the outcome the record predicted:
 * the symbols a reader can be given are given, and the ones that would let a reader write a false
 * lemma are withheld and explained.
 *
 * == It is keyed by constant, not by symbol ==
 *
 * The keys are the reals' **constants** and not the symbols they are spelled with, because the
 * spelling belongs to the notation and there is more than one of it: `>` and `>=` are flipped
 * spellings of `<` and `le`, so `!n:num. n > 0` reaches `Real.Order` and is answered about `NUM_LT`
 * without this table knowing that `>` exists.
 *
 * A flipped spelling also reverses its arguments, and the instruction says so: `a > b` builds the
 * same term as `b < a`, so what a reader has to write is `NUM_LT b a`. Getting that wrong would
 * send somebody to state a claim about the other end of the order, which is worse than the type
 * error it replaces and is the failure this file exists against.
 *
 * == The numerals are part of the same decision ==
 *
 * `0` and `2` belong to the reals as well: `Notation.withNumerals` names four constants and `Real`
 * supplies them, so a digit in a claim about `num` fails for the reason `+` does. It is included
 * because leaving it out is the failure `RefusalSpec` is about, arrived at from the other side: a
 * reader who takes the advice about `NUM_ADD`, writes `NUM_ADD n 0`, and is refused again has been
 * sent back to the start by a message that was right as far as it went.
 *
 * == What it deliberately leaves out ==
 *
 * `neg`, `inv` and `div`. `num` has no negation and no inverse, and its division is `NUM_DIV`,
 * which is not a spelling of `/` but a different function: truncating, total, and with `NUM_MOD`
 * beside it. Naming it for `/` would be a refusal proposing a different claim, which is the one
 * thing a refusal must not do. `CounterpartSpec` asserts that division is the only infix the reals
 * own and this leaves out, so an operator added to the notation later is a decision rather than an
 * omission.
 *
 * `NUM_SUB` is the borderline entry and is in: it truncates, so it is not `-` wherever the right
 * side exceeds the left, and `Peano` declares it the only subtraction `num` can have, so a reader
 * who wrote `-` over `num` meant this one or meant nothing. Its warning travels in the instruction
 * rather than being left for the reader to find out.
 */
object Counterpart {

  /**
   * A constant of the reals, and the constant of `num` that does its job.
   *
   * `CounterpartSpec` asserts every name on both sides is declared by the chain's widest signature,
   * so an entry that goes stale fails there rather than reaching a reader as advice to write a
   * constant that does not exist.
   *
   * **It held five until `docs/adr/0018` and holds one, and the four that left are the measure of
   * what that record bought.** `+`, `*`, `<` and `<=` now stand for the `num` constant as well as
   * the real one, so `!n:num. n + 0 = n` reads, and advice telling its writer to put `NUM_ADD n 0`
   * instead would be advice to rewrite something that already works. An entry here is not merely
   * unnecessary once its symbol is overloaded, it is **wrong**, and wrong in the direction this
   * table exists to prevent: it sends a reader away from the spelling the library now prints.
   *
   * What is left is the one symbol whose two meanings are different operations. `-` at `num` is
   * truncated, which is why `docs/adr/0018` refuses to overload it and why this row keeps the
   * caveat it always carried. `/` has never had a row and still does not; `NUM_DIV` is floor
   * division named by choice, and a reader who writes `x / y` over `num` is told the type error
   * alone, which is the gap this table had before and keeps.
   */
  val onNum: Vector[(String, String)] = Vector(
    Real.Subtraction -> Peano.Subtraction
  )

  /**
   * One thing a reader wrote, and what to write in its place.
   *
   * `wrote` is the text as it stands in the claim and `constant` is the name that replaces it, kept
   * apart from the sentence so that a test can assert which constant was named without quoting a
   * message that is allowed to be improved.
   */
  final case class Spelling(wrote: String, constant: String, instruction: String)

  /**
   * What a claim over `num` that was spelled the reals' way has to be written with.
   *
   * Empty unless the text names the type of the naturals, and that condition is what keeps this
   * from firing on every type error a claim about the reals can produce. It is a condition on the
   * **text** rather than on a term, and it has to be: there is no term, which is why there is a
   * refusal to improve at all.
   *
   * What it does not cover: a claim over `num` with the word `num` nowhere in it, because every one
   * of its naturals arrives from a constant. `NUM_LT (NUM_GCD m n) k` is such a claim and is
   * answered with the type error alone. The alternative was to look every identifier up in the
   * theory and read its type, which is the reader's own job done a second time and one more place
   * for the two answers to disagree.
   */
  def spellings(notation: Notation, text: String): Vector[Spelling] =
    if (!namesNum(text)) Vector.empty
    else operators(notation, text) ++ numeral(text)

  private def operators(notation: Notation, text: String): Vector[Spelling] = {
    val table = onNum.toMap

    symbolsIn(notation, text)
      .flatMap(symbol => notation.infixFor(symbol).map(symbol -> _))
      .flatMap { case (symbol, infix) =>
        table.get(infix.constant).map { constant =>
          // A flipped spelling reverses its arguments, which is the whole of why `>` needs a
          // different sentence from `<` and not the same one with another symbol in it.
          val applied = if (infix.flipped) s"$constant b a" else s"$constant a b"
          val caveat =
            if (infix.constant == Real.Subtraction)
              s" (${Peano.Subtraction} truncates at zero, which `$symbol` does not)"
            else ""

          Spelling(symbol, constant, s"write `$applied` where you wrote `a $symbol b`$caveat")
        }
      }
      .distinct
  }

  /**
   * The numerals, which since 2026-09-12 belong to both types rather than to the reals alone.
   *
   * What this said until that day was that `num` has no numeral notation and that every number in
   * it is spelled out, which was true and is the gap the encoding closed. The remedy it needs now
   * is the opposite one: a digit string reads at whichever type its surroundings force, and a claim
   * that reached this table with a numeral in it is one where nothing forced either. So the
   * sentence is about the annotation, which is what a writer says it with when the context does
   * not.
   *
   * One entry however many digits a claim carries, because there is one thing to say. A list per
   * digit would print the same sentence four times for `!n:num. n + 1 + 1 = n + 2`.
   */
  private def numeral(text: String): Vector[Spelling] =
    if (raw"\d".r.findFirstIn(text).isEmpty) Vector.empty
    else
      Vector(
        Spelling(
          "a numeral",
          Natural.NumberZero,
          s"a numeral reads at ${Real.TypeName} or at ${Natural.TypeName}, whichever the term " +
            s"around it forces; where nothing forces one, say it: write `2:${Natural.TypeName}` " +
            s"or `2:${Real.TypeName}`. `${Natural.NumberZero}` is still the name of `0:num` and " +
            s"still reads"
        )
      )

  /** Whether the text names `num` as a type rather than as part of a longer name. */
  private def namesNum(text: String): Boolean =
    raw"\b${Natural.TypeName}\b".r.findFirstIn(text).isDefined

  /**
   * The notation's symbols that occur in the text, in the order they occur.
   *
   * A scan rather than a `contains` per symbol, because the symbols overlap: a `contains` finds `<`
   * inside `<=` and inside `<=>`, so a claim about the non-strict order would be answered about the
   * strict one, which is a different relation. `Notation.symbols` is sorted longest first for the
   * lexer's sake, and that is what makes the first match here the right one.
   *
   * It is not the reader's lexer and does not try to be. What would tell the two apart is a symbol
   * inside a comment or a string literal, and a claim has neither.
   */
  private def symbolsIn(notation: Notation, text: String): Vector[String] = {
    @tailrec
    def go(at: Int, found: Vector[String]): Vector[String] =
      if (at >= text.length) found
      else
        notation.symbols.find(symbol => text.startsWith(symbol, at)) match {
          case Some(symbol) => go(at + symbol.length, found :+ symbol)
          case None => go(at + 1, found)
        }

    go(0, Vector.empty)
  }
}
