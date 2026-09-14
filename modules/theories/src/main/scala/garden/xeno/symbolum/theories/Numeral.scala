package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Numerals, and what can be proved about them with the rules that exist.
 *
 * A numeral is a term like any other: `4` is `BIT0 (BIT0 1)`, which by the definitions of those
 * two constants is `(1 + 1) + (1 + 1)`. Nothing here is an axiom and nothing here is built into
 * the parser beyond the spelling; the arithmetic has to be proved from the field axioms like
 * everything else.
 *
 * == What is proved here, and what is not ==
 *
 * [[doubling]] proves `n + n = 2n` for any numeral, and it is not a special case: it is exactly
 * the definition of `BIT0` read backwards, so it needs no rearrangement of a sum. `2 + 2 = 4` is
 * an instance.
 *
 * General addition is not here. `2 + 3 = 5` needs the associativity and commutativity axioms
 * applied at chosen positions inside a term, which is rewriting, and rewriting with a lemma at a
 * subterm is the conversion engine that does not exist yet. Deriving the handful of bit lemmas by
 * hand with the congruence rules would work and would be thrown away by that engine, so it waits
 * for it.
 */
object Numeral {

  /**
   * The numeral for a non-negative value, at `real`, said out loud.
   *
   * The annotation is not decoration and was added on 2026-09-12 with a measurement behind it. This
   * read `reals.term(value.toString)` and got a real because a digit string had nowhere else to go;
   * with `num` reading numerals too, a bare digit string put to the **widest** signature is
   * genuinely ambiguous and is refused, and every one of miniF2F's 244 statements went unreadable
   * in one run because `Translate` builds its literals through here. The function's name and its
   * one caller both say `real`, so saying it in the text is the repair rather than a workaround:
   * what broke was a signature-dependent answer to a question that never depended on the signature.
   */
  def of(reals: Signature, value: BigInt): Either[LogicError, Term] =
    if (value < 0) Left(TypeError(s"$value is not a numeral: numerals here are non-negative"))
    else reals.term(s"$value:${Real.TypeName}")

  /** The value a term denotes, if it is a numeral. */
  def valueOf(reals: Signature, term: Term): Option[BigInt] =
    reals.notation.valueOfNumeral(term)

  /**
   * `|- n + n = 2n`, for a numeral `n`.
   *
   * The whole proof is one step: `BIT0 n` is defined as `n + n`, so unfolding the definition at
   * `n` and reversing the equation is the theorem. The result prints as arithmetic because `BIT0
   * n` is the numeral for twice `n`, which is what the encoding was chosen for.
   */
  def doubling(reals: RealTheory, numeral: Term): Either[LogicError, Kernel.Thm] =
    for {
      definition <- reals.definition(Real.Bit0)
      unfolded <- Conv.unfold(definition, List(numeral))
      result <- Conv.sym(unfolded)
    } yield result

  /**
   * `|- BIT1 n = (n + n) + 1`.
   *
   * The other half of the encoding, and equally a definition read backwards: an odd numeral is
   * twice the one below it plus one, and that is what `BIT1` says. It does not say `BIT0 n + 1`,
   * which is how a version of this comment put it: `BIT1` is defined on its own, not through
   * `BIT0`, and the theorem states what the definition states.
   */
  def successorOfDouble(reals: RealTheory, numeral: Term): Either[LogicError, Kernel.Thm] =
    reals.definition(Real.Bit1).flatMap(Conv.unfold(_, List(numeral)))
}
