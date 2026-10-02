package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.theories.Real

/**
 * The names a term about the reals carries when the kernel's printer writes it, and that the reals'
 * own notation never prints.
 *
 * `Real.show` writes `real_le` as `<=`, `real_one` as `1` and the binary encoding of a numeral as
 * its digits, so any of these in a page is a term that reached the reader without the theory the
 * surface held. Read off `Real` rather than written out, so a rename moves the list with it.
 *
 * **A clean answer from this is half an assertion.** A page that stopped naming the term at all
 * holds none of these names either, so every caller also asserts the term is there in the reals'
 * notation.
 */
object KernelSpelling {

  val Names: Vector[String] = Vector(
    Real.Zero,
    Real.One,
    Real.Addition,
    Real.Multiplication,
    Real.Order,
    Real.NonStrictOrder,
    Real.Bit0,
    Real.Bit1
  )

  /** Which of the kernel's spellings `text` contains. */
  def in(text: String): Vector[String] = Names.filter(text.contains)
}
