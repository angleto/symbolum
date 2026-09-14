package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{RealTheory, Signature}

/**
 * The text a session is shown, and the one guarantee that text carries.
 *
 * A formalisation is checked by a person against the source it came from, and what that person
 * reads is a printed term. Printing is not part of any proof, so nothing in this repository made
 * the printed form and the proved form the same object: `Show` and `Parser` are separate pieces of
 * code, and a precedence disagreement between them shows one thing to a reader while the kernel
 * holds another. This prints a term and reads the text back, and hands the text over only when what
 * came back is the term that went in.
 *
 * == What the guarantee is, exactly, and what it is not ==
 *
 * It is that the text and the term are the same object under this theory's notation. Nothing more.
 * It says nothing about whether the term says what the source said, which is the translation
 * problem and is not decidable by any round trip: a formalisation can be legible, provable, and
 * about the wrong claim. What it removes is the one failure a reader cannot catch by reading, which
 * is being shown a formula other than the one that was proved. A reader can still catch a wrong
 * formalisation, and this is what makes that reading worth doing.
 *
 * So the value here is negative and worth stating as such. Without it, a person checking the
 * formalisation against the article is checking a rendering; with it, they are checking the term.
 *
 * == Why it refuses rather than warns ==
 *
 * A translation wrong in a way its reader cannot see must not be used, and refusing is the better
 * failure. Returning the text with a note attached would leave the decision to a caller that has no
 * way to make it: the text looks right, that is the whole problem. So a term that does not survive
 * the round trip produces [[NotLegible]], which `Remedy` reports as a defect in this repository
 * rather than as something the caller asked wrongly.
 *
 * == Why a theorem is taken apart ==
 *
 * `Show.show` renders a theorem as `h1, h2 |- c`, and no reader here reads a sequent: the parser
 * reads propositions. So a theorem is shown by round-tripping each hypothesis and the conclusion
 * separately and assembling the line afterwards, which means every part carries the guarantee and
 * the assembly carries none. The assembly is punctuation.
 */
object Readback {

  /** How a sequent is written when its parts have each been read back. */
  private val Turnstile: String = "|-"

  /**
   * A term as text that reads back as the same term.
   *
   * `RealTheory.term` rather than `proposition` because a term of any type can be shown: a session
   * shows the two sides of an identity as often as it shows a formula, and reading a side back
   * through a reader that insists on a proposition would refuse the legible for being true of
   * nothing.
   */
  def of(reals: Signature, term: Term): Either[TacticError, String] =
    // `Signature.legible` is the choice between the plain form and the annotated one, and it lives
    // there rather than here because the generated document needs the same choice and a second copy
    // of the rule is a second thing that can drift. What is this file's own is the refusal: a
    // caller of a tactic gets a `TacticError` naming the term, and the theories module has no such
    // thing to return.
    reals.legible(term).toRight(notLegible(reals, term))

  /**
   * Why a term could not be shown, with what came back if anything did.
   *
   * Reported against the annotated form, which is the one that was tried last and the one that
   * carries most: a reader of this refusal wants to see the fuller attempt fail, not the plainer.
   * Computed only on the failing path, where a second parse costs nothing anybody is waiting on.
   */
  private def notLegible(reals: Signature, term: Term): TacticError =
    NotLegible(term, reals.term(Show.annotated(reals.notation, term)).toOption)

  /**
   * A theorem as `h1, h2 |- c`, every part of it read back.
   *
   * The hypotheses come in the order the theorem carries them, which the kernel keeps sorted, so
   * two runs that reach the same theorem show the same line.
   */
  def of(reals: Signature, theorem: Kernel.Thm): Either[TacticError, String] =
    for {
      hypotheses <- traverse(theorem.hypotheses.toVector)(of(reals, _))
      conclusion <- of(reals, theorem.conclusion)
    } yield
      if (hypotheses.isEmpty) s"$Turnstile $conclusion"
      else s"${hypotheses.mkString(", ")} $Turnstile $conclusion"

  /**
   * What a session is told about a question and its answer, in the order a reader needs it.
   *
   * The formalisation first and the verdict second, because a verdict about a statement nobody has
   * checked is what this whole file exists to avoid handing over. A reader who stops after the
   * first line has read the thing that can be wrong.
   */
  def report(
    reals: Signature,
    source: String,
    goal: Term,
    outcome: Either[TacticError, Kernel.Thm]
  ): Either[TacticError, String] =
    for {
      formalised <- of(reals, goal)
      verdict <- outcome match {
        case Right(theorem) => of(reals, theorem).map(shown => s"proved: $shown")
        // The theory-aware mapping, because this is the one place a person reads the refusal, and
        // a message that prints the binary encoding of the numerals is the defect `NotEqualTo`
        // exists to prevent.
        case Left(error) =>
          Right(s"not proved: ${error.message}\nnext: ${Remedy.of(reals, error).message}")
      }
    } yield s"source: $source\nformalised: $formalised\n$verdict"

  private def traverse[A, B](
    items: Vector[A]
  )(f: A => Either[TacticError, B]): Either[TacticError, Vector[B]] =
    items.foldLeft[Either[TacticError, Vector[B]]](Right(Vector.empty)) { (accumulated, item) =>
      for {
        done <- accumulated
        next <- f(item)
      } yield done :+ next
    }
}
