package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What a tactic needs from a development in order to read a goal and print an answer.
 *
 * Every stateless entry point in `modules/tactics` used to take a `RealTheory`, and the reason was
 * that a `RealTheory` was the only development there was. It stopped being true on 2026-09-10, when
 * the naturals landed and `Series` became a signature holding `num` beside `real`, and it will stop
 * being true again for anything declared over the reals rather than derived from them.
 *
 * **The interface is measured rather than designed.** A count of what the tactics actually reach for
 * through the theory they are handed: `logic` twenty-one times, `proposition` six, `theory` three,
 * `show` three, and `term`, `notation` and `definitions` once each. That is this trait, and nothing
 * else in `RealTheory` is used by anything downstream. The alternative considered and rejected was a
 * capability record saying what a development offers (a ring? an order? nothing?), which is the
 * right shape once a tactic has to ask; today every one of them wants the same six things, and a
 * record with one inhabitant is an abstraction nobody has tested.
 *
 * == What it deliberately does not carry ==
 *
 * No axioms and no derived facts. A tactic that wants `LT_TOTAL` wants the theory of the reals
 * specifically and should say so by taking one, which `Linarith` and `Ring` do. This is the surface
 * for reading, printing and knowing which connectives exist, and a tactic that needs more than that
 * is not generic over developments however it is typed.
 */
trait Signature {

  /** The connectives, read against this development's own theory. */
  def logic: Logic

  /** The signature proper: what types and constants exist. */
  def theory: Theory

  /** How a term of this development is written and read. */
  def notation: Notation

  /** Read a term of any type in this development's notation. */
  def term(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text)

  /** Read a term whose type this caller already knows, in this development's notation. */
  def term(text: String, expected: Type): Either[LogicError, Term] =
    Parser.term(theory, notation, text, expected)

  /** Read a proposition in this development's notation. */
  def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)

  /** Print a term in this development's notation. */
  def show(term: Term): String = Show.show(notation, term)

  /**
   * A term as text that reads back as the same term, or nothing when no form of it does.
   *
   * The plain form wherever the plain form suffices, and the annotated one where it does not. A
   * free variable prints as a bare name and a bare name carries no type, so `mk_prod (dest_prod a)
   * = a` says nowhere what `a` is and cannot be read back at all; annotating **every** statement
   * instead would put a type on every occurrence of every free name in every statement of
   * `docs/lemmas.md` to serve the two that need it, and the document is read by people.
   *
   * **Which form is chosen is decided by trying, not by predicting.** That is what makes this worth
   * one method rather than a rule each caller applies: `Readback` guarantees a session is shown the
   * term that was proved, `Library.listing` generates a document, and `NotationRoundTripSpec`
   * asserts over both, and the three agreed only by having been written from the same paragraph.
   * They had to agree, since the test is what says the document can be read back.
   */
  def legible(statement: Term): Option[String] = {
    val plain = show(statement)

    if (term(plain).contains(statement)) Some(plain)
    else {
      val annotated = Show.annotated(notation, statement)
      if (term(annotated).contains(statement)) Some(annotated) else None
    }
  }

  /**
   * A statement set in print, and the form it reads back as, or nothing.
   *
   * The pairing is the whole of the guarantee, and the order of the two fields says which is which:
   * `printed` is for the eye and **does not read back**, `legible` is the text a reader compares
   * against the informal claim and pastes into `Ask`. Publishing the first without the second is
   * the failure this repository refuses everywhere else: a rendering a reader cannot check, shown
   * to a reader who has no way of knowing they cannot check it.
   *
   * So the gate is [[legible]] and not the printer. A statement no form of which reads back has no
   * printed form here either, however well it would set: `Library.NotReadable` marks it in the
   * document, as it did before there was a printed form at all. Nothing in the library is in that
   * state today and `LatexSpec` says which population it asked.
   */
  def readable(statement: Term): Option[Signature.Readable] =
    legible(statement).map(text => Signature.Readable(Spellings.standard.show(notation, statement), text))
}

object Signature {

  /**
   * One statement in both forms, which is the only way either of them is published.
   *
   * A case class rather than a pair, because a caller that takes `(String, String)` from a method
   * called `readable` has two texts and the order to remember, and the one mistake that matters
   * here is showing the printed form where the legible one belongs.
   */
  final case class Readable(printed: String, legible: String)
}
