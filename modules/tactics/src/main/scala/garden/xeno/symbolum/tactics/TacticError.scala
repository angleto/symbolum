package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.Expr
import garden.xeno.symbolum.kernel.Term
import garden.xeno.symbolum.logic.LogicError

/**
 * Why a tactic refused, and why the surface above them could not show something.
 *
 * A third error type, above the kernel's and the logic's, for the same reason there were two: each
 * layer fails in its own way and a caller wants to know which layer spoke. What is new here is
 * [[OutsideFragment]], which is not a failure of anything: it is the honest answer when an
 * expression mentions something the theory has no constant for.
 *
 * [[Remedy]] maps every case below to what a caller can do about it, as a total match, so a case
 * added here without a next step named stops compiling rather than reaching a session unusable.
 */
sealed trait TacticError {
  def message: String
}

/**
 * The expression cannot be stated in the theory of the reals as it stands.
 *
 * Not a defect and not a refusal to try: the theory has `+`, `*`, `-`, the order and the numerals,
 * and nothing else. A cosine, a logarithm or a division is outside what any of these tactics can
 * say anything about, and saying so is more useful than failing later for an obscure reason.
 */
final case class OutsideFragment(expression: Expr, reason: String) extends TacticError {
  def message: String = s"$expression is outside the fragment: $reason"
}

/**
 * The computer algebra system proposed an answer and the kernel would not certify it.
 *
 * This is the case the whole arrangement exists for. It means one of two things, and the message
 * cannot tell them apart: either the oracle is wrong, or the certifying tactic is not strong enough
 * to see that it is right. Both are honest outcomes and neither produces a theorem.
 */
final case class NotCertified(claim: String, reason: LogicError) extends TacticError {
  def message: String = s"could not certify $claim: ${reason.message}"
}

/**
 * Sayable, inside the fragment, and too expensive to attempt.
 *
 * Not a refusal by the theory and not a defect. The cost of a certification tracks the numerals in
 * it, and since 2026-09-04 it tracks how many digits they have rather than how large they are: RING
 * collects coefficients instead of expanding them, so what is paid for is the binary arithmetic on
 * the coefficient. Measured warm that day, a product of two numerals costs 7 ms at three digits and
 * 688 ms at twelve.
 *
 * So a caller with a deadline declines rather than starting. [[Oracle.NumeralBudget]] is where the
 * line is and why it is there; the certification itself has no budget, because deciding what is
 * worth waiting for belongs to whoever is waiting.
 */
final case class BeyondBudget(claim: String, largest: BigInt) extends TacticError {
  def message: String =
    s"$claim carries the numeral $largest, whose arithmetic costs more than a caller should wait for"
}

/**
 * A term cannot be shown to a person as text that reads back as the same term.
 *
 * The odd one out in this file, because it is not a refusal to prove anything: the mathematics was
 * settled and the printing is what failed. It is here rather than in the logic because the round
 * trip is a property of a theory's notation against that theory's reader, and [[Readback]], which
 * is what raises it, is the surface a session drives.
 *
 * `readBack` is the term the text came back as, or nothing when the text did not read at all. Both
 * are defects in this repository rather than in what the caller asked, and `Remedy` says so.
 */
final case class NotLegible(term: Term, readBack: Option[Term]) extends TacticError {
  def message: String = readBack match {
    case Some(other) => s"$term prints as text that reads back as $other"
    case None => s"$term prints as text that does not read back at all"
  }
}

/**
 * The goal is provable, and only at a price no procedure here will pay on a caller's behalf.
 *
 * Raised by [[Prove]] when RING and LINARITH have both refused an equation and `Field` proves it by
 * cancelling a denominator, which costs `~(d = 0)` for each one. The theorem `Field` produced is
 * deliberately thrown away and only its hypotheses are kept: a dispatcher whose callers read a
 * `Right` as "proved" would be handing them a conditional theorem under an unconditional name, and
 * a hypothesis nobody looks at is a hypothesis that is not there. What a caller can act on is the
 * price, so the price is what comes back and the theorem is fetched from `Field` by whoever wants
 * it, where the sequent shows what it rests on.
 *
 * `conditions` is `Field.conditions` of that theorem, in the order the kernel keeps them, and they
 * are carried as terms because an error carries values and the surface renders them.
 */
final case class ProvableOnlyUnder(goal: Term, conditions: Vector[Term]) extends TacticError {
  def message: String =
    s"$goal is not a theorem as written; it holds where ${conditions.mkString(" and ")}"
}

/** A failure from the layer below. */
final case class FromLogic(error: LogicError) extends TacticError {
  def message: String = error.message
}

object TacticError {

  /** A result from the logic layer as a result of this one. */
  def lift[T](result: Either[LogicError, T]): Either[TacticError, T] =
    result.left.map(FromLogic.apply)

  /**
   * What a refusal from below is about, when this refusal is one.
   *
   * `LogicError.Standing` partitions the refusals of a decision procedure into three, and it stops
   * at that layer on purpose. [[ProvableOnlyUnder]] is a goal that IS provable, at a price;
   * [[NotLegible]] is about printing and about no claim at all. Neither is a decision, a search that
   * stopped, or a question never put, and a total classification here would mean filing them under
   * one of the three and being wrong about them for ever.
   *
   * So the answer is an `Option`, and `None` means the question did not arise rather than that the
   * answer was no, which is the discipline `Evaluate` and `Refutation` keep. The two cases that do
   * carry a `LogicError` report its standing, so a caller asking `Prove` whether something was
   * decided gets the answer it would get from `Linarith`, and cannot get it by reading one of the
   * two and forgetting the other.
   */
  def standing(error: TacticError): Option[LogicError.Standing] = error match {
    case FromLogic(reason) => Some(reason.standing)
    case NotCertified(_, reason) => Some(reason.standing)
    case OutsideFragment(_, _) | BeyondBudget(_, _) | NotLegible(_, _) | ProvableOnlyUnder(_, _) =>
      None
  }

  /**
   * Whether a result decided the claim against its caller.
   *
   * `LogicError.decided` one layer out, and the predicate a negative check driven through `Prove`
   * is meant to be written with. Everything that is not a decision is false, `None` included.
   */
  def decided[T](result: Either[TacticError, T]): Boolean =
    result.left.toOption.flatMap(standing).exists(_.answersTheGoal)
}
