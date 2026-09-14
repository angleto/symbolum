package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A tactic for identities of a commutative ring: give it an equation and it proves it, or says it
 * cannot.
 *
 * `!x y. (x + y) * (x + y) = x * x + 2 * (x * y) + y * y` goes in and a theorem comes out. Both
 * sides are put in a normal form and compared, and what this adds is the part that makes it a
 * tactic rather than a function: it takes the quantifiers off the goal, works on the body, and puts
 * them back.
 *
 * == Which normal form, and why there are two ==
 *
 * [[Polynomial]] is the one it uses: a sorted sum of monomials, each a numeral coefficient times a
 * sorted product of atoms. A coefficient stays a number, so `2 * x` normalises to `2 * x` and
 * `x + x` to `2 * x` as well.
 *
 * [[Arithmetic.normalisation]] is the other, and it is not a superseded version: it is what the
 * arithmetic lemmas and the structural lemmas of the collecting form are proved with. It expands a
 * coefficient of `n` into `n` copies of the term, which costs nothing on an identity over variables
 * with no numeral in it, which is what those lemmas are. [[Ring.expanding]] is a tactic over it, so
 * the two can be measured against each other; `RingCostSpec` is where that measurement lives.
 *
 * The expansion is what made a coefficient expensive. Measured inside the suite on 2026-09-04,
 * warm, `12 * 12` normalises to 573 nodes in 528 ms through the expanding form and to 15 nodes in
 * 2 ms through this one; `(x + 1)^12` reaches 507 nodes in 143 ms here and 98305 nodes there. Read
 * the times as orders of magnitude and the node counts as facts: the same ladder run cold outside
 * the suite was four to ten times slower and gave the same sizes to the node.
 *
 * == What it does not cover ==
 *
 * Cancelling a *symbolic* inverse. `inv x` is an atom here and stays one, so `x * inv x` does not
 * become `1`: the axiom that would make it `1` holds only under `~(x = 0)`, and this tactic has
 * nowhere to put a hypothesis. [[Field]] is the one that does, and what it returns carries the
 * condition.
 *
 * A denominator that is itself a coefficient is a different matter and is decided here: a numeral,
 * a negated numeral, or either of those over a numeral, which is the whole of what
 * [[Coefficient.ofInverse]] inverts. `~(2 = 0)` is a theorem rather than a hypothesis, so
 * `x / 2 + x / 2 = x` comes back with nothing assumed. `x / (-2) = -(x / 2)` and
 * `x / (2 / 3) = 3 * x / 2` come back the same way, and `FieldSpec` puts both to this tactic and
 * reads the hypothesis list rather than only that they proved. A coefficient in this normal form
 * is a rational number and [[Coefficient]] is its arithmetic: a numeral's `~(d = 0)` comes from
 * [[Positivity.numeralNonZero]], and for a denominator that is not a numeral the condition is
 * discharged by the arithmetic instead, since `Coefficient.inverseOfUnit` takes a factor of one as
 * its premise, a term that multiplies to one cannot be zero, and the factor is the reciprocal the
 * arithmetic computes anyway.
 *
 * Zero is where that stops. `inv 0` stays an atom, because nothing the theory knows multiplies it
 * to one, and the atom is a refusal rather than a gap: `x / 0 + x / 0 = 2 * (x / 0)` is proved
 * with nothing assumed and `x / 0 = 0` is refused, which is the pair `FieldSpec` pins.
 *
 * Division is covered, and used not to be. `x / y` abbreviates `x * inv y`, and unfolding an
 * abbreviation asks for nothing; what asks for `~(y = 0)` is the cancelling, which is a different
 * step. The two were written down as one sentence until 2026-09-08, and the cost of that was that
 * `(z * x) / (2 * y)` and `z * (x / (2 * y))` were two terms.
 *
 * Subtraction and negation are covered: `-` unfolds, negations move down to the atoms, and a term
 * meeting its own negation cancels.
 */
final class Ring private (
  val arithmetic: Arithmetic,
  /**
   * That a numeral is above zero, and so is not zero.
   *
   * Held here rather than built by each consumer so that a theory has one copy of those facts.
   * [[Order]] takes three of the facts it holds from here instead of deriving them again, and the reason
   * they are derived below the ring at all is in [[Positivity]]: a rational coefficient needs
   * `~(n = 0)` for a numeral, and nothing below the order can prove it.
   */
  val positivity: Positivity,
  private val normalisation: Rewrite.Conversion
) {

  val reals: RealTheory = arithmetic.reals


  /**
   * Prove an equation, with or without leading quantifiers.
   *
   * The quantifiers come off, the body is proved about fresh variables, and they go back on in the
   * order they were written. Working on the body is what lets the normalisation see the structure:
   * a quantified statement is an application of a constant to a lambda, and there is nothing in it
   * to distribute.
   */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    Rewrite.proveEquation(reals.logic, normalisation, goal)

  /** Prove an equation written in the theory's notation. */
  def prove(text: String): Either[LogicError, Kernel.Thm] =
    reals.proposition(text).flatMap(prove)

  /** The normal form of a term, as a theorem saying the two are equal. */
  def normalise(term: Term): Either[LogicError, Kernel.Thm] = normalisation(term)

}

object Ring {

  /** Built once over the standard theory of the reals. */
  lazy val standard: Ring =
    construct(Arithmetic.standard).fold(
      error => throw new IllegalStateException(s"the ring tactic does not build: ${error.message}"),
      identity
    )

  /**
   * The tactic over a theory whose arithmetic has already been proved.
   *
   * The collecting normal form is built on that arithmetic rather than beside it: its coefficients
   * are added and multiplied by [[Arithmetic.add]] and [[Arithmetic.multiply]], and its structural
   * lemmas are proved by the expanding normalisation. A second copy of either would be a second
   * thing to keep in agreement.
   */
  def construct(arithmetic: Arithmetic): Either[LogicError, Ring] =
    for {
      positivity <- Positivity.construct(arithmetic)
      coefficient <- Coefficient.construct(arithmetic, positivity)
      collecting <- Polynomial.construct(coefficient)
    } yield new Ring(arithmetic, positivity, collecting.normalisation)

  /**
   * The same tactic over the expanding normal form, which is kept for measuring against.
   *
   * Not deprecated and not a fallback. It decides the same fragment; what differs is the size of
   * the normal form, and a claim about that difference is worth only as much as the pair of
   * measurements behind it. It is also the form that proves the lemmas the collecting one runs on,
   * so it cannot be removed while that one exists.
   */
  def expanding(arithmetic: Arithmetic): Either[LogicError, Ring] =
    Positivity.construct(arithmetic).map(new Ring(arithmetic, _, arithmetic.normalisation))
}
