package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Linear arithmetic over the naturals, as a procedure a caller outside this module can ask.
 *
 * The procedure is `NumberSteps.numLin`, which settles a comparison or an equation of naturals, or a
 * conjunction of them, from facts that are comparisons of naturals, by carrying everything to the
 * reals through `real_of_num` and handing it to `Linarith` with every image known to be
 * non-negative. It was written for the derivations beside `Complex` and stayed private to this
 * module, so the one place a person writes a proof without Scala, the proof language in `tactics`,
 * had no way to say "this is arithmetic" about a goal over `num`. This class is that way and adds
 * nothing to the procedure: what comes back is the theorem `numLin` built, or its refusal.
 *
 * Built over the widest link's kit, because that kit's lookup reaches every fact the procedure
 * cites (`NUM_LE_ANTISYM`, `NUM_REAL_LE_BACK`, `NUM_REAL_NONNEG` and the embedding equations) from
 * whichever link holds it.
 */
final class NaturalLinear private (steps: NumberSteps) {

  /** `goal`, a comparison of naturals or a conjunction of them, from `facts`, or the refusal. */
  def apply(facts: Seq[Kernel.Thm], goal: Term): Either[LogicError, Kernel.Thm] = steps.numLin(facts, goal)
}

object NaturalLinear {

  /** The procedure over `chain`. */
  def of(chain: Chain): Either[LogicError, NaturalLinear] =
    Semiring.construct(chain.peano).map(semiring => new NaturalLinear(new NumberSteps(chain.decision.kit, semiring)))
}
