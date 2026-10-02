package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * `|- inv 0 = 0` in the reals' own vocabulary, which nothing publishes under a name of the reals and
 * the constructed reals prove from their definitions: `inv` and `0` unfolded to `CUT_INV` and the
 * cut of zero, and `CUT_INV_ZERO` read back through them.
 *
 * Two specs need it. `InverseAtZeroSpec` measures what it rests on; `TranscendentalSpec` spends it
 * on `EXP_ONE_IRRATIONAL`'s hypothesis, which it shows idle at a denominator of zero. Written once
 * here so that the two cannot disagree about what was derived.
 */
object InverseAtZero {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => throw new IllegalStateException(error.toString), identity)

  private val reals = Real.standard
  private val cuts = Real.constructed.cuts

  lazy val theorem: Kernel.Thm = {
    val goal = force(reals.proposition("inv (0:real) = 0"))
    val aliases = Vector(force(reals.definition(Real.Inverse)), force(reals.definition(Real.Zero)))
    val unfold = Rewrite.normaliser(force(Rewrite.Rule.all(reals.logic, aliases)), Vector.empty, Ordering.by[Term, String](_.toString))
    val unfolded = force(unfold(goal))
    val onCuts = force(cuts.fact(Cut.InverseZero))
    force(Conv.sym(unfolded).flatMap(back => LogicError.lift(Kernel.eqMp(back, onCuts))))
  }
}
