package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.theories.{Chain, Library}

/**
 * The generator over a handful of the library's lemmas, for the tests that must run under coverage.
 *
 * The passes over the whole library, `ProposeSpec`'s audit and `StandardSweep`, are corpus
 * measurements and the coverage run skips them; `Corpus` has the measurement that moved them there.
 * `audit` and `Sweep.run` were reached by nothing else, so something has to reach them on a
 * population small enough to cost seconds, and this is it.
 *
 * The lemmas are chosen for what their proposals do and for what they cost, measured on 2026-11-12
 * over twelve candidates one at a time. `NUM_LE_CASES` gives one weakening, a claim wholly about
 * `num` that the exact model decides false; `ADD_ASSOC` gives one substitution, which the prover
 * reads as immediate. So both sources and two standings are reached. The obvious candidate,
 * `MUL_INVERSE`, whose weakening is the `Conditional` case `ProposeSpec` guards, cost thirty times
 * as much as the pair on the same machine. The probe timed its two proposals together, so which one
 * costs is not measured; the substitution comes back `Open`, which is the likelier. That guard stays
 * with the corpus pass.
 */
object FewLemmas {

  val Names: Vector[String] = Vector("ADD_ASSOC", "NUM_LE_CASES")

  /** The generator over [[Names]] alone, with the prover and logic the standard one has. */
  lazy val propose: Propose = {
    val standard = Propose.standard
    val chosen = Library.of(Chain.standard).entries.filter(entry => Names.contains(entry.name))
    val few = Library.of(Vector("few" -> chosen.map(entry => entry.name -> entry.theorem).toMap))
    Propose(standard.novelty, few, standard.logic)
  }
}
