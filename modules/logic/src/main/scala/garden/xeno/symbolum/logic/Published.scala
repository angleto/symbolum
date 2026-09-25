package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * What a development hands to the ones above it: its facts, each cited under its own name.
 *
 * Every development of the chain builds on the facts of the ones below, so the proof of a fact
 * near the top used to hold the proofs of everything it rested on, and every report on a proof read
 * all of it. On 2026-09-20 the median fact of `Integer` was eleven thousand inferences and the facts
 * of `Inclusion` up to twenty-four thousand, for a development three quotients short of the reals it
 * is meant to reach. A citation is where a report stops: `Kernel.cite` gives back the same sequent
 * with a record that names the fact, and `Derivation`'s walks read one node there. `docs/adr/0047`
 * is the decision and has the measurement on both sides of it.
 *
 * It is applied where a development publishes, rather than where a consumer reads, because a
 * citation has to be one object for the sharing to hold: two readers of one fact who each built
 * their own citation would be two nodes in a proof that used both, and each would work out the
 * axioms under it again.
 *
 * What it does not reach is a theorem handed across in any other field, a rule set or a law held
 * by a procedure. A report walks those down to the nearest citation, which is where whatever they
 * were proved from was published, and the ADR has how far that is on the chain as it stands.
 */
object Published {

  /**
   * Each fact cited under its key, and a fact already cited under that key left as it is.
   *
   * The second half is for the developments that re-export another's facts, which `Order` does for
   * `Positivity`: citing a citation of the same name again would put two nodes where one is meant,
   * and the reader of the report would see the fact twice.
   */
  def cite(facts: Map[String, Kernel.Thm]): Map[String, Kernel.Thm] =
    facts.map { case (name, theorem) =>
      theorem.derivation match {
        case Derivation.Citation(`name`, _) => name -> theorem
        case _ => name -> Kernel.cite(name, theorem)
      }
    }
}
