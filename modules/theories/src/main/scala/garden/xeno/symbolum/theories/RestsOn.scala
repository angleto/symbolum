package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*

/**
 * What a proof rests on, read as **mathematics** rather than as a list of unproved things.
 *
 * == The tension this exists to survive ==
 *
 * The one thing a hostile reviewer, in the role of a Mathlib maintainer, granted as genuinely not
 * replicable here is the per-proof axiom reach. Lean's `#print axioms` answers
 * `propext, Classical.choice, Quot.sound` for essentially every Mathlib declaration **because the
 * reals are constructed there**, so the answer carries no information about the mathematics. The
 * line this repository can write about itself — fifteen of the sixteen real axioms over 46 goals,
 * and the one never reached is completeness — is a line only an axiomatised theory can write.
 *
 * `docs/adr/0007` decides that the reals will be constructed. That turns the sixteen into theorems.
 * A report that counts **axioms** would then answer "choice, eta, infinity" for every proof, which
 * is precisely Lean's uninformative answer, and the thing that was worth having would evaporate as
 * a side effect of a decision about something else.
 *
 * == The measure that survives it ==
 *
 * Not "which unproved things did this use" but "**which named facts did this use**". A fact keeps
 * its name when it stops being an axiom, so `SQUARE_NONNEG` and `COMPLETENESS` are still sayable
 * the day after the construction lands, and a proof that reaches completeness still says so.
 *
 * `Derivation.restingOn` is the mechanism and it compares by the sequent rather than by identity,
 * which is the same decision one layer down and for the same reason: a fact re-derived on the way
 * is the same fact.
 *
 * == The three buckets, and why three ==
 *
 * **Foundational** is what the formalism asks for rather than the mathematics: choice and eta, and
 * infinity, which is asked of a type nothing else interprets. Those stay after the construction and
 * are the ones a reader can do nothing about.
 *
 * **Domain** is what a development assumes about its own subject: the sixteen today, and an
 * economics or governance theory's own axioms tomorrow. This is the bucket that empties as the
 * construction proceeds, and the one a reader argues with.
 *
 * **Facts** is everything named that the proof went through. It does not shrink when an axiom
 * becomes a theorem, which is the whole point.
 */
final case class Reach(
  foundational: Vector[String],
  domain: Vector[String],
  facts: Vector[String]
) {

  /** The reading a person wants, one line. */
  def summary: String =
    s"${facts.size} named facts, ${domain.size} assumed about the subject, " +
      s"${foundational.size} asked of the formalism"
}

object Reach {

  /**
   * The developments whose statements are asked of the formalism and not of any subject.
   *
   * By label rather than by statement, because the labels are what `Library` already carries and
   * because a statement moves between them: infinity is asked of `ind`, which nothing else
   * interprets, and that is a fact about the formalism however it is spelled.
   */
  private val Foundational: Set[String] = Set("Classical", "Natural, assumed")

  /** The developments whose statements are assumed about their own subject. */
  private val Domain: Set[String] = Set("Real, assumed")

  /**
   * The library of a chain, labelled so that the three buckets can be told apart.
   *
   * `Library.of(chain)` does not carry the classical axioms, because a reader searching for what
   * they have about `x + y` is not looking for the choice operator. Here they are wanted, so this
   * builds its own.
   */
  def library(chain: Chain): Library =
    Library.of(
      Vector(
        "Classical" -> chain.classical.axioms,
        // The classical FACTS and the conditional's definition, added on 2026-09-12 in the change
        // that put them into `Library.of(chain)`, which is what the guard below this file's own
        // list exists to force. They are labelled apart from the axioms on purpose: `Classical` is
        // in `Foundational` above, and the excluded middle is **derived** from choice in 829 steps.
        // Filing it foundational would report a theorem as an assumption, which is the one mistake
        // this three-bucket report exists to prevent.
        "Classical, derived" -> chain.classical.facts,
        "Classical, defined" -> chain.classical.definitions,
        "Natural, assumed" -> chain.naturals.axioms,
        "Real, assumed" -> chain.reals.axioms,
        "Real, defined" -> chain.reals.definitions,
        "Positivity" -> chain.ring.positivity.facts,
        "Order" -> chain.order.facts,
        "Natural" -> chain.naturals.facts,
        // Missing from this list until 2026-09-11, which is thirty named facts and a whole
        // development: every proof that went through `NUM_ADD_SYM` or `NUM_REAL_SUC` reported
        // resting on neither. `SUM_REINDEX` is proved **from** two of them and named neither.
        //
        // The two lists of a chain's developments, this one and `Library.of(chain)`, were
        // maintained by hand and drifted the day `Peano` joined the chain. `RestsOnSpec` compares
        // them now, so the next development to join is added here or fails there.
        "Peano" -> chain.peano.facts,
        "Series" -> chain.series.facts,
        // The four that joined the chain on 2026-09-12, added here in the same change, which is
        // what the guard above is for: `RestsOnSpec` compared the two lists and named all
        // forty-eight before this line existed. `Bounded` is the fifth of that group and holds no
        // facts, so there is nothing of it to label.
        "Divisibility" -> chain.divisibility.facts,
        "Modular" -> chain.modular.facts,
        "Product" -> chain.product.facts,
        "Word" -> chain.word.facts,
        // And the sixth, added in the change that wrote it. The guard did its job on the way here:
        // `RestsOnSpec` compared the two lists and named all twenty-four of these before this line
        // existed, which is what comparing two hand-maintained lists is for.
        "Matrix" -> chain.matrix.facts,
        "Rotation" -> chain.rotation.facts,
        // Joined on 2026-09-13 with the chain itself. `RestsOnSpec` is what found it missing, by
        // the assertion it carries that every name the chain holds is nameable here: a fact the
        // reach report cannot name is reported as an unnamed step of a proof, which reads as the
        // proof resting on something nobody can look up.
        "Magnitude" -> chain.magnitude.facts,
        "Coding" -> chain.coding.facts,
        "Numbering" -> chain.numbering.facts,
        "Language" -> chain.language.facts,
        "Provability" -> chain.provability.facts,
        "Primes" -> chain.primes.facts,
        "Deduction" -> chain.deduction.facts
      )
    )

  /** What a theorem rests on, over a library already built. */
  def of(held: Library, theorem: Kernel.Thm): Reach = {
    val used = held.restingOn(theorem)

    def named(which: Set[String]): Vector[String] =
      used.filter(entry => which.contains(entry.development)).map(_.name).distinct.sorted

    Reach(
      foundational = named(Foundational),
      domain = named(Domain),
      facts = used
        .filterNot(entry => Foundational.contains(entry.development))
        .filterNot(entry => Domain.contains(entry.development))
        .map(_.name)
        .distinct
        .sorted
    )
  }

  /** What a theorem of the standard chain rests on. */
  def of(theorem: Kernel.Thm): Reach = of(standard, theorem)

  private lazy val standard: Library = library(Chain.standard)
}
