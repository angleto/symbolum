package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What a proof rests on, and the property the reading has to have to still be worth anything after
 * `docs/adr/0007`.
 *
 * The measure is over **named facts**, not over axioms, and the difference is the whole card. Once
 * the reals are constructed the sixteen become theorems; a report counting axioms would then answer
 * "choice, eta, infinity" for every proof, which is Lean's uninformative answer arrived at by a
 * different road. A report counting named facts says "this rests on completeness" whether
 * completeness is assumed or derived.
 *
 * The last test is the one that matters: it builds a library where a fact that is an axiom today is
 * labelled as something else, and checks the name still comes back. That is the construction
 * simulated, at the only point where it can be simulated before it happens.
 */
class RestsOnSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val held = Reach.library(chain)

  "A numeral fact" should "rest on the subject and not on the formalism" in {
    // `0 < 12` is arithmetic. Nothing in it asks the formalism for anything: no choice, no eta, no
    // infinity. That the foundational bucket is EMPTY is the assertion, and it is the one that
    // would be impossible to make if the reading counted axioms after the construction.
    val theorem = force(chain.order.positive(12))
    val reach = Reach.of(held, theorem)

    reach.foundational shouldBe empty
    reach.domain should not be empty
    info(s"0 < 12: ${reach.summary}")
  }

  "The naturals" should "name what they asked of the formalism, somewhere" in {
    // The other side, and it is a scan rather than one example because which theorem carries the
    // foundational step is a fact about how the development was built, not something to assert from
    // memory. `num` is carved out of an infinite type, so **something** here must reach infinity; a
    // classification whose foundational bucket were never non-empty would be a bucket nobody fills.
    //
    // `NUM_INDUCTION` is not the one, and that is worth knowing: its proof goes through the
    // type-definition facts and does not re-derive the witness. Found by asking rather than by
    // assuming, which is why this test is written this way.
    val reaching = chain.naturals.facts.toVector
      .map { case (name, theorem) => (name, Reach.of(held, theorem)) }
      .filter { case (_, reach) => reach.foundational.contains(Natural.Infinity) }

    withClue("nothing about the naturals reaches infinity, which cannot be right\n") {
      reaching should not be empty
    }

    info(s"${reaching.size} of ${chain.naturals.facts.size} reach ${Natural.Infinity}: " +
      reaching.map(_._1).sorted.take(6).mkString(", "))
  }

  "Every named fact the chain holds" should "be one this report can name" in {
    // The two lists of a chain's developments are maintained by hand, and they drifted: `Peano`
    // joined the chain on 2026-09-11 and joined `Library.of(chain)` the same day, and this file's
    // own library was not touched. Thirty named facts were invisible to the report, so a proof
    // that went through `NUM_ADD_SYM` said it rested on nothing of the kind, and `SUM_REINDEX` —
    // which is proved **from** two of them — named neither.
    //
    // Asserted as an agreement between the two rather than by listing the developments here a
    // third time. What it catches is the next one to join.
    val chain = Chain.standard
    val reachable = Reach.library(chain).names.toSet
    val held = Library.of(chain).names.toSet

    withClue(s"held by the chain and not nameable by the reach report: ${(held -- reachable).toVector.sorted.mkString(", ")}\n") {
      (held -- reachable) shouldBe empty
    }

    // And the other direction is deliberately not empty: this library carries the classical and
    // natural axioms, which `Library.of(chain)` leaves out because a reader searching for what
    // they have about `x + y` is not looking for the choice operator.
    (reachable -- held) should not be empty
  }

  it should "name the facts a proof was actually built from" in {
    // The measurement that found the gap, kept as the case. `SUM_REINDEX` is proved by an
    // induction whose rules are the sum's two recurrences and `NUM_ADD`'s two, so a report that
    // cannot say `NUM_ADD_ZERO` is a report about a different proof.
    val chain = Chain.standard
    val reach = Reach.of(Reach.library(chain), force(chain.series.fact(Series.Reindex)))

    reach.facts should contain(Peano.AddAtZero)
    reach.facts should contain(Peano.AddAtSuccessor)
    reach.facts should contain(Series.AtSuccessor)
  }

  "The three buckets" should "not overlap, so a name is in exactly one" in {
    val theorem = force(chain.order.positive(12))
    val reach = Reach.of(held, theorem)

    reach.foundational.intersect(reach.domain) shouldBe empty
    reach.foundational.intersect(reach.facts) shouldBe empty
    reach.domain.intersect(reach.facts) shouldBe empty
  }

  "A fact that stops being an axiom" should "still be named by a proof that rests on it" in {
    // `docs/adr/0007` simulated. The same theorem is read against a library where the sixteen are
    // labelled "Real, derived" instead of "Real, assumed", which is what the day after the
    // construction looks like: the domain bucket empties and **the names move to the facts bucket
    // rather than disappearing**.
    //
    // If this reading counted axioms, the second answer would be strictly less informative than the
    // first, which is the failure the card was opened to prevent.
    val theorem = force(chain.order.positive(12))

    val afterConstruction = Library.of(
      Vector(
        "Classical" -> chain.classical.axioms,
        "Natural, assumed" -> chain.naturals.axioms,
        "Real, derived" -> chain.reals.axioms,
        "Real, defined" -> chain.reals.definitions,
        "Positivity" -> chain.ring.positivity.facts,
        "Order" -> chain.order.facts
      )
    )

    val before = Reach.of(held, theorem)
    val after = Reach.of(afterConstruction, theorem)

    after.domain shouldBe empty
    before.domain.foreach(name => after.facts should contain(name))

    withClue(s"before: ${before.summary}; after: ${after.summary}\n") {
      (after.facts ++ after.domain ++ after.foundational).toSet shouldBe
        (before.facts ++ before.domain ++ before.foundational).toSet
    }
  }

  /**
   * The count of named facts in the one-line reading, at one and elsewhere.
   *
   * Card 601788d5 found it by widening db67b658's census to a count followed by a modifier and then
   * the plural, `${facts.size} named facts`, which printed "1 named facts" wherever a proof went
   * through one named fact. That it does is measured here and not assumed: the lemmas of `Order`
   * are searched for one whose reading holds exactly one, and the search has to find it.
   */
  "The one-line reading" should "take the singular at one named fact and the plural elsewhere" in {
    val readings = chain.order.facts.toVector.sortBy(_._1).map { case (name, theorem) =>
      name -> Reach.of(held, theorem)
    }
    val one = readings.find(_._2.facts.size == 1)
    val several = readings.find(_._2.facts.size > 1)

    withClue("no lemma of Order rests on exactly one named fact, so the site is not reached: ") {
      one should not be empty
    }
    withClue("no lemma of Order rests on more than one: ") { several should not be empty }

    one.get._2.summary should startWith("1 named fact,")
    several.get._2.summary should startWith(s"${several.get._2.facts.size} named facts,")
  }
}
