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
 * The test that matters built a library where a fact that was then an axiom was labelled as
 * derived, and checked the name still came back: the construction simulated, at the only point
 * where it could be simulated before it happened. `docs/adr/0053` made it happen, and the test
 * reads the standard library now.
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
    // The subject is the sixteen of the reals, named facts since `docs/adr/0053` and assumed until
    // then; the half of the assertion that says the reading is about the subject at all.
    reach.facts.toSet.intersect(Real.Laws.map(_._1).toSet) should not be empty
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

  "The buckets" should "not overlap, so a name is in exactly one" in {
    val theorem = force(chain.order.positive(12))
    val reach = Reach.of(held, theorem)

    reach.foundational.intersect(reach.domain) shouldBe empty
    reach.foundational.intersect(reach.facts) shouldBe empty
    reach.domain.intersect(reach.facts) shouldBe empty
  }

  "A fact that stopped being an axiom" should "still be named by a proof that rests on it" in {
    // `docs/adr/0007` happened: `docs/adr/0053` proved the sixteen from the cuts on the rationals.
    // This test simulated that day before it came, by reading one theorem against a library where
    // the sixteen were labelled derived, and asserted that the domain bucket emptied and the names
    // moved to the facts bucket rather than disappearing. That is now the report itself, measured
    // on the standard library rather than on a relabelled copy.
    val theorem = force(chain.order.positive(12))
    val reach = Reach.of(held, theorem)
    val sixteen = Real.Laws.map(_._1).toSet

    reach.domain shouldBe empty
    reach.foundational shouldBe empty
    withClue(s"${reach.summary}\n") {
      reach.facts.toSet.intersect(sixteen) should not be empty
    }

    // What keeps it informative is where the walk stops. Entered, the sixteen's own proofs reach the
    // rationals and the classical axioms, and the same theorem would be reported as resting on
    // choice: true of the construction and nothing a reader of `0 < 12` needs.
    held.restingOn(theorem).map(_.development) should contain("Classical")
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
    // Searched over the whole library in name order since `docs/adr/0053`: the lemmas of `Order`
    // were enough until the sixteen became named facts, after which none of them rests on exactly
    // one.
    val readings = held.entries.sortBy(_.name).view.map { entry =>
      entry.name -> Reach.of(held, entry.theorem)
    }
    val one = readings.find(_._2.facts.size == 1)
    val several = readings.find(_._2.facts.size > 1)

    withClue("no lemma rests on exactly one named fact, so the site is not reached: ") {
      one should not be empty
    }
    withClue("no lemma rests on more than one: ") { several should not be empty }

    one.get._2.summary should startWith("1 named fact,")
    several.get._2.summary should startWith(s"${several.get._2.facts.size} named facts,")
  }

  /**
   * `docs/adr/0047` splits a report in two at a cited fact, and this holds both halves on a fact
   * the chain really publishes. The accounting stops there: a proof going through the citation is
   * three inferences whatever the fact's own proof holds, and it rests on the same axioms as the
   * same proof written around the citation. The reach does not stop there, by that record's
   * decision: a named fact used **inside** the cited proof is one the proof used.
   *
   * The inner fact is chosen with a statement different from the cited one, which is what the
   * kernel's own case in `DerivationSpec` cannot do: there the only named statement is the cited
   * fact's, which the root of the proof already concludes, so a reach that stopped at the citation
   * would still find it. Here a reach that stopped at the citation loses the inner names.
   */
  "A proof citing a published fact" should "be counted short and still name what the fact used" in {
    def forced[T](result: Either[KernelError, T]): T =
      result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

    val found = held.entries.iterator.flatMap { entry =>
      entry.theorem.derivation match {
        case Derivation.Citation(_, proof) if Derivation.size(proof) > 3 =>
          val inner = held.restingOn(proof)
            .filterNot(_.theorem.conclusion == entry.theorem.conclusion)
          if (inner.isEmpty) None else Some((entry, proof, inner))
        case _ => None
      }
    }.nextOption()
    val (entry, proof, inner) =
      found.getOrElse(fail("no fact of the library is cited and rests on another named fact"))

    val statement = entry.theorem.conclusion
    val through = forced(Kernel.eqMp(Kernel.refl(statement), entry.theorem))
    val around = forced(Kernel.eqMp(Kernel.refl(statement), proof))

    Derivation.size(through) shouldBe 3
    Derivation.size(around) shouldBe 2 + Derivation.size(proof)
    Derivation.census(through).get("Citation") shouldBe Some(1)
    Derivation.axiomsOf(through) shouldBe Derivation.axiomsOf(around)

    val reached = held.restingOn(through).map(_.name).toSet
    reached should contain(entry.name)
    reached should contain allElementsOf inner.map(_.name)
    Reach.of(held, through) shouldBe Reach.of(held, around)
    info(s"${entry.name}: ${Derivation.size(proof)} steps behind the citation, ${inner.size} named facts inside it")
  }
}
