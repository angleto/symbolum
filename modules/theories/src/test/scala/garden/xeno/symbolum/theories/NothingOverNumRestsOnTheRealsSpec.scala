package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * No development about `num` alone is believed on an axiom of the real numbers.
 *
 * It was true before this file and nothing said so. `Semiring` exists because it was once false:
 * until 2026-09-13 an identity of the naturals was decided by embedding both sides with
 * `real_of_num`, asking `RING`, and bringing the answer back, which charged the sixteen axioms of
 * a complete ordered field to twenty-eight of `Modular`'s thirty-eight published lemmas. That is
 * formally correct and says something false about what was needed, which matters most for exactly
 * the development at the end of this list: a theorem about the incompleteness of arithmetic that
 * rests on the reals is a theorem about something else.
 *
 * The property was repaired and left unguarded, and the measurement on 2026-09-15 that it held at
 * 44 of 44 in `Modular` and 57 of 57 in `Language` is a reading of one afternoon rather than a
 * check. What would break it is not a redesign: it is one derivation below `Language` reaching for
 * `Real` to get an arithmetic fact that `Peano` happens not to have, which is precisely what
 * happened three times in the week before this was written, in the other direction, with
 * `NUM_ADD_LE_CANCEL` and the three multiplicative lemmas nobody noticed were missing until a
 * proof reached for them. So this is the paragraph turned into something that fails.
 */
final class NothingOverNumRestsOnTheRealsSpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard

  /** What the reals ask anyone to believe, as the sixteen propositions themselves. */
  private val realAxioms: Set[Term] = chain.reals.axioms.values.map(_.conclusion).toSet

  /**
   * The developments that are about `num` and nothing else, by name.
   *
   * A written list rather than a scan, because what makes a development belong here is what it is
   * about and no property of it says so. A development added to the chain and not to this list is
   * unguarded, which is the limit of this test and is why it is stated.
   */
  private val overNumAlone: Vector[(String, Map[String, Kernel.Thm])] = Vector(
    "modular" -> chain.modular.facts,
    "coding" -> chain.coding.facts,
    "primes" -> chain.primes.facts,
    "numbering" -> chain.numbering.facts,
    "language" -> chain.language.facts,
    "provability" -> chain.provability.facts,
    "deduction" -> chain.deduction.facts
  )

  private def reachesAReal(theorem: Kernel.Thm): Boolean =
    Real.spent(theorem).exists(realAxioms.contains)

  "The reals" should "be believed on the reals' axioms, which is what the check is against" in {
    // Not the point of the file and it is here because everything below is a `diff` against this
    // set: were it empty, every assertion after it would pass while checking nothing.
    realAxioms should have size 16
  }

  it should "be reached by a development that IS about them, which says the check can see one" in {
    // The calibration. `Order` decides inequalities over the reals, so its facts reach the axioms;
    // if this ever came back empty the assertions below would be measuring an instrument that
    // reports nothing rather than a property of the developments.
    val orderFacts = chain.order.facts.values.count(reachesAReal)
    withClue(s"facts of Order reaching an axiom of the reals: $orderFacts\n") {
      orderFacts should be > 0
    }
  }

  "Every development about num alone" should "reach no axiom of the reals, in any fact it publishes" in {
    val leaking = overNumAlone.flatMap { case (development, facts) =>
      facts.toVector.collect { case (name, theorem) if reachesAReal(theorem) => s"$development.$name" }
    }
    leaking shouldBe empty
  }

  it should "publish something, so that the assertion above is not empty" in {
    // The other half of the discipline this repository already applies to its reach report: an
    // assertion over an empty collection passes. Seven developments and the counts they held on
    // 2026-09-15 were 44, 4, 2, 35, 57, 10 and 6, so the floor is well under any of them.
    overNumAlone.foreach { case (development, facts) =>
      withClue(s"$development publishes: ") { facts should not be empty }
    }
    overNumAlone.map(_._2.size).sum should be >= 100
  }
}
