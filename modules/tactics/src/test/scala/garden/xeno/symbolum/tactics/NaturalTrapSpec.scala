package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.*

/**
 * The misreadings the naturals fragment invites, and what separates them.
 *
 * `TranslationTrapSpec` does this for the reals. Transplanting its entries would measure nothing:
 * a trap is only a measurement when it is a wrong reading the fragment **invites**, and this
 * fragment invites its own. The first is the useful one and it is the off-by-one of an exclusive
 * bound: `Sum f n` is `f ZERO + … + f (n-1)`, so "the sum of the first n values" and "the sum of the
 * values up to n" are different statements and an author writes whichever their prose suggested.
 *
 * == The witness point is not available here, and the report says so ==
 *
 * `Refutation` samples the reals and `Evaluate` enumerates a declared type only where a model has
 * sized it. Nothing sizes `num`. So on this fragment a pair is separated by a **proof** or by a
 * **decision** or not at all, and never by a point, and a corpus that returned fewer points in
 * silence would be reporting a weaker system as a stronger one. The report keeps the kinds apart,
 * which is the discipline track T keeps for the same reason.
 */
class NaturalTrapSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard

  /**
   * The chain's widest signature, asked for by that name rather than by which development it is.
   *
   * It was `chain.peano` until 2026-09-11 and it is `chain.series` now, because the two swapped
   * places so that `NUM_ADD` could appear inside a `Sum`. The traps below name `Sum`, `NUM_LE` and
   * `SUC`, which are three developments' constants, and the first test here fails on a name no
   * signature declares: reaching for `Chain.widest` is how that stays true whichever development
   * ends up on top.
   */
  private val series: Signature = chain.widest
  private val prove = force(Prove.construct(chain.order, series, Library.of(chain)))

  private val recurrences = Vector(
    force(chain.series.fact(Series.AtZero)),
    force(chain.series.fact(Series.AtSuccessor))
  )

  /** The two readings of one sentence, and why anybody would write the second. */
  private final case class Trap(source: String, faithful: String, plausible: String, why: String)

  /** How a pair was shown to be two statements, on a fragment where no point is available. */
  private enum Witness:
    case Proved(detail: String)
    case Decided(detail: String)
    case Printed
    case None

  private val traps: Vector[Trap] = Vector(
    Trap(
      "La somma del primo valore.",
      "Sum (f:num->real) (SUC ZERO) = f ZERO",
      "Sum (f:num->real) (SUC ZERO) = f ZERO + f (SUC ZERO)",
      "an exclusive upper bound read as inclusive: `Sum f n` stops before `f n`"
    ),
    Trap(
      "La somma di nessun valore è zero.",
      "Sum (f:num->real) ZERO = 0",
      "Sum (f:num->real) ZERO = f ZERO",
      "the empty sum read as the first term: the same off-by-one at the other end"
    ),
    Trap(
      "Zero è il più piccolo.",
      "!n:num. NUM_LE ZERO n",
      "!n:num. NUM_LE (SUC ZERO) n",
      "a base case at ZERO read as a base case at one, which is the commonest induction slip"
    ),
    Trap(
      "Per ogni numero ce n'è uno almeno altrettanto grande.",
      "!n:num. ?m:num. NUM_LE n m",
      "?m:num. !n:num. NUM_LE n m",
      "the quantifier swap, on `num` rather than on the reals: the second claims a largest number"
    )
  )

  /* ---------------------------------------------------------------- reading and measuring */

  private def readOf(text: String): Term = force(series.proposition(text))

  private def shown(text: String): String =
    Readback.of(series, readOf(text)).fold(error => s"<unreadable: ${error.message}>", identity)

  private def settles(text: String): Boolean = {
    val goal = readOf(text)

    prove(goal).isRight ||
    Rewrite.Rule
      .all(series.logic, recurrences)
      .flatMap(rules => Induct.afterRewriting(rules, goal)(chain.ring.prove))
      .isRight
  }

  private lazy val measured: Vector[(Trap, Witness, Boolean, Boolean)] =
    traps.map { trap =>
      val faithful = settles(trap.faithful)
      val plausible = settles(trap.plausible)

      val witness =
        if (faithful && !plausible) Witness.Proved("the faithful reading, and not the other")
        else if (!faithful && plausible) Witness.Proved("the misreading, and not the faithful one")
        else if (shown(trap.faithful) != shown(trap.plausible)) Witness.Printed
        else Witness.None

      (trap, witness, plausible && !faithful, shown(trap.faithful) == shown(trap.plausible))
    }

  /* ------------------------------------------------------------------------ the tests */

  "Every constant a trap names" should "be declared, or the trap is about a free variable" in {
    // The hazard this repository already has a row for: an unknown letter-initial name parses as a
    // VARIABLE, so a trap naming a constant the theory does not have is a well-typed statement
    // about an arbitrary function, and it would separate from its twin for a reason that has
    // nothing to do with the naturals.
    val named = traps.flatMap(trap => Vector(trap.faithful, trap.plausible))
      .flatMap(_.split("[^A-Za-z_]+"))
      .filter(word => word.nonEmpty && word.head.isUpper)
      .distinct

    val undeclared = named.filterNot(series.theory.constants.contains)

    withClue(s"named in a trap and declared nowhere, so it reads as a variable: ${undeclared.mkString(", ")}\n") {
      undeclared shouldBe empty
    }
  }

  "Every trap on the naturals" should "be two statements, and never one" in {
    measured.foreach { case (trap, witness, _, _) =>
      withClue(s"${trap.source}\n  faithful: ${trap.faithful}\n  plausible: ${trap.plausible}\n") {
        readOf(trap.faithful) should not be readOf(trap.plausible)
      }

      info(s"${trap.source}")
      info(s"    says:  ${shown(trap.faithful)}")
      info(s"    reads: ${shown(trap.plausible)}")
      info(s"    ${trap.why}")
      info(witness match {
        case Witness.Proved(detail) => s"    separated by a proof: $detail"
        case Witness.Decided(detail) => s"    separated by a decision: $detail"
        case Witness.Printed => "    separated only by what is PRINTED: nothing here decides either"
        case Witness.None => "    NOT SEPARATED by anything this system has"
      })
    }
  }

  it should "be shown to a reader as two different texts" in {
    // Must be empty, and on this fragment it carries more weight than on the reals: where no point
    // and no decision is available, what is printed is the only thing left between a reader and a
    // statement they did not mean.
    val invisible = measured.collect { case (trap, _, _, true) => trap.source }

    withClue(s"printed identically:\n${invisible.mkString("\n")}\n") {
      invisible shouldBe empty
    }
  }

  it should "never settle the misreading while the faithful one is refused" in {
    val dangerous = measured.collect { case (trap, _, true, _) => s"${trap.source} -> ${trap.plausible}" }

    withClue(s"the misreading settles where the faithful reading does not:\n${dangerous.mkString("\n")}\n") {
      dangerous shouldBe empty
    }
  }

  "What separates a pair on this fragment" should "be reported by kind, since no point is available" in {
    // The line the card asks for in its own words: nothing sizes `num`, so no pair here can be
    // separated by a witness point, and the report must say that rather than return fewer points
    // in silence. The kinds are counted apart for the reason `Refutation.Outcome` keeps its cases
    // apart.
    val byProof = measured.count { case (_, Witness.Proved(_), _, _) => true; case _ => false }
    val byDecision = measured.count { case (_, Witness.Decided(_), _, _) => true; case _ => false }
    val byPrinting = measured.count { case (_, Witness.Printed, _, _) => true; case _ => false }
    val notAtAll = measured.collect { case (trap, Witness.None, _, _) => trap.source }

    info(
      s"${traps.length} traps: $byProof separated by a proof, $byDecision by a decision, " +
        s"$byPrinting only by what is printed, ${notAtAll.length} not at all. " +
        "No point is available on this fragment: nothing sizes `num`."
    )
    notAtAll.foreach(source => info(s"  not separated: $source"))

    byProof + byDecision + byPrinting + notAtAll.length shouldBe traps.length
    notAtAll shouldBe empty
  }
}
