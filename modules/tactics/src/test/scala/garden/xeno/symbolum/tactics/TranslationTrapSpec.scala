package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.Term
import garden.xeno.symbolum.theories.Real

/**
 * The one way this system can mislead, put to it on purpose.
 *
 * The kernel certifies the inference and not the translation. So the failure that carries the
 * authority of a proof is not a wrong proof: it is a plausible and wrong *formalisation*, followed
 * by a correct proof of it. `Translate` names that danger on the narrow border it guards,
 * `Expr -> Term`; the border with a sentence in Italian is the same danger with nothing on it.
 *
 * == Why this is a corpus of traps and not of examples ==
 *
 * A set of statements that formalise correctly measures nothing, because the failure is not that
 * the obvious reading is hard to find. It is that a *wrong* reading is obvious. So each case below
 * carries two readings of one sentence: the one that says what the sentence says, and one a careful
 * person might write instead, which says something else.
 *
 * == What the surface can guarantee, and what it cannot ==
 *
 * It can guarantee that the two readings are **different statements**, and say why with a witness:
 * a point where one holds and the other fails, or a decision where the prover settles one and
 * refuses the other. And it can guarantee that a reader is shown the term rather than a rendering
 * of it, through [[Readback]].
 *
 * It cannot guarantee that the reader notices. That is not a limit of this file, it is the same
 * limit `Readback` states about itself, and the reason the source sentence is carried beside every
 * case: what a person checks is a sentence against a sentence.
 *
 * == The three buckets, and why all three must be empty ==
 *
 *  - **dangerous**: the prover proves the misreading and refuses the faithful one. This is the
 *    failure the whole file is about, and it must be empty: a system that answers the question
 *    nobody asked while refusing the one they did is worse than one that refuses both.
 *  - **invisible**: the two readings print as the same text. Must be empty, or the surface offers
 *    a reader nothing to compare.
 *  - **uncaught**: no mechanical witness separates them here. Empty since 2026-09-10, asserted so
 *    and printed with its count either way: a trap in this bucket is one this system cannot help
 *    with at all, and its members would be the finding.
 */
class TranslationTrapSpec extends AnyFlatSpec with Matchers {

  private val reals = Real.standard
  private val prove = Prove.standard
  private val refutation = Refutation.standard
  private val quantified = Quantified.standard

  /**
   * One sentence and two readings of it.
   *
   * `source` is in the author's words, because that is what a person compares against, and because
   * a trap whose sentence nobody would write is not a trap.
   */
  private final case class Trap(source: String, faithful: String, plausible: String, why: String)

  /** How a pair was shown to be two statements rather than one. */
  private enum Witness:
    case Diverging(point: String)
    case Decided(detail: String)
    case None

  private val traps: Vector[Trap] = Vector(
    Trap(
      "La media dei due valori supera dieci.",
      "10 < (x:real + y:real) / 2",
      "10 < x:real + y:real",
      "a mean read as a sum: the misreading is satisfied by one large value and one small"
    ),
    Trap(
      "Il valore è almeno dieci.",
      "10 <= x:real",
      "10 < x:real",
      "'at least' read as 'more than': the two differ at exactly ten and nowhere else"
    ),
    Trap(
      "Se x è positivo, il suo doppio lo supera.",
      "!x:real. 0 < x ==> x < 2 * x",
      "!x:real. x < 2 * x",
      "a side condition dropped: the conclusion is stated for every x, and fails below zero"
    ),
    Trap(
      "Se y è sotto x, allora y meno uno è sotto x.",
      "!x:real y:real. y < x ==> y - 1 < x",
      "!x:real y:real. y - 1 < x ==> y < x",
      "an implication read backwards, which is what reading it as a biconditional adds"
    ),
    Trap(
      "Il tasso è sceso di tre punti, da venti a diciassette.",
      "20 - 3 = 17",
      "20 - 20 * 3 / 100 = 17",
      "percentage points read as per cent: three points off twenty is not three per cent of twenty"
    ),
    Trap(
      "Il valore è cresciuto del cinquanta per cento, da dieci a quindici.",
      "10 + 10 * 50 / 100 = 15",
      "10 * 50 / 100 = 15",
      "'grown by' read as 'grown to': the misreading takes the increase for the level"
    ),
    Trap(
      "La media fra un mezzo e un quarto è tre ottavi.",
      "(1 / 2 + 1 / 4) / 2 = 3 / 8",
      "(1 + 1) / (2 + 4) = 3 / 8",
      "the mean of two ratios read as the ratio of the sums, which is a different number"
    ),
    Trap(
      "La soglia è di due ore e la misura è di novanta minuti, dunque sta sotto.",
      "90 < 120",
      "90 < 2",
      "a unit dropped: the threshold is compared in hours against a measure in minutes"
    ),
    Trap(
      "Per ogni valore ce n'è uno più grande.",
      "!x:real. ?y:real. x < y",
      "?y:real. !x:real. x < y",
      "the quantifiers swapped, the classic misreading: separated by a decision, so no theorem comes back"
    )
  )

  /* ------------------------------------------------------------------ the machinery */

  private def readOf(text: String): Term =
    reals.proposition(text).fold(error => fail(s"$text does not read: ${error.message}"), identity)

  /** The text a reader is shown, which is the term or nothing. */
  private def shown(text: String): String =
    Readback
      .of(reals, readOf(text))
      .fold(error => fail(s"$text does not read back: ${error.message}"), identity)

  /**
   * How the two readings were shown to differ.
   *
   * A point first, because a witness a reader can check without trusting anything here is worth
   * more than a verdict. The search is asked in both directions, since which of the two is the
   * wider statement is not known in advance. A decision comes second: the prover settling one and
   * refusing the other says they are different statements without exhibiting where.
   */
  private def witnessFor(trap: Trap): Witness = {
    val faithful = readOf(trap.faithful)
    val plausible = readOf(trap.plausible)

    // A witness over no variables is the empty map, which reads as a point and is not one: a
    // closed statement is settled by deciding it, and reporting `()` as the place two readings
    // diverge would be the surface saying it had shown something it had not.
    def point(premise: Term, claim: Term): Option[String] =
      refutation.counterexample(Vector(premise), claim) match {
        case Refutation.Solved(values, _) if values.nonEmpty =>
          Some(values.toVector.sortBy(_._1).mkString(", "))
        case Refutation.Found(values, _) if values.nonEmpty =>
          Some(values.toVector.sortBy(_._1).mkString(", "))
        case _ => Option.empty
      }

    point(faithful, plausible)
      .map(Witness.Diverging.apply)
      .orElse(point(plausible, faithful).map(Witness.Diverging.apply))
      .getOrElse {
        (prove(faithful).isRight, prove(plausible).isRight) match {
          case (true, false) => Witness.Decided("the faithful reading is proved, the other refused")
          case (false, true) => Witness.Decided("the misreading is proved, the faithful one refused")
          case _ => decided(faithful, plausible)
        }
      }
  }

  /**
   * The last resort, and the one the quantifier swap needed.
   *
   * A tactic proves or refuses, and a refusal is not a disproof, so a pair neither tactic settles
   * comes back undecided from the step above however different the two statements are.
   * `Quantified` decides instead of proving: it eliminates the quantifiers over untrusted linear
   * forms and answers whether the claim holds over the reals. It produces no theorem and this file
   * must not read one into it; what it gives here is that the two readings have different truth
   * values, which is exactly what a trap asks.
   */
  private def decided(faithful: Term, plausible: Term): Witness =
    (quantified.decide(faithful), quantified.decide(plausible)) match {
      case (Right(Quantified.Holds), Right(Quantified.Fails)) =>
        Witness.Decided("the faithful reading holds and the misreading does not, decided not proved")
      case (Right(Quantified.Fails), Right(Quantified.Holds)) =>
        Witness.Decided("the misreading holds and the faithful one does not, decided not proved")
      case _ => Witness.None
    }

  private lazy val measured: Vector[(Trap, Witness, Boolean, Boolean)] =
    traps.map { trap =>
      val dangerous = prove(trap.plausible).isRight && prove(trap.faithful).isLeft
      val invisible = shown(trap.faithful) == shown(trap.plausible)
      (trap, witnessFor(trap), dangerous, invisible)
    }

  /* ------------------------------------------------------------------------ the tests */

  "Every trap" should "be two statements, and never one" in {
    // The precondition for the whole file. A pair whose readings say the same thing is not a trap,
    // and would quietly inflate the count below.
    measured.foreach { case (trap, witness, _, _) =>
      withClue(s"${trap.source}\n  faithful: ${trap.faithful}\n  plausible: ${trap.plausible}\n") {
        readOf(trap.faithful) should not be readOf(trap.plausible)
      }

      info(s"${trap.source}")
      info(s"    says:  ${shown(trap.faithful)}")
      info(s"    reads: ${shown(trap.plausible)}")
      info(s"    ${trap.why}")
      info(witness match {
        case Witness.Diverging(point) => s"    separated by a point: $point"
        case Witness.Decided(detail) => s"    separated by a decision: $detail"
        case Witness.None => "    NOT SEPARATED by anything this system has"
      })
    }
  }

  it should "be shown to a reader as two different texts" in {
    // Must be empty. A reader compares a sentence against what is printed, so two readings that
    // print alike leave nothing to compare and the surface has failed before anyone reads it.
    val invisible = measured.collect { case (trap, _, _, true) => trap.source }

    withClue(s"printed identically, so a reader cannot tell them apart:\n${invisible.mkString("\n")}\n") {
      invisible shouldBe empty
    }
  }

  it should "never be proved in the misreading while the faithful one is refused" in {
    // The assertion the card is about, and the one that would make this system misleading rather
    // than merely limited: a theorem handed over for the question nobody asked, beside a refusal
    // for the question they did. Worse than refusing both, because it carries the authority of a
    // proof.
    val dangerous = measured.collect { case (trap, _, true, _) => s"${trap.source} -> ${trap.plausible}" }

    withClue(s"the misreading is provable where the faithful reading is not:\n${dangerous.mkString("\n")}\n") {
      dangerous shouldBe empty
    }
  }

  "The traps this system cannot separate" should "be named, because they are the finding" in {
    // Printed with its count, and asserted empty below. A trap here is one where nothing in this
    // repository helps: a reader who writes the wrong reading gets no point, no decision and no
    // complaint, and the only guard left is that the printed form differs and somebody looks at it.
    val uncaught = measured.collect { case (trap, Witness.None, _, _) => trap }

    info(s"${traps.length} traps: ${traps.length - uncaught.length} separated mechanically, ${uncaught.length} not")
    uncaught.foreach(trap => info(s"  not separated: ${trap.source} (${trap.why})"))

    // Empty since 2026-09-10, and the entry that left is worth its paragraph. The quantifier swap
    // was the one nothing here could separate: no tactic decides a quantified statement, so neither
    // reading was proved, and the sampler declines a universal premise because there is no finite
    // domain to enumerate. It is the failure autoformalisation is most known for and it was this
    // measurement's honest headline. `Quantified` settles it by elimination rather than by proof,
    // so the pair is separated by a decision and not by a theorem, which is the distinction the
    // report is careful to print.
    //
    // The list stays, and it fails when an entry stops failing as well as when one starts. What it
    // records is the discipline rather than the members.
    uncaught.map(_.source) shouldBe empty
  }

  "The quantifier swap" should "be decided in both directions, since that is what left the list" in {
    // Pinned on its own rather than only through the count above, because a change to `Quantified`
    // that made it refuse both would empty the list in the report and pass the assertion there.
    val faithful = readOf("!x:real. ?y:real. x < y")
    val plausible = readOf("?y:real. !x:real. x < y")

    quantified.decide(faithful) shouldBe Right(Quantified.Holds)
    quantified.decide(plausible) shouldBe Right(Quantified.Fails)
  }
}
