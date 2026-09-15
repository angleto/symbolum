package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.*
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.*

/**
 * What the field fragment adds to another prover's ring corpus, and what it costs there.
 *
 * Track F of `docs/evaluation.md`, and it asks two questions of the same file rather than one,
 * because a tactic that carries hypotheses has two ways of being wrong and only one of them is
 * about proving power.
 *
 * == The first question: what does it cost ==
 *
 * `Field` is `Ring` plus one step, `d * inv d` becomes `1`, and the step costs a hypothesis. So the
 * thing to check before anything else is that it does not charge one where it did not need it.
 * Every goal in track R goes through `Field` as well, and every one the ring fragment certifies has
 * to come back proved and with nothing assumed.
 *
 * That is asserted here rather than argued because the argument is easy to believe and is not the
 * evidence: a condition reaches a theorem only through the inference that used it, so a
 * cancellation rule that never fires contributes nothing. `FieldSpec` pins that on one example.
 * This pins it on every goal a library's users actually wrote in that file.
 *
 * == The second question: what does it add ==
 *
 * Two populations, asked separately, because they are two different questions wearing one word.
 *
 * The first is inside track R. Its selection rule counts the declarations upstream closed with
 * `ring` or `ring1` alone, and the reading that went with it, that such a goal has no denominator
 * to cancel and leaves this fragment nothing to add, held for every one this system could read
 * until `LeanSyntax` learned `⁻¹` on 2026-09-09. The ones that became readable that evening are
 * not ring identities in this theory: Mathlib's `⁻¹` is total and this one is not, so
 * `(1/x)^2 = 1/x^2` holds at zero there and is undetermined here. `Ring` is right to refuse them,
 * `Field` proves them charging a condition, and that is what a hypothesis-carrying tactic is for.
 *
 * The second is what track R's rule deliberately throws away: the declarations upstream closed with
 * `field_simp; ring`, where `ring` was handed a goal after a preprocessing step. Asking `Field`
 * those directly is the fair question, and it is fairer than asking `ring` was: upstream needed two
 * tactics for them and this is one tactic being asked to do both jobs.
 *
 * == What the field goals say ==
 *
 * All of them are proved. That is pinned below against the size of the corpus rather than only
 * reported through `info`, because the outcomes a corpus suite can quietly slide into are the ones
 * that empty its failure list instead of filling it.
 *
 * They said one thing with one cause on 2026-09-09, and the finding is kept rather than deleted
 * because it is what the work was aimed at. Every one of them needs the inverse of a *product*
 * taken apart, `inv (a * b)` into `inv a * inv b`, which was then the step `Field` refused by name
 * and documented itself as refusing; two of the three were unreadable on top of that, being written
 * with `⁻¹`. Measured by hand and outside the suite that day, because a measurement of an
 * unreadable declaration cannot live in the code: `2 * x^3 * 2 / (24 * x) = x^2 / 6` was refused as
 * written, and the same goal with its denominator split, `... / 24 / x`, was proved assuming
 * `~(x = 0)`. Nothing else moved. So the fragment did reach these goals, and one step stood between
 * it and them.
 *
 * That step is `Field.reciprocal`, which takes a denominator apart by recursion before anything is
 * assumed about it and closes with `Coefficient.inverseOfUnit`; the reader takes `⁻¹` as `1 / x`
 * rather than as `x ^ -1`, so the two that could not be read are read.
 */
class FieldCorpusSpec extends AnyFlatSpec with Matchers {

  private val CorpusFile: String = "third-party/mathlib/MathlibTest/Tactic/Ring/Ring.lean"

  private enum Outcome:
    case Proved, Outside, Unreadable, Unproved

  private def read(relative: String): String =
    LeanCorpus.read(relative).getOrElse(fail(s"cannot find $relative"))

  private val corpus: Vector[LeanCorpus.Declaration] = LeanCorpus.declarations(read(CorpusFile))

  private val field = Field.standard
  private val reals = field.reals

  /** The goal of a declaration, as a proposition of this theory, or why it could not be read. */
  private def goalOf(declaration: LeanCorpus.Declaration): Either[(Outcome, String), Term] =
    LeanCorpus.goalOf(declaration) match {
      case None => Left((Outcome.Unreadable, "no goal separator"))
      case Some(text) =>
        LeanSyntax.equation(text) match {
          case Left(why) => Left((Outcome.Unreadable, why))
          case Right((left, right)) =>
            val translated = for {
              leftTerm <- Translate.toTerm(reals, left)
              rightTerm <- Translate.toTerm(reals, right)
              equation <- TacticError.lift(LogicError.lift(Term.eq(leftTerm, rightTerm)))
            } yield equation

            translated.left.map {
              case outside: OutsideFragment => (Outcome.Outside, outside.reason)
              case other => (Outcome.Unreadable, other.message)
            }
        }
    }

  /* --------------------------------------------------- what the fragment costs on track R */

  /** The declarations track R measures, by the rule track R uses. */
  private val ringGoals: Vector[LeanCorpus.Declaration] =
    corpus.filter { declaration =>
      val closed = LeanCorpus.tactic(declaration)
      closed == "ring" || closed == "ring1"
    }

  private lazy val onRingGoals: Vector[(LeanCorpus.Declaration, Either[String, Kernel.Thm])] =
    ringGoals.flatMap { declaration =>
      goalOf(declaration).toOption.map { goal =>
        (declaration, field.prove(goal).left.map(_.message))
      }
    }

  /**
   * Track R's goals split by whether the ring fragment certifies them.
   *
   * The split is the population the claim below is about, and it was the whole population until
   * 2026-09-09: every goal the corpus stated was one RING certified. Three are not, since
   * `LeanSyntax` learned `⁻¹`, and they are not ring identities in this theory at all — Mathlib's
   * `⁻¹` is total and this one is not, so `(1/x)^2 = 1/x^2` holds at zero there and is undetermined
   * here. Asking whether FIELD over-charges on a goal that genuinely needs a condition would
   * measure nothing, so the two questions are asked separately rather than averaged into one.
   */
  private lazy val (ringIdentities, needingACondition)
      : (Vector[(LeanCorpus.Declaration, Either[String, Kernel.Thm])],
         Vector[(LeanCorpus.Declaration, Either[String, Kernel.Thm])]) =
    onRingGoals.partition { case (declaration, _) =>
      goalOf(declaration).toOption.exists(goal => Ring.standard.prove(goal).isRight)
    }

  "The field fragment" should "prove every goal the ring fragment certifies, assuming nothing" in {
    // Both halves matter and the second is the one worth the suite. A tactic that returns a
    // theorem with a hypothesis nobody needed has not proved the goal it was given, and a reader
    // who checks only that something came back cannot tell.
    val refused = ringIdentities.collect { case (declaration, Left(why)) => s"line ${declaration.line}: $why" }
    withClue(s"refused by the field fragment although the ring fragment proves them:\n${refused.mkString("\n")}\n") {
      refused shouldBe empty
    }

    val assumed = ringIdentities.collect {
      case (declaration, Right(theorem)) if theorem.hypotheses.nonEmpty =>
        s"line ${declaration.line}: ${theorem.hypotheses.map(reals.show).mkString(", ")}"
    }
    withClue(s"a condition was assumed where nothing needed one:\n${assumed.mkString("\n")}\n") {
      assumed shouldBe empty
    }

    info(s"${ringIdentities.size} of track R's goals put to FIELD: all proved, none assuming anything")
  }

  it should "prove the rest, and charge exactly the condition the other theory does not need" in {
    // The three the ring fragment refuses, and the assertion is what FIELD charges rather than that
    // it succeeded. Each condition has to be about one variable: `~(x = 0)`, never `~(x * y = 0)`
    // and never a numeral. A product condition would be sound and weaker than the truth, and it is
    // exactly what a tactic that split only the outermost denominator produced for a day, so it is
    // worth an assertion rather than a comment.
    val variable = """\~\((\p{L}[\p{L}\p{Nd}_']*) = 0\)""".r

    val charged = needingACondition.map { case (declaration, outcome) =>
      declaration.line -> outcome.map(_.hypotheses.map(reals.show).sorted)
    }

    charged.foreach { case (line, conditions) =>
      withClue(s"line $line: ") {
        conditions.map(_.nonEmpty) shouldBe Right(true)
        conditions.map(_.filterNot(variable.matches)) shouldBe Right(Nil)
      }
    }

    info(
      s"${charged.size} goals the ring fragment refuses: all proved by FIELD, " +
        s"each assuming only that a variable is not zero (${charged.map(_._2).mkString("; ")})"
    )
  }

  /* ------------------------------------------------- what the fragment adds, and cannot yet */

  /**
   * The declarations upstream closed with `field_simp` and then `ring`.
   *
   * Track R throws these away, and correctly: `field_simp; ring` hands `ring` a goal this system
   * was never given. They are exactly the goals this fragment exists for, so here they are the
   * corpus rather than the offcuts.
   */
  private val fieldGoals: Vector[LeanCorpus.Declaration] =
    corpus.filter(declaration => LeanCorpus.tactic(declaration) == "field_simp ring")

  private lazy val outcomes: Vector[(LeanCorpus.Declaration, Outcome, String)] =
    fieldGoals.map { declaration =>
      val result = goalOf(declaration) match {
        case Left(failure) => failure
        case Right(goal) =>
          field.prove(goal) match {
            case Right(_) => (Outcome.Proved, "")
            case Left(error) => (Outcome.Unproved, error.message)
          }
      }
      (declaration, result._1, result._2)
    }

  private def count(outcome: Outcome): Int = outcomes.count(_._2 == outcome)

  "FIELD against the field goals of the ring corpus" should "leave nothing readable unproved" in {
    info(
      s"${corpus.size} declarations, ${fieldGoals.size} closed by field_simp then ring: " +
        s"proved ${count(Outcome.Proved)}, unreadable ${count(Outcome.Unreadable)}, " +
        s"outside the fragment ${count(Outcome.Outside)}, unproved ${count(Outcome.Unproved)}"
    )

    outcomes.foreach { case (declaration, outcome, why) =>
      info(s"line ${declaration.line}: $outcome${if (why.isEmpty) "" else s" ($why)"}")
    }

    val unproved = outcomes.collect { case (declaration, Outcome.Unproved, why) => (declaration.line, why) }
    val unexplained = unproved.filterNot { case (line, _) => KnownUnproved.contains(line) }
    withClue(
      "read, and not proved, and not on the written exception list:\n" +
        unexplained.map { case (line, why) => s"line $line: $why" }.mkString("\n") + "\n"
    ) {
      unexplained shouldBe empty
    }

    // The half that decides whether it is an exception list. The day the inverse of a product can
    // be taken apart, this says so instead of sitting there claiming a limit that is gone.
    val fixed = KnownUnproved -- unproved.map(_._1).toSet
    withClue(s"on the exception list and no longer failing, so remove them: $fixed\n") {
      fixed shouldBe empty
    }

    // The side neither of those closes, and the one this suite could pass green while losing. Both
    // lists above are about a goal that was read and not proved, so a declaration that stopped
    // being readable, or that `Translate` began refusing, empties them rather than filling them.
    // What is stated here is therefore the count that has to hold: everything the corpus offers is
    // proved, except what the exception list excuses, against the size of the corpus rather than
    // against a number written down here.
    withClue(
      s"${fieldGoals.size} field goals: proved ${count(Outcome.Proved)}, " +
        s"unreadable ${count(Outcome.Unreadable)}, outside the fragment ${count(Outcome.Outside)}, " +
        s"read and unproved ${count(Outcome.Unproved)}, excused ${KnownUnproved.size}\n"
    ) {
      count(Outcome.Proved) shouldBe (fieldGoals.size - KnownUnproved.size)
    }
  }

  /**
   * The written exception list, which is where a failing case goes when the prover is not fixed
   * instead, and it is empty.
   *
   * Line 94, `2 * x ^ 3 * 2 / (24 * x) = x ^ 2 / 6`, was its one member for a few hours on
   * 2026-09-09: it is read, it is a field goal, and its denominator is a product, so settling it
   * needed `inv (24 * x)` to become `inv 24 * inv x`. It left the list by the suite failing on an
   * entry that had stopped failing.
   *
   * What the entry recorded was measured and it was right: the same goal with its denominator
   * written `/ 24 / x` was already proved assuming `~(x = 0)` and nothing else, so one step stood
   * between the fragment and the goal. That step is `Field.reciprocal`, which takes `24 * x` apart
   * by recursion and closes with `Coefficient.inverseOfUnit`; no lemma about the inverse of a
   * symbolic product was added, and the condition the goal carries is `~(x = 0)` alone, because a
   * numeral factor is settled rather than assumed.
   */
  private val KnownUnproved: Set[Int] = Set.empty

  it should "reach the corpus rather than bounce off it" in {
    // Three declarations is a small corpus, and a suite over a small corpus can pass by reading
    // none of it. This is the guard: the file has to still contain the goals this measures.
    fieldGoals should have length 3
    onRingGoals.size should be > (ringGoals.size / 2)
  }

  "The counts in the evaluation document" should "be the ones this suite measures" in {
    // Spelled from the measurement rather than written beside it, so the two cannot drift.
    // `RingCorpusSpec` carries the same test for track R and states the convention both follow: if
    // the suite and the document disagree, the document is wrong.
    //
    // Both directions, because containment alone lets a table grow a row nothing measures. The
    // table is found by the row naming its own corpus and then read out to its own edges, so a row
    // is compared against track F's table and not against an identically worded row of another
    // track's, and no surrounding prose is matched on.
    val evaluation = read("docs/evaluation.md")
    val anchor = "| declarations closed by `field_simp` then `ring` |"

    val claims = Vector(
      s"$anchor ${fieldGoals.size} |",
      s"| proved | ${count(Outcome.Proved)} |",
      s"| unreadable | ${count(Outcome.Unreadable)} |",
      s"| refused as outside the fragment | ${count(Outcome.Outside)} |",
      s"| read, and unproved | ${count(Outcome.Unproved)} |"
    )

    val lines = evaluation.split("\n", -1).toVector
    val at = lines.indexWhere(_.startsWith(anchor))
    withClue(s"docs/evaluation.md has no row beginning `$anchor`\n") {
      at should be >= 0
    }

    val above = lines.take(at).reverse.takeWhile(_.startsWith("|")).reverse
    val below = lines.drop(at).takeWhile(_.startsWith("|"))
    val rule = Set('|', '-', ' ')
    val rows = (above ++ below).map(_.trim).filterNot(_.forall(rule))

    val missing = claims.filterNot(claim => rows.contains(claim))
    withClue(s"track F's table in docs/evaluation.md does not say:\n${missing.mkString("\n")}\n") {
      missing shouldBe empty
    }

    val unmeasured = rows.filterNot(row => claims.contains(row))
    withClue(s"track F's table states a row this suite does not measure:\n${unmeasured.mkString("\n")}\n") {
      unmeasured shouldBe empty
    }
  }
}
