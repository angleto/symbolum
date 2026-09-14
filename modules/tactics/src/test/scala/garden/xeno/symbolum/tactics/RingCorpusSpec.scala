package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.*

/**
 * How much of another prover's ring corpus this one certifies.
 *
 * Track R of `docs/evaluation.md`. `OracleCertificationSpec` compares the system against
 * expressions nobody wrote down; this compares it against expressions somebody else wrote down,
 * for a different prover, without knowing this one existed. Those are different questions and both
 * are worth asking: a generator cannot produce the goal shapes a library's users actually bring,
 * and a library's tests cannot be tuned to what this system happens to reach.
 *
 * == The corpus is read, not transcribed ==
 *
 * The file is `third-party/mathlib/MathlibTest/Tactic/Ring/Ring.lean`, frozen at the commit its
 * notice names and byte-identical to upstream, which the hash check below pins. Nothing selects
 * examples by hand. Whoever transcribes a benchmark chooses which cases to carry across and how to
 * write them, and both choices flatter the system being measured; an earlier measurement of this
 * same file was taken that way and reported fourteen certifications out of twenty-one hand-copied
 * goals, where reading the file finds more of both.
 *
 * So every count here is produced by the code below, and the same counts appear in
 * `docs/evaluation.md`, where the last test asserts they agree. If this suite and that document
 * disagree, the document is wrong.
 *
 * == The four buckets ==
 *
 *  - **unreadable**: [[LeanSyntax]] does not read the goal, because it is written with `•`, `↑`, a
 *    lambda, or a type ascription that could be a coercion. This says nothing about the prover. It
 *    is the width of the reader, and it is deliberately narrow. `⁻¹` was in this list until
 *    2026-09-09 and is not: the reader takes it, and takes it as `1 / x` rather than as `x ^ -1`,
 *    which is what lands such a goal inside the fragment instead of just outside it.
 *  - **outside the fragment**: read, and then refused by [[Translate]] by name: an exponent with a
 *    variable in it, or anything else the theory of the reals has no constant for. Also not a
 *    failure. A quotient left this bucket on the same day and for a reason of its own: `x / y`
 *    abbreviates `x * inv y`, unfolding an abbreviation asks for nothing, and what asks for
 *    `~(y = 0)` is the cancellation, which is the tactic's step and never the reader's.
 *  - **beyond the numeral bound**: read, inside the fragment, and declined because
 *    `Oracle.NumeralBudget` says the arithmetic on its numerals costs more than a caller should
 *    wait for. **This bucket is empty, and it held one goal until 2026-09-04.** The goal was
 *    `(876544 : ℤ) * -1 + (1000000 - 123456) = 0`, and what put it there was RING expanding a
 *    coefficient of `n` into `n` copies of a term. RING collects them now, the budget moved from
 *    100 to a million million on the measurement recorded in `Oracle`, and the goal is certified.
 *    The exact value still selects nothing here and is still not tuned to this corpus: no goal in
 *    the file has a written numeral above 1000000, so any budget above that partitions it the same
 *    way.
 *  - **certified**, and **in the fragment and unproved**. A member of the last is a goal this
 *    system can state, can afford, and cannot prove, while another prover's test suite says it is
 *    true: that is a finding about RING. It must hold nothing but what the written exception list
 *    below excuses, and nothing that list excuses may have stopped failing.
 *
 * == What it costs ==
 *
 * About 330 ms on 2026-09-04, warm, and no goal dominates it. It cost a second or two earlier that
 * day, and one goal was most of it: `(x + 1) ^ 6 = (1 + x) ^ 6` took 1033 ms of a 1055 ms total in
 * one run and 2033 of 2195 in another, because its expansion carried the coefficient 20 although
 * nothing written in it exceeds 6. Two runs of the same work on the same machine differing by a
 * factor of two is the reason none of the timings in this file are quoted as though they were
 * stable: what they established was which goal dominated and why, and the answer to why is what
 * changed.
 *
 * That goal was the same lesson `OracleCertificationSpec` records from the other direction, and it
 * is why the bound below is a guard rather than a cost model. It still is: the cost now follows the
 * digits of a numeral rather than its value, which is a different function of the input and not a
 * constant one.
 */
class RingCorpusSpec extends AnyFlatSpec with Matchers {

  /** The corpus, and the notice that says where it came from. */
  private val CorpusFile: String = "third-party/mathlib/MathlibTest/Tactic/Ring/Ring.lean"
  private val NoticeFile: String = "third-party/mathlib/README.md"

  private enum Outcome:
    case Certified, Outside, Unreadable, BeyondBound, Unproved

  /* ------------------------------------------------------------------ the measurement */

  private def read(relative: String): String =
    LeanCorpus.read(relative).getOrElse(fail(s"cannot find $relative"))

  private val oracle = Oracle.standard

  private val corpus: Vector[LeanCorpus.Declaration] = LeanCorpus.declarations(read(CorpusFile))

  /**
   * The declarations upstream closed with `ring` or `ring1` and nothing else.
   *
   * The whole proof, not a proof mentioning the tactic. `field_simp; ring` asks `ring` a different
   * goal from the one written down, and `conv => ring` asks it a subterm; counting either would be
   * claiming this system was offered a question it was not offered. `ring!` and `ring_nf` are
   * different tactics with different contracts.
   */
  private val ringGoals: Vector[LeanCorpus.Declaration] =
    corpus.filter { declaration =>
      val closed = LeanCorpus.tactic(declaration)
      closed == "ring" || closed == "ring1"
    }

  /** Computed once: the certifications cost about nine seconds and each test wants the same run. */
  private lazy val outcomes: Vector[(LeanCorpus.Declaration, Outcome, String)] =
    ringGoals.map { declaration =>
      val result = LeanCorpus.goalOf(declaration) match {
        case None => (Outcome.Unreadable, "no goal separator")
        case Some(text) =>
          LeanSyntax.equation(text) match {
            case Left(why) => (Outcome.Unreadable, why)
            case Right((left, right)) =>
              // The same budget `Discovery` consults. One rule about what RING can afford, stated
              // once in `Oracle` with the measurement that put it there.
              Oracle.affordable(left, right) match {
                case Left(largest) => (Outcome.BeyondBound, s"largest written numeral $largest")
                case Right(_) =>
                  oracle.certifyIdentity(left, right) match {
                    case Right(_) => (Outcome.Certified, "")
                    case Left(error: OutsideFragment) => (Outcome.Outside, error.reason)
                    case Left(error) => (Outcome.Unproved, error.message)
                  }
              }
          }
      }
      (declaration, result._1, result._2)
    }

  private def count(outcome: Outcome): Int = outcomes.count(_._2 == outcome)

  /* ------------------------------------------------------------------------- the tests */

  "The vendored corpus" should "be the file its notice describes" in {
    // Both directions of the same agreement: editing the file without re-measuring, or rewriting
    // the notice without touching the file, each fail here. The corpus is only evidence while it
    // is upstream's own text.
    val hash = LeanCorpus.hashOf(CorpusFile).getOrElse(fail(s"cannot find $CorpusFile"))

    withClue(s"$CorpusFile now hashes to $hash; $NoticeFile does not say so\n") {
      read(NoticeFile) should include(hash)
    }
  }

  "RING against Mathlib's ring corpus" should "leave nothing in the fragment unproved" in {
    info(
      s"${corpus.size} declarations, ${ringGoals.size} proved by exactly ring or ring1: " +
        s"certified ${count(Outcome.Certified)}, outside the fragment ${count(Outcome.Outside)}, " +
        s"unreadable ${count(Outcome.Unreadable)}, beyond the numeral bound ${count(Outcome.BeyondBound)}, " +
        s"unproved ${count(Outcome.Unproved)}"
    )

    val unproved = outcomes.collect { case (declaration, Outcome.Unproved, why) => (declaration.line, why) }
    val unexplained = unproved.filterNot { case (line, _) => KnownUnproved.contains(line) }
    withClue(
      "stated, affordable, and not proved, and not on the written exception list:\n" +
        unexplained.map { case (line, why) => s"line $line: $why" }.mkString("\n") + "\n"
    ) {
      unexplained shouldBe empty
    }

    // The other half of an exception list, and the half that decides whether it is one. A list
    // that only ever excuses grows stale silently: the day the tactic learns to do one of these,
    // nothing says so and the entry sits there claiming a limit that is gone.
    val fixed = KnownUnproved -- unproved.map(_._1).toSet
    withClue(s"on the exception list and no longer failing, so remove them: $fixed\n") {
      fixed shouldBe empty
    }
  }

  /**
   * The written exception list, which is what TST-09's discipline asks for instead of relaxing the
   * assertion above.
   *
   * It held two entries, both the same goal `x/2 + x/2 = x`, stated twice in the corpus. They
   * arrived on 2026-09-09 when the reader learned to read a quotient, and they left later the same
   * day when a coefficient stopped having to be a whole number. Neither was removed by hand: the
   * second assertion above fails when a listed line stops failing, so the list said so itself.
   *
   * **The three here are a different kind of entry, and the only one so far that is not about this
   * prover at all.** Lines 65, 66 and 70 are `(1/x)^2 = 1/x^2`, the same again, and
   * `1/x^2/y = 1/(y * x^2)`, and they became readable the same evening, when `LeanSyntax` learned
   * `⁻¹`. Upstream closes each with plain `ring`, and upstream is right: in Mathlib `⁻¹` is a total
   * function with `0⁻¹ = 0`, so `(a * b)⁻¹ = a⁻¹ * b⁻¹` holds everywhere, zero included, and the
   * identity needs no hypothesis.
   *
   * Here it is not a theorem. `inv` is the field axiom's inverse and the theory says nothing
   * whatever about `inv 0`, so at `x = 0` these compare two terms nobody has constrained. RING is
   * right to refuse them and `Field` proves all three assuming `~(x = 0)`, which `FieldCorpusSpec`
   * asserts. So the entry records a difference between two theories rather than a limit of a
   * tactic, and the way to remove it is a decision about the theory, which is not a decision a test
   * may take.
   *
   * **That decision was taken on 2026-09-10 and is recorded in `docs/adr/0007`: not by adopting the
   * convention, but by removing the question.** `inv 0 = 0` is not free anywhere. Mathlib admits it
   * as a field of the `GroupWithZero` class these declarations sit under, so it is an axiom there
   * too and merely uncounted; HOL Light proves it, because HOL Light constructs its reals. Asserting
   * it here would be a seventeenth axiom that is not a field axiom, which spends the property that
   * the sixteen can be read against a textbook. Since the reals are to be constructed, `inv` becomes
   * a defined constant and the convention becomes a choice inside a definition, costing no axiom.
   * Until then these three stay, and this list keeps recording what it records.
   */
  private val KnownUnproved: Set[Int] = Set(65, 66, 70)

  it should "reach the corpus rather than bounce off it" in {
    // The bucket above is empty on a reader that reads nothing, which is how a must-be-empty
    // assertion goes quietly wrong. This is the guard: most of what is readable is also certified.
    count(Outcome.Certified) should be > (ringGoals.size / 4)
  }

  "The reader" should "refuse an ascription that could be a coercion" in {
    // The one place this pipeline could lie. Dropping `(876544 : ℤ)` to its literal cannot change
    // what the text says; dropping `(n : ℝ)` where `n : ℕ` would, and the kernel would then certify
    // a true theorem about a statement nobody wrote. Pinned because it is a decision, not an
    // oversight: the corpus contains an instance of each.
    LeanSyntax.equation("(2 : R) * a = a * 2") should matchPattern { case Right(_) => }
    LeanSyntax.equation("(x : a) = x * 1").left.map(_.contains("coercion")) shouldBe Left(true)
  }

  it should "read the inverse symbol, and read it as a quotient" in {
    // What emptied six of the unreadable bucket on 2026-09-09, and the reading is a decision rather
    // than a detail: `Translate` refuses a negative exponent by name and does not refuse a
    // quotient, so `x ^ -1` would have moved these goals from one bucket to the next instead of
    // into the fragment. `LeanSyntax` argues for the quotient in its own comment; this is what
    // holds it to the argument, and it is stated by reading the same claim written both ways rather
    // than by building an `Expr` here, so the reader is compared against itself.
    val bySymbol = LeanSyntax.equation("(a * b)⁻¹ = a⁻¹ * b⁻¹")
    val byQuotient = LeanSyntax.equation("1 / (a * b) = (1 / a) * (1 / b)")

    bySymbol should matchPattern { case Right((Div(_), Mul(_))) => }
    bySymbol shouldBe byQuotient
  }

  "The counts in the evaluation document" should "be the ones this suite measures" in {
    // Spelled from the measurement rather than written beside it, so the two cannot drift. The
    // document states these as a table, one row per line, which is why each claim is one line.
    val evaluation = read("docs/evaluation.md")
    val claims = Vector(
      s"| declarations in the file | ${corpus.size} |",
      s"| proved by exactly `ring` or `ring1` | ${ringGoals.size} |",
      s"| read as this arithmetic | ${ringGoals.size - count(Outcome.Unreadable)} |",
      s"| not read here | ${count(Outcome.Unreadable)} |",
      s"| certified by RING | ${count(Outcome.Certified)} |",
      s"| refused as outside the fragment | ${count(Outcome.Outside)} |",
      s"| beyond the numeral bound | ${count(Outcome.BeyondBound)} |",
      s"| in the fragment and unproved | ${count(Outcome.Unproved)} |"
    )

    val missing = claims.filterNot(evaluation.contains)
    withClue(s"docs/evaluation.md does not say:\n${missing.mkString("\n")}\n") {
      missing shouldBe empty
    }
  }
}
