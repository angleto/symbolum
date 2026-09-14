package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.*

/**
 * What the vendored ring corpus costs, measured once and read by everything that quotes it.
 *
 * `CostCorpusSpec` asserts these counts and `garden.xeno.symbolum.tactics.Evaluation` writes them into
 * `docs/evaluation.md`. They were two readings of the same corpus until 2026-09-12, one of them
 * hand-copied, and the consequence is on the record: the per-rule census in that document summed
 * to 196623 beside a total line that said 153953, and the table had been stale through two separate
 * repairs before anyone added the column up.
 *
 * The corpus itself is frozen at the commit `RingCorpusSpec`'s notice names, so what moves these
 * numbers is a tactic changing what it reaches for, which is the change worth being told about.
 */
object RingCost {

  /** The file, vendored, and read rather than transcribed. */
  val CorpusFile: String = "third-party/mathlib/MathlibTest/Tactic/Ring/Ring.lean"

  private val cost = Cost.standard

  /** The theory the goals are read into, exposed because a caller printing a term needs it. */
  val reals: Signature = cost.reals

  /**
   * The vendored file, or nothing to measure.
   *
   * Loud rather than empty, and not an `Either`: the corpus is committed in this repository, so a
   * missing file is a broken checkout and every count below it would otherwise come back as a
   * cheerful zero. `CostCorpusSpec` said the same thing with `fail` while it owned this.
   */
  private def read(relative: String): String =
    LeanCorpus
      .read(relative)
      .getOrElse(throw new IllegalStateException(s"cannot find $relative"))

  /** Every declaration in the file, whether or not it reads as a proposition here. */
  lazy val declarations: Vector[LeanCorpus.Declaration] = LeanCorpus.declarations(read(CorpusFile))

  /** The goal of a declaration as a proposition here, when it reads as one. */
  def goalOf(declaration: LeanCorpus.Declaration): Option[Term] =
    LeanCorpus.goalOf(declaration).flatMap { text =>
      LeanSyntax.equation(text).toOption.flatMap { case (left, right) =>
        (for {
          leftTerm <- Translate.toTerm(reals, left)
          rightTerm <- Translate.toTerm(reals, right)
          equation <- TacticError.lift(LogicError.lift(Term.eq(leftTerm, rightTerm)))
        } yield equation).toOption
      }
    }

  /** One report per goal that reads, priced. */
  lazy val reports: Vector[Cost.Report] =
    declarations.flatMap(goalOf).flatMap(goal => cost.of(goal).toOption)

  /** The proofs, which is what a census of inferences is over. */
  lazy val proved: Vector[Cost.Report] = reports.filter(_.outcome == Cost.Outcome.Proved)

  /**
   * The census over all of them, heaviest rule first.
   *
   * Keyed by `Derivation.census`'s own key, which is the rule's simple name. The document spells
   * those out in words, and [[inWords]] is the one place that translation happens.
   */
  lazy val census: Vector[(String, Int)] =
    proved
      .flatMap(_.census.toVector)
      .groupBy(_._1)
      .map { case (rule, counted) => (rule, counted.map(_._2).sum) }
      .toVector
      .sortBy { case (rule, howMany) => (-howMany, rule) }

  /** Every inference of every proof in the corpus, which is the census added up. */
  lazy val inferences: Int = census.map(_._2).sum

  /** `EqualityElimination` as a reader wants to read it, and not as a class is named. */
  def inWords(rule: String): String =
    rule
      .replaceAll("([a-z0-9])([A-Z])", "$1 $2")
      .toLowerCase
}
