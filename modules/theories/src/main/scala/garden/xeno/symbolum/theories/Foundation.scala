package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The command that writes the generated table of `README.md`: what each development asks you to
 * believe.
 *
 * The fourth user of [[Generated]], and the one whose absence had already cost something. The front
 * page's first table said the naturals cost **two** axioms and a development holding both
 * **eighteen**, while `NaturalSpec` asserted three and nineteen and `ChainSpec` asserted nineteen in
 * four places. The figures were right when they were written and went stale on 2026-09-10, when eta
 * landed in `Classical.scala` and took the classical logic from one axiom to two. They were repaired
 * by hand on 2026-09-14 and would have gone stale again at the next axiom, which is why the repair
 * is this file rather than that edit.
 *
 * A second site carried the same error and was in no report: the capability table's row for the
 * naturals, which said "two axioms of their own". Both are now one generated region, so there is one
 * copy and a test that fails naming the command.
 *
 * == Why the three counts are read off `Real.standard`, `Natural.standard` and `Chain.standard` ==
 *
 * Because that is what the sentence means. The claim is about **whichever development you build
 * on**, and the reals and the naturals are siblings rather than a chain: `Real.standard` sits over
 * `Logic.standard`, which has no axioms, so a session proving something about the reals is not asked
 * to believe the choice operator or eta. `NaturalSpec` asserts exactly that division, and it is the
 * reason this table has three rows rather than one number.
 *
 * `Chain.standard` is the third row because a development holding both is what the chain assembles,
 * and `widest` is where to read it: which development is last changes whenever a link is added, and
 * naming one here would be the same defect this file exists to remove, one layer up.
 *
 * == What is not in the table, deliberately ==
 *
 * The sixteen names of the field. A row listing them would be sixteen identifiers wide on the front
 * page, and `docs/lemmas.md` already lists every one of them under the development that holds it.
 * The three of the naturals **are** named, because the page named them by hand before this file
 * existed and dropping that would have made the document say less than it used to.
 */
object Foundation {

  /** Where the table goes, relative to the repository root. */
  val Document: String = "README.md"

  /** The command that runs this, written here so that the document and the message cannot drift. */
  val Command: String = "sbt \"theories/runMain garden.xeno.symbolum.theories.Foundation\""

  /** What each development asks a reader to believe. */
  val TrustedBase: Generated = Generated("trusted-base", Document, Command)

  /**
   * The name an axiom is held under, for the axioms a reader can be shown by name.
   *
   * A term nothing names is reported as unnamed rather than skipped: a table that silently dropped
   * an axiom it could not name would show a count and a list that disagree, which is worse on this
   * page than anywhere else in the repository.
   */
  private def named(naturals: Natural, reals: RealTheory): Map[Term, String] =
    (naturals.classical.axioms ++ naturals.axioms ++ reals.axioms).map { case (name, axiom) =>
      axiom.conclusion -> name
    }

  /** The axioms a theory holds, by name, in an order that does not move between runs. */
  private def heldBy(theory: Theory, names: Map[Term, String]): Vector[String] =
    theory.axioms.toVector.map(names.getOrElse(_, "an unnamed axiom")).sorted

  /**
   * The table, as a function of the three developments and of nothing written here.
   *
   * Takes them rather than reaching for the standard ones so that a test can put a development it
   * built to the same question, which is what stops this from being a second copy of the figures.
   */
  def trustedBaseTable(naturals: Natural, reals: RealTheory, both: Signature): String = {
    val names = named(naturals, reals)
    val three = heldBy(naturals.theory, names)

    Generated.table(
      Vector("A development built on", "Axioms it asks you to believe", "Which they are"),
      Vector(
        Vector(
          "the reals alone",
          reals.theory.axioms.size.toString,
          "a complete ordered field, listed in `Real.scala` and in [docs/lemmas.md](docs/lemmas.md)"
        ),
        Vector(
          "the naturals alone",
          naturals.theory.axioms.size.toString,
          three.map(name => s"`$name`").mkString(", ")
        ),
        Vector(
          "both, which is what the standard chain assembles",
          both.theory.axioms.size.toString,
          "the two rows above, added, since they share none"
        )
      )
    )
  }

  /** Every generated section of the front page, against the developments a reader would build on. */
  def sections(): Vector[(Generated, String)] =
    Vector(
      TrustedBase ->
        trustedBaseTable(Natural.standard, Real.standard, Chain.standard.widest)
    )

  def main(arguments: Array[String]): Unit =
    Generated.run(arguments, Document, sections())
}
