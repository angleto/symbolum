package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The command that writes the generated tables of `docs/proving.md`.
 *
 * One table today, and it is the one that was in two places at once. The eight statements
 * [[garden.xeno.symbolum.logic.Classical]] derives, what each of them rests on and what each of them costs,
 * were written out by hand in the guide **and** in that file's own docstring: two copies of one
 * measurement, agreeing on the day they were written and both wrong on 2026-09-11, when `Conv.refl`
 * began sharing the reflexivity of an atom and every step count in them moved.
 *
 * The docstring copy is gone rather than generated a second time. A Scaladoc comment cannot carry a
 * marker a splice can find without the marker showing up in the rendered page, and a rule with two
 * implementation sites is a defect even while the two agree; what the file says now is where the
 * table is and what a reader will find there.
 *
 * == Where each column comes from ==
 *
 *   - **the statement** is `Classical.Statements`, the text the derivation is compared against,
 *     rather than the printer's rendering of the conclusion. `ClassicalSpec` parses each of those
 *     and checks the derivation arrived at it, so the column is bound to the code by that test; the
 *     printer's form names the bound variables the derivation happened to use and is not.
 *   - **what it rests on** is `Derivation.axiomsOf`, matched against the two axioms this extension
 *     asserts. `ClassicalSpec` asserts the same division independently.
 *   - **the steps** are `Derivation.size`, which is the figure nothing but a test was holding.
 *
 * == Why it is here and not in `modules/logic` ==
 *
 * [[Generated]] is, and it is here because `Lemmas` is. `theories` depends on `logic`, so this can
 * see `Classical`; the other direction would need the splice mechanism copied into a module that
 * has no other use for it.
 */
object Guide {

  /** Where the tables go, relative to the repository root. */
  val Document: String = "docs/proving.md"

  /** The command that runs this, written here so that the document and the message cannot drift. */
  val Command: String = "sbt \"theories/runMain garden.xeno.symbolum.theories.Guide\""

  /** The eight classical statements, with what each rests on and what each costs. */
  val ClassicalTable: Generated = Generated("classical", Document, Command)

  /**
   * The table, in the order the statements are derived in, or the first refusal that stopped it.
   *
   * Ordered by `Classical.Statements` rather than by size: the order a reader wants is the order
   * the file builds them in, and sorting by the step count would reshuffle the table every time one
   * of the derivations changed.
   */
  def classicalTable(classical: Classical): Either[String, String] = {
    val named: Map[Term, String] =
      classical.axioms.map { case (name, axiom) => axiom.conclusion -> name }

    val rows = Classical.Statements.map { case (name, statement) =>
      classical.fact(name).left.map(_.message).map { theorem =>
        val axioms = Derivation.axiomsOf(theorem).toVector.map(named.getOrElse(_, "an unnamed axiom"))
        Vector(
          s"`$name`",
          s"`⊢ $statement`",
          if (axioms.isEmpty) "nothing" else axioms.sorted.map(axiom => s"`$axiom`").mkString(", "),
          Derivation.size(theorem).toString
        )
      }
    }

    rows
      .foldLeft[Either[String, Vector[Vector[String]]]](Right(Vector.empty)) { (acc, row) =>
        for { rows <- acc; next <- row } yield rows :+ next
      }
      .map(rows => Generated.table(Vector("Theorem", "Statement", "Rests on", "Steps"), rows))
  }

  /** Every generated section of the guide, against the standard classical extension. */
  def sections(): Either[String, Vector[(Generated, String)]] =
    classicalTable(Classical.standard).map(table => Vector(ClassicalTable -> table))

  def main(arguments: Array[String]): Unit =
    sections() match {
      case Left(why) =>
        System.err.println(s"$Document was not rewritten: $why")
        sys.exit(1)
      case Right(sections) => Generated.run(arguments, Document, sections)
    }
}
