package garden.xeno.symbolum.published

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.LogicError
import garden.xeno.symbolum.tactics.{Elaborate, Workspace}
import garden.xeno.symbolum.theories.{Generated, Library}

import java.nio.charset.StandardCharsets

/**
 * The proof documents this repository publishes, checked, and their theorems as a library.
 *
 * A document written in the proof language (`docs/language.md`) is checked by the kernel wherever it
 * is checked, and that makes it a theorem for whoever checked it. What publishing adds is that the
 * repository holds it: the document is one of [[Published.Names]], it is checked on every run of
 * the suite, its theorems are a [[Library]] a caller asks the way it asks the chain's, and
 * `docs/published.md` lists them and is compared with this code. `docs/adr/0070` is the decision,
 * this module is its third increment, and `docs/adr/0073` decides what a document sees and why the
 * published ones are made again in one theory.
 *
 * == Why a module of its own ==
 *
 * The documents are checked by the elaborator in `tactics`, so what holds them sits above it. The
 * library of the chain is built in `theories`, two floors below, and it cannot see a document
 * without inverting the graph; so the published theorems are a library of their own, beside the
 * chain's rather than inside it, which is how they are offered.
 *
 * == What publishing refuses ==
 *
 * Everything that would let a published theorem mean less than it says:
 *
 *  - a document that does not check, in any declaration or import: an incomplete proof is not a
 *    theorem anywhere in this repository, and here it is not a published one either;
 *  - a name two published documents both declare, constant or theorem. Each document is checked in
 *    a theory of its own, holding what it imports, so two documents that do not import each other
 *    could each define `DOUBLE`; the published documents are then made again in **one** theory, in
 *    the order they were checked, and the kernel refuses the second definition. One theory is what
 *    keeps the argument `SoundnessAttackSpec` makes about two theories declaring one name from
 *    applying to a reader who takes theorems from two documents;
 *  - an axiom. The language has no declaration that asserts one, and the one theory is compared
 *    with the chain's: the axioms are the same list, or nothing is published. A domain assumption
 *    reaches the library only as the hypothesis of a theorem, as the ADR asks.
 *
 * A document whose name is not in [[Published.Names]] is not read even when a published one
 * imports it, so nothing reaches the library by being imported.
 */
final class Published private (
  /** The published documents, in the order they were checked: each after what it imports. */
  val documents: Vector[Published.Document],
  /** The one theory every published document is made again in, and its notation and logic. */
  val scope: Elaborate.Scope,
  /** Every published theorem and definition, labelled with the document that holds it. */
  val library: Library
) {

  /** The listing `docs/published.md` carries: each document, what it imports, and its statements. */
  def listing: String =
    documents.map { document =>
      val imports =
        if (document.imports.isEmpty) "Imports nothing."
        else s"Imports ${document.imports.map(name => s"`$name`").mkString(", ")}."
      val lines = library.from(document.name).sortBy(_.name).map { entry =>
        val statement = scope.legible(entry.theorem.conclusion)
          .getOrElse(s"${Library.NotReadable} ${scope.show(entry.theorem.conclusion)}")
        s"  ${entry.name.padTo(24, ' ')} $statement"
      }
      s"## ${document.name}\n\n$imports\n\n```\n${lines.mkString("\n")}\n```"
    }.mkString("\n\n")
}

object Published {

  /**
   * Every published document, by name. Each is `NAME.sym` under [[Resources]].
   *
   * A list rather than a scan of the directory, because a jar has no directory to scan; `PublishedSpec`
   * compares it with the files in both directions, so a document added on disk and not here, or
   * named here and not on disk, is a red run and not a document silently left out.
   */
  val Names: Vector[String] = Vector("Doubling", "Parity")

  /** Where the documents are, on the classpath. */
  val Resources: String = "garden/xeno/symbolum/published"

  /** One published document: its name, the documents it imports, and the report it checked to. */
  final case class Document(name: String, imports: Vector[String], report: Elaborate.Report)

  /** The text of a published document, or nothing for a name that is not one. */
  def source(name: String): Option[String] =
    if (!Names.contains(name)) None
    else
      Option(getClass.getClassLoader.getResourceAsStream(s"$Resources/$name.sym")).map { stream =>
        try new String(stream.readAllBytes(), StandardCharsets.UTF_8) finally stream.close()
      }

  /** The published documents over the standard chain. */
  lazy val standard: Published =
    of(Elaborate.standard).fold(refusals => throw new IllegalStateException(refusals.mkString("\n")), identity)

  /**
   * The published documents checked by `elaborate` and read from `source`, or every reason they
   * cannot be published.
   *
   * Every reason, not the first: a document that does not check and a name two documents share are
   * repaired in different places, and a list that stops at the first sends its reader round once per
   * problem.
   */
  def of(elaborate: Elaborate, names: Vector[String] = Names, source: String => Option[String] = source): Either[Vector[String], Published] = {
    val checked = new Workspace(elaborate, name => if (names.contains(name)) source(name) else None).check(names)
    val missing = names.filterNot(name => checked.find(name).isDefined).map(name => s"$name: no document of that name could be read")
    val failing = checked.done.filterNot(_.report.ok).map(done => s"${done.name} does not check:\n${done.report.render}")
    val chain = elaborate.chain.widest
    val base = Elaborate.Scope(chain.theory, chain.notation, chain.logic)

    // The one theory: every published definition made again, in the order the documents were checked.
    val (scope, clashes) = checked.done.foldLeft((base, Vector.empty[String])) { case ((current, refused), done) =>
      done.report.entries.filter(_.status == Elaborate.Status.Defined).foldLeft((current, refused)) {
        case ((inner, problems), entry) =>
          entry.theorem.flatMap(theorem => Term.destEq(theorem.conclusion)) match {
            case None => (inner, problems :+ s"${done.name}: ${entry.name} is defined and its defining theorem is not an equation")
            case Some((_, body)) =>
              val made = for {
                pair <- LogicError.lift(Kernel.defineConstant(inner.theory, entry.name, body))
                logic <- inner.logic.over(pair._1)
              } yield Elaborate.Scope(pair._1, inner.notation, logic)
              made match {
                case Right(wider) => (wider, problems)
                case Left(error) =>
                  (inner, problems :+ s"${done.name}: ${entry.name} cannot be defined beside the other published documents: ${error.render(inner.show)}")
              }
          }
      }
    }

    // One name, one fact: a theorem name two documents share is refused even when neither imports
    // the other, which the per-document check cannot see.
    val facts = checked.done.flatMap(done => done.report.entries.collect {
      case entry if entry.theorem.isDefined => (entry.name, done.name, entry.theorem.get)
    })
    val shared = facts.groupBy(_._1).toVector.sortBy(_._1).collect {
      case (name, holders) if holders.size > 1 => s"$name is declared in ${holders.map(_._2).distinct.mkString(" and ")}"
    }
    val axioms =
      if (scope.theory.axioms == chain.theory.axioms) Vector.empty
      else Vector(s"the published documents assert ${scope.theory.axioms.size - chain.theory.axioms.size} axioms of their own")

    val refusals = missing ++ failing ++ clashes ++ shared ++ axioms
    if (refusals.nonEmpty) Left(refusals)
    else {
      val documents = checked.done.map(done => Document(done.name, done.parsed.imports.map(_.name), done.report))
      val library = Library.of(checked.done.map(done =>
        done.name -> done.report.entries.collect { case entry if entry.theorem.isDefined => entry.name -> entry.theorem.get }.toMap))
      Right(new Published(documents, scope, library))
    }
  }

  /* ------------------------------------------------------------------ the page */

  /** Where the listing goes, relative to the repository root. */
  val Page: String = "docs/published.md"

  /** The command that writes it, written here so that the page and the message cannot drift. */
  val Command: String = "tools/sbt \"published/runMain garden.xeno.symbolum.published.Published\""

  /** The generated region of the page. */
  val Section: Generated = Generated("published", Page, Command)

  def main(arguments: Array[String]): Unit =
    Generated.run(arguments, Page, Vector(Section -> standard.listing))
}
