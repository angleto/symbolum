package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*

/**
 * Documents that import each other, checked in the order their imports put them in.
 *
 * A document names what it builds on with `import NAME`, and this resolves the name through
 * `source`, which answers the text of the document of that name or nothing. The checker reads files
 * from the directory of the document it was given; the publication module reads its own documents.
 * Neither decision is made here, which is why the source is a function.
 *
 * == What a document sees ==
 *
 * Exactly what it imports, directly or through another import: the definitions of those documents,
 * made again in the theory it is read in, and their theorems as facts it may cite. A document it
 * does not import is not visible to it, even when it was checked earlier, so what a document cites
 * is a function of its own imports and never of the order somebody happened to check things in.
 * That is why each document gets a theory of its own rather than one theory growing as documents
 * are checked: one growing theory would let a document use a constant of any document checked
 * before it, and its imports would stop saying what it rests on.
 *
 * What the publication module needs on top of this, one theory holding every published document so
 * that a name defined twice is refused by the kernel, it builds from the same reports.
 *
 * == Recovery ==
 *
 * As inside a document: a problem is reported where it is and everything else is still checked. An
 * import naming no document, or closing a cycle, is a problem of the importing document's imports
 * and is left out of what it sees. An imported document that does not check is a problem too, and
 * what that document did prove is still seen, so the importer's proofs are checked against the facts
 * they were written to use, and a proof citing one of its failed declarations is told it failed.
 */
final class Workspace(elaborate: Elaborate, val source: String => Option[String]) {
  import Workspace.*
  import Elaborate.{Imported, Problem, Report, Status}

  /**
   * Check the documents named, and every document they import, each after what it imports.
   *
   * The result holds every document reached, in the order checked: a document comes after
   * everything it imports, and documents with no order between them come in the order they were
   * first reached, so the result is a function of the names given and the texts.
   */
  def check(names: Vector[String]): Checked = {
    val (read, seen) = reach(names)
    val order = sorted(read, seen)
    order.foldLeft(Checked(Vector.empty)) { (checked, name) =>
      read(name) match {
        case None => checked
        case Some(parsed) =>
          val (imported, problems) = environment(name, parsed, read, checked)
          val report = elaborate.check(parsed, imported)
          checked.add(Done(name, parsed, report.copy(imports = problems ++ report.imports)))
      }
    }
  }

  /**
   * Every document reached from `names` through imports, read, or nothing where no text answered,
   * and the order they were first reached in, which is what breaks ties when they are sorted.
   */
  private def reach(names: Vector[String]): (Map[String, Option[Document.Parsed]], Vector[String]) = {
    @annotation.tailrec
    def go(pending: List[String], found: Map[String, Option[Document.Parsed]], seen: Vector[String]): (Map[String, Option[Document.Parsed]], Vector[String]) =
      pending match {
        case Nil => (found, seen)
        case name :: rest if found.contains(name) => go(rest, found, seen)
        case name :: rest =>
          val parsed = source(name).map(Document.read)
          val next = parsed.toList.flatMap(_.imports.map(_.name))
          go(rest ++ next, found + (name -> parsed), seen :+ name)
      }
    go(names.toList, Map.empty, Vector.empty)
  }

  /**
   * The documents in an order where each comes after what it imports. A document on a cycle is put
   * after the documents outside it, and the cycle is reported by `environment`, which is where the
   * import that closes it is.
   */
  private def sorted(read: Map[String, Option[Document.Parsed]], seen: Vector[String]): Vector[String] = {
    val imports: Map[String, Vector[String]] =
      read.map { case (name, parsed) => name -> parsed.toVector.flatMap(_.imports.map(_.name)).filter(read.contains) }
    @annotation.tailrec
    def go(done: Vector[String], left: Vector[String]): Vector[String] =
      if (left.isEmpty) done
      else
        left.find(name => imports(name).forall(done.contains)) match {
          case Some(ready) => go(done :+ ready, left.filterNot(_ == ready))
          case None => done ++ left
        }
    go(Vector.empty, seen)
  }

  /** What `name` sees, and the problems of its imports. */
  private def environment(
    name: String,
    parsed: Document.Parsed,
    read: Map[String, Option[Document.Parsed]],
    checked: Checked
  ): (Imported, Vector[Problem]) = {
    val problems = parsed.imports.flatMap { taken =>
      if (taken.name == name)
        Some(Problem(taken.line, s"$name imports itself", Some("remove the import"), None))
      else if (read.get(taken.name).forall(_.isEmpty))
        Some(Problem(taken.line, s"no document named ${taken.name}", Some(s"the import looks for ${taken.name}.sym beside this document"), None))
      else if (closure(taken.name, read).contains(name))
        Some(Problem(taken.line, s"${taken.name} imports $name, directly or through another import, so the two form a cycle",
          Some("a cycle has no order to check its documents in; move what both need into a third document they both import"), None))
      else
        checked.find(taken.name).filterNot(_.report.ok).map(_ =>
          Problem(taken.line, s"${taken.name} does not check, so only what it did prove is imported",
            Some(s"check ${taken.name} on its own and repair it"), None))
    }
    // What is seen: every document reachable through imports that resolved and close no cycle,
    // in the order they were checked, each reached through the first import of `name` that leads to it.
    val usable = parsed.imports.filter(taken => taken.name != name && read.get(taken.name).exists(_.isDefined) &&
      !closure(taken.name, read).contains(name))
    val via: Map[String, Int] = usable.foldLeft(Map.empty[String, Int]) { (found, taken) =>
      (closure(taken.name, read) + taken.name).foldLeft(found)((acc, reached) => if (acc.contains(reached)) acc else acc + (reached -> taken.line))
    }
    val seen = checked.done.filter(done => via.contains(done.name))
    val (imported, clashes) = seen.foldLeft((Imported.none, Vector.empty[Problem])) { case ((acc, clashing), done) =>
      val line = via(done.name)
      val definitions = done.report.entries.collect {
        case entry if entry.status == Status.Defined =>
          entry.theorem.flatMap(t => Term.destEq(t.conclusion)).map { case (_, body) =>
            Imported.Definition(done.name, entry.name, body, line)
          }
      }.flatten
      val facts = done.report.entries.collect {
        case entry if entry.status == Status.Defined || entry.status == Status.Proved =>
          entry.theorem.map(t => entry.name -> Imported.Fact(done.name, Kernel.cite(entry.name, t)))
      }.flatten
      val failures = done.report.entries.collect {
        case entry if entry.status == Status.Incomplete || entry.status == Status.Refused =>
          entry.name -> Imported.Failure(done.name, entry.line)
      }
      // Two imported documents declaring one name: the first is kept, and the second is a problem
      // of this document's imports, since a citation of the name could mean either.
      val ours = (facts.map(_._1) ++ failures.map(_._1)).distinct
      val before = (name: String) => acc.facts.get(name).map(_.document).orElse(acc.failures.get(name).map(_.document))
      val clash = ours.flatMap(name => before(name).map(other =>
        Problem(line, s"$name is declared in both $other and ${done.name}, which this document imports",
          Some("one of them has to rename it"), None)))
      val fresh = (name: String) => before(name).isEmpty
      (Imported(acc.definitions ++ definitions.filter(d => fresh(d.name)),
        acc.facts ++ facts.filter(f => fresh(f._1)), acc.failures ++ failures.filter(f => fresh(f._1))),
        clashing ++ clash)
    }
    (imported, problems ++ clashes)
  }

  /** Every document `name` imports, directly or through another import, among those read. */
  private def closure(name: String, read: Map[String, Option[Document.Parsed]]): Set[String] = {
    @annotation.tailrec
    def go(pending: List[String], found: Set[String]): Set[String] =
      pending match {
        case Nil => found
        case next :: rest =>
          val more = read.get(next).flatten.toList.flatMap(_.imports.map(_.name)).filterNot(found.contains)
          go(rest ++ more, found ++ more)
      }
    go(List(name), Set.empty)
  }
}

object Workspace {

  /** One document checked: its name, what was read, and the report. */
  final case class Done(name: String, parsed: Document.Parsed, report: Elaborate.Report)

  /** Every document checked, in the order they were checked. */
  final case class Checked(done: Vector[Done]) {
    def add(one: Done): Checked = copy(done = done :+ one)
    def find(name: String): Option[Done] = done.find(_.name == name)

    /** Every document checks and every import resolved. */
    def ok: Boolean = done.forall(_.report.ok)
  }

  /** The documents of a directory, each read from `NAME.sym` there. */
  def directory(elaborate: Elaborate, path: java.nio.file.Path): Workspace =
    new Workspace(elaborate, name => {
      val file = path.resolve(s"$name.sym")
      if (Document.DocumentName.matches(name) && java.nio.file.Files.isRegularFile(file))
        Some(java.nio.file.Files.readString(file))
      else None
    })
}
