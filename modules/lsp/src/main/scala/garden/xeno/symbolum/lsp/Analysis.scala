package garden.xeno.symbolum.lsp

import garden.xeno.symbolum.tactics.{Document, Elaborate, Workspace}

/**
 * What the language server says about a document, with the protocol left out, so that every answer
 * it gives is a function of the text and is asserted as one.
 *
 * The report is the checker's. The document is checked by `Workspace` through the elaborator `Check`
 * uses, its imports resolved as `Check` resolves them, so a problem an editor underlines is a
 * problem the checker prints, on the same line and in the same words: one elaborator and three
 * front ends, which is `docs/adr/0070`. Lines are counted from 1 here, as the report counts them;
 * the protocol counts from 0, and converting is [[Server]]'s business.
 */
object Analysis {

  enum Severity { case Error, Warning }

  /** One thing on one line: the refusal first, then what to try and the goal at that point. */
  final case class Diagnostic(line: Int, message: String, severity: Severity)

  /** A declaration as an outline shows it, over the lines it spans. */
  final case class Outline(name: String, kind: Elaborate.Kind, status: Elaborate.Status, from: Int, to: Int)

  /** A document checked: its lines, which positions are counted in, the report, and the notices. */
  final case class Checked(lines: Vector[String], report: Elaborate.Report, notices: Vector[Diagnostic])

  /**
   * The document called `name`, whose text is `text`, checked with what it imports.
   *
   * An import reads the published document of that name first and `beside` second, which is the
   * checker's order: a published name is the published document wherever the importer sits. A file
   * beside the document carrying a published name is therefore not read, and a warning on the import
   * line says so, where the checker says it on its error stream.
   */
  def check(
    elaborate: Elaborate,
    name: String,
    text: String,
    published: String => Option[String],
    beside: String => Option[String]
  ): Checked = {
    val workspace = new Workspace(elaborate, asked => if (asked == name) Some(text) else published(asked).orElse(beside(asked)))
    val report = workspace.check(Vector(name)).find(name).map(_.report).getOrElse(Elaborate.Report(Vector.empty, Vector.empty))
    val shadowed = Document.read(text).imports.collect {
      case imported if imported.name != name && published(imported.name).isDefined && beside(imported.name).isDefined =>
        Diagnostic(imported.line,
          s"${imported.name}.sym beside this document is not read, because ${imported.name} is a published document and the import reads that one",
          Severity.Warning)
    }
    Checked(text.split("\n", -1).toVector.map(_.stripSuffix("\r")), report, shadowed)
  }

  /** Every problem of the report, on its line, and the notices. */
  def diagnostics(checked: Checked): Vector[Diagnostic] = {
    def message(problem: Elaborate.Problem): String = (problem.reason +: problem.detail).mkString("\n")
    val report = checked.report
    report.syntax.map(malformed => Diagnostic(malformed.line, malformed.reason, Severity.Error)) ++
      report.imports.map(problem => Diagnostic(problem.line, message(problem), Severity.Error)) ++
      report.entries.flatMap(_.problems.map(problem => Diagnostic(problem.line, message(problem), Severity.Error))) ++
      checked.notices
  }

  /**
   * Every declaration with the lines it spans, which `Document.extent` decides: a theorem runs to the
   * `qed` that closes its proof, as the reader reads it, and anything else is its one line.
   */
  def outline(checked: Checked): Vector[Outline] =
    checked.report.entries.map { entry =>
      Outline(entry.name, entry.kind, entry.status, entry.line, entry.line + Document.extent(checked.lines, entry.line - 1) - 1)
    }

  /**
   * What a reader is shown at `line`: the declaration it belongs to and what became of it, and the
   * goal at that line of the proof, which is `Elaborate.Entry.goalAt`. On the declaration's own
   * first line, the statement, and for a proved theorem what it rests on and cost. Nothing on a line
   * no declaration spans, an import or a blank line between two declarations.
   */
  def hover(checked: Checked, line: Int): Option[String] =
    outline(checked).find(span => span.from <= line && line <= span.to).flatMap { span =>
      checked.report.entries.find(_.line == span.from).map { entry =>
        val head = s"${entry.kind.word} ${entry.name}: ${entry.status.toString.toLowerCase}"
        val shown = entry.goalAt(line).filter(_ => line != entry.line).map(_.text).getOrElse(
          if (entry.kind == Elaborate.Kind.Datatype) entry.statement else s"|- ${entry.statement}")
        val price = if (line == entry.line) entry.price.toVector.flatMap(_.lines("this document")) else Vector.empty
        (Vector(head, "", "```", shown, "```") ++ (if (price.isEmpty) Vector.empty else "" +: price.map("- " + _))).mkString("\n")
      }
    }
}
