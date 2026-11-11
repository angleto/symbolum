package garden.xeno.symbolum.tactics

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

/**
 * What the checker command does: `published/runMain garden.xeno.symbolum.published.Check FILE...`.
 *
 * The command's entry point is in the publication module and not here, because an `import` may name
 * a published document and only a module above that one can read them; this object is everything
 * else, so it is tested where the elaborator is. `run` takes the published documents as a function.
 *
 * Each file is checked against the standard chain, which is built once, and against the documents it
 * imports. An import naming a published document reads that one; any other is read from the file's
 * own directory: `import Doubling` is `Doubling.sym` beside it. A file beside it with a published
 * name is not read, and the command says so on the error stream rather than choosing silently. Its
 * report is printed: every declaration with its status, every problem with its line, the refusal,
 * what to try and the goal at that point. `--json` prints the same report as one JSON object per
 * file, which is the form a program driving the checker reads instead of parsing the prose.
 *
 * An imported document is checked, and is not printed: a problem in it is reported on the import
 * line of the file that was asked about, as an import problem, and the file to check next is the
 * one that line names.
 *
 * The exit status is 0 when every declaration of every file is proved or defined, nothing failed to
 * read and every import resolved to a document that checks, and 1 otherwise, so a script can tell a
 * document that checks from one that does not without reading either form.
 */
object Check {

  /** What one invocation prints on each stream, and the status it exits with. */
  final case class Outcome(status: Int, out: Vector[String], err: Vector[String])

  /**
   * The invocation without the process around it, so what it prints and the status it chooses are
   * asserted rather than read off a terminal. `elaborate` is by name: a usage error or a missing
   * file is answered without building the chain. `published` answers the text of a published
   * document by name, and nothing for any other name.
   */
  def run(arguments: Vector[String], elaborate: => Elaborate, published: String => Option[String] = _ => None): Outcome = {
    val (flags, paths) = arguments.partition(_.startsWith("--"))
    val unknown = flags.filterNot(_ == "--json")
    val missing = paths.filterNot(path => Files.isRegularFile(Paths.get(path)))
    if (unknown.nonEmpty || paths.isEmpty)
      Outcome(2, Vector.empty,
        "usage: Check [--json] FILE..." +: (if (unknown.nonEmpty) Vector(s"unknown flag: ${unknown.mkString(" ")}") else Vector.empty))
    else if (missing.nonEmpty) Outcome(2, Vector.empty, Vector(s"no such file: ${missing.mkString(", ")}"))
    else {
      val json = flags.contains("--json")
      val checker = elaborate
      val checked = paths.map { path =>
        val file = Paths.get(path).toAbsolutePath
        val name = file.getFileName.toString.stripSuffix(".sym")
        val beside = Workspace.directory(checker, file.getParent)
        val workspace = new Workspace(checker, asked =>
          if (asked == name) Some(new String(Files.readAllBytes(file), StandardCharsets.UTF_8))
          else published(asked).orElse(beside.source(asked)))
        val done = workspace.check(Vector(name))
        val hidden = done.done.map(_.name).filter(other => other != name && published(other).isDefined && beside.source(other).isDefined)
          .map(other => s"$path: $other.sym beside it is not read, because $other is a published document and the import reads that one")
        (path, done.find(name).map(_.report).getOrElse(Elaborate.Report(Vector.empty, Vector.empty)), hidden)
      }
      val printed = checked.flatMap { case (path, report, _) =>
        if (json) Vector(s"""{"file":"${path.replace("\\", "\\\\").replace("\"", "\\\"")}","report":${report.json}}""")
        else Vector(s"== $path", report.render)
      }
      Outcome(if (checked.forall(_._2.ok)) 0 else 1, printed, checked.flatMap(_._3))
    }
  }
}
