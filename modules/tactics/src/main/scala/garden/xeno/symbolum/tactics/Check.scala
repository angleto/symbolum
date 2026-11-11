package garden.xeno.symbolum.tactics

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

/**
 * Check proof documents from the command line: `tactics/runMain garden.xeno.symbolum.tactics.Check FILE...`.
 *
 * Each file is checked on its own against the standard chain, which is built once, and its report is
 * printed: every declaration with its status, every problem with its line, the refusal, what to try
 * and the goal at that point. `--json` prints the same report as one JSON object per file, which is
 * the form a program driving the checker reads instead of parsing the prose.
 *
 * The exit status is 0 when every declaration of every file is proved or defined and nothing failed
 * to read, and 1 otherwise, so a script can tell a document that checks from one that does not
 * without reading either form.
 */
object Check {

  /** What one invocation prints on each stream, and the status it exits with. */
  final case class Outcome(status: Int, out: Vector[String], err: Vector[String])

  def main(arguments: Array[String]): Unit = {
    val outcome = run(arguments.toVector, Elaborate.standard)
    outcome.out.foreach(println)
    outcome.err.foreach(System.err.println)
    sys.exit(outcome.status)
  }

  /**
   * The invocation without the process around it, so what it prints and the status it chooses are
   * asserted rather than read off a terminal. `elaborate` is by name: a usage error or a missing
   * file is answered without building the chain.
   */
  def run(arguments: Vector[String], elaborate: => Elaborate): Outcome = {
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
      val reports = paths.map { path =>
        path -> checker.check(new String(Files.readAllBytes(Paths.get(path)), StandardCharsets.UTF_8))
      }
      val printed = reports.flatMap { case (path, report) =>
        if (json) Vector(s"""{"file":"${path.replace("\\", "\\\\").replace("\"", "\\\"")}","report":${report.json}}""")
        else Vector(s"== $path", report.render)
      }
      Outcome(if (reports.forall(_._2.ok)) 0 else 1, printed, Vector.empty)
    }
  }
}
