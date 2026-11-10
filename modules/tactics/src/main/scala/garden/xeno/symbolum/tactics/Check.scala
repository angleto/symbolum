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

  def main(arguments: Array[String]): Unit = {
    val (flags, paths) = arguments.toVector.partition(_.startsWith("--"))
    val unknown = flags.filterNot(_ == "--json")
    if (unknown.nonEmpty || paths.isEmpty) {
      System.err.println("usage: Check [--json] FILE...")
      if (unknown.nonEmpty) System.err.println(s"unknown flag: ${unknown.mkString(" ")}")
      sys.exit(2)
    }
    val json = flags.contains("--json")
    val missing = paths.filterNot(path => Files.isRegularFile(Paths.get(path)))
    if (missing.nonEmpty) {
      System.err.println(s"no such file: ${missing.mkString(", ")}")
      sys.exit(2)
    }
    val elaborate = Elaborate.standard
    val reports = paths.map { path =>
      val text = new String(Files.readAllBytes(Paths.get(path)), StandardCharsets.UTF_8)
      path -> elaborate.check(text)
    }
    reports.foreach { case (path, report) =>
      if (json) println(s"""{"file":"${path.replace("\\", "\\\\").replace("\"", "\\\"")}","report":${report.json}}""")
      else {
        println(s"== $path")
        println(report.render)
      }
    }
    sys.exit(if (reports.forall(_._2.ok)) 0 else 1)
  }
}
