package garden.xeno.symbolum.published

import garden.xeno.symbolum.tactics.Elaborate

/**
 * Check proof documents from the command line:
 * `tools/sbt "published/runMain garden.xeno.symbolum.published.Check [--json] FILE..."`.
 *
 * Everything it does is `garden.xeno.symbolum.tactics.Check.run`, which says what it prints and
 * which status it exits with. What this adds is the published documents, so a document anywhere may
 * `import Parity` and cite what the repository publishes; that is why the command lives in this
 * module, the lowest one that can read them.
 */
object Check {

  /** What the command prints and the status it exits with, without the process: what `main` does. */
  def run(arguments: Vector[String]): garden.xeno.symbolum.tactics.Check.Outcome =
    garden.xeno.symbolum.tactics.Check.run(arguments, Elaborate.standard, Published.source)

  def main(arguments: Array[String]): Unit = {
    val outcome = run(arguments.toVector)
    outcome.out.foreach(println)
    outcome.err.foreach(System.err.println)
    sys.exit(outcome.status)
  }
}
