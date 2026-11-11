package garden.xeno.symbolum.published

import garden.xeno.symbolum.tactics.Session

/**
 * The notebook from the command line:
 * `tools/sbt "published/runMain garden.xeno.symbolum.published.Notebook [port]"`.
 *
 * Everything it does is `garden.xeno.symbolum.tactics.Notebook.run`, which says what it serves and
 * where it listens. What this adds is the published documents, so a session may `import Parity`
 * and cite what the repository publishes, which is why the command lives in this module, as the
 * checker's does.
 */
object Notebook {

  /**
   * The session the command serves, which reads the published documents. Out of [[main]] because
   * `main` blocks until the process is stopped, and this is the half that differs from a session
   * built in `tactics`: `PublishedSpec` imports `Parity` into it.
   */
  def session: Session = Session.standard(Published.source)

  def main(arguments: Array[String]): Unit =
    garden.xeno.symbolum.tactics.Notebook.run(arguments, session)
}
