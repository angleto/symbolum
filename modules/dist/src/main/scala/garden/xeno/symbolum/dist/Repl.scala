package garden.xeno.symbolum.dist

/**
 * A Scala REPL with the whole system already on the classpath, from the distribution.
 *
 * `sbt core/console` is the same thing from inside a checkout of this repository, and it is the
 * only thing that was. A person who installed the tarball had the jars and no way to sit in front
 * of them, which is most of what working on a theory interactively means: [[garden.xeno.symbolum.tactics.Notebook]]
 * is a column of cells over one session and answers a different question.
 *
 * {{{
 *   bin/symbolum-repl
 *   scala> import garden.xeno.symbolum.theories.Chain
 *   scala> val chain = Chain.standard
 * }}}
 *
 * == Why the classpath is passed again ==
 *
 * The compiler's own classpath and the interpreted code's classpath are two different things. The
 * launcher puts every jar of the distribution on the JVM's, which is what lets this object find
 * `dotty.tools.repl.Main` at all, and the REPL compiles what it is typed against whatever
 * `-classpath` it was given rather than against what its host process happens to hold. Without the
 * argument below the session starts, imports nothing, and reports `garden` as not found, which is
 * the failure that looks like a broken build and is not one.
 *
 * Arguments are appended rather than prepended so that a caller can override: the REPL reads the
 * last `-classpath` it is given, so `bin/symbolum-repl -classpath ...` is the caller's and not
 * this one's.
 *
 * == The other way to get this ==
 *
 * `scala-cli repl --dep garden.xeno::symbolum-tactics:<version>` is the same session without a
 * distribution, once the modules are on a registry, and it is what the README offers first: it
 * costs nothing to build and nothing to carry. What it needs is a network and scala-cli. This one
 * needs neither, and costs the tarball the compiler's jars. Neither is the better answer in
 * general, which is why both are documented.
 */
object Repl {

  /**
   * How a caller runs this, from an unpacked distribution.
   *
   * The one declaration of the name. `README.md` and `.github/workflows/publish.yml` each wrote it
   * out as well until 2026-09-16, three hand-written copies with nothing comparing them, and
   * `LauncherSpec` compares them now: the two documents are citations of this value and go red
   * when it moves.
   */
  val Command: String = "bin/symbolum-repl"

  /**
   * What the REPL is started with, separated from starting it.
   *
   * A session reads stdin and does not return, so a spec that called [[main]] would hang, and that
   * is the whole reason the launcher had no test while the other four could have one. What can be
   * checked is everything except the delegation: that the process's own classpath is passed, that
   * it is passed under `-classpath`, and that a caller's arguments come after so that a caller's
   * own `-classpath` is the one the REPL reads. This function is that part, and [[main]] is the
   * one line left that a test cannot enter.
   */
  def arguments(caller: Array[String]): Array[String] =
    Array("-classpath", System.getProperty("java.class.path")) ++ caller

  def main(arguments: Array[String]): Unit =
    dotty.tools.repl.Main.main(Repl.arguments(arguments))
}
