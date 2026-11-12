package garden.xeno.symbolum.lsp

import garden.xeno.symbolum.published.Published
import garden.xeno.symbolum.tactics.Elaborate
import org.eclipse.lsp4j.launch.LSPLauncher

/**
 * The language server from the command line, speaking the protocol on its standard streams:
 * `bin/symbolum-language-server` from the distribution, or from a checkout
 * `tools/sbt "lsp/runMain garden.xeno.symbolum.lsp.LanguageServer"`. An editor starts it; a person
 * does not talk to it. `docs/language.md` says how Neovim is told to.
 *
 * Standard output is the protocol and nothing else may write to it: one line printed by anything
 * below, a library building the chain or a `println` left in a procedure, would be read by the
 * editor as a malformed message and end the session. So the stream is taken for the protocol before
 * anything runs, and everything else that prints goes to standard error, which editors log.
 */
object LanguageServer {

  def main(arguments: Array[String]): Unit = {
    val protocol = System.out
    System.setOut(System.err)
    Console.withOut(System.err) {
      val server = new Server(() => Elaborate.standard, Published.source, status => sys.exit(status))
      val launcher = LSPLauncher.createServerLauncher(server, System.in, protocol)
      server.connect(launcher.getRemoteProxy)
      launcher.startListening().get()
      ()
    }
  }
}
