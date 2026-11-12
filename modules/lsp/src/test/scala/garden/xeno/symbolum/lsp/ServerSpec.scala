package garden.xeno.symbolum.lsp

import garden.xeno.symbolum.tactics.Elaborate
import java.io.{PipedInputStream, PipedOutputStream}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import java.util.concurrent.{CompletableFuture, LinkedBlockingQueue, TimeUnit}
import org.eclipse.lsp4j.{
  DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams, DocumentSymbolParams, HoverParams,
  InitializeParams, MessageActionItem, MessageParams, Position, PublishDiagnosticsParams, ShowMessageRequestParams,
  TextDocumentContentChangeEvent, TextDocumentIdentifier, TextDocumentItem, VersionedTextDocumentIdentifier
}
import org.eclipse.lsp4j.launch.LSPLauncher
import org.eclipse.lsp4j.services.LanguageClient
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import scala.jdk.CollectionConverters.*

/**
 * The protocol, spoken over a pair of pipes by lsp4j's own client, as an editor speaks it.
 *
 * `AnalysisSpec` asserts what is said; this asserts that it reaches the editor: the capabilities a
 * client reads before asking anything, diagnostics published on open and on change and cleared on
 * close, the hover and the outline at the protocol's positions, which count lines from 0, and the
 * exit status the protocol prescribes.
 */
class ServerSpec extends AnyFlatSpec with Matchers {

  private lazy val elaborate: Elaborate = Elaborate.standard

  /** A client that records what the server publishes, in order. */
  private final class Recording extends LanguageClient {
    val published = new LinkedBlockingQueue[PublishDiagnosticsParams]()
    override def publishDiagnostics(params: PublishDiagnosticsParams): Unit = published.add(params)
    override def telemetryEvent(event: Object): Unit = ()
    override def showMessage(params: MessageParams): Unit = ()
    override def showMessageRequest(params: ShowMessageRequestParams): CompletableFuture[MessageActionItem] =
      CompletableFuture.completedFuture(new MessageActionItem("ok"))
    override def logMessage(params: MessageParams): Unit = ()

    /** The next diagnostics published for `uri`, skipping any for other documents. */
    def next(uri: String): PublishDiagnosticsParams = {
      val found = published.poll(5, TimeUnit.MINUTES)
      if (found == None.orNull) fail(s"nothing published for $uri")
      else if (found.getUri == uri) found
      else next(uri)
    }
  }

  /** A server and a client joined by pipes, both listening; `exits` collects what the server ends with. */
  private final class Connected(published: Map[String, String] = Map.empty) {
    val exits = new LinkedBlockingQueue[Integer]()
    private val toClient = new PipedInputStream(1 << 20)
    private val fromServer = new PipedOutputStream(toClient)
    private val toServer = new PipedInputStream(1 << 20)
    private val fromClient = new PipedOutputStream(toServer)
    val server = new Server(() => elaborate, published.get, status => exits.add(status))
    private val serving = LSPLauncher.createServerLauncher(server, toServer, fromServer)
    server.connect(serving.getRemoteProxy)
    serving.startListening()
    val client = new Recording
    private val talking = LSPLauncher.createClientLauncher(client, toClient, fromClient)
    talking.startListening()
    val remote = talking.getRemoteProxy
  }

  private def directory(files: (String, String)*): Path = {
    val made = Files.createTempDirectory("symbolum-lsp-")
    files.foreach { case (name, text) => Files.write(made.resolve(name), text.getBytes(StandardCharsets.UTF_8)) }
    made
  }

  private val proved = "theorem ZERO_RIGHT : !n:num. n + 0 = n\nproof\n  fix n\n  show n + 0 = n by arith\nqed"
  private val wrong = proved.replace("n + 0 = n", "n + 1 = n")

  "The server" should "say what it offers when the editor starts it" in {
    val connected = new Connected
    val capabilities = connected.remote.initialize(new InitializeParams).get(1, TimeUnit.MINUTES).getCapabilities
    capabilities.getHoverProvider.getLeft shouldBe true
    capabilities.getDocumentSymbolProvider.getLeft shouldBe true
    capabilities.getTextDocumentSync.getLeft.toString shouldBe "Full"
  }

  it should "publish a document's problems when it opens and when it changes, and clear them when it closes" in {
    val connected = new Connected
    connected.remote.initialize(new InitializeParams).get(1, TimeUnit.MINUTES)
    val uri = directory().resolve("Mine.sym").toUri.toString
    val documents = connected.remote.getTextDocumentService

    documents.didOpen(new DidOpenTextDocumentParams(new TextDocumentItem(uri, "symbolum", 1, wrong)))
    val opened = connected.client.next(uri).getDiagnostics.asScala.toVector
    opened should have size 1
    // The protocol counts lines from 0: the report's line 4 is line 3 here.
    opened.head.getRange.getStart.getLine shouldBe 3
    opened.head.getMessage.getLeft should include("|- n + 1 = n")

    val change = new TextDocumentContentChangeEvent(proved)
    documents.didChange(new DidChangeTextDocumentParams(new VersionedTextDocumentIdentifier(uri, 2), java.util.List.of(change)))
    connected.client.next(uri).getDiagnostics shouldBe empty

    documents.didChange(new DidChangeTextDocumentParams(new VersionedTextDocumentIdentifier(uri, 3), java.util.List.of(new TextDocumentContentChangeEvent(wrong))))
    connected.client.next(uri).getDiagnostics should have size 1
    documents.didClose(new DidCloseTextDocumentParams(new TextDocumentIdentifier(uri)))
    connected.client.next(uri).getDiagnostics shouldBe empty
  }

  it should "answer a hover with the goal at that line, and the outline with the declarations" in {
    val connected = new Connected
    connected.remote.initialize(new InitializeParams).get(1, TimeUnit.MINUTES)
    val uri = directory().resolve("Mine.sym").toUri.toString
    val documents = connected.remote.getTextDocumentService
    documents.didOpen(new DidOpenTextDocumentParams(new TextDocumentItem(uri, "symbolum", 1, proved)))
    connected.client.next(uri)

    val hover = documents.hover(new HoverParams(new TextDocumentIdentifier(uri), new Position(3, 4))).get(1, TimeUnit.MINUTES)
    hover.getContents.getRight.getValue should include("|- n + 0 = n")
    val outside = documents.hover(new HoverParams(new TextDocumentIdentifier(uri), new Position(40, 0))).get(1, TimeUnit.MINUTES)
    Option(outside) shouldBe empty

    val symbols = documents.documentSymbol(new DocumentSymbolParams(new TextDocumentIdentifier(uri))).get(1, TimeUnit.MINUTES).asScala
    symbols.map(_.getRight.getName) shouldBe Seq("ZERO_RIGHT")
    symbols.head.getRight.getRange.getEnd.getLine shouldBe 4
  }

  it should "read an import from the editor's text of a document beside it, and check its importer again when it changes" in {
    val twice = "define TWICE := \\n:num. n + n\ntheorem TWICE_ZERO : TWICE 0 = 0\nproof\n  rewrite TWICE\n  by arith\nqed"
    val holding = directory("A.sym" -> twice)
    val importer = holding.resolve("B.sym").toUri.toString
    val imported = holding.resolve("A.sym").toUri.toString
    val connected = new Connected
    connected.remote.initialize(new InitializeParams).get(1, TimeUnit.MINUTES)
    val documents = connected.remote.getTextDocumentService

    documents.didOpen(new DidOpenTextDocumentParams(
      new TextDocumentItem(importer, "symbolum", 1, "import A\ntheorem AGAIN : TWICE 0 = 0 by exact TWICE_ZERO")))
    connected.client.next(importer).getDiagnostics shouldBe empty

    // A's text in the editor no longer proves TWICE_ZERO, and the file on disk still does: B is
    // checked again against the editor's text, and its citation fails.
    documents.didOpen(new DidOpenTextDocumentParams(new TextDocumentItem(imported, "symbolum", 1, "define TWICE := \\n:num. n + n")))
    connected.client.next(importer).getDiagnostics should not be empty
  }

  it should "exit with 0 after a shutdown, as the protocol says" in {
    val connected = new Connected
    connected.remote.initialize(new InitializeParams).get(1, TimeUnit.MINUTES)
    connected.remote.shutdown().get(1, TimeUnit.MINUTES)
    connected.remote.exit()
    connected.exits.poll(1, TimeUnit.MINUTES) shouldBe 0
  }

  it should "exit with 1 when the editor goes without a shutdown" in {
    val connected = new Connected
    connected.remote.initialize(new InitializeParams).get(1, TimeUnit.MINUTES)
    connected.remote.exit()
    connected.exits.poll(1, TimeUnit.MINUTES) shouldBe 1
  }
}
