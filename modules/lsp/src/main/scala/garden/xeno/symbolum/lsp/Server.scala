package garden.xeno.symbolum.lsp

import garden.xeno.symbolum.tactics.{Elaborate, Workspace}
import java.net.URI
import java.nio.file.{Path, Paths}
import java.util.concurrent.CompletableFuture
import java.util.concurrent.atomic.AtomicReference
import org.eclipse.lsp4j.{
  DidChangeConfigurationParams, DidChangeTextDocumentParams, DidChangeWatchedFilesParams, DidCloseTextDocumentParams,
  DidOpenTextDocumentParams, DidSaveTextDocumentParams, DiagnosticSeverity, DocumentSymbol, DocumentSymbolParams, Hover,
  HoverParams, InitializeParams, InitializeResult, MarkupContent, MarkupKind, Position, PublishDiagnosticsParams, Range,
  ServerCapabilities, ServerInfo, SymbolInformation, SymbolKind, TextDocumentSyncKind
}
import org.eclipse.lsp4j.jsonrpc.messages.Either as Choice
import org.eclipse.lsp4j.services.{LanguageClient, LanguageClientAware, TextDocumentService, WorkspaceService}
import scala.jdk.CollectionConverters.*
import scala.util.Try

/**
 * The language server: the protocol around [[Analysis]], and nothing it decides is decided here.
 *
 * It offers three things, each answered from the checker's report on the text the editor holds:
 * every problem as a diagnostic on its line, with what to try and the goal at that point; the goal
 * at the line under the cursor, as a hover, for a proof that checked as much as for one that did
 * not; and the declarations as an outline. The text is synchronised whole on every change, which
 * costs nothing next to checking it.
 *
 * An import is read from the published documents, then from a document open in the editor beside
 * this one, then from the file beside it on disk, so an unsaved change to an imported document is
 * seen by the document importing it. A change to any open document checks again every open document
 * in its directory, since any of them may import it.
 *
 * `elaborate` is built the first time a document is checked and not before, so `initialize` answers
 * at once and the chain is built while the editor is opening the file. `end` is what ends the
 * process, a parameter so that a test can run the protocol to its end without ending its own.
 */
final class Server(elaborate: () => Elaborate, published: String => Option[String], end: Int => Unit)
    extends org.eclipse.lsp4j.services.LanguageServer
    with LanguageClientAware
    with TextDocumentService
    with WorkspaceService {

  private lazy val checker: Elaborate = elaborate()

  /** What the server holds: the client, the text of each open document and its report. */
  private final case class State(
    client: Option[LanguageClient],
    texts: Map[String, String],
    checked: Map[String, Analysis.Checked],
    shutdown: Boolean
  )

  private val state = new AtomicReference(State(None, Map.empty, Map.empty, shutdown = false))

  /* ------------------------------------------------------------------- lifecycle */

  override def initialize(params: InitializeParams): CompletableFuture[InitializeResult] = {
    val capabilities = new ServerCapabilities()
    capabilities.setTextDocumentSync(TextDocumentSyncKind.Full)
    capabilities.setHoverProvider(java.lang.Boolean.TRUE)
    capabilities.setDocumentSymbolProvider(java.lang.Boolean.TRUE)
    CompletableFuture.completedFuture(new InitializeResult(capabilities, new ServerInfo("symbolum")))
  }

  override def shutdown(): CompletableFuture[Object] = {
    state.updateAndGet(_.copy(shutdown = true))
    CompletableFuture.completedFuture(Option.empty[Object].orNull)
  }

  /** The protocol's rule: 0 after a `shutdown` request, 1 when the client exits without one. */
  override def exit(): Unit = end(if (state.get.shutdown) 0 else 1)

  override def connect(client: LanguageClient): Unit = {
    state.updateAndGet(_.copy(client = Some(client)))
    ()
  }

  override def getTextDocumentService: TextDocumentService = this

  override def getWorkspaceService: WorkspaceService = this

  /* ------------------------------------------------------------------- documents */

  override def didOpen(params: DidOpenTextDocumentParams): Unit =
    changed(params.getTextDocument.getUri, Some(params.getTextDocument.getText))

  override def didChange(params: DidChangeTextDocumentParams): Unit =
    params.getContentChanges.asScala.lastOption.foreach(change => changed(params.getTextDocument.getUri, Some(change.getText)))

  /** The document is read from disk again by whatever imports it, and its diagnostics are cleared. */
  override def didClose(params: DidCloseTextDocumentParams): Unit = {
    val uri = params.getTextDocument.getUri
    changed(uri, None)
    state.get.client.foreach(_.publishDiagnostics(new PublishDiagnosticsParams(uri, java.util.List.of())))
  }

  /** Saving changes the file a closed importer reads, and an open one already read the buffer. */
  override def didSave(params: DidSaveTextDocumentParams): Unit = ()

  override def hover(params: HoverParams): CompletableFuture[Hover] = {
    val answer = state.get.checked.get(params.getTextDocument.getUri)
      .flatMap(Analysis.hover(_, params.getPosition.getLine + 1))
      .map(text => new Hover(new MarkupContent(MarkupKind.MARKDOWN, text)))
    CompletableFuture.completedFuture(answer.orNull)
  }

  override def documentSymbol(params: DocumentSymbolParams): CompletableFuture[java.util.List[Choice[SymbolInformation, DocumentSymbol]]] = {
    val symbols = state.get.checked.get(params.getTextDocument.getUri).toVector.flatMap { checked =>
      Analysis.outline(checked).map { span =>
        val range = new Range(new Position(span.from - 1, 0), new Position(span.to - 1, checked.lines.lift(span.to - 1).fold(0)(_.length)))
        val kind = span.kind match {
          case Elaborate.Kind.Definition => SymbolKind.Constant
          case Elaborate.Kind.Theorem => SymbolKind.Function
          case Elaborate.Kind.Datatype => SymbolKind.Enum
        }
        Choice.forRight[SymbolInformation, DocumentSymbol](new DocumentSymbol(span.name, kind, range, range, span.status.toString.toLowerCase))
      }
    }
    CompletableFuture.completedFuture(symbols.asJava)
  }

  override def didChangeConfiguration(params: DidChangeConfigurationParams): Unit = ()

  override def didChangeWatchedFiles(params: DidChangeWatchedFilesParams): Unit = ()

  /* ------------------------------------------------------------------- checking */

  /**
   * `uri` now holds `text`, or is closed, and every open document in its directory is checked again.
   *
   * The checking happens outside the update of the state, because `updateAndGet` may run its
   * function more than once and a check is neither cheap nor something to repeat; what goes in
   * the update is the replacing of one map entry by another.
   */
  private def changed(uri: String, text: Option[String]): Unit = {
    val now = state.updateAndGet(held =>
      text.fold(held.copy(texts = held.texts - uri, checked = held.checked - uri))(t => held.copy(texts = held.texts + (uri -> t))))
    val directory = path(uri).map(_.getParent)
    val affected = now.texts.toVector.filter { case (other, _) => other == uri || (directory.isDefined && path(other).map(_.getParent) == directory) }
    affected.foreach { case (other, otherText) =>
      val checked = Analysis.check(checker, name(other), otherText, published, beside(other))
      state.updateAndGet(held => if (held.texts.get(other).contains(otherText)) held.copy(checked = held.checked + (other -> checked)) else held)
      publish(other, checked)
    }
  }

  private def publish(uri: String, checked: Analysis.Checked): Unit = {
    val diagnostics = Analysis.diagnostics(checked).map { found =>
      val index = (found.line - 1).max(0)
      val text = checked.lines.lift(index).getOrElse("")
      val start = text.indexWhere(!_.isWhitespace).max(0)
      val range = new Range(new Position(index, start), new Position(index, text.length.max(start)))
      val severity = found.severity match {
        case Analysis.Severity.Error => DiagnosticSeverity.Error
        case Analysis.Severity.Warning => DiagnosticSeverity.Warning
      }
      new org.eclipse.lsp4j.Diagnostic(range, found.message, severity, "symbolum")
    }
    state.get.client.foreach(_.publishDiagnostics(new PublishDiagnosticsParams(uri, diagnostics.asJava)))
  }

  /** An import of a document beside `uri`: the editor's text when it is open, the file when not. */
  private def beside(uri: String): String => Option[String] = {
    val directory = path(uri).map(_.getParent)
    asked =>
      directory.flatMap { holding =>
        val file = holding.resolve(s"$asked.sym")
        state.get.texts.collectFirst { case (other, text) if path(other).contains(file) => text }
          .orElse(Workspace.directory(checker, holding).source(asked))
      }
  }

  /** The file a URI names, or nothing for a document that is not a file, which imports nothing beside it. */
  private def path(uri: String): Option[Path] = Try(Paths.get(new URI(uri)).toAbsolutePath.normalize).toOption

  /** The name the document is checked under, its file's name without `.sym`. */
  private def name(uri: String): String =
    path(uri).map(_.getFileName.toString.stripSuffix(".sym")).getOrElse("Document")
}
