package garden.xeno.symbolum.tactics

import com.sun.net.httpserver.{HttpExchange, HttpServer}
import java.net.InetSocketAddress
import java.nio.charset.StandardCharsets
import java.util.concurrent.atomic.AtomicReference
import scala.jdk.CollectionConverters.*

/**
 * The interface: one long-lived process holding one [[Session]], and a page that drives it.
 *
 * `sbt "tactics/runMain garden.xeno.symbolum.tactics.Notebook"`, then open what it prints. The page is a
 * column of cells; typing a line and pressing enter runs it, and the answer appears under it with
 * the statement set in print where the signature can set it.
 *
 * == Why this and not Jupyter, which was the other design and is not wrong ==
 *
 * The plan offered two, and the argument for this one is not that Almond would have been hard. It
 * is that a Scala cell can reach `Kernel.assertAxiom` and `Term.variable`, both public and neither
 * recorded anywhere, so a page's content stops being a function of the page: a reader cannot tell,
 * from a notebook, what a result was believed on. The command language here is small on purpose,
 * and what it buys is that the transcript **is** the development. A Jupyter kernel remains the
 * right answer for the algebra half in `modules/core`, where nothing is being certified and there
 * is no soundness to lose, and `CONTRIBUTING.md` has listed it there for as long as it has existed.
 *
 * == Where the safety actually lives ==
 *
 * Not here. [[Session]] holds one theory and the class comment there is the argument; this file is a
 * transport that does no reasoning of its own, so what is asserted about the *reasoning* is in
 * `SessionSpec`, which covers the model this renders.
 *
 * What is asserted about this file is what a test can hold, and since 2026-09-16 that is two things
 * rather than one. [[Notebook.render]] and [[Notebook.cells]] are pure functions from a session to a
 * page, so a test calls them. The three endpoints are private and reachable only through a running
 * server, so `NotebookSpec` starts one on port 0 and asks it over a socket. This paragraph read
 * "there is no `NotebookSpec` pinning HTML" until that day, which was true when it was written and
 * stopped being true with `f9ae333`, and what it was guarding against survives the correction: that
 * spec does not pin the markup either. What it pins is the behaviours here that exist because of a
 * failure this file records, none of which is a property of the HTML: the 404 on an unknown path, the
 * thread pool, and since 2026-09-16 the ordering, which is what [[Notebook.advance]] is for.
 *
 * The half of the ordering that lives in the page cannot be pinned there and is not claimed to be.
 * `notebook.js` is what stops this page racing itself, and nothing in this repository runs
 * JavaScript. What a test reaches is the server's own promise, that a command is applied to the
 * transcript its writer read or to none, and that is what leaves the page's queue checkable by its
 * consequence rather than unchecked: a page that stopped queueing would start collecting
 * [[Notebook.Conflict]] where it used to reorder silently, which is a visible failure in place of
 * an invisible one.
 *
 * == What it binds to, and what it is not ==
 *
 * The loopback address and nothing else, with no authentication, no session cookie and no origin
 * check, because it is a single-user tool on the machine that runs it. It is **not** a service and
 * must not be put on an interface that leaves the machine: anything that can reach the port can
 * assert an axiom into the session and read everything in it. Binding is explicit here rather than
 * left to a default for exactly that reason, and the port is a flag so that two sessions can run
 * without either being reachable from outside.
 *
 * The server is the one in the JDK, `jdk.httpserver`, so this adds no dependency. That is worth a
 * line because it was the decision: the repository has exactly one runtime dependency in six
 * modules, Breeze in `modules/core`, and a web framework for a localhost page would have been the
 * second and the first one above the trust boundary.
 */
object Notebook {

  /** How a caller runs this. */
  val Command: String = "sbt \"tactics/runMain garden.xeno.symbolum.tactics.Notebook [port]\""

  /** Where it listens. Loopback, always: see the class comment. */
  val Host: String = "127.0.0.1"

  /** The port when the caller names none. */
  val DefaultPort: Int = 8642

  /**
   * The header a writer names the transcript it read in, which is how this surface is ordered.
   *
   * It carries the number of cells the writer had in front of it. [[Notebook.advance]] is where it
   * is spent and carries the argument; what belongs on the name is that it is the writer's
   * reading and not the writer's identity, so two pages that are genuinely in step are both
   * served, and one that has fallen behind is refused whichever of them got there first.
   */
  val After: String = "Symbolum-After"

  /**
   * What a writer is told when the transcript it read is no longer the one it would write to.
   *
   * The body of such an answer is the cells as they stand rather than a message about a failure: a
   * writer that has fallen behind needs the state, and that is exactly what it has to read before
   * it can write again.
   */
  val Conflict: Int = 409

  /** Written once, because every answer this serves but the 404 is the page or part of it. */
  private val Html: String = "text/html; charset=utf-8"

  def main(arguments: Array[String]): Unit = {
    val port = arguments.headOption.flatMap(_.toIntOption).getOrElse(DefaultPort)

    println("building the chain, which is the slow part and happens once")
    val started = System.nanoTime()
    val session = new AtomicReference[Session](Session.standard)
    println(f"ready in ${(System.nanoTime() - started) / 1000000000.0}%.1f s")

    val server = serve(port, session)

    println(s"open http://$Host:${server.getAddress.getPort}")
    println("this is a single-user tool on loopback with no authentication; do not expose the port")
    println("ctrl-c to stop")

    // `HttpServer.start` returns as soon as it is listening, so a `main` that stopped here would
    // end, and `sbt runMain` would report success and take the server down with it. That is what
    // the first version of this file did, and the symptom was a page that was never reachable and
    // a build that said it had succeeded. Blocking is the whole fix, and the hook is what makes
    // ctrl-c a clean stop rather than a killed process.
    val stopped = new java.util.concurrent.CountDownLatch(1)
    Runtime.getRuntime.addShutdownHook(new Thread(() => {
      server.stop(0)
      stopped.countDown()
    }))
    stopped.await()
  }

  /**
   * The server, listening, for a caller that decides when to stop it.
   *
   * Out of [[main]] so that it can be driven, and that is not a testing convenience. The three
   * endpoints below are private and reachable only through a running server, so until this existed
   * the one surface in this project that speaks to a browser was the one nothing exercised, and two
   * of its behaviours are there because of failures this file records: the 404 on an unknown path,
   * and the thread pool. Neither is worth asserting against a fake exchange, because both are about
   * what a client on the other end of a socket receives.
   *
   * **Port 0 asks the operating system for a free one**, which is what a test wants and what a
   * person never types. The answer is `getAddress.getPort` and not the argument, which is the one
   * thing a caller passing 0 must not forget.
   *
   * **It receives the session rather than owning it, and that is a decision.** The alternative is
   * for this to build `Session.standard` itself, which would stop a caller handing it a session
   * some other caller had already advanced. It does not, for two reasons that are about where the
   * safety property lives. The append-only single-theory transcript is `Session`'s: `run` appends,
   * `truncate` discards after a point, and a second `declare` of one name is refused by the kernel,
   * none of which depends on who built the session. And an already-advanced session is not a shape
   * the running server cannot reach -- it is what every request after the first one meets, since
   * the reference this is handed is the same one the handlers update. What owning the session would
   * buy is that `main` could not be given the wrong chain, and `main` does not take one.
   *
   * A pool rather than `null`, which is the default and runs every exchange on the accepting
   * thread. A browser keeps a connection open and asks for more than the page (a favicon at
   * least), so one thread serialises those behind each other and the tab sits there loading. It
   * did, on the first version of this file, and the symptom was a page that answered `curl`
   * perfectly and would not finish rendering in Chrome. Four is a single user's page, not a
   * capacity estimate.
   */
  def serve(port: Int, session: AtomicReference[Session]): HttpServer = {
    val server = HttpServer.create(new InetSocketAddress(Host, port), 0)
    server.createContext("/", exchange => root(exchange, session))
    server.createContext("/run", exchange => run(exchange, session))
    server.createContext("/truncate", exchange => truncate(exchange, session))
    server.setExecutor(java.util.concurrent.Executors.newFixedThreadPool(4))
    server.start()
    server
  }

  /* ------------------------------------------------------------------ the endpoints */

  /**
   * The page, and a refusal for everything else.
   *
   * The root context is a **prefix** match in this server, so without this every unknown path is
   * answered with the whole page: a request for `/favicon.ico` came back as `text/html` and the
   * browser was told the page was its icon. Answering 404 is not tidiness, it is the difference
   * between a client that knows there is nothing there and one that is handed something wrong.
   */
  private def root(exchange: HttpExchange, session: AtomicReference[Session]): Unit =
    if (exchange.getRequestURI.getPath == "/")
      respond(exchange, Html, render(session.get))
    else respond(exchange, "text/plain; charset=utf-8", s"no ${exchange.getRequestURI.getPath} here", 404)

  /**
   * Run what was written, in the order it was written, and answer with the cells.
   *
   * **The body is one command per line and not one command**, which is what makes replaying a
   * development a single request. Five lines pasted into the box arrive together, are folded over
   * one state in order, and become five cells whose numbering is the order they were written in;
   * nothing about that order is left to the network. Before 2026-09-16 a five-line body was one
   * unreadable command, so the only way to replay a development was five requests, which is the
   * shape the defect lived in.
   *
   * Blank lines are dropped rather than recorded as unreadable: they are what a paste is made of
   * between one command and the next, and a transcript is a lie if it holds cells its writer did
   * not write. A line that is not blank and does not read is still kept, which is [[Session]]'s
   * rule and is the opposite case.
   */
  private def run(exchange: HttpExchange, session: AtomicReference[Session]): Unit = {
    val lines = body(exchange).linesIterator.map(_.trim).filter(_.nonEmpty).toVector
    advance(exchange, session, current => current.runAll(lines))
  }

  /**
   * Go back to after `n` commands, which is the only way backwards.
   *
   * A separate endpoint rather than a flag on `/run`, because discarding thirty-seven results is
   * not a variant of running one: the page asks before it calls this, and what it says it will
   * discard is what this discards.
   */
  private def truncate(exchange: HttpExchange, session: AtomicReference[Session]): Unit = {
    val count = body(exchange).trim.toIntOption.getOrElse(0)
    advance(exchange, session, current => current.truncate(count))
  }

  /**
   * Advance the session, but never from a transcript other than the one the writer read.
   *
   * == What went wrong without it ==
   *
   * The handler was `session.updateAndGet(current => current.run(line))` and the page fired a
   * `fetch` per submission with nothing waiting for the one before it. Five commands written
   * faster than the round trip arrived as five concurrent POSTs, and the server numbered them in
   * arrival order: measured on 2026-09-16, `declare` landed as cell 2 and the `derive` that cites
   * it as cell 1, which then failed naming a fact that did not exist yet. Three seconds between
   * submissions and the order was the written one, which is what says it was a race rather than a
   * sorting.
   *
   * == The two halves, and why neither is the other's fix ==
   *
   * The page writes one at a time, which is `notebook.js`'s queue, and that is what keeps the
   * count a writer sends current. This is the other half: a writer names the transcript it read in
   * the `Symbolum-After` header, and a command is applied to that transcript or to none. So a
   * second tab, a reload with a request in flight, or anything driving the port that is not this
   * page cannot interleave itself into a development; what it gets is [[Conflict]] and the cells
   * as they actually stand, which is the state it has to re-read before writing again. A caller
   * that sends no header is not refused, because `curl` is how this surface is exercised by hand
   * and it has nothing to be stale about.
   *
   * == Under one lock rather than a compare-and-set ==
   *
   * Two reasons, and the second is the one that costs something. `AtomicReference.updateAndGet`
   * **re-applies** its function when it loses the race, so a contended `prove` runs the whole
   * proof search twice and the second run is against a state its caller never saw: re-applying is
   * precisely the blind write this exists to refuse. And a compare-and-set here would carry a
   * failure branch that only a genuine race reaches, which is a branch no test can be made to
   * enter on purpose.
   *
   * What the lock costs is that a long `prove` makes a concurrent submission wait rather than run
   * beside it. That is the semantics rather than a compromise: there is one theory in a session,
   * so two commands were never independent. Nothing else takes it -- the page itself and the 404
   * only read -- so the browser's other requests are not behind it.
   */
  private def advance(exchange: HttpExchange, session: AtomicReference[Session], step: Session => Session): Unit = {
    val expected = Option(exchange.getRequestHeaders.getFirst(After)).flatMap(_.toIntOption)
    val advanced = session.synchronized {
      val read = session.get
      if (expected.exists(_ != read.entries.size)) None
      else {
        val updated = step(read)
        session.set(updated)
        Some(updated)
      }
    }
    advanced match {
      case Some(updated) => respond(exchange, Html, cells(updated))
      case None => respond(exchange, Html, cells(session.get), Conflict)
    }
  }

  private def body(exchange: HttpExchange): String =
    new String(exchange.getRequestBody.readAllBytes(), StandardCharsets.UTF_8)

  private def respond(exchange: HttpExchange, contentType: String, text: String, status: Int = 200): Unit = {
    val bytes = text.getBytes(StandardCharsets.UTF_8)
    exchange.getResponseHeaders.add("Content-Type", contentType)
    exchange.sendResponseHeaders(status, bytes.length.toLong)
    val stream = exchange.getResponseBody
    try stream.write(bytes)
    finally stream.close()
  }

  /* ------------------------------------------------------------------ the page */

  /**
   * The whole page for a session, which is a pure function of it.
   *
   * Pure so that it can be asserted about and so that the page after a reload is the page before
   * it: the server holds a session and nothing else, and every state the browser can be in is one
   * this function produces from some session.
   */
  def render(session: Session): String =
    s"""<!doctype html>
       |<html lang="en"><head><meta charset="utf-8">
       |<title>symbolum</title>
       |<style>$Style</style>
       |<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css">
       |<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js"></script>
       |</head><body>
       |<h1>symbolum</h1>
       |<p class="note">One theory, one transcript. Re-running a cell discards everything after it.
       |The printed form does not read back: the line under it is the one that does.
       |Paste a whole development and it runs line by line, in the order you pasted it.</p>
       |<div id="cells">${cells(session)}</div>
       |<form id="entry" autocomplete="off">
       |  <input id="line" name="line" placeholder="${Session.Command.Keywords.mkString(" | ")}" autofocus>
       |</form>
       |<p id="trouble" class="trouble"></p>
       |<p class="note">$Help</p>
       |<script>$Script</script>
       |</body></html>""".stripMargin

  /** The cells alone, which is what an endpoint returns so the page replaces one element. */
  def cells(session: Session): String =
    if (session.entries.isEmpty) """<p class="note">Nothing run yet.</p>"""
    else session.entries.map(cell(session, _)).mkString("\n")

  private def cell(session: Session, entry: Session.Entry): String = {
    val head =
      s"""<div class="head"><span class="number">${entry.number}</span>""" +
        s"""<code>${escape(Session.Command.write(entry.command))}</code>""" +
        s"""<button class="back" data-count="${entry.number - 1}" """ +
        s"""title="discard this command and everything after it">back to here</button></div>"""

    val body = entry.outcome match {
      case Session.Outcome.Extended(what) => s"""<div class="extended">${escape(what)}</div>"""
      case Session.Outcome.Proved(name, theorem) => proved(session, entry, name, theorem)
      case Session.Outcome.Report(text) => s"""<pre class="report">${escape(text)}</pre>"""
      case Session.Outcome.Refused(reason, next) =>
        s"""<div class="refused">${escape(reason)}""" +
          next.map(step => s"""<div class="next">try: ${escape(step)}</div>""").getOrElse("") +
          "</div>"
    }

    s"""<div class="cell">$head$body</div>"""
  }

  /**
   * A theorem, in both forms, with what it rests on that the foundation does not hold.
   *
   * The two forms are `Signature.readable`, which returns them together or neither, and the page
   * shows the legible one under the printed one rather than instead of it. That is the same
   * discipline `Essay` follows and for the same reason: a rendering that cannot be read back is
   * published only beside the text that can, so nothing on the page is a formula a reader cannot
   * check against the system.
   *
   * The line naming what it rests on appears **only** when there is something to name, and what it
   * names is `Derivation.foreignTo` against the base chain: the session's own assumptions, spent.
   */
  private def proved(session: Session, entry: Session.Entry, name: String, theorem: garden.xeno.symbolum.kernel.Kernel.Thm): String = {
    val readable = entry.state.readable(theorem.conclusion)
    // The source travels in an attribute rather than between delimiters in the text. Delimiters
    // mean agreeing on how many backslashes survive a Scala interpolator, an HTML document and a
    // JavaScript string literal, and the first version of this file got that wrong in the third
    // of the three: nothing was typeset and nothing said so. An attribute is read back by
    // `dataset` with no escaping to agree on, and the element still shows the source where KaTeX
    // never loaded.
    val printed = readable
      .map(pair => s"""<div class="printed" data-tex="${escape(pair.printed)}">${escape(pair.printed)}</div>""")
      .getOrElse("")
    val legible = readable.map(_.legible).getOrElse(entry.state.show(theorem.conclusion))

    val rests = entry.restsOn(session.base)
    val assumptions =
      if (rests.isEmpty) ""
      else
        s"""<div class="rests">rests on what this session assumed: """ +
          rests.toVector.map(term => escape(entry.state.show(term))).sorted.mkString(", ") +
          "</div>"

    s"""<div class="proved"><span class="name">${escape(name)}</span>$printed""" +
      s"""<div class="legible">|- ${escape(legible)}</div>$assumptions</div>"""
  }

  private def escape(text: String): String =
    text
      .replace("&", "&amp;")
      .replace("<", "&lt;")
      .replace(">", "&gt;")
      .replace("\"", "&quot;")

  /**
   * One example per command, and the placeholder above it is generated from the same list.
   *
   * Written out rather than generated because an example is not a keyword: `derive` takes an
   * inference and two fact names, and a list built from `Keywords` would print the word alone,
   * which is the part a reader already has. What it costs is that this line and the keywords can
   * disagree, which they did the hour `derive` landed -- the placeholder listed eight commands
   * and this line seven -- and it was visible in a browser and in nothing else. `NotebookSpec`
   * asserts every keyword appears here, so the next one cannot arrive without its example.
   */
  private val Help: String =
    "declare p : bool &middot; define twice := \\x:real. x + x &middot; assume NAME : claim &middot; " +
      "prove NAME : claim &middot; derive NAME : mp FACT FACT &middot; ask claim &middot; " +
      "find name-or-shape &middot; show NAME"

  /**
   * The page's stylesheet and its behaviour, read from resources beside this class.
   *
   * They are files of their own language rather than string literals here, and the reason is a
   * guard rather than taste: `StyleSpec` scans every Scala source for `return`, `var`, `while`,
   * `null` and casts, and its own docstring records that it does not strip string literals. A
   * JavaScript program living in a Scala string put four `return`s into this file, none of which
   * was Scala, and the honest repair is not an entry in an exception list: it is that a Scala
   * source should not contain a program in another language for a scan to misread.
   *
   * What it buys beyond the guard is that the page's behaviour is editable as JavaScript, by an
   * editor that knows it is JavaScript, and a reader looking for what the page does finds
   * `notebook.js` rather than a string at the bottom of a server.
   */
  private def resource(name: String): String = {
    val stream = Option(getClass.getResourceAsStream(name))
      .getOrElse(throw new IllegalStateException(s"the page's $name is not on the classpath"))
    try new String(stream.readAllBytes(), StandardCharsets.UTF_8)
    finally stream.close()
  }

  private lazy val Style: String = resource("notebook.css")

  /**
   * The page's own behaviour, which is three things and deliberately no more.
   *
   * Submit a line, replace the cells with what comes back, and ask before going back. The formulas
   * are typeset by KaTeX where it loaded and are left as their source where it did not, which is
   * the only sensible failure for a page served on loopback to a machine that may be offline: the
   * line that reads back is under every formula anyway, so nothing is lost but the typesetting.
   *
   * This described the JavaScript when the JavaScript was a string literal in this file, and was
   * left behind attached to nothing when it became `notebook.js`. A doc comment at the end of an
   * object documents the next member, and there is no next member: it compiled, it rendered
   * nowhere, and nothing checks that a comment has a subject.
   *
   * Since 2026-09-16 it is four things rather than three, and the fourth is what the file above is
   * mostly about: submissions are queued, so one is in flight at a time. What is worth saying here
   * is the cost of the arrangement rather than the behaviour. That queue is three mutable bindings
   * and `StyleSpec` cannot see them, because it scans Scala sources and this is not one, so the
   * page holds the only mutable state in this project that no scan reviews and no test executes.
   * It is written down rather than fixed: running it would want a JavaScript runtime in the build,
   * which is a dependency this repository does not have for a page served on loopback.
   */
  private lazy val Script: String = resource("notebook.js")
}
