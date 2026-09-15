package garden.xeno.symbolum.tactics

import java.net.URI
import java.net.http.{HttpClient, HttpRequest, HttpResponse}
import java.util.concurrent.atomic.AtomicReference
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The one surface in this project that speaks to a browser, exercised over a socket.
 *
 * `Notebook` was 101 uncovered statements of 172, the largest single hole in the coverage of
 * `modules/tactics`, and the reason is structural rather than neglect: its three endpoints are
 * private and reachable only through a running server, so nothing could reach them without one.
 * `SessionSpec` has thirteen tests and one of them touches the page at all.
 *
 * == Why a real server and not a fake exchange ==
 *
 * Every behaviour worth asserting here is about what a client on the other end of a socket
 * receives, and two of them are in the file because of failures it records. A request for
 * `/favicon.ico` came back as the whole page with `text/html` on it, because the root context is a
 * **prefix** match, and the browser was told the page was its icon. And the page answered `curl`
 * perfectly while never finishing in Chrome, because one thread served a connection a browser
 * keeps open. A fake `HttpExchange` asserts the handler's arithmetic and neither of those.
 *
 * The server listens on port **0**, so the operating system picks a free one and two runs of this
 * suite, or a run beside somebody's notebook on 8642, cannot collide.
 *
 * == What it does not cover ==
 *
 * `main` itself: the printing, and the latch that keeps the process alive until the shutdown hook
 * fires. What is left in it after [[Notebook.serve]] came out is a `println`, a build of the
 * chain, and a block, and a test that asserted a process blocks would either hang or assert
 * nothing. The failure that argues for it is recorded where it happened, in `main`'s own comment:
 * a version that did not block reported success and took the server down with it.
 *
 * And the page as a **page**: that KaTeX typesets, that the script rebinds the form, that anything
 * is legible. Those need a browser, which is `994aa06c`'s territory and not a unit test's.
 */
class NotebookSpec extends AnyFlatSpec with Matchers {

  /**
   * One session, shared, for the reason `SessionSpec` shares its own: `Session.standard` builds the
   * whole tactic surface, measured in hundreds of milliseconds, and every use below is a reading of
   * the same immutable value.
   */
  private lazy val fresh: Session = Session.standard

  private val client: HttpClient = HttpClient.newHttpClient()

  /**
   * A server on a free port, stopped whatever the body does.
   *
   * Unconditional rather than a stop at the end of each test: a failed assertion would otherwise
   * leave a listening socket and a thread pool behind for the rest of the run, and the next test
   * to ask for a port would be the one that looked broken.
   */
  private def withServer[T](session: Session)(body: (String, AtomicReference[Session]) => T): T = {
    val held = new AtomicReference[Session](session)
    val server = Notebook.serve(0, held)
    try body(s"http://${Notebook.Host}:${server.getAddress.getPort}", held)
    finally server.stop(0)
  }

  private def get(base: String, path: String): HttpResponse[String] =
    client.send(
      HttpRequest.newBuilder(URI.create(s"$base$path")).GET().build(),
      HttpResponse.BodyHandlers.ofString()
    )

  private def post(base: String, path: String, body: String): HttpResponse[String] =
    client.send(
      HttpRequest
        .newBuilder(URI.create(s"$base$path"))
        .POST(HttpRequest.BodyPublishers.ofString(body))
        .build(),
      HttpResponse.BodyHandlers.ofString()
    )

  /* ------------------------------------------------------------------ the cells */

  "The cells" should "say so when nothing has been run, rather than rendering nothing" in {
    // An empty div and "nothing here yet" look the same to a reader of the source and opposite to
    // a reader of the page: the first reads as a page that failed to load.
    Notebook.cells(fresh) should include("Nothing run yet")
  }

  it should "render each of the four outcomes as its own kind of cell" in {
    // The four are not one answer with a flag on it, which is what `Session.Outcome` is for, and a
    // page that rendered a refusal like a result would be the same merge one layer out. One
    // session carrying all four, because the assertion is that they stay apart.
    val session = fresh.runAll(
      Vector(
        "declare p : bool",                 // Extended
        "assume P_HOLDS : p",               // Proved
        "find ABS_TRIANGLE",                // Report
        "prove NOPE : !x:real. x @ 0 = x"   // Refused
      )
    )

    val rendered = Notebook.cells(session)

    withClue(s"$rendered\n") {
      rendered should include("""class="extended"""")
      rendered should include("""class="proved"""")
      rendered should include("""class="report"""")
      rendered should include("""class="refused"""")

      // The refusal carries what to try next, which is the whole reason `Remedy` is wired to this
      // surface. `SessionSpec` asserts the outcome holds one; this asserts the page shows it.
      rendered should include("""class="next"""")
    }

    // Every cell offers the way back, which is the only way backwards in an append-only
    // transcript: four commands, four buttons.
    """class="back"""".r.findAllMatchIn(rendered).size shouldBe 4
  }

  it should "name what a theorem rests on only when the session assumed something" in {
    // The empty case is the one worth pinning, because a line that always appears says nothing.
    // `SessionSpec` holds both sides for the outcome; this holds them for the page.
    val assumed = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p"))
    val unassumed = fresh.run("find ABS_TRIANGLE")

    Notebook.cells(assumed) should include("rests on what this session assumed")
    Notebook.cells(unassumed) should not include "rests on what this session assumed"
  }

  it should "escape what a reader typed, so a transcript cannot write the page" in {
    // A line that does not read is **kept** in the transcript, because a dropped line makes the
    // transcript a lie, and that is what puts a reader's text on the page whatever it contains.
    // The characters are `escape`'s four, checked by being sent through as a command rather than
    // by calling it: what matters is that nothing between the reader and the page skips it.
    val session = fresh.run("""declare <script>alert("x & y")</script> : bool""")
    val rendered = Notebook.cells(session)

    withClue(s"$rendered\n") {
      rendered should include("&lt;script&gt;")
      rendered should include("&amp;")
      rendered should include("&quot;")
      rendered should not include "<script>alert"
    }
  }

  /* ------------------------------------------------------------------ over a socket */

  "The page endpoint" should "answer the root with the page and everything else with a 404" in {
    withServer(fresh) { (base, _) =>
      val page = get(base, "/")
      page.statusCode shouldBe 200
      page.headers.firstValue("Content-Type").orElse("") should include("text/html")
      page.body should startWith("<!doctype html>")

      // The failure this behaviour exists for: the root context is a prefix match, so without it a
      // browser asking for its icon is handed the whole page with `text/html` on it and told that
      // is the icon. 404 is the difference between a client that knows there is nothing there and
      // one that has been given something wrong.
      val absent = get(base, "/favicon.ico")
      absent.statusCode shouldBe 404
      absent.headers.firstValue("Content-Type").orElse("") should include("text/plain")
      absent.body should include("favicon.ico")
      absent.body should not include "<!doctype html>"
    }
  }

  "The run endpoint" should "extend the transcript and answer with the cells alone" in {
    // The cells and not the page: the browser replaces one element, and an endpoint returning the
    // whole document would replace the form the reader is typing in.
    withServer(fresh) { (base, held) =>
      val answer = post(base, "/run", "declare p : bool")

      answer.statusCode shouldBe 200
      answer.body should include("""class="extended"""")
      answer.body should not include "<!doctype html>"

      held.get.entries should have size 1
      held.get.entries.head.outcome shouldBe a[Session.Outcome.Extended]
    }
  }

  it should "refuse a second declaration of one name, which is the session's soundness argument" in {
    // Not a convenience. `SoundnessAttackSpec` derives `|- F` from two theories that each declare
    // one name, and what rules that out through this surface is that there is one theory to
    // declare into and the kernel refuses the second itself. It is asserted here over the wire,
    // because this is the surface a person actually types at.
    withServer(fresh) { (base, held) =>
      post(base, "/run", "declare p : bool").statusCode shouldBe 200
      val second = post(base, "/run", "declare p : bool")

      second.statusCode shouldBe 200
      second.body should include("""class="refused"""")
      second.body.toLowerCase should include("already declared")

      held.get.entries should have size 2
      held.get.entries(1).outcome shouldBe a[Session.Outcome.Refused]
    }
  }

  "The truncate endpoint" should "discard what it says it discards, and nothing else" in {
    // Going back is the only way backwards in an append-only transcript, and it is its own endpoint
    // rather than a flag on `/run` because discarding results is not a variant of producing one.
    withServer(fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p", "find ABS_TRIANGLE"))) {
      (base, held) =>
        held.get.entries should have size 3

        val answer = post(base, "/truncate", "1")
        answer.statusCode shouldBe 200

        held.get.entries should have size 1
        held.get.entries.head.outcome shouldBe a[Session.Outcome.Extended]
        answer.body should include("""class="extended"""")
        answer.body should not include """class="proved""""
    }
  }

  it should "read a count it cannot make sense of as none, rather than failing the request" in {
    // The page asks before it calls this, so a body that is not a number is a client that has gone
    // wrong rather than a reader who has. Answering the empty transcript is the safe reading: it
    // discards everything, which the page has already warned about, and it keeps the surface
    // answering instead of returning a stack trace to a browser.
    withServer(fresh.run("declare p : bool")) { (base, held) =>
      val answer = post(base, "/truncate", "not a number")

      answer.statusCode shouldBe 200
      held.get.entries shouldBe empty
      answer.body should include("Nothing run yet")
    }
  }
}
