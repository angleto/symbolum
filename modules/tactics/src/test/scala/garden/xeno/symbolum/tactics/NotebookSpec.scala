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
 *
 * `notebook.js`'s queue is in that second list and is worth naming separately, because it is half
 * of a fix the rest of this file does assert. Nothing in this repository runs JavaScript, so that
 * the page sends one request at a time is not checked here or anywhere. What is checked is the
 * server's side of it, that a command is applied to the transcript its writer read or to none, and
 * the two meet at a consequence: a page that stopped queueing would start collecting refusals
 * where it used to reorder the transcript quietly.
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
    client.send(request(base, path, body).build(), HttpResponse.BodyHandlers.ofString())

  /** The same, naming the transcript the writer read, which is what [[Notebook.After]] carries. */
  private def postAfter(base: String, path: String, body: String, after: Int): HttpResponse[String] =
    client.send(
      request(base, path, body).header(Notebook.After, after.toString).build(),
      HttpResponse.BodyHandlers.ofString()
    )

  private def request(base: String, path: String, body: String): HttpRequest.Builder =
    HttpRequest.newBuilder(URI.create(s"$base$path")).POST(HttpRequest.BodyPublishers.ofString(body))

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
    //
    // **The negative half of this was vacuous until 2026-09-16, and coverage is what said so.**
    // It was written with `find ABS_TRIANGLE` as the unassumed session, which is a `Report` and
    // never reaches [[Notebook.proved]] at all, so the absent line was absent because nothing had
    // rendered a theorem rather than because a theorem had rendered without it. The statement that
    // decides it, `if (rests.isEmpty) ""`, had an invocation count of **zero** in a report where
    // the test beside it was green: the assertion held for a session that could not have failed
    // it. This is the guard `CLAUDE.md` asks for under "an assertion is only as good as the
    // thought somebody gave to what would make it empty", met in the file rather than in the rule.
    //
    // So the negative case is now a **proved** theorem that assumed nothing, which is the only
    // shape that can distinguish the two, and the report stays as a third case because a cell that
    // is not a theorem should not carry the line either.
    val assumed = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p"))
    val provedFreely = fresh.run("prove SQ : !x:real. 0 <= x * x")
    val reported = fresh.run("find ABS_TRIANGLE")

    withClue(s"${Notebook.cells(provedFreely)}\n") {
      // The case that makes the assertion non-vacuous: a theorem is on the page, and the line is
      // not, because this session spent nothing of its own to get it.
      Notebook.cells(provedFreely) should include("""class="proved"""")
      Notebook.cells(provedFreely) should not include "rests on what this session assumed"
    }

    Notebook.cells(assumed) should include("rests on what this session assumed")
    Notebook.cells(reported) should not include "rests on what this session assumed"
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

  it should "carry an example of every command, which a browser is the only place that shows" in {
    // Found by opening the page rather than by any assertion here: `derive` landed, the placeholder
    // is generated from `Keywords` and listed eight commands, and the line under it is written by
    // hand and listed seven. Both are on screen together, a centimetre apart, and nothing compared
    // them. So they are compared now.
    //
    // The keyword alone is what a reader already has from the placeholder, so this asserts the
    // example exists rather than asserting the two lists are equal: what is missing when it fails
    // is a reader's only statement of the SHAPE a command takes.
    // Read from the help paragraph alone and not from the whole page, which is the difference
    // between a check and a check-shaped sentence: the placeholder is ON the page and is built from
    // the same list, so a search over the page finds every keyword whatever the examples say, and
    // passes on exactly the state this was written for.
    val page = Notebook.render(Session.standard)
    val examples = page.linesIterator.filter(_.contains("&middot;")).mkString(" ")

    withClue("no help paragraph was found on the page: ") {
      examples should not be empty
    }

    Session.Command.Keywords.foreach { keyword =>
      withClue(s"the page offers `$keyword` and its examples do not show it: $examples\n") {
        examples should include(keyword)
      }
    }
  }

  it should "carry the header name the server reads, which is the one fact this page states twice" in {
    // `Notebook.After` is a Scala constant and `notebook.js` writes the same string in its own
    // language, because a JavaScript file that took it from Scala would have to be assembled
    // rather than read, and it is a file so that an editor knows it is JavaScript.
    //
    // So the copy is guarded instead of removed, which is the second of the three remedies this
    // repository uses for a fact written twice and the right one when the two copies cannot be one
    // file. What a drift costs without this is the whole of the ordering: the page would send a
    // header nobody reads, every submission would look like a writer that named nothing, and the
    // refusal that catches a stale write would never fire. Nothing else would go red.
    val page = Notebook.render(fresh)

    withClue(s"the page does not name `${Notebook.After}`, so the server's ordering header is unsent: ") {
      page should include(Notebook.After)
    }
  }

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

  it should "run a whole development in one submission, in the order it was written" in {
    // **The case the ordering defect was found on, and the acceptance criterion of the card that
    // asked for this.** Five commands written faster than the round trip used to be five POSTs
    // racing each other, and the page numbered them in arrival order: `derive AT_ONE` landed as
    // cell 1 and failed naming `RULE`, which was cell 5. Sent as one body they are folded over one
    // state in the order they appear, so nothing about that order is the network's to decide.
    //
    // The two `derive` lines are what makes this an assertion about **order** rather than about
    // parsing: each cites a fact an earlier line produced, so any order but the written one leaves
    // a refusal on the page. A test over five independent lines would pass on a shuffle.
    val development =
      """declare good : real -> bool
        |assume RULE : !r:real. good r ==> good (r + 1)
        |assume GOOD_ONE : good 1
        |derive AT_ONE : specialise RULE at 1
        |derive GOOD_TWO : mp AT_ONE GOOD_ONE""".stripMargin

    withServer(fresh) { (base, held) =>
      val answer = post(base, "/run", development)
      answer.statusCode shouldBe 200

      val entries = held.get.entries
      withClue(s"${held.get.render}\n") {
        entries should have size 5
        entries.map(_.number) shouldBe Vector(1, 2, 3, 4, 5)
        entries.map(entry => Session.Command.write(entry.command)) shouldBe
          development.linesIterator.toVector

        // Nothing was refused, which is the half that says the order is right rather than merely
        // preserved: a shuffle of these five refuses at least twice.
        entries.map(_.outcome).collect { case refused: Session.Outcome.Refused => refused } shouldBe empty
        entries.last.outcome shouldBe a[Session.Outcome.Proved]
      }
    }
  }

  it should "drop the blank lines a paste is made of, rather than recording them as commands" in {
    // A transcript holding cells its writer did not write is the same defect as one holding them
    // in an order its writer did not choose. A line that is not blank and does not read is kept,
    // which is `Session`'s rule and the opposite case: the assertion below holds both.
    withServer(fresh) { (base, held) =>
      post(base, "/run", "\ndeclare p : bool\n\n   \nnot a command\n").statusCode shouldBe 200

      held.get.entries should have size 2
      held.get.entries.head.outcome shouldBe a[Session.Outcome.Extended]
      held.get.entries(1).outcome shouldBe a[Session.Outcome.Refused]
    }
  }

  "A writer that names the transcript it read" should "be served when it is the current one" in {
    withServer(fresh.run("declare p : bool")) { (base, held) =>
      val answer = postAfter(base, "/run", "declare q : bool", after = 1)

      answer.statusCode shouldBe 200
      answer.body should include("""class="extended"""")
      held.get.entries should have size 2
    }
  }

  it should "be refused, and handed the cells, when the transcript has moved under it" in {
    // API is not the word for a page on loopback, but the property is the ordinary one: a mutable
    // resource does not take a blind write. The writer presents what it read and a mismatch gets
    // the current state back, because what a writer that has fallen behind needs is not an error
    // message, it is the transcript it has to read before writing again.
    withServer(fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p"))) { (base, held) =>
      val answer = postAfter(base, "/run", "declare q : bool", after = 1)

      answer.statusCode shouldBe Notebook.Conflict
      held.get.entries should have size 2
      held.get.commands.map(Session.Command.write) should not contain "declare q : bool"

      // The cells as they stand, which is the reason this answer has a body at all.
      answer.body should include("""class="proved"""")
      answer.body should include("P_HOLDS")
    }
  }

  it should "let one of two concurrent writers through and refuse the other, never interleave them" in {
    // **The test the card asked for: a concurrent submission and an assertion about order.** It is
    // the half of the fix a test can reach. The other half is the page's queue, and nothing in
    // this repository runs JavaScript, so what is asserted here is the property that makes the
    // queue's absence visible instead of silent: two writers that both read the empty transcript
    // cannot both write to it.
    //
    // The outcome is deterministic although the race is not. Whichever reaches the lock first
    // applies its command; the other then reads a transcript of one entry, has named zero, and is
    // refused. Nothing in the assertion depends on which of the two won, which is what keeps it
    // from being a flake: what is pinned is that exactly one did.
    withServer(fresh) { (base, held) =>
      val first = client.sendAsync(
        request(base, "/run", "declare p : bool").header(Notebook.After, "0").build(),
        HttpResponse.BodyHandlers.ofString()
      )
      val second = client.sendAsync(
        request(base, "/run", "declare q : bool").header(Notebook.After, "0").build(),
        HttpResponse.BodyHandlers.ofString()
      )

      val statuses = Vector(first.join().statusCode, second.join().statusCode).sorted

      withClue(s"${held.get.render}\n") {
        statuses shouldBe Vector(200, Notebook.Conflict)
        held.get.entries should have size 1
      }
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
