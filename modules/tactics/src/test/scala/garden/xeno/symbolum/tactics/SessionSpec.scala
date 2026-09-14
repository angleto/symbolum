package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * What a session guarantees, and the attack it exists to make unassemblable.
 *
 * The assertions here are not that the commands work, though they do. They are the three properties
 * that make a cell interface safe to put in front of somebody, each stated so that the input which
 * would make it vacuous is asserted against too:
 *
 *  - **one theory**, so that the falsity `SoundnessAttackSpec` derives from two cannot be built by
 *    running cells in an order nobody thought about;
 *  - **the transcript is the session**, so that what a reader sees is a function of the commands
 *    and replaying them reproduces it;
 *  - **nothing a session assumed is hidden**, so that a theorem standing on the reader's own
 *    assumption says so on the line where it is printed.
 *
 * The distinction the first of those turns on is worth stating, because a reader will otherwise
 * think this file forbids more than it does. A session that assumes `p` and then assumes `~p` gets
 * an **inconsistent theory**, and everything follows from it; that is not the defect, it is a user
 * assuming contradictory things and it is fully accounted for, because every consequence names both
 * assumptions. The defect is falsity assembled from two theories each of which looks consistent,
 * where nothing on any page says where it came from. One is a bad assumption, the other is a broken
 * instrument.
 */
class SessionSpec extends AnyFlatSpec with Matchers {

  /**
   * One empty session, shared.
   *
   * A `val` rather than a `def` because a session is immutable and every operation returns a new
   * one, so the fifteen uses below are fifteen readings of the same empty state. It matters to the
   * suite's clock rather than to the assertions: `Session.standard` builds the tactic surface and
   * the cost report, measured at 334 to 717 ms and 312 ms on 2026-09-13, and a `def` here would
   * have put ten seconds into a file that asserts nothing about either.
   */
  private lazy val fresh: Session = Session.standard

  /* ------------------------------------------------------------------ one theory */

  "A session" should "hold one theory, so a name cannot be declared into two of them" in {
    // The attack in `SoundnessAttackSpec` needs two theories that each declare `p : bool`: a
    // constant declared and never defined has `origin = None`, so the two are the same constant,
    // and a `Kernel.Thm` carries no theory, so an axiom from one meets the negation of it from the
    // other inside a single rule. Through this surface there is one theory to declare into, and the
    // kernel refuses the second declaration itself.
    val session = fresh.runAll(Vector("declare p : bool", "declare p : bool"))

    session.entries(0).outcome shouldBe a[Session.Outcome.Extended]
    session.entries(1).outcome match {
      case Session.Outcome.Refused(reason, _) => reason.toLowerCase should include("already declared")
      case other => fail(s"a second declaration of one name was taken: $other")
    }
  }

  it should "take the whole theory back when a command is replaced, not just the line" in {
    // The rule the class comment argues for: re-running a cell truncates. What would make this
    // assertion vacuous is a session that never held the fact in the first place, so the middle
    // line asserts it was there before the replacement dropped it.
    val session = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p", "prove TRIV : !x:real. x + 0 = x"))

    session.state.fact("P_HOLDS") shouldBe defined
    session.state.theory.axioms.size shouldBe fresh.state.theory.axioms.size + 1

    val (replaced, discarded) = session.replace(2, Session.Command.Assume("P_FAILS", "~p"))

    withClue("the replaced session still holds the theorem of the command it replaced: ") {
      replaced.state.fact("P_HOLDS") shouldBe None
    }
    withClue("the assumption that was replaced is still in the theory: ") {
      replaced.assumptions.map(_._1) shouldBe Vector("P_FAILS")
    }
    discarded.map(Session.Command.write) shouldBe Vector("prove TRIV : !x:real. x + 0 = x")
  }

  it should "count a declared constant as one theory's, so the two states are not siblings" in {
    // `truncate` hands back the earlier theory rather than the current one with rows hidden, which
    // is the property that makes "go back and edit" safe. Asserted on the constant rather than on
    // the entry count, because an entry count would pass on a session that kept the theory.
    val session = fresh.runAll(Vector("declare p : bool", "declare q : bool"))

    session.state.theory.constants.keySet should contain allOf ("p", "q")
    session.truncate(1).state.theory.constants.keySet should contain("p")
    session.truncate(1).state.theory.constants.keySet should not contain "q"
    session.truncate(0).state.theory.constants.keySet should not contain "p"
  }

  /* -------------------------------------------------------- the transcript is the session */

  "The transcript" should "replay to the same theory, which is what makes it the session" in {
    val lines = Vector(
      "declare p : bool",
      "assume P_HOLDS : p",
      "define twice := \\x:real. x + x",
      "prove SQ : !x:real. 0 <= x * x"
    )
    val session = fresh.runAll(lines)
    val replayed = fresh.runAll(session.transcript.linesIterator.toVector)

    replayed.state.theory.axioms shouldBe session.state.theory.axioms
    replayed.state.theory.constants shouldBe session.state.theory.constants
    replayed.state.theory.typeOperators shouldBe session.state.theory.typeOperators
    replayed.state.named.map(_._1) shouldBe session.state.named.map(_._1)

    // And the population, so that a transcript which replayed nothing would not pass this.
    session.state.named.map(_._1) shouldBe Vector("P_HOLDS", "twice", "SQ")
  }

  it should "read back every command it writes" in {
    val commands = Vector(
      Session.Command.Declare("p", "bool"),
      Session.Command.Define("twice", "\\x:real. x + x"),
      Session.Command.Assume("P_HOLDS", "p"),
      Session.Command.Prove("SQ", "!x:real. 0 <= x * x"),
      Session.Command.Ask("!x:real. x + 0 = x"),
      Session.Command.Find("SUM"),
      Session.Command.Show("ABS_TRIANGLE")
    )

    commands.foreach { command =>
      withClue(s"${Session.Command.write(command)}: ") {
        Session.Command.read(Session.Command.write(command)) shouldBe Right(command)
      }
    }
  }

  it should "keep a line that did not read, because a dropped line makes the transcript a lie" in {
    val session = fresh.run("wobble something")

    session.entries.size shouldBe 1
    session.entries.head.outcome match {
      case Session.Outcome.Refused(reason, _) =>
        Session.Command.Keywords.foreach(keyword => reason should include(keyword))
      case other => fail(s"an unknown command was taken: $other")
    }
  }

  /* ------------------------------------------------------ nothing assumed is hidden */

  "A theorem standing on what a session assumed" should "name the assumption" in {
    val session = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p"))
    val entry = session.entries.last

    val rests = entry.restsOn(session.base)
    rests should have size 1
    entry.state.show(rests.head) shouldBe "p"
  }

  it should "name nothing where the foundation already believed it, which is the empty case" in {
    // The assertion above passes on an implementation that returns every axiom it can find, so the
    // pair is what carries the content: a theorem of the library rests on nothing this session
    // added, and the same call says so.
    val session = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p", "prove SQ : !x:real. 0 <= x * x"))
    val proved = session.entries.last

    proved.outcome shouldBe a[Session.Outcome.Proved]
    withClue("a library theorem was reported as standing on the session's assumption: ") {
      proved.restsOn(session.base) shouldBe empty
    }
  }

  it should "move the axiom count exactly where an axiom was asserted and nowhere else" in {
    // Definitions and proofs are conservative and a declaration is too, so the count is a check on
    // all four commands at once: if `define` ever asserted anything this fails naming it.
    val before = fresh.state.theory.axioms.size

    fresh.run("declare p : bool").state.theory.axioms.size shouldBe before
    fresh.run("define twice := \\x:real. x + x").state.theory.axioms.size shouldBe before
    fresh.run("prove SQ : !x:real. 0 <= x * x").state.theory.axioms.size shouldBe before
    fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p")).state.theory.axioms.size shouldBe before + 1
  }

  /* ------------------------------------------------------------------ what it refuses */

  "A claim written in a vocabulary the session introduced" should "be refused saying so" in {
    // The limit this repository chose rather than a defect: `CLAUDE.md` says a domain gets
    // accounting and not search, because `Ring` and `Linarith` decide fragments of the reals and
    // have nothing to say about an arbitrary axiom. So no tactic can spend `P_HOLDS`, and what a
    // session needs in order to is a hand derivation, which is the `derive` command this language
    // does not have yet and the `Recorder` in `modules/logic` is the surface for.
    //
    // Asserted so that the day it lands this test says the picture changed, rather than the
    // refusal quietly becoming wrong.
    val session = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p", "prove FROM_P : p"))

    session.entries.last.outcome match {
      case Session.Outcome.Refused(reason, _) =>
        reason should include("p")
        reason should include("this session introduced")
      case other => fail(s"a claim over an assumed constant was settled by a tactic: $other")
    }
  }

  "A refusal" should "carry the next step, which is what `Remedy` is for" in {
    // `RemedySpec` requires every verdict this module declares to be mapped or named as an
    // exception, and `Session.Outcome` is named on the ground that its refusal case has already
    // been through `Remedy`. That entry is a claim about this file, so it is asserted here: an
    // unreadable claim gets a next step, and it is not the message repeated.
    val session = fresh.run("prove NOPE : !x:real. x @ 0 = x")

    session.entries.head.outcome match {
      case Session.Outcome.Refused(reason, next) =>
        withClue("a refusal arrived with no next step: ") { next shouldBe defined }
        next.get should not be reason
      case other => fail(s"an unreadable claim was taken: $other")
    }
  }

  "The page" should "render from a session, with the stylesheet and the script it needs" in {
    // Not a golden page and not a test of how it looks. Two things a test can hold: the page is a
    // pure function of a session, and the two files it reads off the classpath are there. The
    // second is why this exists at all: the stylesheet and the behaviour moved out of the Scala
    // source into resources on 2026-09-13, and a resource that fails to package throws at the
    // first request rather than at compilation, which is the worst moment to find out.
    val session = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p"))
    val page = Notebook.render(session)

    page should startWith("<!doctype html>")
    withClue("the stylesheet did not load off the classpath: ") { page should include("#line:focus") }
    withClue("the behaviour did not load off the classpath: ") { page should include("katex.render") }

    // Both forms of the statement, which is the discipline the page shares with `Essay`: what is
    // set in print is published only beside the text that reads back.
    page should include("data-tex=")
    page should include("|- p")

    // And what the session assumed, on the page rather than in the reader's head.
    page should include("rests on what this session assumed")

    // Pure: the same session renders the same page.
    Notebook.render(session) shouldBe page
  }

  "The reading commands" should "answer without touching the theory" in {
    val session = fresh.runAll(Vector("ask !x:real. x + 0 = x", "find ABS_TRIANGLE", "show ABS_TRIANGLE"))

    session.entries.foreach { entry =>
      withClue(s"${Session.Command.write(entry.command)}: ") {
        entry.outcome shouldBe a[Session.Outcome.Report]
      }
    }
    session.state.theory.axioms shouldBe fresh.state.theory.axioms
    session.state.theory.constants shouldBe fresh.state.theory.constants
    session.state.named shouldBe empty

    val texts = session.entries.map(_.outcome).collect { case Session.Outcome.Report(text) => text }
    texts(1) should include("ABS_TRIANGLE")
    texts(2) should include("## What on this page is checked")
  }
}
