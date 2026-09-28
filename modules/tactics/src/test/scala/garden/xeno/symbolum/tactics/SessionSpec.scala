package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.theories.Library

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
   * one, so every use below is a reading of the same empty state. It matters to the suite's clock
   * rather than to the assertions: `Session.standard` builds the tactic surface and the cost
   * report, measured at 334 to 717 ms and 312 ms on 2026-09-13, and a `def` here would have paid
   * that once per use, in a file that asserts nothing about either.
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
    // The limit this repository chose rather than a defect, and it did not move when `derive`
    // landed: `Ring` and `Linarith` decide fragments of the reals and have nothing to say about an
    // arbitrary axiom, so no TACTIC can spend `P_HOLDS`. What changed is that a session now has a
    // way to spend it by hand, which is `derive` over the `Recorder`, and the tests under "A hand
    // derivation" below are that half. This assertion is the other half and has to keep holding:
    // the two commands answer different questions and `prove` must not start guessing.
    val session = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p", "prove FROM_P : p"))

    session.entries.last.outcome match {
      case Session.Outcome.Refused(reason, _) =>
        reason should include("p")
        reason should include("this session introduced")
      case other => fail(s"a claim over an assumed constant was settled by a tactic: $other")
    }
  }

  "A refusal of a goal the session can read" should "write the goal in the session's notation" in {
    // Card 9fefbf75. The reason was the error's `message`, which writes terms in the kernel's
    // printing, so a cell reading `x * x >= 1` was answered `found ((real_le real_one) ((real_mul
    // x) x))`, and the second goal came back with `BIT1 real_one` for its 3.
    //
    // The negatives alone would pass on a reason that stopped naming the goal at all, which a
    // rewording could do, so each reason is also asserted to carry the goal in the reals' notation.
    val claims = Vector(
      "prove SQUARE_AT_LEAST_ONE : !x:real. x * x >= 1" -> "1 <= x * x",
      "prove SQUARES_DOMINATE : !x:real y:real. x * x + y * y >= 3 * (x * y)" -> "3 * (x * y)"
    )
    val session = fresh.runAll(claims.map(_._1))

    session.entries.zip(claims).foreach { case (entry, (_, written)) =>
      entry.outcome match {
        case Session.Outcome.Refused(reason, _) =>
          info(reason)
          reason should include(written)
          Vector("real_le", "real_mul", "real_one", "BIT1").foreach { name =>
            reason should not include name
          }
          entry.render(session.state) should not include "real_le"
        case other => fail(s"a false inequality was not refused: $other")
      }
    }
  }

  /* ---------------------------------------------------- what a session can spend by hand */

  "A hand derivation" should "let a session's own axiom reach a conclusion, which no tactic can" in {
    // Criterion 2 of the card this command comes from, and the whole point of the command: a
    // session declares a vocabulary, assumes something in it, and gets a consequence out. Before
    // `derive` the last line was refused by every tactic there is, correctly, and the accounting
    // promise above it was therefore true of theorems nobody could reach.
    val session = fresh.runAll(
      Vector(
        "declare good : real -> bool",
        "declare fine : real -> bool",
        "assume RULE : !r:real. good r ==> fine r",
        "assume GOOD_ONE : good 1",
        "derive AT_ONE : specialise RULE at 1",
        "derive FINE_ONE : mp AT_ONE GOOD_ONE"
      )
    )
    val conclusion = session.entries.last

    withClue(session.transcript + "\n") {
      conclusion.outcome shouldBe a[Session.Outcome.Proved]
    }
    conclusion.state.show(
      conclusion.outcome.asInstanceOf[Session.Outcome.Proved].theorem.conclusion
    ) shouldBe "fine 1"
  }

  it should "carry both assumptions it spent, which is the accounting the command exists for" in {
    // The half that makes the one above worth having. A conclusion reached by hand from two
    // assumptions names two, and `Derivation.foreignTo` is what says so: a derivation that
    // silently dropped one would still produce the theorem and would be the defect this whole
    // surface is built against.
    val session = fresh.runAll(
      Vector(
        "declare good : real -> bool",
        "declare fine : real -> bool",
        "assume RULE : !r:real. good r ==> fine r",
        "assume GOOD_ONE : good 1",
        "derive AT_ONE : specialise RULE at 1",
        "derive FINE_ONE : mp AT_ONE GOOD_ONE"
      )
    )
    val conclusion = session.entries.last
    val rests = conclusion.restsOn(session.base).map(conclusion.state.show)

    // Compared against what the session records having assumed, rather than against the text that
    // was typed. The kernel binds by de Bruijn index and `Abs` carries no name, so the binder in
    // `!r:real. good r ==> fine r` comes back as whatever the printer chose, and an assertion on
    // the typed spelling fails on a correct answer. What is being asserted is the property that
    // matters and is stronger: the conclusion rests on exactly the two things this session assumed,
    // no more and no fewer, with both sides rendered by the same printer.
    rests shouldBe conclusion.state.assumed.map(pair => conclusion.state.show(pair._2)).toSet
    rests should have size 2
  }

  it should "leave the theory exactly as it found it, on every inference it offers" in {
    // Criterion 3, and it is asserted over the whole vocabulary rather than over one case, because
    // the property is structural and a single case would pass on an implementation that had one
    // branch reaching `declareConstant`. A session holds ONE theory: that is what makes the falsity
    // `SoundnessAttackSpec` derives unassemblable here, and a command that could grow a second
    // would reopen it whatever else it did.
    val start = fresh.runAll(
      Vector(
        "declare good : real -> bool",
        "assume RULE : !r:real. good r",
        "assume PAIR : good 1 /\\ good 2",
        "assume IMP : good 1 ==> good 2"
      )
    )
    val constants = start.state.theory.constants.keySet
    val axioms = start.state.theory.axioms.size

    // Each step cites what the one before it produced, which is what makes this a derivation and
    // not five independent readings, and it is why the fold below threads the session through.
    val steps = Vector(
      "derive A : specialise RULE at 1",
      "derive B : left PAIR",
      "derive C : right PAIR",
      "derive D : both B C",
      "derive E : mp IMP A"
    )

    // **This ran every step from `start` until 2026-09-16, and that made it vacuous on two of the
    // five.** `D` cites `B` and `C` and `E` cites `A`, none of which `start` holds, so both were
    // refused with "no fact named B"; a refused step leaves the state untouched by construction,
    // so the two assertions below passed **without the inference having run at all**. A bad branch
    // in `both` or in `mp` reaching `declareConstant` is exactly what this test exists to catch and
    // exactly what it could not have seen. Found by a verification that executed the loop's own
    // expression rather than reading it.
    //
    // Two things repair it and both are needed. The fold, so each step meets the session the
    // previous one produced. And the outcome asserted **before** the theory is looked at, because
    // "the theory did not change" is true of a refusal too: without that line this guard stays
    // green on a `derive` that has stopped working entirely.
    steps.foldLeft(start) { (session, step) =>
      val next = session.run(step)
      val entry = next.entries.last

      withClue(s"$step did not produce a theorem: ${entry.render(next.state)}\n") {
        entry.outcome shouldBe a[Session.Outcome.Proved]
      }
      withClue(s"$step changed the theory: ") {
        next.state.theory.constants.keySet shouldBe constants
        next.state.theory.axioms.size shouldBe axioms
      }
      next
    }

    // And the vocabulary the fold ran over is the published one, so an inference added without a
    // case here stops being covered loudly rather than quietly.
    //
    // It reads the inference out of the step's own text, which is a weak thing to read and is
    // sound only because of the line above it: a step asserted `Proved` is one whose inference the
    // surface actually performed, so a name here that nothing executes cannot reach this
    // assertion. On its own, which is how it stood, it certified that five names were **mentioned**.
    steps.map(_.split(" : ")(1).takeWhile(_ != ' ')).toSet shouldBe Session.Surface.Inferences.toSet
  }

  it should "read a specialise argument against the binder it instantiates, not against nothing" in {
    // `1` alone is ambiguous between `real` and `num` and the parser refuses it, correctly: the
    // thing that determines it is the quantifier being instantiated, and that is in the command's
    // hand rather than in the text. So the argument is elaborated against the binder's type, which
    // is `Signature.term(text, expected)` used where the expectation actually lives.
    val session = fresh.runAll(
      Vector("declare good : real -> bool", "assume RULE : !r:real. good r", "derive AT_ONE : specialise RULE at 1")
    )

    withClue(session.entries.last.render(session.state) + "\n") {
      session.entries.last.outcome shouldBe a[Session.Outcome.Proved]
    }

    // And the control, because the assertion above passes on an implementation that guesses `real`
    // for every numeral: a quantifier over `num` takes the same text to the other type.
    val naturals = fresh.runAll(
      Vector("declare small : num -> bool", "assume LOW : !n:num. small n", "derive AT_ONE : specialise LOW at 1")
    )
    val proved = naturals.entries.last.outcome.asInstanceOf[Session.Outcome.Proved]
    naturals.state.show(proved.theorem.conclusion) shouldBe "small 1"
  }

  it should "keep the account, because a derivation nobody can read back is a claim" in {
    // The `Recorder` is what makes this a derivation rather than a theorem that appeared. Each step
    // leaves a line, and the lines accumulate across cells, which is the reason the account lives
    // on the state rather than on one entry: the argument is written across the transcript.
    val session = fresh.runAll(
      Vector(
        "declare good : real -> bool",
        "declare fine : real -> bool",
        "assume RULE : !r:real. good r ==> fine r",
        "assume GOOD_ONE : good 1",
        "derive AT_ONE : specialise RULE at 1",
        "derive FINE_ONE : mp AT_ONE GOOD_ONE"
      )
    )

    session.state.script.size shouldBe 2
    val account = session.state.script.render(session.state.notation, Map.empty)
    account should include("specialise")
    account should include("modus ponens")

    // The empty case, so the assertion above is not satisfied by an account that always has lines:
    // a session that derived nothing has none.
    fresh.run("declare good : real -> bool").state.script.size shouldBe 0
  }

  it should "refuse an inference it does not have, by name, rather than guessing" in {
    val session = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p", "derive X : contradiction P_HOLDS"))

    session.entries.last.outcome match {
      case Session.Outcome.Refused(reason, next) =>
        reason should include("no inference `contradiction`")
        next.getOrElse(fail("a refusal with no next step")) should include("specialise")
      case other => fail(s"an inference nobody wrote was accepted: $other")
    }
  }

  it should "refuse a fact it does not hold, and say what it does hold" in {
    val session = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p", "derive X : left NOWHERE"))

    session.entries.last.outcome match {
      case Session.Outcome.Refused(reason, _) =>
        reason should include("no fact named NOWHERE")
        reason should include("P_HOLDS")
      case other => fail(s"a name nothing holds was resolved: $other")
    }
  }

  it should "say the shape of an inference given the wrong number of names" in {
    // The refusal branches are the ones a derivation actually meets, since getting a hand proof
    // wrong is the ordinary case and getting it right is the exception. Three shapes at once: too
    // few names, too many, and `specialise` without its `at`.
    val session = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p"))

    val shapes = Vector(
      "derive X : mp P_HOLDS" -> "mp <IMPLICATION> <ANTECEDENT>",
      "derive X : left P_HOLDS P_HOLDS" -> "left <CONJUNCTION>",
      "derive X : both P_HOLDS" -> "both <FACT> <FACT>",
      "derive X : specialise P_HOLDS" -> "specialise <FACT> at <term>"
    )

    shapes.foreach { case (line, shape) =>
      session.run(line).entries.last.outcome match {
        case Session.Outcome.Refused(reason, _) =>
          withClue(s"$line was refused without saying how it is written: ") {
            reason should include(shape)
          }
        case other => fail(s"$line was accepted: $other")
      }
    }
  }

  it should "pass the rule's own refusal through, when the names are right and the inference is not" in {
    // The branch where the parsing succeeds and the LOGIC refuses: `mp` on something that is not an
    // implication. What must not happen is this being reported as a malformed command, because the
    // command was well formed and the reader needs the rule's own words.
    val session = fresh.runAll(Vector("declare p : bool", "assume P_HOLDS : p", "derive X : mp P_HOLDS P_HOLDS"))

    session.entries.last.outcome match {
      case Session.Outcome.Refused(reason, next) =>
        reason should not include "written `"
        next should not be empty
      case other => fail(s"modus ponens on a non-implication produced $other")
    }
  }

  it should "say it holds nothing yet when the first command of a session is a derivation" in {
    // The empty case of the refusal that lists what the session holds. Asserted because the message
    // is built by a branch nothing else reaches, and a list that reads as empty where it should read
    // as "nothing yet" is the difference between a reader thinking the name is wrong and knowing
    // there is nothing to name.
    fresh.run("derive X : left NOWHERE").entries.last.outcome match {
      case Session.Outcome.Refused(reason, _) => reason should include("nothing yet")
      case other => fail(s"a derivation in an empty session produced $other")
    }
  }

  it should "refuse a library name that two developments hold, rather than picking one" in {
    // `Library.named` returns every entry of a name and its own docstring records that some names
    // are held by two developments each, so a lookup that took the first would pick by map
    // iteration order. The session resolves a name the library holds ONCE and refuses one it holds
    // twice with different statements, which is the honest answer.
    val library = Library.of(fresh.base)
    val ambiguous = library.shared.find(name => library.named(name).map(_.theorem).distinct.size > 1)

    ambiguous match {
      case None =>
        // Not a failure: the library may hold no name whose two entries differ. Said out loud
        // rather than passing silently, because a vacuous case that reads as a check is the thing
        // this file is full of guards against.
        info("no library name is held twice with two different statements, so this case is empty today")
      case Some(name) =>
        fresh.run(s"derive X : left $name").entries.last.outcome match {
          case Session.Outcome.Refused(reason, _) => reason should include("different statements")
          case other => fail(s"an ambiguous library name was resolved: $other")
        }
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

  /* ------------------------------------------------- the refusal surface of a line */

  /**
   * Every way a line can fail to be a command, which is the half a person meets most.
   *
   * This surface exists to be typed at, so a malformed line is the ordinary case rather than the
   * exceptional one, and each refusal says how the command is written rather than that it is wrong.
   * None of these paths was reached by anything: the session's own coverage was 72 uncovered
   * statements of 355, and most of them are here.
   */
  "A line that is not a command" should "be refused saying how the command is written" in {
    val refusals = Vector(
      "" -> "an empty line is not a command",
      "   " -> "an empty line is not a command",
      "declare p" -> "declare is written",
      "declare : bool" -> "declare is written",
      "declare p :" -> "declare is written",
      "define f" -> "define is written",
      "assume NAME" -> "assume is written",
      "prove NAME" -> "prove is written",
      "ask" -> "ask wants",
      "find" -> "find wants",
      "show" -> "show wants"
    )

    refusals.foreach { case (line, expected) =>
      withClue(s"`$line`: ") {
        Session.Command.read(line).left.map(_.take(expected.length)) shouldBe Left(expected)
      }
    }
  }

  it should "be kept in the transcript as the reader typed it" in {
    // A dropped line makes the transcript a lie, which is why `Unreadable` exists at all; this is
    // the other end of it, that writing one back gives the line and not a description of it.
    val session = fresh.run("declare p")

    session.entries.head.outcome shouldBe a[Session.Outcome.Refused]
    Session.Command.write(session.entries.head.command) shouldBe "declare p"
    session.transcript shouldBe "declare p"
  }

  "A command the theory refuses" should "come back refused at declare, define, assume or prove" in {
    // One per command that touches the theory, because they fail through four different paths and
    // a single case would leave three of them unread. The claims are chosen to fail at the reader
    // rather than at the prover, which is what keeps this test quick.
    val session = fresh.runAll(
      Vector(
        "declare q : nosuchtype",
        "define f := @@@",
        "assume A : @@@",
        "prove B : @@@",
        "show NO_SUCH_LEMMA"
      )
    )

    session.entries.take(4).foreach { entry =>
      withClue(s"${Session.Command.write(entry.command)}: ") {
        entry.outcome shouldBe a[Session.Outcome.Refused]
      }
    }

    // `show` of a name nothing holds answers rather than refusing, because the absence is the
    // answer to a question that was put, not a line that did not read. The distinction is worth
    // pinning. Since 2026-09-18 what it answers with is an `Outcome.Page` rather than a `Report`,
    // which is card 07a0d66b: a document and a line of text are different things to whoever is
    // showing them.
    session.entries(4).outcome shouldBe a[Session.Outcome.Page]
  }

  /* ---------------------------------------------------------- the session as a reader sees it */

  "The rendered transcript" should "say so when nothing has been run" in {
    fresh.render shouldBe "nothing run yet"
  }

  it should "show each outcome of a mixed session in the shape that outcome has" in {
    // The text form, which is what a caller with no browser reads, and the counterpart of the
    // page `Notebook` renders. One session carrying all four, because what is asserted is that
    // they stay apart: a refusal printed like a result is the same merge one layer out.
    val session = fresh.runAll(
      Vector(
        "declare p : bool",
        "assume P_HOLDS : p",
        "find ABS_TRIANGLE",
        "prove NOPE : !x:real. x @ 0 = x"
      )
    )

    val rendered = session.render

    withClue(s"$rendered\n") {
      rendered should include("[1] declare p : bool")
      rendered should include("P_HOLDS  |-")
      rendered should include("ABS_TRIANGLE")
      rendered should include("refused:")
      rendered should include("try:")
    }

    // Numbered from one and in order, which is what makes `back to here` mean anything.
    rendered.indexOf("[1]") should be < rendered.indexOf("[4]")
  }

  "What an entry rests on" should "be empty for every outcome that is not a theorem" in {
    // The `Proved` case walks the derivation; the other three have nothing to walk. Asserted
    // because an entry that answered with the session's assumptions for a refusal would put them
    // on a page under something that was never proved.
    val session = fresh.runAll(Vector("declare p : bool", "find ABS_TRIANGLE", "declare p"))

    session.entries.drop(1).foreach { entry =>
      withClue(s"${Session.Command.write(entry.command)}: ") {
        entry.restsOn(session.base) shouldBe empty
      }
    }
  }

  "The reading commands" should "answer without touching the theory" in {
    val session = fresh.runAll(Vector("ask !x:real. x + 0 = x", "find ABS_TRIANGLE", "show ABS_TRIANGLE"))

    // Two of the three report and the third pages, which is the split card 07a0d66b made: what they
    // have in common, and what this test is about, is that none of them changes the theory. The
    // outcome each one produces is asserted by kind rather than by "not a refusal", so a command
    // that started refusing would fail here rather than passing on a weaker claim.
    val answered = session.entries.map(_.outcome).collect {
      case Session.Outcome.Report(text) => text
      case Session.Outcome.Page(markdown) => markdown
    }

    answered should have size 3
    session.state.theory.axioms shouldBe fresh.state.theory.axioms
    session.state.theory.constants shouldBe fresh.state.theory.constants
    session.state.named shouldBe empty

    answered(1) should include("ABS_TRIANGLE")
    answered(2) should include("## What on this page is checked")

    // And the page is the third one rather than any of them: `ask` and `find` write lines.
    session.entries.map(_.outcome).count(_.isInstanceOf[Session.Outcome.Page]) shouldBe 1
    session.entries.last.outcome shouldBe a[Session.Outcome.Page]
  }

  /* ------------------------------------------------- `show` over what the session holds */

  /**
   * What `show` answered, or the failure that says it did not answer at all.
   *
   * `show` answers rather than refusing even when it finds nothing, which the test above pins, so
   * a page and a "nothing holds this name" arrive the same way and this helper is about neither.
   * Both are an `Outcome.Page`, which is what `show` produces and what nothing else does.
   */
  private def reported(entry: Session.Entry): String = entry.outcome match {
    case Session.Outcome.Page(markdown) => markdown
    case other => fail(s"expected a page, got $other")
  }

  "show" should "reach a fact this session derived, and name what that fact rests on" in {
    // The transcript of card c16234d1, which answered `no lemma named …` three lines under the cell
    // that produced the theorem. `show` read `Library.of(chain)` and nothing else, so the message
    // was true of the library and false of the session, which is the collapse of "I did not look
    // there" into "it does not exist".
    //
    // The three below were **seen failing against that version**, on 2026-09-18: the one line that
    // routes `Show` was put back to `Essay.of(chain, name)` and nothing else touched, and this test
    // and the refusal one went red while the library control stayed green. That last part is what
    // makes the trio a guard about the session rather than about `show` in general.
    val session = fresh.runAll(
      Vector(
        "declare good : real -> bool",
        "declare fine : real -> bool",
        "assume RULE : !r:real. good r ==> fine r",
        "assume GOOD_ONE : good 1",
        "derive AT_ONE : specialise RULE at 1",
        "derive FINE_ONE : mp AT_ONE GOOD_ONE",
        "derive AT_ZERO : specialise RULE at 0",
        "show FINE_ONE"
      )
    )
    val page = withClue(session.transcript + "\n")(reported(session.entries.last))

    page should include("# FINE_ONE")
    page should not include "no fact named"

    // The two assumptions are NAMED on the page rather than counted as axioms nobody holds, which
    // is what the session's own facts being in front of the library buys. Without it the page says
    // of an unnamed axiom that `Library.of` holds no classical axiom, which is a true sentence
    // about something else.
    page should include("RULE")
    page should include("GOOD_ONE")

    // And the account is this theorem's rather than the transcript's. `AT_ZERO` is a step of the
    // same session, recorded in the same script, and it is not part of how `FINE_ONE` was reached.
    //
    // Asserted beside the step that IS part of it, printed by the same renderer at the same size:
    // an absence read off an instrument that printed nothing at all would look exactly like this
    // one. The form is the page's own, which sets a sequent for reading rather than for reading
    // back, so it is `\\mathrm{good}(1)` and not `good 1`; that is what the page shows a reader and
    // asserting the other spelling is asserting about a renderer nothing here uses.
    page should include("\\mathrm{good}(1)")
    page should not include "\\mathrm{good}(0)"
  }

  it should "still answer with the library's page for a name the library holds" in {
    // The control the card asks for by name: a guard on the new case alone passes on a `show` that
    // has stopped looking in the library at all.
    reported(fresh.runAll(Vector("show ABS_TRIANGLE")).entries.last) should include("# ABS_TRIANGLE")
  }

  it should "name both places it looked when neither of them holds the name" in {
    // The half that is right whatever is decided about what `show` reaches. A reader who spelled a
    // name wrong and a reader whose name is somewhere else get different sentences.
    val session = fresh.runAll(Vector("prove SQ : !x:real. 0 <= x * x", "show NOPE"))
    val text = reported(session.entries.last)

    text should include("no fact named NOPE")
    text should include("SQ")
    text should include("library")
  }
}
