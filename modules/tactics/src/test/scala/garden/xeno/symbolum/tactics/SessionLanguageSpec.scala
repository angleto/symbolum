package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.theories.Chain
import java.nio.file.{Files, Path, Paths}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The proof language in a notebook session: `theorem` checked by the checker's elaborator against
 * the session, and `import` taking a document whole or not at all (`docs/adr/0074`).
 *
 * Each property is asserted beside the input that would make it vacuous: a cell cut wrong would
 * still produce entries, so the count of entries is asserted; an import that half-applied would
 * still leave a session, so the theory is compared with the one before.
 */
class SessionLanguageSpec extends AnyFlatSpec with Matchers {

  /** Two documents, the second importing the first, and one that does not check. */
  private val documents: Map[String, String] = Map(
    "A" ->
      """define TWICE := \n:num. n + n
        |theorem TWICE_ZERO : TWICE 0 = 0
        |proof
        |  rewrite TWICE
        |  by arith
        |qed""".stripMargin,
    "B" ->
      """import A
        |theorem TWICE_ZERO_AGAIN : TWICE 0 = 0 by exact TWICE_ZERO""".stripMargin,
    "Broken" -> "theorem NOT_SO : 0 = 1:num by arith"
  )

  private lazy val fresh: Session = Session.of(Chain.standard, documents.get)

  /** A theorem proved by induction-free steps, named as asked, as the lines a session is given. */
  private def proof(name: String, claim: String = "!n:num. n + 0 = n", body: String = "n + 0 = n"): Vector[String] =
    Vector(s"theorem $name : $claim", "proof", "  fix n", s"  show $body by arith", "qed")

  private def lines(text: String): Vector[String] = text.linesIterator.toVector

  /** The last entry's outcome. */
  private def last(session: Session): Session.Outcome = session.entries.last.outcome

  "A theorem in a session" should "be checked by the elaborator and held as a fact" in {
    val session = fresh.runAll(proof("ZERO_RIGHT"))
    last(session) match {
      case Session.Outcome.Proved(name, theorem, _, price) =>
        name shouldBe "ZERO_RIGHT"
        theorem.hypotheses shouldBe empty
        price.map(_.inferences).getOrElse(0) should be > 0
      case other => fail(s"expected a proof, got $other")
    }
    session.state.fact("ZERO_RIGHT") should not be empty
    // And a later command reaches it by name, which is what holding it means.
    last(session.run("derive AT_ONE : specialise ZERO_RIGHT at 1")) shouldBe a[Session.Outcome.Proved]
  }

  it should "run to its qed when pasted with its proof, so a step is not read as a command" in {
    // `show` is a session command and a proof step; inside the proof it is the step.
    val pasted =
      """theorem ZERO_RIGHT : !n:num. n + 0 = n
        |proof
        |  fix n
        |  show n + 0 = n by arith
        |qed
        |ask !x:real. x + 0 = x""".stripMargin
    val session = fresh.runAll(lines(pasted))
    session.entries.map(_.command.getClass.getSimpleName) shouldBe Vector("Theorem", "Ask")
    session.entries.head.outcome shouldBe a[Session.Outcome.Proved]
  }

  it should "count the proof of every have inside it, and run to the end when never closed" in {
    val nested =
      """theorem T : !n:num. n + 0 = n
        |proof
        |  fix n
        |  have h : n + 0 = n
        |  proof
        |    by arith
        |  qed
        |  by exact h
        |qed""".stripMargin
    val session = fresh.runAll(lines(nested))
    session.entries should have size 1
    session.entries.head.outcome shouldBe a[Session.Outcome.Proved]

    val open = fresh.runAll(lines("theorem U : !n:num. n + 0 = n\nproof\n  fix n\nask !x:real. x = x"))
    // Unclosed, so it runs to the end and is one cell, and the reader says what it met: inside a
    // proof `ask` is a step, and no step is called that.
    open.entries should have size 1
    last(open) match {
      case Session.Outcome.Refused(reason, _) => reason should startWith("line 4: no step `ask`")
      case other => fail(s"expected a refusal, got $other")
    }
  }

  it should "show every problem with its goal, and leave the session holding nothing new" in {
    val session = fresh.runAll(lines(
      """theorem WRONG : !n:num. n + 1 = n
        |proof
        |  fix n
        |  by arith
        |qed""".stripMargin))
    last(session) match {
      case Session.Outcome.Incomplete(name, problems) =>
        name shouldBe "WRONG"
        problems should not be empty
        problems.head.goal.getOrElse("") should include("|- n + 1 = n")
      case other => fail(s"expected an incomplete proof, got $other")
    }
    session.state.named shouldBe empty
    session.render should include("|- n + 1 = n")
  }

  it should "read the session's own constants, cite its assumptions, and name them in what it rests on" in {
    val session = fresh.runAll(Vector("declare p : bool", "assume P : p", "theorem Q : p by exact P"))
    last(session) match {
      case Session.Outcome.Proved(_, theorem, _, price) =>
        price.map(_.document) shouldBe Some(Vector("P"))
        // The citation is where the price stops, and not where what it rests on stops.
        session.entries.last.restsOn(session.base) should have size 1
        Derivation.cited(theorem) shouldBe Set("P")
      case other => fail(s"expected a proof, got $other")
    }
    session.render should include("from this session: P")
  }

  it should "refuse a name the session already holds, saying the session holds it" in {
    val session = fresh.runAll(proof("T") ++ proof("T", "!n:num. 0 + n = n", "0 + n = n"))
    last(session) match {
      case Session.Outcome.Incomplete(_, problems) => problems.head.reason shouldBe "this session already declares T"
      case other => fail(s"expected a refusal, got $other")
    }
  }

  it should "refuse a cell that is not one theorem, and an import written inside one" in {
    last(fresh.run("theorem")) shouldBe a[Session.Outcome.Refused]
    last(fresh.runAll(proof("T") :+ "theorem")) shouldBe a[Session.Outcome.Refused]
  }

  "The transcript of a session with a proof in it" should "replay to the same facts" in {
    val session = fresh.runAll(lines(
      """declare p : bool
        |assume P : p
        |theorem T : !n:num. n + 0 = n
        |proof
        |  fix n
        |  by arith
        |qed
        |theorem Q : p by exact P""".stripMargin))
    val replayed = fresh.runAll(lines(session.transcript))
    replayed.commands shouldBe session.commands
    replayed.state.named.map(_._1) shouldBe Vector("P", "T", "Q")
    replayed.state.named.map(_._2) shouldBe session.state.named.map(_._2)
  }

  "An import" should "make a document's definitions in the session and hold its theorems, with what it imports" in {
    val session = fresh.run("import B")
    last(session) match {
      case Session.Outcome.Extended(what) => what shouldBe "imported A, B: 3 facts"
      case other => fail(s"expected the session to grow, got $other")
    }
    session.state.documents shouldBe Vector("A", "B")
    session.state.theory.constants.keySet should contain("TWICE")
    // Cited by a theorem, it is priced as imported, under its document.
    val cited = session.run("theorem MINE : TWICE 0 = 0 by exact TWICE_ZERO")
    last(cited) match {
      case Session.Outcome.Proved(_, _, _, price) => price.map(_.imported) shouldBe Some(Vector("A.TWICE_ZERO"))
      case other => fail(s"expected a proof, got $other")
    }
    // And a document already in the session is not made twice.
    last(session.run("import A")) shouldBe Session.Outcome.Extended("A is already imported")
  }

  it should "change nothing when any of it is refused" in {
    // The session already defines TWICE, differently, so A cannot be made in it.
    val before = fresh.run("define TWICE := \\n:num. n")
    val after = before.run("import B")
    last(after) match {
      case Session.Outcome.Refused(reason, _) => reason should include("TWICE, defined in A, cannot be defined in this session")
      case other => fail(s"expected a refusal, got $other")
    }
    after.state.theory shouldBe before.state.theory
    after.state.imported.facts shouldBe empty
    after.state.documents shouldBe empty

    last(fresh.run("import Broken")) match {
      case Session.Outcome.Refused(reason, _) => reason should startWith("Broken does not check")
      case other => fail(s"expected a refusal, got $other")
    }
    last(fresh.run("import Nowhere")) shouldBe Session.Outcome.Refused(
      "no document named Nowhere", Some("a session imports the documents its command can read: the published ones"))
  }

  it should "refuse a fact whose name the session already holds" in {
    val held = fresh.runAll(proof("TWICE_ZERO"))
    held.state.fact("TWICE_ZERO") should not be empty
    val after = held.run("import A")
    last(after) match {
      case Session.Outcome.Refused(reason, _) => reason shouldBe "TWICE_ZERO, declared in A, is a name this session already holds"
      case other => fail(s"expected a refusal, got $other")
    }
    after.state.documents shouldBe empty
  }

  it should "be refused inside a theorem cell, where it would change the theory mid-cell" in {
    val session = fresh
    val withImport = Session.Command.Theorem("import A\ntheorem U : 0 + 0 = 0:num by arith")
    last(session.run(withImport)) match {
      case Session.Outcome.Incomplete(_, problems) => problems.head.reason should include("in a session an import is a command of its own")
      case other => fail(s"expected the import refused, got $other")
    }
  }

  "The notebook example in docs/language.md" should "run as the cells it says it is, each one landing" in {
    def locate(relative: String): Path = {
      def search(directory: Path, remaining: Int): Path =
        if (remaining < 0) fail(s"could not find $relative from ${Paths.get("").toAbsolutePath}")
        else {
          val candidate = directory.resolve(relative)
          if (Files.exists(candidate)) candidate else search(directory.getParent, remaining - 1)
        }
      search(Paths.get("").toAbsolutePath, 5)
    }
    val reference = new String(Files.readAllBytes(locate("docs/language.md")), "UTF-8").linesIterator.toVector
    val section = reference.indexWhere(_ == "## In the notebook")
    withClue("docs/language.md has no section `## In the notebook`, which this reads: ") { section should be >= 0 }
    val open = reference.indexWhere(_.trim == "```", section)
    val example = reference.slice(open + 1, reference.indexWhere(_.trim == "```", open + 1))

    val session = fresh.runAll(example)
    withClue(s"${session.render}\n") {
      // The page says four cells, and that `show` inside the proof is a step and not a cell.
      session.entries should have size 4
      session.entries.map(_.outcome).collect { case refused: Session.Outcome.Refused => refused } shouldBe empty
      session.entries.map(_.outcome).collect { case incomplete: Session.Outcome.Incomplete => incomplete } shouldBe empty
      session.state.fact("ZERO_RIGHT") should not be empty
    }
  }
}
