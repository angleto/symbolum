package garden.xeno.symbolum.published

import garden.xeno.symbolum.kernel.Derivation
import garden.xeno.symbolum.tactics.{Elaborate, Session}
import java.io.ByteArrayOutputStream
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import scala.jdk.CollectionConverters.*

/**
 * The published documents check, their page is what the code says, and publishing refuses what it
 * says it refuses.
 *
 * The refusals are asserted on documents written here for the purpose rather than on the published
 * ones, which all pass: a gate seen only passing is a gate nobody has seen work.
 */
class PublishedSpec extends AnyFlatSpec with Matchers {

  private lazy val elaborate: Elaborate = Elaborate.standard

  private def locate(relative: String): Path = {
    def search(directory: Path, remaining: Int): Path =
      if (remaining < 0) fail(s"could not find $relative from ${Paths.get("").toAbsolutePath}")
      else {
        val candidate = directory.resolve(relative)
        if (Files.exists(candidate)) candidate else search(directory.getParent, remaining - 1)
      }
    search(Paths.get("").toAbsolutePath, 5)
  }

  "Every published document" should "check, with every import resolved" in {
    val published = Published.of(elaborate)
    withClue(published.left.getOrElse(Vector.empty).mkString("\n\n")) { published.isRight shouldBe true }
    val documents = published.toOption.get.documents
    documents.map(_.name).toSet shouldBe Published.Names.toSet
    documents.foreach(document => document.report.ok shouldBe true)
    // Something is published, and something imports something: the property below is about these.
    documents.flatMap(_.report.entries) should not be empty
    documents.exists(_.imports.nonEmpty) shouldBe true
  }

  it should "be on disk under the name the list gives, and the list should name every one on disk" in {
    val directory = locate(s"modules/published/src/main/resources/${Published.Resources}")
    val onDisk = Files.list(directory).iterator().asScala.map(_.getFileName.toString).filter(_.endsWith(".sym"))
      .map(_.stripSuffix(".sym")).toSet
    onDisk shouldBe Published.Names.toSet
    Published.Names.distinct shouldBe Published.Names
  }

  it should "be a library: every theorem and definition, under its document, resting on no hypothesis" in {
    val published = Published.standard
    published.documents.foreach { document =>
      val declared = document.report.entries.map(_.name).toSet
      published.library.from(document.name).map(_.name).toSet shouldBe declared
    }
    published.library.entries.foreach(entry => entry.theorem.hypotheses shouldBe empty)
    published.library.entries.map(_.name).distinct.size shouldBe published.library.entries.size
  }

  it should "assert no axiom beyond the chain's" in {
    Published.standard.scope.theory.axioms shouldBe elaborate.chain.widest.theory.axioms
  }

  it should "state every theorem in the one theory, though each was proved in its document's own" in {
    // What makes one theory meaningful: a theorem proved where its document was checked is about
    // the constants the one theory holds, because a defined constant carries its definition
    // (`docs/adr/0008`). A theorem about a constant the one theory does not hold would be foreign.
    val published = Published.standard
    published.library.entries.foreach { entry =>
      withClue(entry.name) { Derivation.foreignTo(published.scope.theory, entry.theorem).clean shouldBe true }
    }
    // The control: the same theorems against the chain alone, where DOUBLE is not a constant.
    published.library.entries.exists(entry => !Derivation.foreignTo(elaborate.chain.widest.theory, entry.theorem).clean) shouldBe true
  }

  "docs/published.md" should "be what the command produces" in {
    val text = new String(Files.readAllBytes(locate(Published.Page)), "UTF-8")
    val generated = Published.Section.partOf(text).fold(why => fail(why), identity)
    withClue(s"${Published.Page} is not what the code says; run:\n  ${Published.Command}\n") {
      generated shouldBe Published.standard.listing.trim
    }
    Published.Names.foreach(name => generated should include(s"## $name"))
  }

  "The command that writes it" should "leave an up-to-date page alone, and put a disturbed region back" in {
    // Run on a copy, twice: the first run takes the branch that writes nothing, so alone it would
    // pass over a command whose write is broken; the second starts from a wrong region and has to
    // write the right one.
    val committed = new String(Files.readAllBytes(locate(Published.Page)), StandardCharsets.UTF_8)
    val copy = Files.createTempFile("symbolum-published-", ".md")
    try {
      Files.write(copy, committed.getBytes(StandardCharsets.UTF_8))
      quietly(Published.main(Array(copy.toString))) should include("already what the code says")
      new String(Files.readAllBytes(copy), StandardCharsets.UTF_8) shouldBe committed

      val disturbed = Published.Section.spliced(committed, "this is not what the code says").fold(why => fail(why), identity)
      Files.write(copy, disturbed.getBytes(StandardCharsets.UTF_8))
      quietly(Published.main(Array(copy.toString))) should include("rewritten")
      new String(Files.readAllBytes(copy), StandardCharsets.UTF_8) shouldBe committed
    } finally { Files.deleteIfExists(copy); () }
  }

  "The checker command" should "let a document outside the repository import a published one" in {
    // The reason the command lives in this module. The document sits in a directory of its own,
    // with no Parity.sym or Doubling.sym beside it, and cites a theorem Doubling proves, reached
    // through Parity's import of it.
    val directory = Files.createTempDirectory("symbolum-check-")
    val importing = directory.resolve("Mine.sym")
    val alone = directory.resolve("Alone.sym")
    val claim = "theorem MINE : DOUBLE (SUC 0) = SUC (SUC (DOUBLE 0)) by exact DOUBLE_SUC"
    try {
      Files.write(importing, s"import Parity\n$claim".getBytes(StandardCharsets.UTF_8))
      Files.write(alone, claim.getBytes(StandardCharsets.UTF_8))
      val checked = Check.run(Vector(importing.toString))
      withClue(checked.out.mkString("\n")) {
        checked.status shouldBe 0
        checked.out.exists(_.contains("MINE: proved")) shouldBe true
        checked.out.exists(_.contains("imported: Doubling.DOUBLE_SUC")) shouldBe true
      }
      // The control: the same claim without the import does not check, so the import is what did.
      Check.run(Vector(alone.toString)).status shouldBe 1
    } finally {
      Files.deleteIfExists(importing)
      Files.deleteIfExists(alone)
      Files.deleteIfExists(directory)
      ()
    }
  }

  "The notebook command's session" should "import a published document and cite what it proves" in {
    // What the command adds to the notebook of `tactics`, asserted on the session it serves. The
    // control is the same theorem without the import, which does not check, so the import did it.
    val claim = "theorem MINE : DOUBLE (SUC 0) = SUC (SUC (DOUBLE 0)) by exact DOUBLE_SUC"
    val imported = Notebook.session.run("import Parity")
    // Every entry carrying a theorem is a fact, the definition of DOUBLE included, as in a document.
    val facts = Published.standard.documents.map(_.report.entries.count(_.theorem.isDefined)).sum
    facts should be > 4
    imported.entries.last.outcome shouldBe Session.Outcome.Extended(s"imported Doubling, Parity: $facts facts")
    imported.run(claim).entries.last.outcome match {
      case Session.Outcome.Proved(_, _, _, price) => price.map(_.imported) shouldBe Some(Vector("Doubling.DOUBLE_SUC"))
      case other => fail(s"expected a proof, got $other")
    }
    val alone = Notebook.session.run(claim)
    alone.entries.last.outcome should not be a[Session.Outcome.Proved]
    alone.state.fact("MINE") shouldBe empty
  }

  /** Run something that prints, keeping its output out of the suite's log and returning it. */
  private def quietly(body: => Unit): String = {
    val captured = new ByteArrayOutputStream()
    Console.withOut(captured)(body)
    captured.toString(StandardCharsets.UTF_8)
  }

  /** Publishing documents given here as text. */
  private def publish(documents: (String, String)*): Either[Vector[String], Published] = {
    val texts = documents.toMap
    Published.of(elaborate, documents.map(_._1).toVector, texts.get)
  }

  "Publishing" should "refuse a document that does not check, and say which" in {
    val refused = publish("Good" -> "theorem G : T by auto", "Bad" -> "theorem B : 0 = 1:num by arith")
    refused.isLeft shouldBe true
    refused.left.toOption.get should have size 1
    refused.left.toOption.get.head should startWith("Bad does not check:\nline 1: theorem B: incomplete")
    // The control: the good one alone publishes.
    publish("Good" -> "theorem G : T by auto").isRight shouldBe true
  }

  it should "refuse one name defined in two documents that do not import each other" in {
    val refused = publish("P" -> "define SHARED_C := 1:num", "Q" -> "define SHARED_C := 2:num")
    // Each checks on its own, since neither sees the other.
    refused.left.toOption.get.exists(_.contains("does not check")) shouldBe false
    refused.left.toOption.get.exists(_.startsWith("Q: SHARED_C cannot be defined beside the other published documents")) shouldBe true
  }

  it should "refuse one theorem name declared in two documents that do not import each other" in {
    val refused = publish("P" -> "theorem SHARED_T : T by auto", "Q" -> "theorem SHARED_T : T by auto")
    refused shouldBe Left(Vector("SHARED_T is declared in P and Q"))
  }

  it should "refuse a name it cannot read, and an import of a document it does not publish" in {
    Published.of(elaborate, Vector("Absent"), _ => None) shouldBe Left(Vector("Absent: no document of that name could be read"))
    // `Other` has a text, and is not among the names published, so the import does not reach it.
    val texts = Map("Main" -> "import Other\ntheorem M : T by auto", "Other" -> "theorem O : T by auto")
    val refused = Published.of(elaborate, Vector("Main"), texts.get)
    refused.left.toOption.get.head should include("line 1: import: no document named Other")
  }

  it should "give a published document to an import from anywhere, and nothing else" in {
    Published.Names.foreach(name => Published.source(name) should not be empty)
    Published.source("NotPublished") shouldBe None
  }
}
