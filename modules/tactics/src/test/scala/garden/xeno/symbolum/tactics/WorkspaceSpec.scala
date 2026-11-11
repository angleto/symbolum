package garden.xeno.symbolum.tactics

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Documents that import each other: what each one sees, in which order they are checked, and every
 * way an import can fail to be usable.
 *
 * The property everything else rests on is the first test's pair: a document sees what it imports
 * and nothing else. Each "it sees" assertion has its "it does not" beside it, checked in the same
 * run, because a workspace that let every document see everything checked before it would pass every
 * positive assertion here and make a document's imports say nothing about what it rests on.
 */
class WorkspaceSpec extends AnyFlatSpec with Matchers {
  import Elaborate.{Report, Status}

  private lazy val elaborate: Elaborate = Elaborate.standard

  /** A workspace over documents given as text by name. */
  private def workspace(documents: (String, String)*): Workspace = {
    val texts = documents.toMap.map { case (name, text) => name -> text.stripMargin }
    new Workspace(elaborate, texts.get)
  }

  private val Twice =
    """define TWICE_N := \n:num. n + n
      |theorem TWICE_N_ZERO : TWICE_N 0 = 0
      |proof
      |  rewrite TWICE_N
      |  by arith
      |qed"""

  private def report(checked: Workspace.Checked, name: String): Report =
    checked.find(name).map(_.report).getOrElse(fail(s"$name was not checked"))

  "A document" should "see what it imports, directly or through another import, and nothing else" in {
    val checked = workspace(
      "A" -> Twice,
      "B" -> "import A\ntheorem USES : TWICE_N 0 = 0 by exact TWICE_N_ZERO",
      "C" -> "import B\ntheorem THROUGH : TWICE_N 0 = 0 by exact TWICE_N_ZERO",
      "D" -> "theorem ALONE : T by exact TWICE_N_ZERO\ntheorem CONSTANT : TWICE_N 0 = 0 by auto"
    ).check(Vector("C", "D", "A"))

    // Each after what it imports, and otherwise in the order first reached: C, D, A, B, of which D
    // is the first with nothing left to wait for.
    checked.done.map(_.name) shouldBe Vector("D", "A", "B", "C")
    report(checked, "B").ok shouldBe true
    report(checked, "C").ok shouldBe true
    report(checked, "B").entries.head.price.map(_.imported) shouldBe Some(Vector("A.TWICE_N_ZERO"))
    report(checked, "C").entries.head.price.map(_.imported) shouldBe Some(Vector("A.TWICE_N_ZERO"))
    // The walk stops at an imported theorem: what A's proof used is A's price, not B's. The input
    // that would make this vacuous is a proof that used nothing, and A's did.
    report(checked, "B").entries.head.price.map(_.facts) shouldBe Some(Vector.empty)
    report(checked, "A").entries(1).price.map(_.facts).getOrElse(Vector.empty) should not be empty
    report(checked, "B").entries.head.price.map(_.axioms) shouldBe report(checked, "A").entries(1).price.map(_.axioms)

    // D was checked after A in the same run and does not import it, so A is not there for it.
    val alone = report(checked, "D")
    alone.ok shouldBe false
    alone.entries.head.problems.head.reason should startWith("no fact named TWICE_N_ZERO")
    alone.entries.head.problems.head.reason should not include "nor does any document it imports"
    // Nor is A's constant: TWICE_N reads as a variable, so nothing says what type its 0 is.
    alone.entries(1).problems.head.reason should startWith("the type of the numeral 0 is not determined")
  }

  it should "be checked after everything it imports, whatever order it was asked for in" in {
    val documents = Seq("A" -> Twice, "B" -> "import A\ntheorem USES : TWICE_N 0 = 0 by exact TWICE_N_ZERO")
    workspace(documents*).check(Vector("B")).done.map(_.name) shouldBe Vector("A", "B")
    workspace(documents*).check(Vector("B", "A")).done.map(_.name) shouldBe Vector("A", "B")
  }

  it should "say which documents it imports when a name is not found among them" in {
    val checked = workspace("A" -> Twice, "B" -> "import A\ntheorem T : TWICE_N 0 = 0 by exact NOWHERE").check(Vector("B"))
    report(checked, "B").entries.head.problems.head.reason shouldBe
      "no fact named NOWHERE: this proof holds no fact of its own, this document declares none of that name, " +
        "nor does any document it imports (A), and the library has no lemma of that name"
  }

  "An import" should "be a problem of the importing document when it names nothing, itself, or a cycle" in {
    val checked = workspace(
      "Missing" -> "import Nope\ntheorem T : T by auto",
      "Self" -> "import Self\ntheorem T : T by auto",
      "F" -> "import G\ntheorem TF : T by auto",
      "G" -> "import F\ntheorem TG : T by auto"
    ).check(Vector("Missing", "Self", "F"))

    report(checked, "Missing").imports.map(p => (p.line, p.reason, p.next)) shouldBe
      Vector((1, "no document named Nope", Some("the import looks for Nope.sym beside this document")))
    report(checked, "Self").imports.map(_.reason) shouldBe Vector("Self imports itself")
    report(checked, "F").imports.map(_.reason) shouldBe Vector("G imports F, directly or through another import, so the two form a cycle")
    report(checked, "G").imports.map(_.reason) shouldBe Vector("F imports G, directly or through another import, so the two form a cycle")
    // The declarations are still checked, and they are proved: an import problem marks the document.
    Vector("Missing", "Self", "F", "G").foreach { name =>
      report(checked, name).entries.map(_.status) shouldBe Vector(Status.Proved)
      report(checked, name).ok shouldBe false
    }
  }

  it should "bring what a failing document did prove, and say a failed one failed" in {
    val checked = workspace(
      "H" -> "theorem GOOD : 0 + 0 = 0:num by arith\ntheorem BAD : 0 = 1:num by arith",
      "I" -> "import H\ntheorem USES_GOOD : 0 + 0 = 0:num by exact GOOD\ntheorem USES_BAD : 0 = 1:num by exact BAD"
    ).check(Vector("I"))

    val importer = report(checked, "I")
    importer.imports.map(_.reason) shouldBe Vector("H does not check, so only what it did prove is imported")
    importer.entries.map(_.status) shouldBe Vector(Status.Proved, Status.Incomplete)
    importer.entries(1).problems.head.reason shouldBe "BAD is declared in H on line 2 and its proof did not check, so it is not a fact"
  }

  it should "be a problem when two imported documents declare one name, theorem or definition" in {
    val checked = workspace(
      "J" -> "theorem SAME : T by auto\ndefine CONST_X := 1:num",
      "K" -> "theorem SAME : T by auto\ndefine CONST_X := 2:num",
      "L" -> "import J\nimport K\ntheorem USES : T by exact SAME"
    ).check(Vector("L"))

    report(checked, "L").imports.map(p => (p.line, p.reason)) shouldBe Vector(
      (2, "SAME is declared in both J and K, which this document imports"),
      (2, "CONST_X is declared in both J and K, which this document imports"))
    // The first is kept, so the proof citing the name is still checked against one fact.
    report(checked, "L").entries.map(_.status) shouldBe Vector(Status.Proved)
  }

  it should "be reported unresolved, not dropped, when a document is checked on its own" in {
    val alone = elaborate.check("import Doubling\ntheorem T : T by auto")
    alone.imports.map(p => (p.line, p.reason)) shouldBe
      Vector((1, "`import Doubling` resolves to nothing: this document was checked on its own"))
    alone.ok shouldBe false
    elaborate.check("theorem T : T by auto").imports shouldBe empty
  }

  "A declaration" should "not take the name of a library lemma or of an imported fact" in {
    val checked = workspace(
      "A" -> Twice,
      "M" -> """import A
               |theorem ADD_SYM : T by auto
               |define NUM_ADD_SYM := 1:num
               |theorem TWICE_N_ZERO : T by auto
               |theorem FREE : T by auto""".stripMargin
    ).check(Vector("M"))

    val entries = report(checked, "M").entries
    entries.map(e => (e.name, e.status)) shouldBe Vector(
      ("ADD_SYM", Status.Refused), ("NUM_ADD_SYM", Status.Refused), ("TWICE_N_ZERO", Status.Refused), ("FREE", Status.Proved))
    entries(0).problems.head.reason should startWith("ADD_SYM is a lemma of the library (")
    entries(1).problems.head.reason should startWith("NUM_ADD_SYM is a lemma of the library (")
    entries(2).problems.head.reason shouldBe "TWICE_N_ZERO is declared in A, which this document imports"
  }

  "The report" should "print and encode its import problems and what a proof imported" in {
    val checked = workspace("A" -> Twice, "B" -> "import A\nimport Nope\ntheorem USES : TWICE_N 0 = 0 by exact TWICE_N_ZERO")
      .check(Vector("B"))
    val b = report(checked, "B")
    val text = b.render
    text should include("line 2: import: no document named Nope\n  try: the import looks for Nope.sym beside this document")
    text should include("  imported: A.TWICE_N_ZERO")
    text should endWith("1 declarations: 1 proved, 0 defined, 0 not proved, 1 import problems")
    b.json should include(""""imports":[{"line":2,"message":"no document named Nope"""")
    b.json should include(""""imported":["A.TWICE_N_ZERO"]""")
    // And neither key where there is nothing to say.
    report(checked, "A").json should not include "\"imports\""
    report(checked, "A").json should not include "\"imported\""
  }

  "`cases h from F`" should "split a fact that is a disjunction into its two cases" in {
    val proved = elaborate.check(
      """theorem SWAP : !p:bool. !q:bool. p \/ q ==> q \/ p
        |proof
        |  fix p q
        |  assume h
        |  cases k from h
        |  case left:
        |    right
        |    by exact k
        |  case right:
        |    left
        |    by exact k
        |  end
        |qed""".stripMargin)
    proved.ok shouldBe true
  }

  it should "refuse a fact that is not a disjunction, and branches with other labels" in {
    val notOne = elaborate.check(
      """theorem T : !p:bool. p ==> p
        |proof
        |  fix p
        |  assume h
        |  cases k from h
        |  case left:
        |    by exact k
        |  case right:
        |    by exact k
        |  end
        |qed""".stripMargin)
    notOne.entries.head.problems.map(p => (p.line, p.reason)) shouldBe
      Vector((5, "`cases k from h` wants h to be a disjunction A \\/ B, and it is p"))

    val labels = elaborate.check(
      """theorem T : !p:bool. !q:bool. p \/ q ==> q \/ p
        |proof
        |  fix p q
        |  assume h
        |  cases k from h
        |  case pos:
        |    by auto
        |  case neg:
        |    by auto
        |  end
        |qed""".stripMargin)
    labels.ok shouldBe false
    labels.entries.head.problems.head.line shouldBe 6
  }

  "The command line" should "read an import beside the file, and a published one before it" in {
    val directory = Files.createTempDirectory("workspace")
    def write(name: String, text: String): Path =
      Files.write(directory.resolve(name), text.stripMargin.getBytes(StandardCharsets.UTF_8))
    try {
      write("Local.sym", Twice)
      write("Pub.sym", "theorem SHADOWED : F by auto")
      val main = write("Main.sym",
        "import Local\nimport Pub\ntheorem USES : TWICE_N 0 = 0 by exact TWICE_N_ZERO\ntheorem USES_PUB : T by exact FROM_PUB")
      val published = Map("Pub" -> "theorem FROM_PUB : T by auto")

      val outcome = Check.run(Vector(main.toString), elaborate, published.get)
      withClue(outcome.out.mkString("\n")) { outcome.status shouldBe 0 }
      outcome.err shouldBe Vector(s"$main: Pub.sym beside it is not read, because Pub is a published document and the import reads that one")

      // Without the published documents the file beside it is read, and its theorem is not FROM_PUB.
      val without = Check.run(Vector(main.toString), elaborate)
      without.status shouldBe 1
      without.err shouldBe empty
      without.out.mkString("\n") should include("no fact named FROM_PUB")
    } finally {
      Files.list(directory).forEach(Files.delete(_))
      Files.delete(directory)
    }
  }

  "A directory" should "answer a document by its name and nothing that is not one" in {
    val directory = Files.createTempDirectory("workspace")
    try {
      Files.write(directory.resolve("Here.sym"), "theorem T : T by auto".getBytes(StandardCharsets.UTF_8))
      val source = Workspace.directory(elaborate, directory).source
      source("Here") shouldBe Some("theorem T : T by auto")
      source("Absent") shouldBe None
      source("../Here") shouldBe None
      source("Here.sym") shouldBe None
    } finally {
      Files.list(directory).forEach(Files.delete(_))
      Files.delete(directory)
    }
  }
}
