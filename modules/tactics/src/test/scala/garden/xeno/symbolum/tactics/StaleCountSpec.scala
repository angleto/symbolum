package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.tactics.StaleCount.*

import java.nio.file.{Files, Paths}
import scala.jdk.CollectionConverters.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The pieces of [[StaleCount]], each pointed at an input whose answer is known before it is run.
 *
 * The check itself runs in CI over a change, which no test here can be, so what is held here is
 * that each half reads what it says it reads: the counting over sources written for the purpose and
 * over every enumeration of this repository, the reading of prose over a sentence that must be
 * found and the sentences beside it that must not, and the choice of base over each event.
 *
 * It was seen red on the change that motivated it, outside this suite since that needs history: on
 * 2026-11-13, from `d47d4901` to `6c98f0d7`, where `Refutation.Outcome` went from seven cases to
 * eight, it named 18 of the 19 sentences that still said seven, and nothing else. The nineteenth
 * named `docs/adr/0005` rather than the type, which is outside what it reads by construction.
 */
class StaleCountSpec extends AnyFlatSpec with Matchers {

  private def count(source: String): Map[String, Int] =
    enumerations("modules/x/src/main/scala/Thing.scala", source).map(e => e.name -> e.cases).toMap

  "Counting" should "count the declarations extending a sealed trait, across a constructor spanning lines" in {
    val source =
      """object Thing {
        |  sealed trait Outcome
        |  final case class Found(at: Int) extends Outcome
        |  final case class Inconclusive(
        |      first: Int,
        |      second: Int
        |  ) extends Outcome {
        |    def size: Int = first + second
        |  }
        |  case object Nothing extends Outcome // a trailing note extends Outcome in prose only
        |}
        |""".stripMargin
    count(source) shouldBe Map("Outcome" -> 3)
  }

  it should "count a sealed child as its own leaves, which is what a sentence about the cases counts" in {
    val source =
      """sealed trait Answer
        |final case class Yes(n: Int) extends Answer
        |sealed abstract class Refusal extends Answer
        |case object Unread extends Refusal
        |case object Undecided extends Refusal
        |""".stripMargin
    count(source) shouldBe Map("Answer" -> 3, "Refusal" -> 2)
  }

  it should "count the names an enum's own case lines declare, and no case inside a method" in {
    val braces =
      """enum Rule {
        |  case Identity, Literals
        |  case Factor(depth: Int) extends Rule
        |  def isFold: Boolean = this match {
        |    case Literals => true
        |    case _ => false
        |  }
        |}
        |""".stripMargin
    val indented =
      """object Holder {
        |  enum Why:
        |    case Hidden
        |    case Refused(reason: String)
        |
        |    def text: String = this match
        |      case Hidden => "hidden"
        |      case Refused(r) => r
        |  val after = 1
        |}
        |""".stripMargin
    count(braces) shouldBe Map("Rule" -> 3)
    count(indented) shouldBe Map("Why" -> 2)
    count("enum Kind { case Definition, Theorem }\n") shouldBe Map("Kind" -> 2)
  }

  it should "name a nested enumeration by its file and a top-level one by its own name as well" in {
    val nested = enumerations("modules/x/src/main/scala/Refutation.scala", "object Refutation {\n  sealed trait Outcome\n}\n")
    val top = enumerations("modules/x/src/main/scala/Config.scala", "enum Rule {\n  case A\n}\n")
    nested.map(_.names) shouldBe Vector(Set("Refutation"))
    top.map(_.names) shouldBe Vector(Set("Config", "Rule"))
  }

  it should "find every enumeration this repository declares, each with at least one case" in {
    val root = Paths.get("").toAbsolutePath
    if (!Files.isDirectory(root.resolve("modules"))) fail(s"no `modules/` directory under $root")
    val sources = Files.walk(root.resolve("modules")).iterator().asScala.toVector
      .filter(path => path.toString.endsWith(".scala") && path.toString.contains("/src/main/"))
    val declaration = """(?m)^[ \t]*(?:[\w\[\]]+[ \t]+)*(?:sealed[ \t]+(?:\w+[ \t]+)*(?:trait|class)|enum)[ \t]+(\w+)""".r
    val read = sources.map { path =>
      val text = garden.xeno.symbolum.scan.Comments.withoutComments(Files.readString(path))
      (root.relativize(path).toString, declaration.findAllMatchIn(text).map(_.group(1)).toVector,
        enumerations(root.relativize(path).toString, Files.readString(path)))
    }
    val declared = read.map(_._2.length).sum
    // A floor, so that a walk finding nothing cannot pass: 73 declarations on 2026-11-13.
    declared should be >= 50
    read.foreach { case (file, names, found) =>
      withClue(file) {
        found.map(_.name).distinct.sorted shouldBe names.distinct.sorted
        found.filter(_.cases == 0) shouldBe empty
      }
    }
  }

  private val refutation = Enumeration("modules/tactics/src/main/scala/Refutation.scala", "Outcome", 8, topLevel = false)
  private val eight = Moved(refutation, was = 7)

  private def comments(source: String): Vector[Paragraph] = prose("modules/x/src/main/scala/Other.scala", source)

  "Reading prose" should "find the old count beside the name across a line break of a comment run" in {
    val found = copies("Other.scala", comments(
      """  // That is the same discipline `Refutation` keeps
        |  // seven outcomes for, one level up.
        |  val x = 1
        |""".stripMargin), eight)
    found.map(_.line) shouldBe Vector(2)
  }

  it should "find it in a docstring, in digits, and after a colon in the same sentence" in {
    val doc =
      """/**
        | * Seven outcomes and seven is the point: `Refutation` keeps them apart.
        | */
        |""".stripMargin
    copies("Other.scala", comments(doc), eight).map(_.line) shouldBe Vector(2)
    copies("Other.scala", comments("// `Refutation.Outcome` has 7 cases.\n"), eight) should have size 1
  }

  it should "not find a number that is not the old count, or one beyond the window, or in another sentence" in {
    val misses = Vector(
      "// `Refutation` keeps eight outcomes apart.",
      "// `Refutation` is the file, and one two three four five six words later come seven things.",
      "// `Refutation` keeps its outcomes apart. Seven lemmas arrived the same day.",
      "// `Cost` keeps seven answers apart.",
      "// `Outcome` keeps seven answers apart.",
      "// The seven are what `Refutation` kept until 2026-11-12, when the eighth arrived."
    )
    misses.foreach(line => withClue(line)(copies("Other.scala", comments(line + "\n"), eight) shouldBe empty))
  }

  it should "end a paragraph at a blank comment line, so a name and a number in two paragraphs do not meet" in {
    val two =
      """/**
        | * About `Refutation`
        | *
        | * seven unrelated things.
        | */
        |""".stripMargin
    copies("Other.scala", comments(two), eight) shouldBe empty
  }

  it should "read no string literal, which is code" in {
    copies("Other.scala", comments("val s = \"`Refutation` keeps seven\"\n"), eight) shouldBe empty
  }

  it should "read the comments of sources and scripts, and Markdown outside the decision records" in {
    readsProse("docs/numerics.md") shouldBe true
    readsProse("AGENTS.md") shouldBe true
    readsProse("modules/tactics/src/test/scala/X.scala") shouldBe true
    readsProse("build.sbt") shouldBe true
    readsProse("tools/coverage-gate.sh") shouldBe true
    readsProse("tools/sbt") shouldBe true
    readsProse(".github/workflows/ci.yml") shouldBe true
    readsProse("docs/adr/0077-a-point.md") shouldBe false
    readsProse("tools/verify/README.txt") shouldBe false
    readsProse("LICENSE") shouldBe false
    val md = prose("docs/x.md", "The outcomes are kept apart the way `Refutation`\nkeeps its seven apart.\n")
    copies("docs/x.md", md, eight).map(_.line) shouldBe Vector(2)
  }

  it should "read the comment runs of a script, and neither its code nor its first line" in {
    val script =
      """#!/bin/sh -- `Refutation` keeps seven
        |# That is the distinction `Refutation` keeps
        |# between seven answers, one floor down.
        |echo "`Refutation` keeps seven"
        |#
        |# seven things, in a paragraph of their own.
        |""".stripMargin
    copies("tools/x.sh", prose("tools/x.sh", script), eight).map(_.line) shouldBe Vector(3)
  }

  "Comparing two versions" should "report an enumeration whose count moved and none that did not" in {
    val before = "object Refutation {\n  sealed trait Outcome\n  case object A extends Outcome\n}\nenum Same {\n  case X\n}\n"
    val after = "object Refutation {\n  sealed trait Outcome\n  case object A extends Outcome\n  case object B extends Outcome\n}\nenum Same {\n  case X\n}\n"
    val file = "modules/t/src/main/scala/Refutation.scala"
    moved(Vector((file, Some(before), Some(after)))).map(m => (m.enumeration.name, m.was, m.now)) shouldBe
      Vector(("Outcome", 1, 2))
    moved(Vector((file, None, Some(after)), (file, Some(before), None))) shouldBe empty
  }

  "The base" should "be the commit before a push, a pull request's base, and nothing for any other event" in {
    base("push", "abc123", "") shouldBe Some("abc123")
    base("pull_request", "abc123", "def456") shouldBe Some("def456")
    base("push", "0000000000000000000000000000000000000000", "") shouldBe None
    base("pull_request", "abc123", "") shouldBe None
    base("workflow_dispatch", "abc123", "def456") shouldBe None
  }
}
