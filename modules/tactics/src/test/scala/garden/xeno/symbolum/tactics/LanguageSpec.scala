package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path, Paths}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Every example in `docs/language.md` checks, so the reference cannot describe a language that is not this one.
 *
 * The examples are the fenced blocks tagged `sym`. A block tagged `sym` alone is checked as a
 * document of its own; a block tagged `sym NAME` is the document `NAME`, which another named block
 * may import, and the named blocks are checked together through `Workspace` as the files of one
 * directory would be. Each must prove or define everything it declares and resolve every import.
 * The counts of blocks found are asserted to be above zero, because a change to the fence tag would
 * otherwise turn this into a test over nothing that passes.
 */
class LanguageSpec extends AnyFlatSpec with Matchers {

  private def locate(relative: String): Path = {
    def search(directory: Path, remaining: Int): Path =
      if (remaining < 0) fail(s"could not find $relative from ${Paths.get("").toAbsolutePath}")
      else {
        val candidate = directory.resolve(relative)
        if (Files.exists(candidate)) candidate else search(directory.getParent, remaining - 1)
      }
    search(Paths.get("").toAbsolutePath, 5)
  }

  /** Every `sym` block: the line it starts on, the name its fence gives if any, and its text. */
  private lazy val blocks: Vector[(Int, Option[String], String)] = {
    val lines = new String(Files.readAllBytes(locate("docs/language.md")), "UTF-8").linesIterator.toVector
    val opens = lines.indices.filter(i => lines(i).trim == "```sym" || lines(i).trim.startsWith("```sym "))
    opens.map { start =>
      val end = lines.indexWhere(_.trim == "```", start + 1)
      val name = Some(lines(start).trim.stripPrefix("```sym").trim).filter(_.nonEmpty)
      (start + 1, name, lines.slice(start + 1, end).mkString("\n"))
    }.toVector
  }

  private lazy val examples: Vector[(Int, String)] = blocks.collect { case (line, None, text) => (line, text) }

  private lazy val named: Map[String, (Int, String)] = blocks.collect { case (line, Some(name), text) => name -> (line, text) }.toMap

  "docs/language.md" should "hold examples, so the check below is about something" in {
    examples.size should be > 3
    named.size should be > 1
  }

  it should "name each document once, so an import in it means one block" in {
    blocks.flatMap(_._2).distinct.size shouldBe blocks.flatMap(_._2).size
  }

  it should "describe documents that import each other and check together" in {
    val checked = new Workspace(Elaborate.standard, name => named.get(name).map(_._2)).check(named.keys.toVector.sorted)
    val failing = checked.done.filterNot(_.report.ok).map(done =>
      s"the document ${done.name} at line ${named(done.name)._1} of docs/language.md:\n${done.report.render}")
    withClue(failing.mkString("\n\n")) { failing shouldBe empty }
    checked.done.map(_.name).toSet shouldBe named.keySet
    checked.done.exists(_.parsed.imports.nonEmpty) shouldBe true
  }

  it should "describe a language in which every one of its examples checks" in {
    val elaborate = Elaborate.standard
    val failing = examples.flatMap { case (line, text) =>
      val report = elaborate.check(text)
      if (report.ok) None else Some(s"the example at line $line of docs/language.md:\n${report.render}")
    }
    withClue(failing.mkString("\n\n")) { failing shouldBe empty }
  }
}
