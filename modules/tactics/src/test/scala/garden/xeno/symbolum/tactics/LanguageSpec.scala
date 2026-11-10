package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path, Paths}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Every example in `docs/language.md` checks, so the reference cannot describe a language that is not this one.
 *
 * The examples are the fenced blocks tagged `sym`. Each is checked as a document of its own and must
 * prove or define everything it declares. The count of blocks found is asserted to be above zero,
 * because a change to the fence tag would otherwise turn this into a test over nothing that passes.
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

  private lazy val examples: Vector[(Int, String)] = {
    val lines = new String(Files.readAllBytes(locate("docs/language.md")), "UTF-8").linesIterator.toVector
    val opens = lines.indices.filter(i => lines(i).trim == "```sym")
    opens.map { start =>
      val end = lines.indexWhere(_.trim == "```", start + 1)
      (start + 1, lines.slice(start + 1, end).mkString("\n"))
    }.toVector
  }

  "docs/language.md" should "hold examples, so the check below is about something" in {
    examples.size should be > 3
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
