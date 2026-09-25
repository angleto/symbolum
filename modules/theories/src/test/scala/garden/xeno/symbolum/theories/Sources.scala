package garden.xeno.symbolum.theories

import garden.xeno.symbolum.scan.Comments

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

/**
 * This repository's own source files, for the assertions that are about where something is written
 * rather than about what it proves.
 *
 * Two claims this development makes are of that kind: that the trusted base is the kernel plus
 * the files `RealSpec` lists as its foundation, and that the module supplying `~(n = 0)` sits below
 * the ring rather than above it. Neither can be settled by proving anything, both stop being true
 * silently, and a document saying them is a document that gets believed after it goes stale.
 */
object Sources {

  /** The directory holding `build.sbt`, from wherever the tests were started. */
  def repositoryRoot(): Path = {
    def search(directory: Path, remaining: Int): Path =
      if (directory == null || remaining < 0)
        sys.error("could not find build.sbt above the working directory")
      else if (Files.exists(directory.resolve("build.sbt"))) directory
      else search(directory.getParent, remaining - 1)

    search(Paths.get("").toAbsolutePath, 5)
  }

  /** Every Scala file that ships, which is every `src/main` source under `modules`. */
  def main(): Vector[Path] = {
    val root = repositoryRoot()
    Files
      .walk(root.resolve("modules"))
      .iterator()
      .asScala
      .filter { path =>
        val text = path.toString
        text.endsWith(".scala") && text.contains("/src/main/") && !text.contains("/target/")
      }
      .toVector
  }

  /** A source file's path relative to the repository root, which is how a test names one. */
  def relative(path: Path): String = repositoryRoot().relativize(path).toString

  /**
   * A source file with its comments removed.
   *
   * Needed because the interesting question is what the code depends on, and a file that explains
   * why it does not depend on something has to name it in order to say so. Reading the prose as
   * code would make every such explanation into the thing it warns about.
   *
   * The decision of what a comment is moved to `garden.xeno.symbolum.scan.Comments` on 2026-09-16,
   * and what moved with it is a defect this site had: the pair of substitutions here dropped from a
   * `//` to the end of the line whether or not the slashes were inside a string literal, and on
   * that day three lines of `Notebook.scala` were exactly that. The census this feeds is
   * `RealSpec`'s over `assertAxiom`, so the shape of the defect was a line declaring an axiom that
   * a census does not see.
   */
  def code(relative: String): String =
    Comments.withoutComments(Files.readString(repositoryRoot().resolve(relative)))
}
