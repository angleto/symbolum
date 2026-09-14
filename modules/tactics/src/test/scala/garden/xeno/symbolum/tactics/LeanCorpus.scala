package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path, Paths}
import java.security.MessageDigest
import scala.jdk.CollectionConverters.*

/**
 * How a vendored Lean file is cut into declarations, shared by the corpora that read one.
 *
 * The rule is here rather than in each suite because it is the first place a count can go quietly
 * wrong, and two copies of it would drift into two different benchmarks that look like one. What
 * each suite decides for itself is which declarations it is entitled to count and how to read what
 * they claim; this decides only where a declaration begins and ends.
 *
 * Nothing here interprets Lean. It is layout and brackets.
 */
object LeanCorpus {

  /** One top-level declaration: what it claims, and the tactic that closed it. */
  final case class Declaration(line: Int, keyword: String, statement: String, proof: String)

  /**
   * Split a file into declarations.
   *
   * A declaration starts at column zero with `example`, `theorem` or `lemma` and continues while
   * the lines below it are indented, which is Lean's own layout convention and is what these files
   * follow throughout. A blank line or a new column-zero line ends it.
   */
  def declarations(text: String): Vector[Declaration] = {
    val keywords = Vector("example", "theorem", "lemma")
    val lines = text.split("\n", -1).toVector

    lines.zipWithIndex.collect {
      case (first, index) if keywords.exists(first.startsWith) =>
        val body =
          lines.drop(index + 1).takeWhile(line => line.trim.nonEmpty && line.head.isWhitespace)
        val whole = (first +: body).mkString("\n")
        val keyword = first.takeWhile(!_.isWhitespace)

        whole.indexOf(":= by") match {
          // No `:= by` means the declaration was closed by a term rather than a tactic, so it is
          // not a claim about any tactic and falls out at the next step.
          case -1 => Declaration(index + 1, keyword, whole, "")
          case marker =>
            Declaration(
              index + 1,
              keyword,
              whole.substring(0, marker),
              whole.substring(marker + ":= by".length)
            )
        }
    }
  }

  def withoutComments(text: String): String = {
    val withoutBlocks = text.replaceAll("(?s)/-.*?-/", " ")
    withoutBlocks
      .split("\n")
      .map(line => line.indexOf("--") match { case -1 => line; case at => line.substring(0, at) })
      .mkString(" ")
  }

  /** The proof as one line, so a tactic and a proof that merely mentions it can be told apart. */
  def tactic(declaration: Declaration): String =
    withoutComments(declaration.proof).trim.split("\\s+").mkString(" ")

  /**
   * The binder groups and the goal: everything after the `:` that follows the binders.
   *
   * Binders are the `(…)`, `{…}` and `[…]` groups between the keyword and that colon, and they are
   * found by counting brackets of all three kinds at once, which is what lets a universe annotation
   * like `PUnit.{u + 1}` inside a parenthesis not end the group early. The goal is what is left.
   */
  def split(declaration: Declaration): Option[(Vector[String], String)] = {
    val text = declaration.statement
    var at = declaration.keyword.length
    val groups = collection.mutable.ListBuffer.empty[String]

    def skipSpace(): Unit = while (at < text.length && text(at).isWhitespace) at += 1

    skipSpace()
    if (declaration.keyword != "example") {
      while (at < text.length && !text(at).isWhitespace) at += 1 // the name
      skipSpace()
    }

    var scanning = true
    while (scanning) {
      skipSpace()
      if (at < text.length && "({[".contains(text(at))) {
        val start = at
        var depth = 0
        var closed = false
        while (at < text.length && !closed) {
          val c = text(at)
          if ("({[".contains(c)) depth += 1
          else if (")}]".contains(c)) {
            depth -= 1
            if (depth == 0) closed = true
          }
          at += 1
        }
        if (closed) groups += text.substring(start, at) else scanning = false
      } else scanning = false
    }

    skipSpace()
    Option.when(at < text.length && text(at) == ':')(
      (groups.toVector, text.substring(at + 1).trim)
    )
  }

  /** The goal alone, for a caller that has no use for the binders. */
  def goalOf(declaration: Declaration): Option[String] = split(declaration).map(_._2)

  /* --------------------------------------------------------------------- reading */

  def read(relative: String): Option[String] =
    locate(relative).map(path => Files.readAllLines(path).asScala.mkString("\n"))

  def hashOf(relative: String): Option[String] =
    locate(relative).map { path =>
      MessageDigest
        .getInstance("SHA-256")
        .digest(Files.readAllBytes(path))
        .map(byte => f"$byte%02x")
        .mkString
    }

  /** Walk up from wherever the tests were started, as `DocumentationSpec` does and for its reason. */
  def locate(relative: String): Option[Path] = {
    def search(directory: Path, remaining: Int): Option[Path] =
      if (remaining < 0 || directory == null) None
      else {
        val candidate = directory.resolve(relative)
        if (Files.exists(candidate)) Some(candidate) else search(directory.getParent, remaining - 1)
      }

    search(Paths.get("").toAbsolutePath, 5)
  }
}
