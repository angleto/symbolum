package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.scan.Comments

import java.nio.file.{Files, Path, Paths}
import scala.sys.process.{Process, ProcessLogger}
import scala.util.Try

/**
 * A count of an enumeration's cases written in prose, read again on the day the count moves.
 *
 * == What it is for ==
 * On 2026-11-12 `Refutation.Outcome` gained an eighth case, and nineteen sentences across the
 * repository still said the outcomes were seven. None of them was new: each had been true when it
 * was written and became false when the case was added, in files the change did not open. Most were
 * written across a line break, so a search line by line did not see them either.
 *
 * So the question this asks is narrow on purpose: **in a change that moved the number of cases of
 * an enumeration, does any prose beside that enumeration's name still say the old number?** It
 * reads the change, not the tree. The other way to ask was a gate over the whole population, every
 * number word near the name of any enumeration, and it was measured before this was written: on
 * 2026-11-13 it read 90 sentences on a tree where every live copy of the outcomes' count had been
 * removed, about 35 of them a count of cases and the rest numbers about something else, so about 55
 * would have needed an entry in a list of exceptions. The rate at which new such sentences appear
 * in `modules/` was about one in seven weeks. The harm came from old sentences made false, and that
 * is the moment this reads.
 *
 * What it costs in false alarms was measured over the line's own history on 2026-11-13: every
 * commit on the first-parent line of `7.0`, merges included and each against its first parent. 19
 * of them moved the count of some enumeration, and two drew a report: `6c98f0d7`, where it named 18
 * stale sentences, and `c46b13c0`, where `Session.Outcome` went from four to five and a sentence in
 * `DocumentationSpec` about finding "four sentences in `Session.scala`" was read as a count of it.
 * One wrong report in that history, against the population gate's 55 standing ones.
 *
 * == What counts as a case, and as the name ==
 * A `sealed` trait or class counts the declarations in its own file that extend it, a sealed child
 * counting as its own leaves, which is what a sentence means by "the outcomes":
 * `Refutation.Outcome` reads eight. An `enum` counts the names its `case` lines declare at the
 * body's own indentation, so `case A, B` is two and a `case` inside a method of the enum is none.
 * Both read code with the comments off, through [[Comments]], which is this repository's one
 * decision about what a comment is.
 *
 * The name a sentence uses is the file's: `Refutation`, not `Outcome`, which half the files under
 * `tactics` declare. A top-level enumeration whose name differs from its file's adds its own name.
 * A mention is the name as a word, inside backticks or a link or bare, or the first segment of a
 * dotted path, `Refutation.Outcome` included.
 *
 * == What counts as a copy ==
 * The old count, as a word from two to twenty or in digits, within six words of a mention and in
 * the same sentence, a sentence ending at a full stop, a semicolon, a question mark or an
 * exclamation mark. Not at a colon: "Seven outcomes and seven is the point: `Refutation` keeps them
 * apart" was one of the nineteen until 2026-11-13, and with the colon as a boundary it was the one
 * missed. Prose is the comments of every Scala source under `modules/`, joined into one paragraph
 * per run of comment lines and ended by a blank one, and every Markdown file outside `docs/adr/`.
 * Joining is the repair the census needed: of the nineteen, most were written across a line break.
 *
 * Two kinds of sentence are photographs and are not read. A decision record keeps what was measured
 * when the decision was taken, which is why `docs/adr/` is outside. And a sentence carrying a date
 * in the form 2026-11-12 is a statement about that day, which stays true when the count moves
 * again.
 *
 * == What it does not cover ==
 * A copy written after the count moved, of a count that is true: that is the population gate above,
 * and it was not built. A count that moved twice within one push is compared at its two ends. A
 * sentence counting the cases more than six words away from the name, or in a sentence of its own
 * that names nothing, such as "It has seven." after one naming the type. A sentence naming the
 * count through something other than the type: the nineteenth said `docs/adr/0005` "keeps seven
 * answers apart", and a record is not an enumeration this can count. A file that moved
 * or an enumeration renamed in the change is a new enumeration with no old count. A number in a
 * string literal is not prose and is not read.
 *
 * == Running it ==
 * `tools/sbt "tactics/Test/runMain garden.xeno.symbolum.tactics.StaleCount"` compares the working
 * tree with `HEAD~1`, and a revision after the class name replaces that base. CI calls it with
 * `--event NAME before=SHA base=SHA`, and which of the two it compares from is decided here rather
 * than in the workflow: a push from `before`, a pull request from `base`, anything else names no
 * change. The keys are there because an empty value would vanish from sbt's argument list and move
 * the next one into its place. It exits 0 when no copy is left, 1 naming each copy, and 2 when it
 * could not read the base, which is never reported as a pass.
 */
object StaleCount {

  /** An enumeration, keyed by the file declaring it and its own name, with the cases it has. */
  final case class Enumeration(file: String, name: String, cases: Int, topLevel: Boolean) {
    def stem: String = Paths.get(file).getFileName.toString.stripSuffix(".scala")

    /** The words a sentence uses for it. The class comment says why `Outcome` alone is not. */
    def names: Set[String] = if (topLevel) Set(stem, name) else Set(stem)
  }

  /** An enumeration whose count differs between the base and the working tree. */
  final case class Moved(enumeration: Enumeration, was: Int) {
    def now: Int = enumeration.cases
  }

  /** A sentence still saying the old count, with the line the number is on. */
  final case class Copy(file: String, line: Int, moved: Moved, sentence: String) {
    def describe: String =
      s"$file:$line: `${moved.enumeration.stem}.${moved.enumeration.name}` went from ${moved.was} " +
        s"cases to ${moved.now} in this change, and this still says ${moved.was}: $sentence"
  }

  private val Declaration = """\b(class|object|trait|enum)\s+(\w+)""".r
  private val Parent = """\b(?:extends|with)\s+([A-Z]\w*)""".r
  private val EnumLine = """^(\s*)(?:[\w\[\]]+\s+)*enum\s+(\w+)""".r.unanchored

  /** Every enumeration declared in `source`, with its number of cases. */
  def enumerations(file: String, source: String): Vector[Enumeration] = {
    val code = Comments.withoutComments(source)
    sealedOnes(file, code) ++ enums(file, code)
  }

  /**
   * The sealed traits and classes, each with its leaves in this file.
   *
   * Declarations and parent clauses are read in the order they occur, and a parent belongs to the
   * declaration last opened, which is right across a constructor whose parameters span lines,
   * `Refutation.Inconclusive` being one.
   */
  private def sealedOnes(file: String, code: String): Vector[Enumeration] = {
    val lines = code.split("\n", -1).toVector
    val modifier = Set("sealed", "abstract", "final", "case", "private")
    val events = lines.flatMap { line =>
      val declared = Declaration.findAllMatchIn(line).map { m =>
        val modifiers = line.substring(0, m.start).trim.split("\\s+").toVector.filter(_.nonEmpty)
        val top = !line.headOption.exists(_.isWhitespace) && modifiers.forall(modifier)
        (m.start, Left((m.group(2), modifiers.contains("sealed"), top)))
      }
      val parents = Parent.findAllMatchIn(line).map(m => (m.start, Right(m.group(1))))
      (declared ++ parents).toVector.sortBy(_._1).map(_._2)
    }
    val (_, edges, sealedNames) =
      events.foldLeft((Option.empty[String], Vector.empty[(String, String)], Map.empty[String, Boolean])) {
        case ((_, edges, sealedNames), Left((name, isSealed, top))) =>
          val next =
            if (isSealed) sealedNames + (name -> (top || sealedNames.getOrElse(name, false)))
            else sealedNames
          (Some(name), edges, next)
        case ((Some(current), edges, sealedNames), Right(parent)) if current != parent =>
          (Some(current), edges :+ (parent -> current), sealedNames)
        case (state, Right(_)) => state
      }
    val children = edges.groupMap(_._1)(_._2).view.mapValues(_.distinct).toMap
    def leaves(name: String, seen: Set[String]): Int =
      children.getOrElse(name, Vector.empty).map { child =>
        if (sealedNames.contains(child) && !seen.contains(child) && children.contains(child))
          leaves(child, seen + child)
        else 1
      }.sum
    sealedNames.toVector.sortBy(_._1).map { case (name, top) =>
      Enumeration(file, name, leaves(name, Set(name)), top)
    }
  }

  /** The enums, each with the names its own `case` lines declare. Both braces and indentation. */
  private def enums(file: String, code: String): Vector[Enumeration] = {
    val lines = code.split("\n", -1).toVector
    def indent(line: String): Int = line.takeWhile(_ == ' ').length
    lines.zipWithIndex.collect { case (EnumLine(lead, name), at) => (lead.length, name, at) }.map {
      case (lead, name, at) =>
        val header = lines(at)
        val open = header.indexOf('{', header.indexOf(name))
        val body =
          if (open >= 0) {
            val depths = lines.drop(at).scanLeft(0) { (depth, line) =>
              depth + line.count(_ == '{') - line.count(_ == '}')
            }
            val closing = depths.drop(1).indexWhere(_ <= 0)
            // `enum Kind { case Definition, Theorem }` opens and closes its body on one line.
            if (closing == 0) Vector(header.substring(open + 1, header.lastIndexOf('}')))
            else lines.slice(at + 1, if (closing < 0) lines.length else at + closing)
          } else
            lines.drop(at + 1).takeWhile(line => line.trim.isEmpty || indent(line) > lead)
        val members = body.filter(_.trim.nonEmpty)
        val level = if (members.isEmpty) 0 else members.map(indent).min
        val cases = members
          .filter(line => indent(line) == level && line.trim.startsWith("case "))
          .map { line =>
            val declared = line.trim.stripPrefix("case ").takeWhile(c => c != '(' && c != '[' && c != '{')
            declared.split("\\bextends\\b").head.split(",").count(_.trim.nonEmpty)
          }
          .sum
        Enumeration(file, name, cases, lead == 0)
    }
  }

  /** A paragraph of prose, joined, with the line each of its characters came from. */
  final case class Paragraph(text: String, lines: Vector[Int]) {
    def lineAt(offset: Int): Int = lines(math.min(math.max(offset, 0), lines.length - 1))
  }

  private val Marker = """^\s*(?:/\*\*|/\*|\*/|\*(?!/)|//+)?\s?""".r

  /** The prose of a file: the comment runs of a Scala source, the paragraphs of a Markdown one. */
  def prose(file: String, source: String): Vector[Paragraph] = {
    val pieces: Vector[(Int, String)] =
      if (file.endsWith(".scala"))
        Comments.split(source).map { line =>
          val text = Marker.replaceFirstIn(line.comment, "").stripSuffix("*/").trim
          (line.number, if (line.isComment) text else "\u0000")
        }
      else source.linesIterator.zipWithIndex.map { case (line, at) => (at + 1, line.trim) }.toVector
    // A paragraph ends at a line with no prose on it: code, a blank comment line, a blank line.
    val (done, open) = pieces.foldLeft((Vector.empty[Vector[(Int, String)]], Vector.empty[(Int, String)])) {
      case ((done, open), (number, text)) =>
        if (text.isEmpty || text == "\u0000") (if (open.isEmpty) done else done :+ open, Vector.empty)
        else (done, open :+ (number, text))
    }
    (if (open.isEmpty) done else done :+ open).map { run =>
      val text = run.map(_._2).mkString(" ")
      val lines = run.flatMap { case (number, piece) => Vector.fill(piece.length + 1)(number) }
      Paragraph(text, lines)
    }
  }

  private val Words = Vector(
    "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven",
    "twelve", "thirteen", "fourteen", "fifteen", "sixteen", "seventeen", "eighteen", "nineteen", "twenty"
  )
  private val Dated = """\d{4}-\d{2}-\d{2}""".r
  private val Window = 6

  /** The spellings of `count` a sentence would use: the digits, and the word from two to twenty. */
  def spellings(count: Int): Set[String] =
    Set(count.toString) ++ (if (count >= 2 && count < Words.length) Set(Words(count)) else Set.empty)

  private def bare(token: String): String =
    token.toLowerCase.replaceAll("""^[^a-z0-9]+|[^a-z0-9]+$""", "")

  private def mentions(token: String, names: Set[String]): Boolean = {
    val word = token.replaceAll("""^[^A-Za-z0-9_]+""", "").replaceAll("""'s\b.*$""", "")
    val first = word.takeWhile(c => c.isLetterOrDigit || c == '_')
    names.contains(first)
  }

  /** Every sentence of `paragraphs` saying `moved.was` within the window of the name. */
  def copies(file: String, paragraphs: Vector[Paragraph], moved: Moved): Vector[Copy] = {
    val said = spellings(moved.was)
    val names = moved.enumeration.names
    paragraphs.flatMap { paragraph =>
      val text = paragraph.text
      val ends = """(?<=[.;?!])\s+""".r.findAllMatchIn(text).map(m => (m.start, m.end)).toVector
      val bounds = (0 +: ends.map(_._2)).zip(ends.map(_._1) :+ text.length)
      bounds.flatMap { case (start, end) =>
        val sentence = text.substring(start, end)
        val tokens = """\S+""".r.findAllMatchIn(sentence).toVector
        if (Dated.findFirstIn(sentence).nonEmpty) Vector.empty
        else
          tokens.zipWithIndex.collect {
            case (token, at)
                if said.contains(bare(token.matched)) &&
                  tokens
                    .slice(math.max(0, at - Window), at + Window + 1)
                    .exists(t => mentions(t.matched, names)) =>
              Copy(file, paragraph.lineAt(start + token.start), moved, sentence)
          }.take(1)
      }
    }
  }

  /** Where prose is read: comments under `modules/`, and Markdown outside the decision records. */
  def readsProse(file: String): Boolean =
    (file.startsWith("modules/") && file.endsWith(".scala")) ||
      (file.endsWith(".md") && !file.startsWith("docs/adr/"))

  /** What moved between two versions of each changed file: `(path, before, after)`. */
  def moved(changes: Vector[(String, Option[String], Option[String])]): Vector[Moved] =
    changes.flatMap {
      case (file, Some(before), Some(after)) =>
        val was = enumerations(file, before).map(e => e.name -> e.cases).toMap
        enumerations(file, after).collect {
          case now if was.get(now.name).exists(_ != now.cases) => Moved(now, was(now.name))
        }
      case _ => Vector.empty
    }

  /** The base a CI event compares from, or `None` where the event names no change. */
  def base(event: String, before: String, pullBase: String): Option[String] = {
    val named = event match {
      case "push" => before
      case "pull_request" => pullBase
      case _ => ""
    }
    Option(named).filter(sha => sha.nonEmpty && !sha.forall(_ == '0'))
  }

  def main(args: Array[String]): Unit = sys.exit(run(args.toVector))

  private def run(args: Vector[String]): Int = {
    def keyed(key: String): String =
      args.collectFirst { case arg if arg.startsWith(s"$key=") => arg.stripPrefix(s"$key=") }.getOrElse("")
    val chosen = args match {
      case "--event" +: event +: _ =>
        val chosen = base(event, keyed("before"), keyed("base"))
        if (chosen.isEmpty)
          println(s"stale-count: the event `$event` names no change to read, so nothing was compared.")
        chosen
      case revision +: _ => Some(revision)
      case _ => Some("HEAD~1")
    }
    chosen.fold(0)(compare)
  }

  private def git(root: Path, arguments: String*): Option[String] =
    Try(Process("git" +: "-C" +: root.toString +: arguments).!!(ProcessLogger(_ => ()))).toOption

  private def compare(base: String): Int = {
    val root = git(Paths.get("").toAbsolutePath, "rev-parse", "--show-toplevel")
      .map(top => Paths.get(top.trim))
    root.flatMap(r => git(r, "rev-parse", "--verify", "--quiet", s"$base^{commit}").map(_ => r)) match {
      case None =>
        println(s"stale-count: could not read `$base` as a commit of this repository, " +
          "so nothing was compared. " +
          "A shallow checkout has no history to read; this is not a pass.")
        2
      case Some(root) =>
        val changed = git(root, "diff", "--name-only", base, "--", "modules").getOrElse("")
          .linesIterator.filter(f => f.contains("/src/main/") && f.endsWith(".scala")).toVector
        def current(file: String): Option[String] =
          Some(root.resolve(file)).filter(Files.isRegularFile(_)).map(Files.readString)
        val movedHere = moved(changed.map(f => (f, git(root, "show", s"$base:$f"), current(f))))
        if (movedHere.isEmpty) {
          println(s"stale-count: no enumeration changed its number of cases since `$base`, " +
            s"across ${changed.length} changed sources.")
          0
        } else {
          val files = git(root, "ls-files", "--cached", "--others", "--exclude-standard").getOrElse("")
            .linesIterator.filter(readsProse).toVector
          val found = files.flatMap { file =>
            current(file).toVector.flatMap { source =>
              val paragraphs = prose(file, source)
              movedHere.flatMap(m => copies(file, paragraphs, m))
            }
          }
          movedHere.foreach(m =>
            println(s"stale-count: `${m.enumeration.stem}.${m.enumeration.name}` has ${m.now} cases, " +
              s"against ${m.was} at `$base`."))
          found.foreach(copy => println(copy.describe))
          println(s"stale-count: ${found.length} sentence(s) still say the old count, " +
            s"across ${files.length} files of prose read.")
          if (found.isEmpty) 0 else 1
        }
    }
  }
}
