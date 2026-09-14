package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The imperative constructs this repository has decided not to write, as a scan rather than a habit.
 *
 * Scala is a functional language and the code here is written functionally: no `var`, no `while`,
 * no `return`, no `null`, no `asInstanceOf`. That was 73, 27, 11, 2 and 17 across the tree on
 * 2026-09-12 and reached zero the same night, and the reason it is a test rather than a closed task
 * is that the way back is one hurried line. `scratch/style_count.py` is the same count with a
 * per-module table for reading; this is the floor under it.
 *
 * == What makes a scan like this pass without looking at anything ==
 *
 * Two ways, and both are asserted against below rather than hoped away.
 *
 * The first is **finding nothing to read**: a wrong root, a build that moved the sources, a walk
 * that silently returns an empty stream. A census with no subjects is green. So the scan reports
 * how many files and how many lines of code it looked at, and a floor under both fails before the
 * forbidden-construct assertion can pass vacuously.
 *
 * The second is **a pattern that matches nothing**, which is the failure a regular expression has
 * whenever it is edited. So each pattern is pointed at a line that must match and a line that must
 * not, and the comment-stripper is pointed at a comment it must drop and a line of code it must
 * keep. Those are the cases whose answers are known before the scan is believed, and the scan is
 * not believed without them.
 *
 * == The exception, and what an entry in it has to carry ==
 *
 * [[Excused]] is the list of sites that may hold a forbidden construct, and it is **empty**. A hot
 * numeric kernel in `modules/core` may be imperative if the mutation is confined to a private
 * function, the function's signature is pure, and it carries where it lives the measurement that
 * decided it, the alternative rejected and what it does not cover. "It seemed faster" is not a
 * measurement, and whoever has not measured the functional version does not have the exception. An
 * entry here is that measurement having been made, not permission to skip making it.
 */
class StyleSpec extends AnyFlatSpec with Matchers {

  private val Modules = Vector("kernel", "logic", "theories", "checker", "core", "tactics")

  /**
   * The constructs, by the name a reader would call them.
   *
   * `Array` and `throw new` are deliberately **not** here. Every `Array` left in the tree is the
   * `Array[String]` of a `main`, which is the JVM's signature and not a choice; every `throw new`
   * is a refusal at a boundary that cannot return one, and those are argued where they live.
   */
  private val Forbidden: Vector[(String, scala.util.matching.Regex)] = Vector(
    "var" -> """\bvar\s+[A-Za-z_]""".r,
    "while" -> """\bwhile\s*\(""".r,
    "return" -> """\breturn\b""".r,
    "null" -> """\bnull\b""".r,
    "asInstanceOf" -> """\basInstanceOf\b""".r
  )

  /** Sites allowed to hold one, each with the measurement that bought it. See the class comment. */
  private val Excused: Map[String, String] = Map.empty

  /**
   * Mutable state that carries none of the words above, by site.
   *
   * This is the half a count cannot do, and the reason it is here is that the count already missed
   * one: the lexer built its tokens through a `Vector.newBuilder` all the while the `var` column
   * read zero for `logic`, so "no `var`" was true and "holds no mutable state" was not, and nothing
   * distinguished the two. Each entry below says what the state is and why it is allowed to be
   * state; a new one fails this test until somebody writes the sentence.
   *
   * `java.util.regex` is not counted: a compiled `Pattern` is immutable and matching it allocates a
   * `Matcher` the caller never shares.
   */
  private val ReviewedMutableState: Map[String, String] = Map(
    "Derivation.scala" ->
      ("an identity-keyed set, so that two structurally equal theorems built by different " +
        "derivations count as two nodes; a `Set` on equality would fold `trans(refl p, refl p)` " +
        "into `refl p` and a test says so"),
    "Proof.scala" ->
      ("the same identity-keyed set and map for the printed proof's node numbering, plus a " +
        "`StringBuilder` for the text itself; the walk is iterative because the numeral " +
        "procedures chain hundreds of steps and a recursive one would meet the stack"),
    "Conv.scala" ->
      ("the reflexivity cache, bounded at 8192 against a measured 4287 distinct atoms in the " +
        "standard chain's 112 lemmas, read through `Option` at the boundary because the map is a " +
        "Java one and both of its misses are a `null`"),
    "Arbitrary.scala" ->
      ("pi and the two logarithms memoised per precision, because every reduction wants them and " +
        "a screening run asks a few thousand times; the alternative is a few thousand Machin series"),
    "Notebook.scala" ->
      ("one `AtomicReference` holding the current `Session`, which is the whole mutable state of " +
        "the server and is mutable because a page is a long-lived process and a session is not: " +
        "`Session` itself is immutable and every command returns a new one, so the reference is " +
        "swapped rather than written into, and `updateAndGet` is what keeps two requests from " +
        "interleaving a read and a write of it now that the server runs its exchanges on a pool")
  )

  private val Hidden: Vector[(String, scala.util.matching.Regex)] = Vector(
    "builder" -> """\bnewBuilder\b|\bStringBuilder\b""".r,
    "java map/set" ->
      ("""\bjava\.util\.(concurrent\.)?\w*(HashMap|HashSet)\b""" +
        """|\bjava\.util\.Collections\.newSetFromMap\b""" +
        """|\bConcurrentHashMap\b""").r,
    "atomic" -> """\bAtomic(Integer|Long|Reference|Boolean)\b|@volatile\b""".r
  )

  /**
   * The lines of a source that are code, dropping comments.
   *
   * String literals are not stripped, which is a known limit and the reason [[Forbidden]] holds no
   * pattern a docstring would write in prose: a construct named inside a string is counted, and the
   * cheapest defence against a false positive is to name constructs in comments rather than in
   * strings.
   */
  private def codeLines(text: String): Vector[(Int, String)] =
    text.linesIterator.zipWithIndex
      .foldLeft((Vector.empty[(Int, String)], false)) { case ((kept, inBlock), (line, index)) =>
        val trimmed = line.trim
        if (inBlock) (kept, !trimmed.contains("*/"))
        else if (trimmed.startsWith("/*")) (kept, !trimmed.contains("*/"))
        else if (trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.isEmpty)
          (kept, false)
        else (kept :+ ((index + 1, line)), false)
      }
      ._1

  private def sources: Vector[Path] =
    Modules.flatMap { module =>
      val root = Paths.get(s"modules/$module/src/main")
      if (!Files.exists(root)) Vector.empty
      else {
        val stream = Files.walk(root)
        try stream.iterator().asScala.toVector.filter(_.toString.endsWith(".scala"))
        finally stream.close()
      }
    }

  /* ---------------------------------------------------- the scan can see something */

  // Floors and not equalities: files and lines are added every day and this is not a size budget.
  // Measured on the night of 2026-09-12 at 118 files and 25251 lines of code, by this scan and by
  // `scratch/style_count.py` independently and to the line. Half of each is a floor that a tree
  // which had genuinely lost its sources could not clear.
  "The scan" should "have found the sources, which is the way a census like this passes for free" in {
    val files = sources
    withClue(s"files found: ${files.size}\n") {
      files.size should be >= 59
    }

    val lines = files.map(path => codeLines(Files.readString(path)).size).sum
    withClue(s"lines of code found: $lines\n") {
      lines should be >= 12000
    }

    info(s"${files.size} files, $lines lines of code")
  }

  it should "read a comment as a comment and a line of code as code" in {
    val sample =
      """/** A docstring that says var and while and null.
        |  * A continuation line that says return.
        |  */
        |// A line comment that says asInstanceOf.
        |val kept = 1
        |/* a one-line block that says var */
        |val alsoKept = 2""".stripMargin

    codeLines(sample).map(_._2.trim) shouldBe Vector("val kept = 1", "val alsoKept = 2")
  }

  it should "match each construct where it is written, and not where it is a longer word" in {
    val by = Forbidden.toMap

    by("var").findFirstIn("    private var index: Int = 0") shouldBe defined
    by("var").findFirstIn("  val variance = 1") shouldBe empty

    by("while").findFirstIn("      while (index < end) {") shouldBe defined
    by("while").findFirstIn("  val meanwhile = 1") shouldBe empty

    by("return").findFirstIn("        return Some(value)") shouldBe defined
    by("return").findFirstIn("  val returned = 1") shouldBe empty

    by("null").findFirstIn("  if (found == null) None") shouldBe defined
    by("null").findFirstIn("  val nullable = 1") shouldBe empty

    by("asInstanceOf").findFirstIn("  term.asInstanceOf[FVar]") shouldBe defined
    by("asInstanceOf").findFirstIn("  val asInstanceOfSomething = 1") shouldBe empty
  }

  /* ------------------------------------------------------------------ the census */

  "No source under modules/*/src/main" should "hold a var, a while, a return, a null or a cast" in {
    val found = for {
      path <- sources
      (number, line) <- codeLines(Files.readString(path))
      (name, pattern) <- Forbidden
      if pattern.findFirstIn(line).isDefined
      if !Excused.contains(path.getFileName.toString)
    } yield s"$name at $path:$number"

    withClue(s"${found.size} site(s):\n${found.mkString("\n")}\n") {
      found shouldBe empty
    }
  }

  it should "hold no mutable state a reader has not been told about" in {
    val found = for {
      path <- sources
      (_, line) <- codeLines(Files.readString(path))
      (_, pattern) <- Hidden
      if pattern.findFirstIn(line).isDefined
    } yield path.getFileName.toString

    val unreviewed = found.distinct.sorted.filterNot(ReviewedMutableState.contains)
    withClue(s"holding mutable state and not in the list: ${unreviewed.mkString(", ")}\n") {
      unreviewed shouldBe empty
    }

    // And the list is not passing by being a list of nothing: the four are really there. An entry
    // that stopped matching would mean the state moved or the pattern broke, and either way the
    // sentence beside it has stopped describing the file it names.
    val stale = ReviewedMutableState.keys.toVector.sorted.filterNot(found.contains)
    withClue(s"reviewed and no longer holding any: ${stale.mkString(", ")}\n") {
      stale shouldBe empty
    }
  }

  it should "excuse nothing silently" in {
    // The exception list is empty today. If it stops being, each entry says which measurement
    // bought it, and this reads that the sentence is there rather than that the key is.
    Excused.values.foreach(reason => reason.length should be > 40)
  }
}
