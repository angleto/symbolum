package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The source of this repository is written in English, as a scan rather than a habit.
 *
 * Identifiers, comments and log messages are English whatever language the interface or the
 * conversation around the work speaks, so that a search for a term finds every use of it and a
 * reader who joins later does not need the author's language. Half-translated code is worse than
 * either half: it produces identifiers and prose that no search finds, because the searcher guesses
 * the wrong language.
 *
 * == Why this exists, which is a measurement and not a principle ==
 *
 * On 2026-09-15 one commit appended a new entry to six running count ledgers and wrote **every one
 * of them in Italian**: four in `ProposeSpec`, one in `RediscoverySpec`, one in `LibrarySpec`.
 * Every earlier entry in the same ledgers was English, so each file switched language at its last
 * line. Nothing noticed. Nothing could: no test and no build step read a source file for the
 * language it was written in, and a reviewer reading a diff of one appended comment sees a comment.
 *
 * == Why it is a test and not a commit hook ==
 *
 * A hook lives in `.git/hooks`, which is not tracked, so it protects the clone it was installed in
 * and no other, and it is bypassed by a flag. This repository's guards are tests for that reason:
 * `StyleSpec` scans for imperative constructs, `Consistency` scans its own source for the name of
 * an inference rule, `DocumentationSpec` reads the module directories. A check outside the blocking
 * gate reads as protection and is not, which is the sentence `ci.yml` already carries about
 * triggers and which the same day proved again when a module missing from `root.aggregate` kept
 * sixteen tests from running for an hour while the build stayed green.
 *
 * == The three things that make the detector work, none of which is a better word list ==
 *
 * All three were measured against the six real blocks, which is the only reason to trust them.
 *
 *  - **Comment text only.** Matching over whole files lets identifiers and string literals vote. A
 *    lemma named `NUM_PRIME_POW_CANCEL` and a quoted term of art are not prose.
 *  - **One marker is enough.** An earlier threshold of two markers on one line silently dropped
 *    every single-line entry, which was two of the six blocks and the whole of the third file.
 *  - **The orthography this corpus actually uses.** Italian here is written in ASCII with a
 *    trailing apostrophe standing in for the accent, so a detector that looks for accented
 *    characters finds a third of it. Run against the six blocks, accents plus a short
 *    function-word list found three; the two rules together find all six. The forms themselves are
 *    enumerated in the rule below rather than written out here, because this paragraph is scanned
 *    too and the first draft of it failed this spec's own census.
 *
 * And the trap that produced the third one, because it will produce it again: after the first four
 * blocks were found and fixed the detector returned zero, which looked like completion and was the
 * threshold agreeing with the answer already in hand. **A detector tuned until it agrees with what
 * you already found has stopped being a measurement.** The fixtures below are the defence: each
 * rule is pointed at a line it must match and a line it must not, so an edit that quietly stops
 * matching fails here instead of passing everywhere.
 *
 * == What it does not do ==
 *
 * It does not detect unaccented prose in a language whose function words are not listed, and it
 * says nothing about user-facing text, which resolves from a catalogue by key and is a separate
 * obligation. A file that passes is not a file written in English. It is a file with no evidence of
 * being written in another one, and the distinction is the same one `Refutation` keeps seven
 * outcomes apart for.
 */
class SourceLanguageSpec extends AnyFlatSpec with Matchers {

  /**
   * Sites that may hold non-English prose, each with the reason.
   *
   * Empty, and an entry is a written reason rather than permission to skip writing one. A quoted
   * term of art with no English form, or a test fixture that is deliberately another language, are
   * the real cases. "It was quicker to write" is not one.
   */
  private val Excused: Map[String, String] = Map.empty

  /**
   * The markers, by the name a reader would call them.
   *
   * The word list holds only words with **no English homograph**, which is what keeps it usable
   * without a vocabulary. `non`, `per`, `come`, `prima`, `dove`, `due` and `tre` are deliberately
   * absent though they are common: `non-negative`, `per page`, `come back`, `prima facie`, `dove`
   * and `due date` all occur in English prose, and `non` alone produced 168 candidates of which
   * every one was `non-negative` or `non-positive`.
   */
  private val Markers: Vector[(String, scala.util.matching.Regex)] = Vector(
    "accented" -> """[\u00C0-\u017F]""".r,
    "truncated accent" ->
      ("""(?i)\b(e|ne|se|si|cioe|perche|poiche|finche|affinche|percio|piu|piu|cosi|gia|puo"""
        + """|meta|citta|verita|novita|liberta|qualita|quantita|unita|attivita"""
        + """|possibilita|necessita|positivita|identita|proprieta)'(?![A-Za-z])""").r,
    "function word" ->
      ("""(?i)(?<![A-Za-z'-])(che|della|delle|degli|dei|nella|nello|nelle|negli|sulla|sulle"""
        + """|dalla|dalle|una|uno|gli|sono|essere|questo|questa|questi|queste|quello|quella"""
        + """|quelli|quelle|quindi|invece|anche|senza|ogni|tutto|tutti|tutta|tutte|ancora"""
        + """|mentre|oppure|quando|nessun|nessuna|soltanto|appena)(?![A-Za-z'-])""").r
  )

  /**
   * What exempts a passage, and it exempts the whole comment block rather than one line.
   *
   * A block and not a line because a reason is about a passage: `Relation`'s loop is described
   * across four lines of one docstring and the surname that needs the exemption falls on whichever
   * of them the rewrapping put it on. Making the author move the reason to chase a name down a
   * paragraph is how an exemption mechanism stops being used and the check gets deleted instead.
   */
  private val Reason = """allow-non-english:""".r

  /**
   * The text of every comment, which is the inverse of what `StyleSpec` keeps.
   *
   * That spec drops comments to scan code; this one drops code to scan comments, and the two
   * together are the file. String literals are left out of both: a literal is data, and a lemma
   * name inside one is not prose about the lemma.
   */
  private def commentLines(text: String): Vector[(Int, String)] =
    text.linesIterator.zipWithIndex
      .foldLeft((Vector.empty[(Int, String)], false)) { case ((kept, inBlock), (line, index)) =>
        val trimmed = line.trim
        val entry = (index + 1, line)
        if (inBlock) (kept :+ entry, !trimmed.contains("*/"))
        else if (trimmed.startsWith("/*")) (kept :+ entry, !trimmed.contains("*/"))
        else if (trimmed.startsWith("//") || trimmed.startsWith("*")) (kept :+ entry, false)
        else
          trailing(line) match {
            case Some(comment) => (kept :+ ((index + 1, comment)), false)
            case None => (kept, false)
          }
      }
      ._1

  /**
   * The comment part of a line that is code, or nothing.
   *
   * A `//` inside a string literal is not a comment, and this spec's own fixtures are the proof:
   * they hold lines of another language inside literals on purpose, and the first draft flagged
   * them. Quote parity decides it, which is exact for every line in this tree and would be wrong
   * on an escaped quote inside a literal. That case is absent here and the cost of being wrong on
   * it is a false positive, which is the direction to err in for a check somebody must switch off
   * if it cries wolf.
   */
  private def trailing(line: String): Option[String] = {
    val at = line.indexOf("//")
    if (at < 0) None
    else if (line.take(at).count(_ == '"') % 2 != 0) None
    else Some(line.substring(at))
  }

  /**
   * Every Scala source under `modules/`, main and test alike.
   *
   * The module list is **read from the filesystem** rather than written down, which is the repair
   * for the defect found the same day this spec was written: `modules/sat` was missing from
   * `root.aggregate`, so its sixteen tests never ran while the build stayed green, and a hardcoded
   * list here would reproduce that failure exactly. A module added tomorrow is scanned tomorrow.
   *
   * `DocumentationSpec` reached the same shape first and for the same reason, reading `modules/`
   * and asserting it against `build.sbt`'s `aggregate`. **That guard could not have caught this
   * class, and the reason is worth more than the precedent:** it compares the directories against
   * the build, so it answers "is there a module whose tests never run". A census whose module list
   * is a `val` inside a test is invisible to that comparison by construction, and nothing asks "is
   * there a module some census does not read". That is how the defect outlived the repair that
   * looked like it covered it: the commit that closed the list the build looks at left `sat`
   * outside the list no build looks at.
   *
   * `StyleSpec` is that census today. Its six names miss ten files of `src/main` across four
   * modules, and its own anti-vacuity floor is 59 against 143 found, so three module directories
   * could vanish from it without the floor moving. A floor is a weaker check than an agreement
   * between two readings, which is why the assertion below is the second kind.
   *
   * Test sources are included because all six blocks that produced this spec were in test sources.
   * A scan of `src/main` alone would have found none of them.
   */
  private def sources: Vector[Path] = {
    val modules = Paths.get("modules")
    if (!Files.exists(modules)) Vector.empty
    else {
      val stream = Files.walk(modules)
      try
        stream
          .iterator()
          .asScala
          .toVector
          .filter(path => path.toString.endsWith(".scala"))
          .filterNot(path => path.toString.contains("/target/"))
          .sorted
      finally stream.close()
    }
  }

  /** Contiguous runs of comment lines, which is the unit an exemption applies to. */
  private def blocks(lines: Vector[(Int, String)]): Vector[Vector[(Int, String)]] =
    lines
      .foldLeft(Vector.empty[Vector[(Int, String)]]) { (acc, entry) =>
        acc.lastOption match {
          case Some(run) if run.last._1 == entry._1 - 1 => acc.init :+ (run :+ entry)
          case _ => acc :+ Vector(entry)
        }
      }

  private def offences(path: Path): Vector[String] =
    for {
      block <- blocks(commentLines(Files.readString(path)))
      if !block.exists { case (_, line) => Reason.findFirstIn(line).isDefined }
      (number, line) <- block
      (name, pattern) <- Markers
      hit <- pattern.findFirstIn(line).toVector
      if !Excused.contains(path.getFileName.toString)
    } yield s"$name `$hit` at $path:$number"

  /* ------------------------------------------------ the scan can see something */

  // Floors and not equalities: this is not a size budget. A census with no subjects is green, which
  // is the way a scan like this passes without reading anything, so the floor is what a tree that
  // had genuinely lost its sources could not clear. Measured on 2026-09-15 at 320 files and 38446
  // comment lines, by running these rules over the tree before this file was committed; half of
  // each is the floor.
  "The scan" should "have found the sources, which is how a census like this passes for free" in {
    val files = sources
    withClue(s"scala files found under modules/: ${files.size}\n") {
      files.size should be >= 160
    }

    val lines = files.map(path => commentLines(Files.readString(path)).size).sum
    withClue(s"comment lines found: $lines\n") {
      lines should be >= 19000
    }

    info(s"${files.size} files, $lines comment lines")
  }

  it should "reach every module, including any added after this was written" in {
    // Two readings that must agree, rather than a list written here. A list is what put `sat`
    // outside `StyleSpec` and outside `root.aggregate`, and naming eight modules on a tree that has
    // ten would pass while missing two. So: the modules the scan actually reached, against the
    // directories under `modules/` that hold Scala at all, computed independently of the scan.
    val reached = sources.map(_.toString.split("/")(1)).distinct.sorted

    val stream = Files.list(Paths.get("modules"))
    val holdingScala =
      try
        stream
          .iterator()
          .asScala
          .toVector
          .filter(Files.isDirectory(_))
          .filter { directory =>
            val walk = Files.walk(directory)
            try
              walk
                .iterator()
                .asScala
                .exists(path =>
                  path.toString.endsWith(".scala") && !path.toString.contains("/target/")
                )
            finally walk.close()
          }
          .map(_.getFileName.toString)
          .sorted
      finally stream.close()

    reached shouldBe holdingScala

    // And the floor, because two empty readings agree. Ten on 2026-09-15; `aggregate` is the
    // eleventh directory and holds no source of its own, which is why this is not a count of
    // `modules/`.
    withClue(s"modules reached: ${reached.mkString(", ")}\n") {
      reached.size should be >= 10
    }

    info(s"${reached.size} modules: ${reached.mkString(", ")}")
  }

  it should "read a comment as a comment and a line of code as code" in {
    val sample =
      """/** A docstring.
        |  * A continuation line.
        |  */
        |val kept = 1 // a trailing comment
        |// a line comment
        |val alsoKept = 2""".stripMargin

    val seen = commentLines(sample).map(_._2.trim)
    seen should contain("/** A docstring.")
    seen should contain("* A continuation line.")
    seen should contain("// a trailing comment")
    seen should contain("// a line comment")
    seen should not contain "val alsoKept = 2"
  }

  /* ---------------------------------- each rule against a case whose answer is known */

  it should "match each marker where it is written, and not where English writes the same letters" in {
    val by = Markers.toMap

    by("accented").findFirstIn("// una città e un perché") shouldBe defined
    by("accented").findFirstIn("// a plain English comment about a naive functor") shouldBe empty

    by("truncated accent").findFirstIn("// la meta' negativa e' FALSA a `m = ZERO`") shouldBe defined
    by("truncated accent").findFirstIn("// the parser's own docstring, and the lemmas' order") shouldBe empty
    by("truncated accent").findFirstIn("// don't, it's, we'll") shouldBe empty

    by("function word").findFirstIn("// il residuo che resta qui e' quello della positivita'") shouldBe defined
    by("function word").findFirstIn("// the cheapest procedure that could settle this") shouldBe empty
    by("function word").findFirstIn("// non-negative, per page, come back, prima facie, due date") shouldBe empty
  }

  // The six real blocks, one line from each, because a detector is worth what it catches on the
  // case that produced it. Three of these are the ones a word list and an accent rule miss, which
  // is why both rules are here: `LibrarySpec`'s line carries no accent and no listed word except
  // through the truncated-accent rule, and the two single-line entries carry one marker each.
  it should "catch every one of the six blocks that produced this spec" in {
    val real = Vector(
      "216 con UNO dei quattro nuovi residui, e gli altri tre sono in `unreadable` sotto. E' la",
      "66 con gli altri tre: due tengono `~(NUM_DIVIDES p x)` e uno, quello della positivita',",
      "113 con tre dei quattro: il residuo della positivita' nomina `NUM_LT` e `ZERO`, e due dei",
      "289 con i due lemmi recuperati dal ramo `prime-power-cancellation`: uno e tre antecedenti.",
      "recuperato il 2026-09-15: la positivita' della potenza e la cancellazione di una potenza di",
      "289 con i quattro dei due lemmi recuperati."
    )

    real.foreach { line =>
      withClue(s"missed: $line\n") {
        Markers.exists(_._2.findFirstIn("// " + line).isDefined) shouldBe true
      }
    }
  }

  it should "let a comment block say why it is exempt, on any line of it" in {
    val sample =
      """/** A docstring whose subject is the Lov\u00e1sz condition.
        |  * allow-non-english: a surname, three lines below the accent it excuses.
        |  */
        |val kept = 1""".stripMargin

    val runs = blocks(commentLines(sample))
    runs.size shouldBe 1
    runs.head.exists { case (_, line) => Reason.findFirstIn(line).isDefined } shouldBe true

    // And the control: the same block without the reason is not exempt, so the exemption is doing
    // the work rather than the block structure.
    val bare = sample.linesIterator.filterNot(_.contains("allow-non-english")).mkString("\n")
    blocks(commentLines(bare)).head.exists { case (_, line) =>
      Reason.findFirstIn(line).isDefined
    } shouldBe false
  }

  /* --------------------------------------------------------------------- the census */

  "No comment under modules/" should "be written in a language other than English" in {
    val found = sources.flatMap(offences)

    withClue(s"${found.size} comment line(s) not in English:\n${found.mkString("\n")}\n") {
      found shouldBe empty
    }
  }
}
