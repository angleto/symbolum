package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.scan.Comments

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
 * == What it reads, which was `.scala` and nothing else until 2026-09-16 ==
 *
 * The defect above was found in Scala, so the population was Scala, and that is the population
 * being a habit rather than a decision. The prose it could not see was the denser half:
 * on 2026-09-16 `build.sbt` alone carried 496 comment lines of 710, against `Rules.scala`'s 499
 * of 1030 in a file three times as long, and a comment in `build.sbt` or in `ci.yml` is prose in
 * exactly the way a comment in a `.scala` is. The extensions in [[Formats]] are read now, through
 * two comment readers, and that table carries the per-format measurement, the formats left out
 * and why.
 *
 * Widening it found nothing, and that is the answer rather than a disappointment: the markers
 * over everything the widening added returned zero, with `build.sbt` and the workflows
 * carrying almost all of it. What it buys is the day somebody writes the next ledger entry in a
 * workflow or in the build.
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
   *
   * Both readings come off `scan.Comments` since 2026-09-16, and what this site gained from the
   * move is the one input in this tree where its own rule gave the wrong answer. Quote parity
   * decided whether a `//` was a comment, and the one triple-quoted string in `Mark.scala` that
   * opens with an SVG header has attributes of its own in quotes: the number of quotes before the slashes of its `http`
   * is even, so parity said "outside a string" and the rest of that header was put to this census
   * as English prose. It is the line the docstring on the quote rule said did not exist.
   */
  private def commentLines(text: String): Vector[(Int, String)] =
    Comments.commentLines(text).map(line => (line.number, line.comment))

  /**
   * Comment lines in a language whose comments begin with `#`, which is shell, YAML and
   * `.properties` alike.
   *
   * A second reader and not a second census: the block above answers the same question for the
   * languages that open a block comment with a slash and a star. Two readers cover every format in
   * [[Formats]] because comment syntax is shared and file extensions are not, which is why that
   * table maps extensions to readers instead of one census per format.
   *
   * Spelled out rather than written, and it cost a compile: Scala nests block comments, so those
   * two characters inside a doc comment open a second one and the definition below is swallowed
   * until the next closing marker. The compiler reports it as an unclosed comment at the top of
   * the docstring and a missing brace at end of file, neither of them at the cause.
   */
  private def hashComments(text: String): Vector[(Int, String)] =
    Comments.hashLines(text).map(line => (line.number, line.comment))

  /**
   * The formats this census reads, each with the syntax its comments are written in.
   *
   * Until 2026-09-16 the population was `.scala` and nothing else, and the prose the census could
   * not see was the larger half by density: `build.sbt` alone carried 496 comment lines of 710,
   * against `Rules.scala`'s 499 of 1030 in a file three times as long. The defect this spec exists
   * against is **prose inside a comment**, and a comment in `build.sbt` or in `ci.yml` is prose in
   * exactly the way a comment in a `.scala` is.
   *
   * By extension and not by file, because a file list of length one is the shape `StyleSpec`
   * already argues against: `project/plugins.sbt` is the second `.sbt` of this tree, and a census
   * that read `build.sbt` by name would miss it.
   *
   * What each format contributes is printed by the assertion below rather than written here, for
   * the reason a count in prose goes stale silently. The part worth writing down is the part a
   * count hides: on 2026-09-16 `.js` and `.properties` held **no comment at all**, one file each,
   * so their presence in this table was a commitment about the next comment written in them and
   * not evidence that anything had been read. `.sc` held one.
   *
   * `.yaml` is deliberately absent though it is the same format: no file here uses that spelling,
   * and the assertion below requires every declared format to have found a file, so declaring it
   * would fail. That is the table staying honest rather than an oversight, and the day a `.yaml`
   * lands the line to add is one.
   *
   * `.css` is absent for a reason of its own: `notebook.css` held no comment at all on 2026-09-16,
   * and `//` is not a comment in CSS while it does occur inside a URL, so the reader above would be
   * wrong on it the first time one lands. A third reader for one minified file buys less than it
   * costs, and this sentence is what it buys instead.
   *
   * WHAT THIS DOES NOT CLOSE. A format nobody declares is a format nobody scans, which is this
   * spec's own defect one level up, and nothing here fails when one arrives. The exact population
   * is git's index, and no test in this repository starts a process; a filesystem census cannot
   * answer it, because it reads build output, an editor's dotfiles and whatever a session left
   * lying about. Declared, not solved.
   */
  private val Formats: Vector[(String, String => Vector[(Int, String)])] = Vector(
    ".scala" -> commentLines,
    ".sbt" -> commentLines,
    ".sc" -> commentLines,
    ".js" -> commentLines,
    ".sh" -> hashComments,
    ".yml" -> hashComments,
    ".properties" -> hashComments
  )

  /**
   * Directories whose contents are not this repository's prose, each with the reason.
   *
   * A directory whose name begins with a dot is a tool's rather than this repository's, and
   * `.github` is the exception because the workflows are among the prose this census was widened
   * to read.
   */
  private val Skipped: Map[String, String] = Map(
    "target" -> "build output, which holds generated sources and copies of the ones above them",
    "third-party" -> "corpora from other projects, whose prose is theirs and not this repository's",
    "scratch" -> "the probe directory the project sets aside, untracked by design"
  )

  /**
   * Every file of a declared format, from the repository root rather than from `modules/`.
   *
   * The walk reads the whole tree and filters afterwards, which is the obvious inefficiency and is
   * measured rather than assumed: on 2026-09-16 it was 8123 files including build output, in a
   * tenth of a second.
   */
  private def population: Vector[Path] = {
    val stream = Files.walk(Paths.get("."))
    try
      stream
        .iterator()
        .asScala
        .toVector
        .map(_.normalize)
        .filter(path => Formats.exists { case (suffix, _) => path.toString.endsWith(suffix) })
        .filterNot(path =>
          path.iterator().asScala.exists { part =>
            val name = part.toString
            Skipped.contains(name) || (name.startsWith(".") && name != ".github")
          }
        )
        .sorted
    finally stream.close()
  }

  /** The reader for a path, by its extension. Every path in [[population]] has one. */
  private def reader(path: Path): String => Vector[(Int, String)] =
    Formats.collectFirst { case (suffix, read) if path.toString.endsWith(suffix) => read }.get

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
   * `StyleSpec` was that census on 2026-09-15. Its six names missed ten files of `src/main` across
   * four modules, and its own anti-vacuity floor was 59 against 143 found, so three module
   * directories could have vanished from it without the floor moving; it has read the directory
   * since 2026-09-16. A floor is a weaker check than an agreement between two readings, which is
   * why the assertion below is the second kind.
   *
   * Test sources are included because all six blocks that produced this spec were in test sources.
   * A scan of `src/main` alone would have found none of them.
   */
  private def sources: Vector[Path] =
    population.filter(path =>
      path.toString.endsWith(".scala") && path.toString.startsWith("modules/")
    )

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
      block <- blocks(reader(path)(Files.readString(path)))
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
  // comment lines over `.scala` alone, and on 2026-09-16 over all seven formats at 356 files and
  // a comment total a little under 45000; half of each is the floor.
  //
  // The total is written that loosely on purpose, and the reason is one this file can demonstrate
  // about itself: the census reads its own source, so an exact figure here is changed by writing
  // it. The first draft said 44978, the run that followed printed 44977, and the difference was
  // this paragraph. The file count does not have that problem and is exact. What the live numbers
  // are is what the `info` line below prints, which is the one place they cannot go stale.
  "The scan" should "have found the sources, which is how a census like this passes for free" in {
    val files = population
    withClue(s"files found: ${files.size}\n") {
      files.size should be >= 178
    }

    val lines = files.map(path => reader(path)(Files.readString(path)).size).sum
    withClue(s"comment lines found: $lines\n") {
      lines should be >= 22400
    }

    info(s"${files.size} files, $lines comment lines")
  }

  it should "have found a file of every format it declares, so the table cannot name a dead one" in {
    // The other half of the floor above, and the half a total cannot give: `.scala` is most of the
    // population, so a small format that stopped matching anything would cost a file or two and
    // clear every floor here. An extension nobody uses, or one spelled `.yaml` where the tree
    // writes `.yml`, reads as coverage and is not, which is the defect this spec was widened to
    // repair arriving inside the repair.
    // Named `unmatched` and not `empty`, which is what it was for a minute: `empty` shadows the
    // matcher, so `empty shouldBe empty` compiles, compares the value with itself and passes
    // whatever the population holds. An assertion that cannot fail is the thing this file is about.
    val unmatched =
      Formats.map(_._1).filterNot(suffix => population.exists(_.toString.endsWith(suffix)))

    withClue(s"formats matching no file: ${unmatched.mkString(", ")}\n") {
      unmatched shouldBe empty
    }

    info(Formats.map(_._1).map(s => s"$s: ${population.count(_.toString.endsWith(s))}").mkString(", "))
  }

  it should "reach every module, including any added after this was written" in {
    // Two readings that must agree, rather than a list written here. A list is what put `sat`
    // outside `StyleSpec` and outside `root.aggregate`, and a list that names all but some of the
    // modules on the tree would pass while missing them. So: the modules the scan actually reached,
    // against the directories under `modules/` that hold Scala at all, computed independently of
    // the scan.
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

    // And the floor, because two empty readings agree. Ten on 2026-09-15; `aggregate` is one more
    // directory and holds no source of its own, which is why this is not a count of `modules/`.
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

  it should "read a `#` comment as a comment, and a `#` inside a literal as neither" in {
    // The same discipline as the block above, for the reader the widening added. The negative is
    // taken from `publish.yml` rather than invented: that file echoes markdown headings, and on
    // 2026-09-16 all three `#` occurrences in this tree that were not comments were of that shape.
    val sample =
      """# a line comment
        |sbt.version = 1.10.10
        |key: value # a trailing comment
        |          echo "## Published"
        |          echo '### The libraries'""".stripMargin

    val seen = hashComments(sample).map(_._2.trim)
    seen should contain("# a line comment")
    // The single-quoted heading is the case that decided `quotes`: with double quotes alone it
    // reads as a comment. Scala does not get that rule, and the docstring on `trailing` says why.
    seen should contain("# a trailing comment")
    seen should not contain "sbt.version = 1.10.10"
    seen.exists(_.contains("Published")) shouldBe false
    seen.exists(_.contains("The libraries")) shouldBe false
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

  "No comment in this repository's own source" should "be written in a language other than English" in {
    val found = population.flatMap(offences)

    withClue(s"${found.size} comment line(s) not in English:\n${found.mkString("\n")}\n") {
      found shouldBe empty
    }
  }
}
