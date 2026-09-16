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
 * == Which modules, and why that is not a list here ==
 *
 * The modules are read from `modules/` on disk. Until 2026-09-16 they were a vector written in this
 * file holding six names, and four of the ten directories were not among them: `sat` and `mark`,
 * which hold code, and `dist` and `examples`, which hold little and happen to be clean. What sat
 * outside the scan that day was 34 `var`, 15 `while` and 2 `return` in `sat`, and 5 `var` and 2
 * `while` in `mark`, none of them decided by anybody: the scan was green over two modules it had
 * never opened.
 *
 * `mark`'s seven were rewritten, because not one of them was anything: an angle wound forward by
 * repeated addition, a flag flipped once per crossing of a polygon edge, three counters standing
 * for a position in reading order, a breadth-first walk and a run-length scan. `sat`'s are a
 * conflict-driven solver and are [[Excused]], on the measurement that entry carries. The two
 * `return`s were neither, being early exits from `Solver.run`, and they are gone: that is the
 * per-construct key doing its work in the first hour it existed.
 *
 * That is the second list `sat` had disappeared from in as many days; the first was `root.aggregate`
 * in `build.sbt`, where the consequence was that its sixteen tests did not run in the gate at all.
 * `DocumentationSpec` reads the directories for that one now, and `ChainCoverageSpec.Accounted` was
 * already reading them for a third. **Every module list written by hand is a place where a new
 * module disappears**, and the difference between a list and a walk is not tidiness: a list is
 * silent about what it omits, which is the one thing a census must not be.
 *
 * What survives as a list is [[Excused]], and that is the right shape for it: an omission from a
 * list of modules is invisible, an omission from a list of exceptions is a failing test.
 *
 * == The exception, and what an entry in it has to carry ==
 *
 * [[Excused]] is the list of sites that may hold a forbidden construct. A hot numeric kernel may be
 * imperative if the mutation is confined to a private function, the function's signature is pure,
 * and it carries where it lives the measurement that decided it, the alternative rejected and what
 * it does not cover. "It seemed faster" is not a measurement, and whoever has not measured the
 * functional version does not have the exception. An entry here is that measurement having been
 * made, not permission to skip making it.
 *
 * An entry names a file **and a construct**, not a file. `Solver.scala` is excused its `var` and its
 * `while` on a measurement and is excused nothing else, so a `null` or a cast arriving in it fails
 * this test the way one arriving anywhere else does. Keyed by file alone, the measurement that
 * bought two constructs would have bought all five, which is not what anybody measured.
 */
class StyleSpec extends AnyFlatSpec with Matchers {

  /**
   * The repository root, which is where this scan is run from and where it says so if it is not.
   *
   * The walk this file replaced resolved `modules/<name>/src/main` and returned nothing where the
   * path did not exist, which is the vacuity the class comment is about: a scan run from the wrong
   * directory found no sources, and the floor beneath it is the only thing that would have caught
   * it. This refuses by name instead, because "no `modules/` here" is a sentence a reader can act
   * on and an empty census is not.
   */
  private def root: Path = {
    val here = Paths.get("").toAbsolutePath
    if (!Files.isDirectory(here.resolve("modules")))
      fail(s"no `modules/` directory under $here; this scan reads the repository root")
    else here
  }

  /** Every module directory that holds Scala sources, read rather than listed. See the class comment. */
  private def modules: Vector[String] = {
    val root = this.root.resolve("modules")
    val stream = Files.list(root)
    try
      stream
        .iterator()
        .asScala
        .toVector
        .filter(Files.isDirectory(_))
        .map(_.getFileName.toString)
        .filter(name => Files.exists(root.resolve(name).resolve("src/main")))
        .sorted
    finally stream.close()
  }

  /**
   * The constructs, by the name a reader would call them.
   *
   * `Array` and `throw new` are deliberately **not** here, and the reason has changed for one of
   * them. Every `throw new` is a refusal at a boundary that cannot return one, and those are argued
   * where they live. `Array` was left out because every one in the tree was the `Array[String]` of
   * a `main`, the JVM's signature rather than a choice. That stopped being true when `sat` came
   * inside the walk on 2026-09-16: a solver's assignment, levels, reasons and watch lists are
   * arrays indexed by variable and by literal. What covers them is not this list. They are mutable
   * state, they are named in [[ReviewedMutableState]], and the `var` beside them is what
   * [[Excused]] pays for.
   */
  private val Forbidden: Vector[(String, scala.util.matching.Regex)] = Vector(
    "var" -> """\bvar\s+[A-Za-z_]""".r,
    "while" -> """\bwhile\s*\(""".r,
    "return" -> """\breturn\b""".r,
    "null" -> """\bnull\b""".r,
    "asInstanceOf" -> """\basInstanceOf\b""".r
  )

  /**
   * What the exception on `Solver.scala` cost to establish, which is the sentence [[Excused]] owes.
   *
   * == The measurement ==
   *
   * The functional version was WRITTEN before it was rejected, which is what the class comment
   * means by not having the exception until you have measured. It is a port of the whole solver on
   * to persistent structures: five `Vector`s where there were five arrays indexed by variable, a
   * `Vector[Vector[Int]]` of watch lists where there was an `Array[ArrayBuffer[Int]]`, the trail,
   * its level marks, the clause database and the derivation all threaded through one immutable
   * record. Same algorithm step for step: two watched literals, first-UIP analysis recording every
   * resolution, geometric restarts, a linear scan for the decision.
   *
   * **It is faithful, which is the premise any timing claim rests on and is the part that does not
   * depend on the machine.** On nine instances -- the pigeonhole principle at three to seven holes,
   * and four Tseitin-shaped instances of ten to eighty variables -- the two return the same answer
   * AND derivations of identical length: 70, 280, 1363, 6364 and 39281 steps. A port that answered
   * the same and derived differently would be a different algorithm being timed.
   *
   * **The instrument is thread CPU time and not a wall clock, and that is the part of this
   * measurement worth arguing with.** This machine carried five other builds while the sweep ran,
   * and a wall clock on it reads how long a thread waited for a core: the first attempt, at load
   * 416, returned 3.8, 1.0, 12.8, 1.4 and 6.2 across a family of problems that only grows, which is
   * a reading of the neighbours. `getCurrentThreadCpuTime` does not count the waiting. What it
   * still counts is the cache and the memory bandwidth they take, so this is not the number a
   * quiet machine would give; it is a number whose ordering survives the machine, which is what the
   * question needs. Least of several interleaved rounds, because contention only ever adds.
   *
   * Milliseconds of CPU, 2026-09-16, JVM 23:
   *
   * {{{
   * instance            variables   imperative   functional   factor
   * tseitin(10)                10         0.48         0.59     1.2x
   * tseitin(20)                20         0.58         0.79     1.4x
   * tseitin(40)                40         1.01         2.28     2.3x
   * tseitin(80)                80         1.59         3.23     2.0x
   * pigeonhole(3)              12         0.77         1.46     1.9x
   * pigeonhole(4)              20         1.56         5.01     3.2x
   * pigeonhole(5)              30         5.82        21.65     3.7x
   * pigeonhole(6)              42        38.09       122.42     3.2x
   * pigeonhole(7)              56       408.14      1631.33     4.0x
   * }}}
   *
   * **The factor is the finding and the absolute numbers are not.** It is about 1.2 where the
   * search does nothing and climbs to 4 at the largest instance measured, going 1.9, 3.2, 3.7, 3.2,
   * 4.0 down a family that only grows, and the shape of that is
   * what a persistent structure costs: every assignment rewrites a path of a `Vector` instead of
   * writing a word, and a conflict-driven search assigns and unassigns far more often than it
   * learns. The alternative rejected is therefore the functional port itself, at three to four
   * times the cost and about two hundred and fifty lines of state threaded through every function,
   * which is not the more readable of the two either.
   *
   * == What this does not cover ==
   *
   * The instances `Propositional` sends today are the small end of that range and are settled in
   * milliseconds either way, so nothing here says the functional version would be felt by a reader
   * of this repository **now**. What it says is about the case the module was written for, which
   * `tactics.Consistency`'s own comment names: the goals an enumeration refuses above sixteen
   * atoms. An exception argued from today's traffic would have to be re-argued the first time a
   * register of rules reached that size, which is the situation the solver exists for.
   *
   * It also says nothing about memory, which was not measured, and nothing about a third design:
   * a functional shell over arrays confined to one private function, which is the shape the class
   * comment above actually licenses and which nobody has written for a solver.
   */
  private val SolverReason: String =
    "a conflict-driven solver, whose arrays indexed by variable and by literal, trail, clause " +
      "database and watch lists are what the algorithm is rather than a convenience inside it. " +
      "The functional version was written and timed against this one before this entry existed: " +
      "same answers and identical derivations on nine instances, and between three and four times " +
      "the CPU wherever the search does any work, measured 2026-09-16. What it does not cover, " +
      "and the third design nobody has written, are in the docstring above."

  /**
   * Sites allowed to hold one, by file and by construct, each with the measurement that bought it.
   *
   * See the class comment for what an entry costs, and [[SolverReason]] for the one that was paid.
   * The two below are that one measurement, under the two constructs it bought.
   *
   * Nothing else in `modules/sat` is here, and the file next to it is the argument for reading this
   * list as narrow rather than as a module's pass. `Resolution` and `Cnf` held a `while` and three
   * mutable collections between them on the morning of 2026-09-16 and hold none by the evening,
   * because neither sits on a path any measurement calls hot: the derivation checker walks its
   * steps once and a clause is normalised at the length of a clause. The way to find out whether a
   * site needs an entry is to write the other version first, and two of the three sites that
   * looked like they would need one did not.
   */
  private val Excused: Map[(String, String), String] = Map(
    ("Solver.scala", "var") -> SolverReason,
    ("Solver.scala", "while") -> SolverReason
  )

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
        "procedures chain hundreds of steps and a recursive one would meet the stack. Two " +
        "`HashMap`s beside them number the types and the terms, keyed by structural equality and " +
        "not by identity, which is the opposite choice from the theorems above it and is the " +
        "right one: two equal types are one type and the record is meant to name it once"),
    "Conv.scala" ->
      ("the reflexivity cache, bounded at 8192 against a measured 4287 distinct atoms in the " +
        "standard chain's 112 lemmas, read through `Option` at the boundary because the map is a " +
        "Java one and both of its misses are a `null`"),
    "Arbitrary.scala" ->
      ("pi and the two logarithms memoised per precision, because every reduction wants them and " +
        "a screening run asks a few thousand times; the alternative is a few thousand Machin series"),
    "Propositional.scala" ->
      ("the encoding's three collections, which exist for one property: a subformula met twice " +
        "gets the number it got the first time, so a goal that repeats itself is encoded linearly " +
        "rather than exponentially. `LinkedHashMap` and not `Map` because the insertion order IS " +
        "the numbering, a subformula being numbered before anything containing it, which is what " +
        "lets a clause name its children by number. Not reviewed until 2026-09-16, and not because " +
        "anybody decided it was fine: the pattern list above had no entry for a scala mutable " +
        "collection, so three of them sat in a module this scan had been reading since it existed"),
    "Consistency.scala" ->
      ("one `LinkedHashSet` collecting the atoms of the premises, where the order is the variable " +
        "numbering the enumeration then runs over, so it has to be the order they were met in and " +
        "not the order a `Set` would hand back. Bounded by the sixteen atoms that file refuses " +
        "above, which is the same bound its own comment argues"),
    "Solver.scala" ->
      ("the whole state of a conflict-driven search: five arrays indexed by variable, the watch " +
        "lists indexed by literal, the trail, its level marks, the clause database and the " +
        "derivation. It is excused rather than reviewed away, and [[Excused]] carries the " +
        "measurement; what belongs here is that none of it escapes, since `Solver` is a private " +
        "class whose only public method returns an `Answer` built out of immutable values"),
    "Notebook.scala" ->
      ("one `AtomicReference` holding the current `Session`, which is the whole mutable state of " +
        "the server and is mutable because a page is a long-lived process and a session is not: " +
        "`Session` itself is immutable and every command returns a new one, so the reference is " +
        "swapped rather than written into, and `updateAndGet` is what keeps two requests from " +
        "interleaving a read and a write of it now that the server runs its exchanges on a pool")
  )

  /**
   * The shapes mutable state arrives in without any of the words above being written.
   *
   * `scala mutable` was added on 2026-09-16 and found three collections nobody had reviewed, in
   * `Propositional.scala`, in a module this scan had been reading since it was written. That is the
   * same miss the list below was created for, one library along: `\bvar\b` says nothing about
   * `collection.mutable.ArrayBuffer.empty`, and a file can be built entirely out of the second
   * without ever writing the first.
   *
   * `java.util.regex` is not counted, for the reason [[ReviewedMutableState]] gives.
   */
  private val Hidden: Vector[(String, scala.util.matching.Regex)] = Vector(
    "builder" -> """\bnewBuilder\b|\bStringBuilder\b""".r,
    "java map/set" ->
      ("""\bjava\.util\.(concurrent\.)?\w*(HashMap|HashSet)\b""" +
        """|\bjava\.util\.Collections\.newSetFromMap\b""" +
        """|\bConcurrentHashMap\b""").r,
    "atomic" -> """\bAtomic(Integer|Long|Reference|Boolean)\b|@volatile\b""".r,
    "scala mutable" -> """\b(scala\.)?collection\.mutable\b|\bmutable\.[A-Z]|\bArrayBuffer\b""".r
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
    modules.flatMap { module =>
      // No `if exists` here any more: `modules` returns only the names that have a `src/main`, and
      // a guard that silently yields nothing is the hazard rather than the defence.
      val stream = Files.walk(root.resolve(s"modules/$module/src/main"))
      try stream.iterator().asScala.toVector.filter(_.toString.endsWith(".scala"))
      finally stream.close()
    }

  /* ---------------------------------------------------- the scan can see something */

  // Floors and not equalities: files and lines are added every day and this is not a size budget.
  // Two readings with their dates, because one of them is not what it looks like. At `c503d03` on
  // 2026-09-16 this scan sees 155 files and 44823 lines of code over every module directory; on
  // 2026-09-12 it saw 118 files and 25251 lines, which is what the same scan saw of the same tree
  // while four of the ten directories were outside it. Half of each is a floor that a tree which
  // had genuinely lost its sources could not clear.
  //
  // **Almost none of that difference is the widening**, and the pair is written down to say so.
  // The four directories that came inside hold 10 files and 746 lines between them. The rest is
  // work in modules the scan was already reading: `theories` alone is 33105 lines, having gained
  // about 1700 on the day this was written. A reader who took the jump as the size of what had been
  // unscanned would be wrong by a factor of twenty, which is why a figure like this is quoted with
  // the commit it was taken at rather than as a property of the repository.
  "The scan" should "have found the sources, which is the way a census like this passes for free" in {
    val files = sources
    withClue(s"files found: ${files.size}\n") {
      files.size should be >= 77
    }

    val lines = files.map(path => codeLines(Files.readString(path)).size).sum
    withClue(s"lines of code found: $lines\n") {
      lines should be >= 21000
    }

    info(s"${files.size} files, $lines lines of code")
  }

  /**
   * The walk finds the modules, and it finds the ones a hand-written list had lost.
   *
   * The floor above would be cleared by a walk that had lost `sat` and `mark` between them,
   * because the six large modules carry almost all of the lines: that is exactly the state this
   * scan was in until 2026-09-16 and it was comfortably green. A floor on the size of the corpus
   * cannot see a module missing from it, so the modules are named here and the naming is checked
   * against `build.sbt` rather than against a second list.
   */
  it should "read every module the build aggregates, which a list in this file did not" in {
    val found = modules

    // The first half, and it is about this walk rather than about the build: a directory under
    // `modules/` that this scan does not reach is a module outside the census, which is the whole
    // defect. It reaches one by finding `src/main` under it, so what this catches is a module whose
    // sources are laid out some other way.
    val stream = Files.list(root.resolve("modules"))
    val directories =
      try stream.iterator().asScala.toVector.filter(Files.isDirectory(_)).map(_.getFileName.toString)
      finally stream.close()

    // One directory there legitimately holds no source, and it is invisible until somebody builds:
    // `modules/aggregate` is the project `build.sbt` calls `symbolum`, the pom that names the
    // others, and sbt CREATES that directory for its `target/` the first time the build runs. So
    // this walk sees ten directories in a fresh clone and eleven in a tree anybody has compiled,
    // which is a difference that would have turned this assertion red on exactly the machines it
    // matters on -- and did not turn it red under the scan that first checked it, because that tree
    // had never been built. `DocumentationSpec` subtracts the same name for the same reason, and
    // the subtraction there reads like a no-op on a clean checkout and is not one.
    //
    // So the exemption is "holds no `src` at all", not a name, and it is bounded: a second
    // source-less directory is a question rather than a free pass.
    val sourceless = directories.filterNot(name => Files.isDirectory(root.resolve(s"modules/$name/src")))
    withClue(s"module directories under `modules/` holding no `src` at all: ${sourceless.mkString(", ")}\n") {
      sourceless.toSet.subsetOf(Set("aggregate")) shouldBe true
    }

    val skipped = directories.toSet -- found -- sourceless.toSet
    withClue(s"module directories this scan skips although they hold sources: ${skipped.mkString(", ")}\n") {
      skipped shouldBe empty
    }

    // The second half is the build's end of the same question: a project it aggregates has its
    // tests run, and a directory this scan reads has its sources censused. A name in one and not
    // the other is either a module that escaped the census or a project with no directory, and the
    // second is real: `symbolum` is the aggregating pom and lives in `modules/aggregate`, so it
    // appears here under the name the build gives it and not the name on disk.
    //
    // What this therefore does NOT catch, said because it is the same shape as the defect it
    // guards: a module whose project name differs from its directory name AND which has sources.
    // There is none, and `DocumentationSpec`'s walk over the same line has the same blind spot.
    val aggregated = "\\.aggregate\\(([^)]*)\\)".r
      .findFirstMatchIn(Files.readString(root.resolve("build.sbt")))
      .map(_.group(1).split(",").map(_.trim).toSet)
      .getOrElse(Set.empty)

    val unexplained =
      (aggregated -- found).filter(name => Files.isDirectory(root.resolve(s"modules/$name")))
    withClue(s"aggregated by the build, not censused here, and holding a directory: ${unexplained.mkString(", ")}\n") {
      unexplained shouldBe empty
    }

    // And the half that can go empty in the other direction: a walk returning nothing agrees with
    // every subtraction there is, and a regex matching nothing leaves `aggregated` empty so that
    // every difference above is empty too. The four named first were the ones outside the list this
    // replaced; `sat` is named twice in this repository's guards for that reason.
    found should contain allOf ("sat", "mark", "dist", "examples")
    found should contain allOf ("kernel", "logic", "theories", "checker", "core", "tactics")
    aggregated should contain("symbolum")
    aggregated.size should be > 8
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
      if !Excused.contains((path.getFileName.toString, name))
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

    // And the list is not passing by being a list of nothing: every entry is really there. An entry
    // that stopped matching would mean the state moved or the pattern broke, and either way the
    // sentence beside it has stopped describing the file it names.
    val stale = ReviewedMutableState.keys.toVector.sorted.filterNot(found.contains)
    withClue(s"reviewed and no longer holding any: ${stale.mkString(", ")}\n") {
      stale shouldBe empty
    }
  }

  it should "excuse nothing silently, and excuse nothing that is no longer there" in {
    // Each entry says which measurement bought it, and this reads that the sentence is there rather
    // than that the key is.
    Excused.values.foreach(reason => reason.length should be > 40)

    // The half that would otherwise rot. An excuse outlives what it excuses without failing
    // anything: the construct is rewritten, the entry stays, and the next one to arrive in that file
    // is waved through by a sentence written about something else. So every entry is asserted to be
    // spending itself, by the same argument `ReviewedMutableState` is checked with one test above.
    val sites = for {
      path <- sources
      (_, line) <- codeLines(Files.readString(path))
      (name, pattern) <- Forbidden
      if pattern.findFirstIn(line).isDefined
    } yield (path.getFileName.toString, name)

    val stale = Excused.keys.toVector.sorted.filterNot(sites.contains)
    withClue(s"excused and no longer present: ${stale.mkString(", ")}\n") {
      stale shouldBe empty
    }
  }
}
