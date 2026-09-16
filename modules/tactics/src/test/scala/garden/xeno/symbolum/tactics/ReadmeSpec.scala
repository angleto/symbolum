package garden.xeno.symbolum.tactics

import java.io.{PrintWriter, StringWriter}
import java.net.URLClassLoader
import java.nio.file.{Files, Path, Paths}
import dotty.tools.dotc.Driver
import dotty.tools.dotc.reporting.ConsoleReporter
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Every Scala block of `README.md`, compiled and run as the document holds it.
 *
 * == What this replaces ==
 *
 * `DocumentationSpec` asserts what the front page's examples PRODUCE, and it does that by writing
 * the program again in Scala beside the assertion. That is worth having and it is not a
 * certification of the document: on 2026-09-15 the first example a reader met was
 *
 * {{{ val expr = 2 * n + 3 * n - 1 }}}
 *
 * which does not compile anywhere, because a bare integer to the LEFT of an operator wants two
 * implicit conversions chained, `Int` to `Expr` and then `Expr` to the class carrying the
 * operators, and Scala applies one. The guard beside it evaluated `Num(2) * Var("n") + ...`, which
 * needs no conversion at all, and was green. **A test that rewrites what it certifies does not
 * certify it**, and the two spellings had drifted for as long as both existed.
 *
 * The repair that day pinned the two lines by asserting the document contains them character for
 * character. That closes two blocks of twenty-four and leaves the class alive. This closes the
 * class: the text is read from the file and compiled as it stands, so breaking any line of any
 * block it runs turns this suite red.
 *
 * == How ==
 *
 * One compilation and not twenty-four. Each block becomes the body of its own object in a single
 * generated source, which buys two things that matter more than the time it saves. The first is
 * **isolation**: an object's body cannot see another object's locals, so a block that only works
 * because an earlier block defined a name fails here, loudly, rather than passing on context the
 * document never gave its reader. The second is that a compile error arrives as a reporter's error
 * count and a line number rather than as a string to be recognised in some output.
 *
 * The alternative measured first was one `dotty.tools.repl.ReplDriver` reused across blocks, and it
 * was rejected on a reading rather than on taste: a second submission of `val q = 99` to a reused
 * initial state printed `val q: Int = Queue(1, 2, 3)`, the previous block's value under the new
 * block's type, because the REPL reuses its generated class names. A harness that can silently hand
 * a block the wrong value is the defect this file exists to remove, one level up.
 *
 * A fresh `ReplDriver` per block has no such leak and costs a classpath scan each time: 34 seconds
 * for the first block and about a second for each after it, measured 2026-09-16 on a loaded
 * machine. Twenty-four scans is not a trade worth making for a guard that runs in every suite.
 *
 * == What a prelude is, and what it is not ==
 *
 * Some blocks use a name the prose established in an earlier block of the same section: `x`, or the
 * imports the section opened with. [[Runs]] carries that context as a prelude, which is written
 * HERE and never in the document. So what is executed is the prelude and then the block's own text,
 * unaltered, and every character this guard protects is a character `README.md` holds.
 *
 * == What it does not cover, said rather than left to be found ==
 *
 *   - **The printed answers.** A block writes its result in a trailing comment, `// Output: 5 * n -
 *     1`, and this runs the block without comparing against it. Those comparisons are
 *     `DocumentationSpec`'s and stay there; what moved here is whether the program in the document
 *     is a program at all.
 *   - **Four of the twenty-four blocks do not run**, each with its reason in [[Blocks]] below, and
 *     only three of them are unprotected. Three are sbt build fragments, which are Scala and are
 *     not Scala this classpath can elaborate, so breaking a line of one of those is the one case
 *     this file would not catch. The fourth is a quotation of two lines of `Simplifier.scala`,
 *     which is checked against that file as a quotation one test below. Two others were elliptical,
 *     `val expr = /* ... */` where an expression belongs, and those were repaired in the document
 *     rather than excused here: a comment standing in for a value is not a block that cannot run,
 *     it is a block that misleads, and the repair is the document's rather than this file's.
 */
class ReadmeSpec extends AnyFlatSpec with Matchers {

  /** A block's fate: run it after this prelude, or do not run it and say why. */
  private sealed trait Fate
  private final case class Runs(prelude: String) extends Fate
  private final case class NotRun(reason: String) extends Fate

  private val Imports =
    "import garden.xeno.symbolum._\nimport garden.xeno.symbolum.Dsl._\n"

  /**
   * Every Scala block of the front page, by a line that identifies it, and what happens to it.
   *
   * Keyed by a line of its own text and not by its position, because position is the one key that
   * goes wrong silently: inserting a block renumbers every block after it, and each would then be
   * run under the prelude and the reason belonging to its predecessor. A key that is a line of the
   * block moves with the block. Both directions are asserted below, so a key matching no block and
   * a block matching no key are each a failure.
   */
  private val Blocks: Vector[(String, Fate)] = Vector(
    // The front page's three examples. The third continues the first: it imports the tactics and
    // uses the `x` and the algebra operators the first one set up, which is what the prose says.
    "Derivative(Sin(x ^ Num(2)), \"x\").simplify()" -> Runs(""),
    "Arithmetic.standard.multiply(3, 4)" -> Runs(""),
    "Oracle.standard.certifyIdentity(x + x, Num(3) * x)" -> Runs(Imports + "val x = Var(\"x\")\n"),

    // The installation fragments. `sbt` is not on this classpath and putting it there to elaborate
    // three lines would be a dependency bought for a test: what these say about the coordinates is
    // read by a person, and `DocumentationSpec` checks separately that the modules publish.
    //
    // Each of the three says its own reason rather than pointing at the one above it. That is not
    // style: the test below asserts a reason is long enough to be one, and the third of these was
    // "an sbt build fragment, for the reason above", 43 characters, which is a cross-reference and
    // not a reason. It failed on the first run this file ever had, which is the assertion working
    // on the person who wrote it.
    "resolvers += \"GitHub Package Registry\"" ->
      NotRun("an sbt build fragment declaring a resolver; `resolvers`, `scalaVersion` and " +
        "`libraryDependencies` are sbt's setting keys and are not names on a test classpath, so " +
        "compiling this would mean adding sbt itself as a dependency of a test"),
    "sys.env(\"GITHUB_TOKEN\")" ->
      NotRun("an sbt build fragment declaring credentials, so sbt's `Credentials` and the keys " +
        "around it are not on a test classpath; and it reads `GITHUB_TOKEN` from the environment, " +
        "which a test machine has no reason to hold and which a test must never require"),
    "libraryDependencies += \"garden.xeno\" %% \"symbolum-core\"" ->
      NotRun("an sbt build fragment declaring a dependency, so `libraryDependencies` and the `%%` " +
        "operator are sbt's and not on a test classpath. What it asserts is a published " +
        "coordinate and a version, which no compilation of it here would check either: that is " +
        "read by a person against the registry"),

    // The core's own guide. Every one of these runs as it stands.
    "val expr = Num(2) * n + Num(3) * n - Num(1)" -> Runs(""),
    "val law2 = x ^ Num(0)" -> Runs(""),
    "val result = Integral.definite(x, \"x\", Num(0), Num(1))" -> Runs(""),
    "val solutions3 = Solve.solve(eq2, \"x\")" -> Runs(""),
    "val identity = sin(-x).simplify()" -> Runs(""),
    "exp(x + y).expand(exps)" -> Runs(""),
    "expr.simplify(SimplificationConfig.Collatz0)" -> Runs(""),

    // Two sections whose blocks are bare expressions under the imports their section opened with.
    "// Collatz0 - optimized for Collatz sequences" -> Runs(Imports),
    "  .withoutRules(FactorCommonTerms, MergeFractionsCommonDenom)" -> Runs(""),
    "val result = expr.fullSimplify(customConfig, maxIter = 50)" ->
      Runs(Imports + "val x = Var(\"x\")\n"),
    "val substituted = expr.replaceSymbol(\"y\", z - 1)" ->
      Runs(Imports + "val x = Var(\"x\")\nval y = Var(\"y\")\nval z = Var(\"z\")\n"),
    "val result2 = expr2.eval(Map(\"x\" -> 1.0, \"y\" -> 2.0, \"z\" -> 3.0))" ->
      Runs(Imports + "val x = Var(\"x\")\nval y = Var(\"y\")\nval z = Var(\"z\")\n"),

    // The architecture section quotes two lines of the traversal. They are `case` clauses of a
    // match in another file, so they are not a program and cannot be made one without quoting the
    // match around them, which is the thing the section is explaining rather than showing.
    "case Div(operands) => operands.map(normalise).reduceLeft(Canonical.quotient)" ->
      NotRun("two `case` clauses lifted out of the match in `Simplifier.scala`; a clause is not a " +
        "program, so this is checked as a quotation against that file instead, one test below"),

    "val sum = half + third     // 5/6 (exact)" -> Runs(Imports),

    // The worked examples at the end.
    "val integral = Integral(derivative, \"x\").simplify()" -> Runs(""),
    "val derivative = Derivative(sin(x), \"x\").simplify()" -> Runs(""),
    "val value = rate.eval(Map(\"t\" -> 2.0, \"k\" -> 0.5))" -> Runs(""),
    "val solutions = Solve.solve(equation, \"x\")" -> Runs("")
  )

  /* ------------------------------------------------------------------ reading the document */

  private def readme: String = Files.readString(locate("README.md"))

  /** The fenced Scala blocks, in order, each with the line its first line sits on. */
  private def blocksOf(markdown: String): Vector[(Int, String)] = {
    val lines = markdown.linesIterator.toVector

    def gather(at: Int, found: Vector[(Int, String)]): Vector[(Int, String)] =
      if (at >= lines.length) found
      else if (lines(at).trim != "```scala") gather(at + 1, found)
      else {
        val close = lines.indexWhere(_.trim == "```", at + 1)
        // An unterminated fence is a broken document rather than a block with no end, and the
        // failure a reader wants names the line the fence opened on.
        if (close < 0) fail(s"README.md: a ```scala fence at line ${at + 1} is never closed")
        else gather(close + 1, found :+ ((at + 2, lines.slice(at + 1, close).mkString("\n"))))
      }

    gather(0, Vector.empty)
  }

  /* ------------------------------------------------------------------ the registry agrees */

  "Every Scala block of the README" should "be named exactly once by this file, and name one block" in {
    val blocks = blocksOf(readme)

    // The half that says nothing was forgotten: a block nobody has decided about fails, rather than
    // being carried along unrun and unnoticed, which is how twenty-two of twenty-four came to be
    // certified by paraphrase for as long as they were.
    val unclaimed = blocks.filterNot { case (_, text) =>
      Blocks.exists { case (key, _) => text.contains(key) }
    }
    withClue(s"blocks no entry of `Blocks` names, by first line:\n" +
      s"${unclaimed.map { case (at, text) => s"  line $at: ${text.linesIterator.next()}" }.mkString("\n")}\n") {
      unclaimed shouldBe empty
    }

    // And the half that says no entry has outlived its block. A key matching nothing would leave a
    // prelude and a reason describing text the document no longer holds, which is the stale
    // reference this repository treats as worse than a missing one.
    val orphaned = Blocks.map(_._1).filterNot(key => blocks.exists(_._2.contains(key)))
    withClue(s"entries naming no block of README.md: ${orphaned.mkString(", ")}\n") {
      orphaned shouldBe empty
    }

    // A key naming two blocks would run one of them twice and the other never, and both would look
    // covered. That is the ambiguity a positional key does not have and is the price of this one.
    val ambiguous = Blocks.map(_._1).filter(key => blocks.count(_._2.contains(key)) > 1)
    withClue(s"entries naming more than one block: ${ambiguous.mkString(", ")}\n") {
      ambiguous shouldBe empty
    }

    info(s"${blocks.size} scala blocks, ${Blocks.count { case (_, Runs(_)) => true; case _ => false }} run here")
  }

  it should "give a reason for every one it does not run" in {
    // The reasons are what this test is for. An entry that stopped running its block and said
    // nothing would be indistinguishable from one that never could.
    Blocks.collect { case (key, NotRun(reason)) => (key, reason) }.foreach { case (key, reason) =>
      withClue(s"the reason given for `$key` is too short to be one: ") {
        reason.length should be > 60
      }
    }
  }

  /* ---------------------------------------------------------------------- what is not run */

  "The two lines the architecture section quotes" should "be lines of the file it quotes them from" in {
    // The block above that this replaces, and it is a weaker guarantee said plainly: these two are
    // asserted to be in `Simplifier.scala`, not asserted to do what the section claims. What makes
    // it worth having is that the quotation is the thing that rots, exactly as the two assignments
    // on the front page rotted.
    val simplifier = Files.readString(
      locate("modules/core/src/main/scala/garden/xeno/symbolum/Simplifier.scala"))
    val quoted = blocksOf(readme)
      .find(_._2.contains("case Div(operands)"))
      .getOrElse(fail("the architecture section no longer holds the block this test is about"))
      ._2

    quoted.linesIterator
      .filter(_.trim.startsWith("case "))
      .foreach { line =>
        val body = line.trim.dropWhile(_ != '>').drop(1).trim
        withClue(s"`$body` is quoted by README.md and is not in Simplifier.scala: ") {
          simplifier should include(body)
        }
      }
  }

  /* -------------------------------------------------------------------- compiling and running */

  /**
   * The classpath the blocks compile against, as `build.sbt` writes it.
   *
   * Refused by name rather than falling back to `java.class.path`, which under sbt's own test
   * runner holds the launcher and not this suite: a harness that fell back would compile every
   * block against almost nothing and report an error about `Var`, which reads as a defect in the
   * document rather than as a missing file.
   */
  private def classpath: String = {
    val resource = getClass.getResourceAsStream("/test-classpath.txt")
    if (resource == null)
      fail("test-classpath.txt is not on the test classpath; `build.sbt` generates it for this file")
    else
      try new String(resource.readAllBytes(), "UTF-8").linesIterator.mkString(java.io.File.pathSeparator)
      finally resource.close()
  }

  /** One source holding every block that runs, each as the body of its own object. */
  private def assemble(blocks: Vector[(String, String, String)]): (String, Vector[(String, Int)]) = {
    val (lines, offsets) =
      blocks.zipWithIndex.foldLeft((Vector("package readmeblocks", ""), Vector.empty[(String, Int)])) {
        case ((lines, offsets), ((key, prelude, text), at)) =>
          val opened = lines :+ s"object Block$at {" :+ "  def run(): Unit = {"
          // Indented by four so that a block's own relative indentation survives: Scala 3 reads
          // indentation, and text at column zero inside a brace is legal but its continuation lines
          // are not always read the way the document's author wrote them.
          val body = (prelude.linesIterator.toVector ++ text.linesIterator.toVector).map("    " + _)
          (opened ++ body :+ "  }" :+ "}" :+ "", offsets :+ ((key, opened.length + 1)))
      }
    (lines.mkString("\n"), offsets)
  }

  /**
   * Compile the generated source, returning how many errors and what the compiler said.
   *
   * **Errors and not warnings, and there is a warning here that a reader should know about.** Eight
   * of the blocks write a bare integer to the right of an operator, `x + 1`, which reaches `Expr`
   * through `Dsl.intToNum`; that is an `implicit def` in the Scala 2 style, so Scala 3 warns at
   * every use site that `scala.language.implicitConversions` should be imported. The document does
   * not import it and does not need to: the warning is a warning under default settings, which is
   * what a reader pasting into their own project has. It becomes an error under
   * `-Xfatal-warnings`, which is what THIS repository builds with, so a reader who pasted a block
   * into `modules/core` would be stopped by their own settings and not by the document's.
   *
   * Those flags are deliberately not passed here, and the warnings are deliberately left in the
   * text this returns rather than silenced with `-nowarn`: the failure message is where a reader
   * finds out that the block compiled with something to say. Whether the eight blocks should carry
   * the import is a question about the document rather than about this guard, and nobody has
   * decided it.
   */
  private def compile(source: Path, out: Path): (Int, String) = {
    val buffer = new StringWriter
    val reporter = new Driver().process(
      Array("-classpath", classpath, "-d", out.toString, "-color:never", source.toString),
      new ConsoleReporter(null, new PrintWriter(buffer)))
    (reporter.errorCount, buffer.toString)
  }

  /** Which block a line of the generated source belongs to. */
  private def owner(offsets: Vector[(String, Int)], line: Int): String =
    offsets.takeWhile(_._2 <= line).lastOption.map(_._1).getOrElse("the preamble")

  "Every README block this file runs" should "compile as the document holds it and run without throwing" in {
    val blocks = blocksOf(readme)
    val running = Blocks.collect { case (key, Runs(prelude)) =>
      (key, prelude, blocks.find(_._2.contains(key)).map(_._2).getOrElse(fail(s"no block holds `$key`")))
    }

    val (text, offsets) = assemble(running)
    val directory = Files.createTempDirectory("readme-blocks")
    val out = Files.createDirectory(directory.resolve("classes"))
    val source = directory.resolve("Blocks.scala")
    Files.write(source, text.getBytes("UTF-8"))

    val (errors, said) = compile(source, out)
    val blamed = """(?m)Blocks\.scala:(\d+)""".r
      .findAllMatchIn(said)
      .map(m => owner(offsets, m.group(1).toInt))
      .toVector
      .distinct
    withClue(s"$errors error(s), in the block(s) keyed by ${blamed.mkString("; ")}\n$said\n") {
      errors shouldBe 0
    }

    val loader = new URLClassLoader(Array(out.toUri.toURL), getClass.getClassLoader)
    val threw = running.zipWithIndex.flatMap { case ((key, _, _), at) =>
      val module = loader.loadClass(s"readmeblocks.Block$at$$").getField("MODULE$").get(null)
      try { module.getClass.getMethod("run").invoke(module); None }
      catch { case failure: Throwable => Some(s"`$key` threw ${Option(failure.getCause).getOrElse(failure)}") }
    }
    withClue(s"${threw.size} block(s) threw:\n${threw.mkString("\n")}\n") {
      threw shouldBe empty
    }

    info(s"${running.size} blocks compiled and run from README.md")
  }

  /**
   * The harness, on inputs whose answers are known before it is believed.
   *
   * This is what the file it replaces did not have. A guard that compiles the document's blocks is
   * worth exactly as much as its ability to go red, and the three ways it could quietly stop going
   * red are a compile error not counted, an exception not caught, and a block whose text was never
   * read. The first two are here; the third is the registry test above.
   *
   * The first case is the front page's own defect put back: the line as it stood on 2026-09-15.
   */
  it should "fail on a block that does not compile, and on one that throws" in {
    val directory = Files.createTempDirectory("readme-harness")

    /** The blocks that failed to compile, by key, and the ones that threw, by key. */
    def outcome(blocks: Vector[(String, String, String)]): (Vector[String], Vector[String]) = {
      val (text, offsets) = assemble(blocks)
      val out = Files.createTempDirectory(directory, "classes")
      val source = Files.createTempFile(directory, "Blocks", ".scala")
      Files.write(source, text.getBytes("UTF-8"))
      val (errors, said) = compile(source, out)
      if (errors > 0) {
        val blamed = """\.scala:(\d+)""".r
          .findAllMatchIn(said)
          .map(entry => owner(offsets, entry.group(1).toInt))
          .toVector
          .distinct
        (blamed, Vector.empty)
      } else {
        val loader = new URLClassLoader(Array(out.toUri.toURL), getClass.getClassLoader)
        val threw = blocks.zipWithIndex.collect {
          case ((key, _, _), at) =>
            val module = loader.loadClass(s"readmeblocks.Block$at$$").getField("MODULE$").get(null)
            try { module.getClass.getMethod("run").invoke(module); None }
            catch { case _: Throwable => Some(key) }
        }.flatten
        (Vector.empty, threw)
      }
    }

    // Two compiles and not four, because each one costs a full scan of the classpath. The first
    // block of each pair is sound, so that a harness which simply reported everything as broken
    // would fail here rather than look like a strict one.

    // Two bad blocks at once, which also reads back which block a line belongs to: the first is the
    // line the front page carried until 2026-09-15, the guard of that day being green about it, and
    // the second is any other line of a block broken, which is this card's criterion for finished.
    val (broken, alsoThrew) = outcome(Vector(
      ("sound", Imports, "val n = Var(\"n\")\n(Num(2) * n).simplify()"),
      ("the old line", Imports, "val n = Var(\"n\")\nval expr = 2 * n + 3 * n - 1"),
      ("one line broken", Imports, "val n = Var(\"n\")\nval simplified = n.simplifyy()")))
    broken should contain allOf ("the old line", "one line broken")
    broken should not contain "sound"
    alsoThrew shouldBe empty

    // And a block that compiles and then fails at run time, which no error count would report.
    val (noErrors, threw) = outcome(Vector(
      ("sound", Imports, "val n = Var(\"n\")\n(Num(2) * n).simplify()"),
      ("throws", Imports, "val n = Var(\"n\")\nrequire(n.toString == \"m\", \"deliberate\")")))
    noErrors shouldBe empty
    threw shouldBe Vector("throws")
  }

  /* --------------------------------------------------------------------------------- paths */

  /** Find a repository file from wherever the tests were started, as `DocumentationSpec` does. */
  private def locate(relative: String): Path = {
    def search(directory: Path, remaining: Int): Path =
      if (remaining < 0) fail(s"could not find $relative from ${Paths.get("").toAbsolutePath}")
      else {
        val candidate = directory.resolve(relative)
        if (Files.exists(candidate)) candidate else search(directory.getParent, remaining - 1)
      }

    search(Paths.get("").toAbsolutePath, 5)
  }
}
