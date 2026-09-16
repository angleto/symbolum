package garden.xeno.symbolum.tactics

import java.io.{PrintWriter, StringWriter}
import java.net.URLClassLoader
import java.nio.file.{Files, Path, Paths}
import dotty.tools.dotc.Driver
import dotty.tools.dotc.reporting.ConsoleReporter

/**
 * Compiling and running the Scala blocks of a document exactly as the document holds them.
 *
 * `ReadmeSpec` was the first user and was the whole of it until 2026-09-16: the reading of the
 * fences, the single generated source, the compile, the class loader and the harness's own
 * self-test all lived in that file and named `README.md` in four places. A second document wanting
 * the same guard had two ways to get it and both are defects here. Copying the harness is a second
 * implementation site of one rule, which this repository treats as a defect while the two still
 * agree. Loosening `ReadmeSpec` until it took a parameter would have left the file named after one
 * document owning the mechanism for all of them.
 *
 * So the mechanism is here and the registries stay in the specs. What a spec owns is the list of
 * its document's blocks, the prelude each one needs and the reason each unrun one gives; what this
 * owns is everything that would otherwise be written twice.
 *
 * == Why one compilation per document and not one per block ==
 *
 * Each block becomes the body of its own object in a single generated source. That buys isolation,
 * since an object's body cannot see another object's locals, so a block that only works because an
 * earlier block defined a name fails rather than passing on context the document never gave its
 * reader. It also costs one classpath scan instead of one per block, which was measured at 34
 * seconds for the first and about a second for each after it on a loaded machine.
 *
 * == What it cannot tell you ==
 *
 * That the block does what the document says it does. A block whose printed answer has drifted from
 * what it computes compiles and runs here and is wrong; the answers are `DocumentationSpec`'s, and
 * the two guards are a pair rather than one being the strong version of the other.
 */
object DocumentBlocks {

  /** A block's fate: run it after this prelude, or do not run it and say why. */
  sealed trait Fate

  /** Run it, with this text put in front of it. The prelude is the spec's and never the document's. */
  final case class Runs(prelude: String) extends Fate

  /**
   * Compile it and do not run it, for a reason.
   *
   * The third fate, and it exists because the binary one sent two different blocks to the same
   * place. A block that cannot be compiled here at all -- an sbt fragment, a `case` clause lifted
   * out of a match -- is outside this guard entirely. A block that compiles perfectly well and must
   * not be RUN is a different thing: it writes a file into the working directory, or it is a
   * computation another spec already owns and this one would pay for twice. Excusing the second
   * from compiling too gives up the guard this file exists for, which is the block that stopped
   * being a program, in order to avoid a cost that is only in the running.
   */
  final case class Compiles(prelude: String, reason: String) extends Fate

  /** Neither compiled nor run, for a reason long enough to be one; the specs assert that length. */
  final case class NotRun(reason: String) extends Fate

  /** A block with its prelude, and whether this run is to execute it as well as compile it. */
  final case class Prepared(key: String, prelude: String, text: String, run: Boolean)

  /** A fenced block, with the line its first line sits on so that a failure can name it. */
  final case class Block(line: Int, text: String)

  /** What a compile-and-run of one document's blocks produced. */
  final case class Outcome(errors: Int, said: String, blamed: Vector[String], threw: Vector[String])

  /** Find a repository file from wherever the tests were started. */
  def locate(relative: String): Path = {
    def search(directory: Path, remaining: Int): Path =
      if (remaining < 0)
        throw new IllegalStateException(
          s"could not find $relative from ${Paths.get("").toAbsolutePath}")
      else {
        val candidate = directory.resolve(relative)
        if (Files.exists(candidate)) candidate else search(directory.getParent, remaining - 1)
      }

    search(Paths.get("").toAbsolutePath, 5)
  }

  /** The document, read from the repository root. */
  def read(document: String): String = Files.readString(locate(document))

  /**
   * The fenced Scala blocks of a document, in order.
   *
   * An unterminated fence is a broken document rather than a block with no end, and what is raised
   * names the line the fence opened on, because that is the line somebody has to go and look at.
   */
  def blocksOf(document: String, markdown: String): Vector[Block] = {
    val lines = markdown.linesIterator.toVector

    def gather(at: Int, found: Vector[Block]): Vector[Block] =
      if (at >= lines.length) found
      else if (lines(at).trim != "```scala") gather(at + 1, found)
      else {
        val close = lines.indexWhere(_.trim == "```", at + 1)
        if (close < 0)
          throw new IllegalStateException(
            s"$document: a ```scala fence at line ${at + 1} is never closed")
        else gather(close + 1, found :+ Block(at + 2, lines.slice(at + 1, close).mkString("\n")))
      }

    gather(0, Vector.empty)
  }

  /**
   * The classpath the blocks compile against, as `build.sbt` writes it.
   *
   * Refused by name rather than falling back to `java.class.path`, which under sbt's own test
   * runner holds the launcher and not this suite: a harness that fell back would compile every
   * block against almost nothing and report an error about `Var`, which reads as a defect in the
   * document rather than as a missing file.
   */
  def classpath: String = {
    val resource = getClass.getResourceAsStream("/test-classpath.txt")
    if (resource == null)
      throw new IllegalStateException(
        "test-classpath.txt is not on the test classpath; `build.sbt` generates it for this guard")
    else
      try new String(resource.readAllBytes(), "UTF-8")
        .linesIterator
        .mkString(java.io.File.pathSeparator)
      finally resource.close()
  }

  /** One source holding every block that runs, each as the body of its own object. */
  private def assemble(
    pack: String,
    blocks: Vector[Prepared]
  ): (String, Vector[(String, Int)]) = {
    val (lines, offsets) =
      blocks.zipWithIndex.foldLeft((Vector(s"package $pack", ""), Vector.empty[(String, Int)])) {
        case ((lines, offsets), (Prepared(key, prelude, text, _), at)) =>
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
   * **Errors and not warnings, and there is a warning a reader should know about.** A block that
   * writes a bare integer to the right of an operator, `x + 1`, reaches `Expr` through
   * `Dsl.intToNum`; that is an `implicit def` in the Scala 2 style, so Scala 3 warns at every use
   * site that `scala.language.implicitConversions` should be imported. The documents do not import
   * it and do not need to: the warning is a warning under default settings, which is what a reader
   * pasting into their own project has. It becomes an error under `-Xfatal-warnings`, which is what
   * THIS repository builds with, so a reader who pasted a block into `modules/core` would be
   * stopped by their own settings and not by the document's.
   *
   * Those flags are deliberately not passed here, and the warnings are deliberately left in the
   * text this returns rather than silenced with `-nowarn`: the failure message is where a reader
   * finds out that the block compiled with something to say.
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

  /**
   * Compile the blocks and, if they all compiled, run each one.
   *
   * A block that did not compile is not run, so `threw` is empty whenever `errors` is not zero.
   * That is the honest shape rather than a convenience: a block that could not be built has not
   * been asked whether it works, and reporting it in both columns would count one failure twice.
   */
  def outcome(pack: String, blocks: Vector[Prepared]): Outcome = {
    val (text, offsets) = assemble(pack, blocks)
    val directory = Files.createTempDirectory(s"$pack-blocks")
    val out = Files.createDirectory(directory.resolve("classes"))
    val source = directory.resolve("Blocks.scala")
    Files.write(source, text.getBytes("UTF-8"))

    val (errors, said) = compile(source, out)
    if (errors > 0) {
      val blamed = """(?m)Blocks\.scala:(\d+)""".r
        .findAllMatchIn(said)
        .map(entry => owner(offsets, entry.group(1).toInt))
        .toVector
        .distinct
      Outcome(errors, said, blamed, Vector.empty)
    } else {
      val loader = new URLClassLoader(Array(out.toUri.toURL), getClass.getClassLoader)
      val threw = blocks.zipWithIndex.filter(_._1.run).flatMap { case (prepared, at) =>
        val module = loader.loadClass(s"$pack.Block$at$$").getField("MODULE$").get(null)
        try { module.getClass.getMethod("run").invoke(module); None }
        catch {
          case failure: Throwable =>
            Some(s"`${prepared.key}` threw ${Option(failure.getCause).getOrElse(failure)}")
        }
      }
      Outcome(errors, said, Vector.empty, threw)
    }
  }
}
