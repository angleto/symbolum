package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.tactics.DocumentBlocks.{Block, Compiles, Fate, NotRun, Prepared, Runs}

/**
 * Every Scala block of every other document, compiled as the document holds it.
 *
 * `ReadmeSpec` takes `README.md` and `GuideBlocksSpec` takes `docs/proving.md`, which between them
 * are 71 of the repository's 112 blocks and none of the other four documents. This is the other
 * forty-one, and the reason they are in one file rather than four is the last test below: the
 * population is read off the repository and the three specs together have to cover it exactly, so a
 * document added with a Scala block in it lands red here rather than quietly joining the set nobody
 * compiles.
 *
 * == What it found ==
 *
 * `SIMPLIFICATION_CONFIG_GUIDE.md` had four blocks that declare one `val` name twice or three times
 * to show alternatives side by side, which is not a program: a reader pasting the block gets
 * "already defined". They are the same alternatives under different names now. It also referred to
 * a `configLCD` that nothing defines, two lines under the `configMerged` it means.
 *
 * `CONTRIBUTING.md` printed a test structure with `/* ... */` where the expression and the expected
 * value belong, in the section telling a contributor how to write a test. `ReadmeSpec` met that
 * exact shape on the front page and the note it left is the rule followed here: a comment standing
 * in for a value is not a block that cannot run, it is a block that misleads, and the repair
 * belongs to the document.
 *
 * == The two blocks that are quotations ==
 *
 * The configuration guide prints `SimplificationConfig`'s declaration and `Expr`'s three method
 * signatures. Neither is a program: the first shadows the real class with a local copy that would
 * compile whatever the real one said, and a signature with no body does not compile at all. Both
 * are checked as quotations against the sources instead, which is the guard that matters for them
 * and is what `ReadmeSpec` does for the two `case` clauses the front page lifts out of
 * `Simplifier.scala`.
 *
 * The `Expr` one was not a quotation until 2026-09-16: it was a hand-written `trait Expr` sketch
 * claiming two overloads of `simplify`, where the trait has one method with a defaulted implicit
 * parameter. It compiled, because a local trait always does, and it was wrong about the API it
 * described. That is the case for reading a sketch as a quotation rather than as a program.
 */
class OtherDocumentsSpec extends AnyFlatSpec with Matchers {

  private val Algebra = "import garden.xeno.symbolum._\nimport garden.xeno.symbolum.Dsl._\n"
  private val Rules = "import garden.xeno.symbolum.SimplificationRule._\n"
  private val Config = Algebra + Rules

  /** The three variables the configuration guide's examples use and never declare. */
  private val Names = "val x = Var(\"x\")\nval y = Var(\"y\")\nval n = Var(\"n\")\n"

  /**
   * The same, plus the expression the prose calls `expr`.
   *
   * Two preludes and not one, because three blocks declare an `expr` of their own and a prelude
   * carrying one would collide with it: a block is an object's body, so the prelude and the block
   * share a scope and `expr is already defined` is what comes back. That is the harness working as
   * intended -- the same collision is what stops a block from quietly using a name an earlier block
   * defined -- and it is why the prelude has to be chosen per block rather than per document.
   */
  private val AnExpression = Names + "val expr = Num(2) * n + Num(3) * n - Num(1)\n"

  /**
   * The documents, each with its registry.
   *
   * A registry is keyed by a line of the block's own text, never by position, for `ReadmeSpec`'s
   * reason: inserting a block renumbers every block after it and each would then be compiled under
   * the prelude belonging to its predecessor.
   *
   * **A key beginning with `=` is the whole block**, compared against its trimmed text rather than
   * looked for inside it. Four blocks of the configuration guide are a single expression naming a
   * configuration, and a substring key for one of those names ten other blocks that mention it, so
   * the ambiguity check below refuses it. It is the same trade `ReadmeSpec` records for positional
   * keys, met from the other side: a key short enough to be stable can be too short to be unique.
   */
  private val Documents: Vector[(String, Vector[(String, Fate)])] = Vector(
    "SIMPLIFICATION_CONFIG_GUIDE.md" -> Vector(
      "import garden.xeno.symbolum.{Expr, SimplificationConfig}" -> Runs(Algebra + AnExpression),
      "// Start with default and add rules" -> Runs(Config + AnExpression),

      // Eleven blocks that are nothing but comments: the rule each section is about, written as the
      // rewrite it performs. They compile to an empty body, which is what they are, and they are in
      // the registry rather than excused because a comment block that acquires a line of code
      // should start being compiled without anybody remembering to add it.
      "// x + 0 → x" -> Runs(""),
      "// 2 + 3 → 5" -> Runs(""),
      "// a*b + a*c → a*(b + c)" -> Runs(""),
      "// x + 2*x + 3*y → 3*x + 3*y" -> Runs(""),
      "// n/2 + 1/4 → (2*n + 1)/4" -> Runs(""),
      "// a*(b + c) → a*b + a*c" -> Runs(""),
      "// cos(A) * cos(B) → (cos(A-B) + cos(A+B))/2" -> Runs(""),
      "// (2*n)/4 → n/2" -> Runs(""),
      "// (a*b)/(a*c) → b/c" -> Runs(""),
      "// log(a*b) → log(a) + log(b)" -> Runs(""),
      "// exp(a + b) → exp(a) * exp(b)" -> Runs(""),

      // The four named configurations, each printed as the one expression that names it. These are
      // the whole-text keys: a block that IS `SimplificationConfig.Default` cannot be keyed by a
      // substring, because ten other blocks on the page mention it too.
      "=SimplificationConfig.Default" -> Runs(Algebra),
      "=SimplificationConfig.Minimal" -> Runs(Algebra),
      "=SimplificationConfig.Aggressive" -> Runs(Algebra),
      "=SimplificationConfig.None" -> Runs(Algebra),

      "// Problem expression" -> Runs(Config),
      "// Keep fractions symbolic (default)" -> Runs(Config),
      "val collatz1 = -((n*2 + 1) / 4.0) * cos(n * pi) + n + Num(1,4)" -> Runs(Config + Names),
      "// Expand fully" -> Runs(Config + Names),
      "val expr = x + Num(2)*x + Num(3)*x + y + Num(4)*y" -> Runs(Config + Names),

      "case class SimplificationConfig(" -> NotRun(
        "the declaration of `SimplificationConfig` as `SimplificationConfig.scala` holds it. " +
          "Compiling it would define a second class of that name local to the block, which " +
          "succeeds whatever the real one says, so it is checked as a quotation against that file " +
          "one test below instead"),
      "final def simplify(implicit config: SimplificationConfig = SimplificationConfig.Default): Expr" ->
        NotRun(
          "three signatures lifted from `Expr.scala`. A signature with no body is not a program " +
            "and cannot be compiled on its own, so these are checked as a quotation against that " +
            "file one test below, which is also the only thing that could have caught the sketch " +
            "they replaced"),

      "// Old way (still works)" -> Runs(Config + AnExpression),
      "   val config = SimplificationConfig.Default" -> Runs(Config),
      "   expr.fullSimplify(SimplificationConfig.Aggressive)" -> Runs(Config + AnExpression),
      "   var config = SimplificationConfig.Default" -> Runs(Config),
      "val config = SimplificationConfig.Default.withoutRule(MergeFractionsCommonDenom)" ->
        Runs(Config),
      "val minimal = SimplificationConfig.Minimal" -> Runs(Config)
    ),

    "TESTING.md" -> Vector(
      "(x + Num(2) * x).simplify()" -> Runs(""),
      "// Power operator" -> Runs(""),
      "// Sin and tan" -> Runs(""),
      "// Inverse properties" -> Runs(""),
      "// Differentiation" -> Runs(""),
      "// Linear equation" -> Runs(""),
      "val startTime = System.nanoTime()" -> Runs(
        Algebra + "val complexExpr = (Var(\"x\") + Num(1)) ^ Num(4)\n"),
      "// Test 1: Triple negative" -> Runs("")
    ),

    "CONTRIBUTING.md" -> Vector(
      "def someMethod(paramName: Type): ReturnType = ???" -> NotRun(
        "a Scaladoc template whose parameter type, return type and body are placeholders: " +
          "`Type`, `ReturnType` and a method called `someMethod` are the shape a contributor " +
          "fills in, not names that resolve anywhere, so there is nothing here to compile"),
      "class MyFeatureTest extends AnyFlatSpec with Matchers {" -> Runs("")
    ),

    "docs/adr/0008-a-constant-carries-what-defined-it.md" -> Vector(
      "val asTruth   = Kernel.defineConstant(logic.theory, \"c\", logic.truth).toOption.get._2" -> Compiles(
        "import garden.xeno.symbolum.kernel._\nimport garden.xeno.symbolum.logic._\n" +
          "val logic = Logic.standard\n",
        "it derives `|- T = F` from two theories that each define one name differently, which is " +
          "the unsoundness `docs/adr/0008` exists to record. `SoundnessAttackSpec` runs it and " +
          "asserts what comes back; running it here as well would buy a second site for the one " +
          "derivation in this repository that must never be believed")
    )
  )

  /** Whether a key names a block: a substring of it, or its whole text where the key starts `=`. */
  private def names(block: Block, key: String): Boolean =
    if (key.startsWith("=")) block.text.trim == key.drop(1) else block.text.contains(key)

  /* ------------------------------------------------------------------ the registries agree */

  "Every Scala block of every other document" should "be named exactly once, and name one block" in {
    Documents.foreach { case (document, registry) =>
      val blocks = DocumentBlocks.blocksOf(document, DocumentBlocks.read(document))

      val unclaimed = blocks.filterNot(block => registry.exists { case (key, _) =>
        names(block, key)
      })
      withClue(s"$document: blocks no entry names, by first line:\n" +
        s"${unclaimed.map(block => s"  line ${block.line}: ${block.text.linesIterator.next()}").mkString("\n")}\n") {
        unclaimed shouldBe empty
      }

      val orphaned = registry.map(_._1).filterNot(key => blocks.exists(names(_, key)))
      withClue(s"$document: entries naming no block: ${orphaned.mkString(", ")}\n") {
        orphaned shouldBe empty
      }

      val ambiguous = registry.map(_._1).filter(key => blocks.count(names(_, key)) > 1)
      withClue(s"$document: entries naming more than one block: ${ambiguous.mkString(", ")}\n") {
        ambiguous shouldBe empty
      }
    }

    info(s"${Documents.map { case (document, _) =>
      DocumentBlocks.blocksOf(document, DocumentBlocks.read(document)).size
    }.sum} blocks across ${Documents.size} documents")
  }

  it should "give a reason for every one it does not run" in {
    Documents.foreach { case (document, registry) =>
      registry.collect {
        case (key, Compiles(_, reason)) => (key, reason)
        case (key, NotRun(reason)) => (key, reason)
      }.foreach { case (key, reason) =>
        withClue(s"$document: the reason given for `$key` is too short to be one: ") {
          reason.length should be > 60
        }
      }
    }
  }

  /* -------------------------------------------------------------------- compiling and running */

  "Every block of those documents" should "compile as the document holds it, and run where it is run" in {
    // One compilation for all four, not one each: a compile costs a full classpath scan, measured
    // at 34 seconds for the first and about a second for each source after it, and isolation comes
    // from a block being an object's body rather than from the file it was read out of. The key
    // carries the document so that a failure names where to look.
    val prepared = Documents.flatMap { case (document, registry) =>
      val blocks = DocumentBlocks.blocksOf(document, DocumentBlocks.read(document))

      def textOf(key: String): String =
        blocks.find(names(_, key)).map(_.text).getOrElse(fail(s"$document holds no `$key`"))

      registry.collect {
        case (key, Runs(prelude)) => Prepared(s"$document: $key", prelude, textOf(key), run = true)
        case (key, Compiles(prelude, _)) =>
          Prepared(s"$document: $key", prelude, textOf(key), run = false)
      }
    }

    val outcome = DocumentBlocks.outcome("otherblocks", prepared)

    withClue(s"${outcome.errors} error(s), in the block(s) keyed by " +
      s"${outcome.blamed.mkString("; ")}\n${outcome.said}\n") {
      outcome.errors shouldBe 0
    }
    withClue(s"${outcome.threw.size} block(s) threw:\n${outcome.threw.mkString("\n")}\n") {
      outcome.threw shouldBe empty
    }

    info(s"${prepared.size} blocks compiled and ${prepared.count(_.run)} run")
  }

  /* ------------------------------------------------------------------------- the quotations */

  "The two blocks that are not programs" should "still be what the source says" in {
    // What a quotation buys that compiling does not: the configuration guide's copy of
    // `SimplificationConfig` would compile as a local class however far the real one had drifted,
    // and the `Expr` signatures do not compile at all. Both are compared against the file they are
    // lifted from, line by line, ignoring what indentation the document chose.
    def quoted(document: String, key: String): Vector[String] =
      DocumentBlocks
        .blocksOf(document, DocumentBlocks.read(document))
        .find(names(_, key))
        .getOrElse(fail(s"$document no longer holds the block keyed by `$key`"))
        .text
        .linesIterator
        .map(_.trim)
        .filter(_.nonEmpty)
        .toVector

    val guide = "SIMPLIFICATION_CONFIG_GUIDE.md"
    val config = DocumentBlocks.read("modules/core/src/main/scala/garden/xeno/symbolum/SimplificationConfig.scala")
    val expr = DocumentBlocks.read("modules/core/src/main/scala/garden/xeno/symbolum/Expr.scala")

    quoted(guide, "case class SimplificationConfig(").foreach { line =>
      withClue(s"`$line` is printed by $guide and is not in SimplificationConfig.scala: ") {
        config.linesIterator.map(_.trim).contains(line) shouldBe true
      }
    }

    quoted(guide, "final def simplify(implicit config").foreach { line =>
      // The source ends each signature with ` =` and puts its body on the next line; the document
      // prints the signature alone, which is the honest way to show a surface. So the comparison is
      // a prefix up to the return type rather than equality.
      val prefix = line.stripSuffix(": Expr")
      withClue(s"`$line` is printed by $guide and is not in Expr.scala: ") {
        expr.linesIterator.map(_.trim).exists(_.startsWith(prefix)) shouldBe true
      }
    }
  }

  /* ---------------------------------------------------------------- nothing is left uncovered */

  "The documents that hold a Scala block" should "be exactly the ones some spec compiles" in {
    // The assertion this file exists for, and the one that makes the family closed. The population
    // is read off the repository rather than out of a list, for the reason `ChainCoverageSpec`
    // gives about developments: a list that must cover an enumerated population cannot go quiet,
    // and a list that IS the population can. A document added tomorrow with an example in it fails
    // here, naming itself, instead of joining the set nobody compiles.
    val root = DocumentBlocks.locate("build.sbt").getParent

    val stream = Files.walk(root)
    val withBlocks =
      try
        stream
          .iterator()
          .asScala
          .filter(Files.isRegularFile(_))
          .filter(_.toString.endsWith(".md"))
          // `scratch/` is where this project's own rule says a probe goes, and it is gitignored, so
          // a document there is not a document of this repository: including it would let somebody
          // else's throwaway file turn this guard red. The other four are not source at all.
          .filterNot(path => Vector("/.git/", "/target/", "/third-party/", "/node_modules/", "/scratch/")
            .exists(path.toString.contains))
          .filter(path => Files.readString(path).linesIterator.exists(_.trim == "```scala"))
          .map(path => root.relativize(path).toString)
          .toVector
          .sorted
      finally stream.close()

    val covered = (Documents.map(_._1) :+ "README.md" :+ "docs/proving.md").sorted

    withClue(s"documents holding a Scala block that no spec compiles: " +
      s"${withBlocks.diff(covered).mkString(", ")}\n") {
      withBlocks.diff(covered) shouldBe empty
    }
    withClue(s"documents a spec claims and that hold no Scala block any more: " +
      s"${covered.diff(withBlocks).mkString(", ")}\n") {
      covered.diff(withBlocks) shouldBe empty
    }

    info(s"${withBlocks.size} documents hold a Scala block")
  }
}
