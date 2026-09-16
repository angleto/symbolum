package garden.xeno.symbolum

import java.nio.file.{Files, Path, Paths}

import scala.jdk.CollectionConverters.*

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The numeric library stays on this side of the wall, asserted rather than described.
 *
 * No library anywhere produces `|- det (A * B) = det A * det B`. What a numeric library produces is
 * a number, and a number is evidence: `Spectrum` and `Perron` live in `modules/core` because that
 * is the module nothing on the proof side believes, and the arrangement only works while it stays
 * true.
 *
 * == What the build already enforces, and what it cannot ==
 *
 * `kernel`, `logic` and `theories` declare no path to `core`, so neither library is on their
 * compilation classpath at all and `IsolationSpec` in the kernel already asserts the shape of that
 * graph. `tactics` is different: it depends on `core` **and** on `theories`, because it is the
 * module where the algebra proposes and the kernel checks, so both arrive there transitively and
 * the build cannot stop them without severing the join the module exists for. A scan of the source
 * is what is left, and it is what this file does.
 *
 * == Which names, and why the list is longer than the classpath ==
 *
 * The dependency was Breeze until 2026-09-16 and is JTransforms and commons-math3 now. All three
 * are scanned for, and the retired one deliberately: a scan whose only word is a library nothing
 * can resolve any more passes over every source in the repository and reports nothing, which reads
 * exactly like a scan that found nothing wrong. Keeping the old name costs a string and catches the
 * session that reaches for the library the docstrings still talk about.
 *
 * `checker` is in the list for a different reason again. It depends on `theories` at test scope, so
 * it has no compile path to `core` either, and its whole value is being a second reader that agrees
 * with nothing; a numeric shortcut in it would be the worst place in the repository for one.
 *
 * A source scan is a weaker instrument than a build constraint and says so. It catches the import
 * somebody adds with a good reason on a Tuesday, which is the thing that actually happens, and it
 * would miss a reflective load, which is not.
 */
class NumericIsolationSpec extends AnyFlatSpec with Matchers {

  /** The modules that must not mention it, and the reason each one is in the list is above. */
  private val proofSide = Vector("kernel", "logic", "theories", "tactics", "checker")

  /**
   * What a numeric library is called in a source of this repository, current and retired.
   *
   * Package prefixes rather than artifact names, because what a scan of Scala sources can see is an
   * import. `breeze` is retired and is kept for the reason the docstring gives.
   */
  private val numericLibraries = Vector("breeze", "org.jtransforms", "org.apache.commons.math3")

  private def sourcesOf(module: String): Vector[Path] =
    Files
      .walk(Paths.get(s"modules/$module/src"))
      .iterator
      .asScala
      .toVector
      .filter(_.toString.endsWith(".scala"))

  private def mentions(module: String, words: String*): Vector[String] =
    sourcesOf(module).collect {
      case path if words.exists(Files.readString(path).contains) => s"$module: $path"
    }

  "The proof side" should "never name the numeric library" in {
    val offenders = proofSide.flatMap(module => mentions(module, numericLibraries*))

    withClue(
      "a number out of a numeric library is evidence and never a theorem; these files reach " +
        s"for one:\n${offenders.mkString("\n")}\n") {
      offenders shouldBe empty
    }
  }

  it should "not reach for the two files that use it either" in {
    // `Spectrum` and `Perron` are untrusted by construction, and the reason to keep them out of the
    // proof side is the same reason the library is kept out: a tactic that read a spectral radius
    // and believed it would have put a floating-point number inside a derivation. Nothing does
    // today, and this is what says so on the day somebody tries.
    val offenders = proofSide.flatMap(module => mentions(module, "Spectrum", "Perron"))

    withClue(s"these files name one of them:\n${offenders.mkString("\n")}\n") {
      offenders shouldBe empty
    }
  }

  "The exact arithmetic" should "not have been moved onto the numeric library" in {
    // `theories.Farkas` searches for a certificate by pivoting and its `Rational` is a pair of
    // `BigInt`: a certificate that is nearly a certificate is refused by the ring step afterwards,
    // so the exactness is what makes the search work rather than a preference. `Relation` runs at
    // hundreds of digits, where `Double` has sixteen and the method stops meaning anything. Both
    // are named here so that a session tempted to unify them onto one float library reads this
    // first.
    val farkas = Files.readString(
      Paths.get("modules/theories/src/main/scala/garden/xeno/symbolum/theories/Farkas.scala"))
    farkas should include("BigInt")
    farkas should not include "Double"

    val relation =
      Files.readString(Paths.get("modules/core/src/main/scala/garden/xeno/symbolum/Relation.scala"))
    relation should include("BigDecimal")
    numericLibraries.foreach(library => relation should not include library)
  }

  "The two files that do use one" should "name a library that is actually on the classpath" in {
    // The guard above passes by an empty scan, so it is the one assertion in this file that a
    // retired name would make vacuous rather than false: with `breeze` alone in the list and Breeze
    // gone, every module reports nothing and the file reads green. This is the other direction, and
    // it is what says the list is still pointed at something: the two untrusted files import a
    // library, and it is one of the names scanned for above.
    // An import line rather than the file, which is the difference between this assertion and no
    // assertion: both files talk about Breeze in their prose, so a scan of the whole source would
    // pass on the history alone.
    Vector("Spectrum", "Perron").foreach { name =>
      val imports = Files
        .readString(Paths.get(s"modules/core/src/main/scala/garden/xeno/symbolum/$name.scala"))
        .linesIterator
        .filter(_.startsWith("import "))
        .toVector

      withClue(s"$name imports none of ${numericLibraries.mkString(", ")}: $imports\n") {
        imports.exists(line => numericLibraries.exists(line.contains)) shouldBe true
      }
    }
  }
}
