package garden.xeno.symbolum

import java.nio.file.{Files, Path, Paths}

import scala.jdk.CollectionConverters.*

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The numeric library stays on this side of the wall, asserted rather than described.
 *
 * No library anywhere produces `|- det (A * B) = det A * det B`. What Breeze produces is a number,
 * and a number is evidence: `Spectrum` and `Perron` live in `modules/core` because that is the
 * module nothing on the proof side believes, and the arrangement only works while it stays true.
 *
 * == What the build already enforces, and what it cannot ==
 *
 * `kernel`, `logic` and `theories` declare no path to `core`, so Breeze is not on their compilation
 * classpath at all and `IsolationSpec` in the kernel already asserts the shape of that graph.
 * `tactics` is different: it depends on `core` **and** on `theories`, because it is the module
 * where the algebra proposes and the kernel checks, so Breeze arrives there transitively and the
 * build cannot stop it without severing the join the module exists for. A scan of the source is
 * what is left, and it is what this file does.
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
    val offenders = proofSide.flatMap(module => mentions(module, "breeze"))

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
    relation should not include "breeze"
  }
}
