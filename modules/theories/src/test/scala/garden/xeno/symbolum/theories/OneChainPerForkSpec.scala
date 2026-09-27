package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/**
 * No suite of this module builds a chain of its own, which is what keeps its test fork at one.
 *
 * Every suite here shares one JVM, and `Chain.standard` is a lazy value they all share, so the fork
 * holds one chain from the first suite that touches it until it exits. A chain keeps every
 * derivation it published, because a citation holds the fact it cites, and a second one built
 * beside it doubles the live heap: measured on 2026-09-26, 507 MB with one and 960 MB with two
 * against a heap of 1024, and `theories/test` died of `OutOfMemoryError` twice out of two on the
 * next link (Mycelium card 4222de0a). `ChainSpec` was that second chain until `a810c979`, which made
 * it read `Chain.standardMilliseconds` instead.
 *
 * `build.sbt` then ran `ChainSpec` in a JVM of its own, and that grouping is gone since 2026-09-27
 * by Angelo's decision on the same card: its reason had been removed at the source, and it cost a
 * second build of the chain per run while protecting nothing. This spec is what replaces it, and it
 * guards the property rather than the one suite that once broke it.
 *
 * Seen red on 2026-09-27 with a call appended to `ChainSpec`'s code, naming that file, and green
 * with the same call in a comment, through scala-cli over the classes of the tree that landed it;
 * `tools/verify/perturb-one-chain-per-fork.sh` is the same pair through sbt.
 *
 * WHAT IT DOES NOT COVER. A call spelled otherwise, `construct(` after an `import Chain.*`, or a
 * chain assembled by hand from `Real.construction`, is not a match. Today no test source does
 * either; a suite that needs a second chain for a reason is the case to raise, not to hide.
 */
class OneChainPerForkSpec extends AnyFlatSpec with Matchers {

  /** Spelled in two pieces so that this file, which is read below, does not match itself. */
  private val Call = "Chain.construct" + "("

  private lazy val testSources: Vector[Path] = {
    val root = Sources.repositoryRoot().resolve("modules/theories/src/test")
    Files.walk(root).iterator().asScala.filter(_.toString.endsWith(".scala")).toVector
  }

  private def code(path: Path): String = Sources.code(Sources.relative(path))

  "The test sources of theories" should "not build a chain beside the shared one" in {
    val building = testSources.filter(path => code(path).contains(Call)).map(Sources.relative)
    withClue(s"a second chain in the shared fork, from: ${building.mkString(", ")}\n") {
      building shouldBe empty
    }
  }

  it should "be read by an instrument that finds what is there" in {
    // The control on the empty answer above: the same reading of the same files finds the shared
    // chain in `ChainSpec`'s code, so an empty list is an absence and not a reader that saw nothing.
    testSources.size should be > 100
    testSources.filter(path => code(path).contains("Chain.standard")).map(Sources.relative) should
      contain("modules/theories/src/test/scala/garden/xeno/symbolum/theories/ChainSpec.scala")
  }
}
