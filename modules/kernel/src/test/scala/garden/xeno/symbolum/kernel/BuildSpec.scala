package garden.xeno.symbolum.kernel

import java.net.URLClassLoader
import java.nio.file.{Files, Path}

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The classes say what they were built from, and the reader refuses a classpath that is not one
 * reproducible build.
 *
 * The first test reads the record the build actually wrote for this module and compares it with
 * git asked separately, which is the positive control the rest rest on: a generator that wrote
 * nothing, or wrote a commit from somewhere else, fails there and nowhere else. The others build
 * classpaths out of temporary directories, because the cases a certificate has to refuse are
 * exactly the ones this checkout is not in.
 *
 * Seen failing on 2026-09-25 against the defect it is for: with `++ identitySettings` removed from
 * `commonSettings` and `kernel/clean` run first, the first test failed with "no kernel record among
 * Vector()" and the other five passed. The `clean` was there so that no record an earlier build
 * wrote could answer instead; whether one would have is not measured. The same day `coverage` before the run turned the record's `instrumented` to `true`.
 */
class BuildSpec extends AnyFlatSpec with Matchers {

  private val Clean = "0123456789abcdef0123456789abcdef01234567"
  private val Other = "fedcba9876543210fedcba9876543210fedcba98"

  "The record this build wrote" should "name the kernel and the commit git names for this tree" in {
    val present = Build.modules().fold(faults => fail(faults.mkString("\n")), identity)
    val kernel = present.find(_.module == "kernel").getOrElse(
      fail(s"no kernel record among ${present.map(_.module)}; the resource generator in build.sbt wrote nothing")
    )
    val head = scala.sys.process.Process(Seq("git", "rev-parse", "HEAD")).!!.trim
    // A commit landing in this tree between the build writing the record and this line reading
    // git would fail this too. That is the incremental hazard the record exists to expose, seen
    // from the other side, and on a checkout nobody else is committing into it does not arise.
    withClue("the record names a commit other than the one this tree is at: ") {
      kernel.commit shouldBe Some(head)
    }
    kernel.version should not be empty
  }

  "A classpath of one clean build" should "answer with its commit" in {
    val loader = classpath(record("kernel", Clean), record("theories", Clean))
    Build.reproducibleCommit(loader) shouldBe Right(Clean)
    Build.modules(loader).map(_.map(_.module)) shouldBe Right(Vector("kernel", "theories"))
  }

  "A classpath that is not one build" should "be refused, naming every reason and not the first" in {
    val loader = classpath(
      record("kernel", Clean, dirty = "modules/kernel/src/main/scala/X.scala"),
      record("theories", Other, instrumented = true)
    )
    val reasons = Build.reproducibleCommit(loader).left.getOrElse(fail("a mixed classpath was accepted"))
    reasons.exists(_.contains("modules/kernel/src/main/scala/X.scala")) shouldBe true
    reasons.exists(_.contains("theories: compiled with the coverage instrumentation")) shouldBe true
    reasons.exists(_.contains("different commits")) shouldBe true
    reasons should have size 3
  }

  it should "be refused where the kernel is absent, which is the one module a certificate is about" in {
    // Without this case a classpath carrying only the theories' record would certify, and nothing
    // on it would say which kernel checked anything.
    Build.reproducibleCommit(classpath(record("theories", Clean))) shouldBe
      Left(Vector("no kernel record on this classpath"))
  }

  it should "be refused where the tree had no commit, rather than read as clean" in {
    // An absent commit is an absent answer: reading `unrecorded` as a commit nobody disagrees with
    // is the collapse `Refutation` keeps its seven answers apart to avoid.
    Build.reproducibleCommit(classpath(record("kernel", "unrecorded"))) shouldBe
      Left(Vector("kernel: built from a tree with no commit to name"))
  }

  "A record that cannot be read" should "be named with where it is and what is wrong, every one of them" in {
    val loader = classpath(
      "module=kernel\nversion=7.0.3\ncommit=HEAD\ndirty=\ninstrumented=false\n",
      "module=theories\nversion=7.0.3\ncommit=" + Clean + "\ndirty=\ninstrumented=maybe\n",
      "module=logic\nversion=7.0.3\n"
    )
    val faults = Build.modules(loader).left.getOrElse(fail("three unreadable records were read"))
    faults should have size 3
    faults.exists(fault => fault.contains("build.properties") && fault.contains("`commit` is `HEAD`")) shouldBe true
    faults.exists(_.contains("`instrumented` is `maybe`")) shouldBe true
    faults.exists(_.contains("no `commit`")) shouldBe true
  }

  private def record(
      module: String,
      commit: String,
      dirty: String = "",
      instrumented: Boolean = false
  ): String =
    s"module=$module\nversion=7.0.3\ncommit=$commit\ndirty=$dirty\ninstrumented=$instrumented\n"

  /** A class loader seeing only the given records, one classpath directory each. */
  private def classpath(records: String*): ClassLoader = {
    val roots = records.map { text =>
      val root = Files.createTempDirectory("build-spec")
      val file = root.resolve(Build.ResourceName)
      Files.createDirectories(file.getParent)
      Files.writeString(file, text)
      root
    }
    new URLClassLoader(roots.map((root: Path) => root.toUri.toURL).toArray, null)
  }
}
