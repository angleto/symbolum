package garden.xeno.symbolum.kernel

import java.io.File
import java.lang.management.ManagementFactory

import scala.jdk.CollectionConverters.*

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The tests of this module run in a JVM of their own, at the heap every figure was measured at,
 * asserted from inside that JVM rather than read off `build.sbt`.
 *
 * WHY. `Test / fork := true` in `commonSettings` is what stopped `tools/sbt test` dying of
 * `OutOfMemoryError` in every aggregated run on 2026-09-24 and 25: in the launcher, sbt 1.10.10
 * keeps a finished module's test state for the whole session and the aggregated run holds several
 * modules' chains at once. The comment on `Test / fork` in `build.sbt` carries the measurements.
 * Removing that line is one keystroke with a plausible reason at the time (a faster run, a debugger
 * that wants one JVM), and the suite would stay green on any run short enough to fit, which is
 * every run of one module: the defect shows only in the aggregated command, intermittently. So the
 * property is asserted where it holds, in the JVM the tests are running in.
 *
 * What it reads is `sun.java.command`, which names the main class of this process. A test forked by
 * sbt 1 runs under `sbt.ForkMain` and one forked by sbt 2, which this build has run since
 * 2026-09-25, under `sbt.internal.worker1.WorkerMain`; a test run inside the launcher runs under the
 * launcher's jar. Any other runner, an IDE's for instance, is none of those, and the tests below
 * cancel there rather than fail, because what they guard is this build's configuration and not
 * every way of running a suite.
 *
 * **Until 2026-09-26 it knew only `sbt.ForkMain`, and under sbt 2 all three tests cancelled**: the
 * verification of card 775d62f0 read `succeeded 0, canceled 3` from `kernel/testOnly` with
 * `sun.java.command` naming `WorkerMain`, and the whole suite had reported kernel as green with
 * three cancelled, which is this guard switched off and read as a pass. A cancellation counts as
 * nothing failing, so a guard whose precondition stops matching goes quiet rather than red. The
 * worker's name is matched on its package prefix `sbt.internal.worker`, not on the `1`.
 *
 * Seen failing on 2026-09-25 against the defect it is for: `tools/sbt "set kernel / Test / fork :=
 * false" "kernel/testOnly ...ForkedTestJvmSpec"` failed the first test, `sun.java.command` naming
 * the launcher's `sbt-launch.jar`, and passed the other two, the launcher's own heap being 1g too.
 * The verification of 775d62f0 saw the same red under sbt 2 on 2026-09-26. What this file says
 * about the run with the fork in place under sbt 2 is in the card, and the run is recorded there.
 *
 * WHAT IT DOES NOT COVER. It runs in `kernel`, so a project that does not take `commonSettings` could
 * run its tests in the launcher and nothing here would see it; and it says nothing about the forks
 * running one at a time, which `Tags.ForkedTestGroup` in `build.sbt` limits and which a test inside
 * one fork cannot observe.
 */
class ForkedTestJvmSpec extends AnyFlatSpec with Matchers {

  private val command = Option(System.getProperty("sun.java.command")).getOrElse("")

  private def runBySbt(): Unit = {
    val forked = command.startsWith("sbt.ForkMain") || command.startsWith("sbt.internal.worker")
    val launcher = command.contains("sbt-launch") || command.contains("xsbt.boot")
    assume(forked || launcher, s"not run by sbt (sun.java.command is `$command`), so this build's settings are not what is asked")
  }

  "The tests of this module" should "run in a JVM sbt forked for them, not in the launcher" in {
    runBySbt()
    withClue(s"sun.java.command is `$command`; `Test / fork := true` in build.sbt's commonSettings is gone: ") {
      (command.startsWith("sbt.ForkMain") || command.startsWith("sbt.internal.worker")) shouldBe true
    }
  }

  it should "run at the one gigabyte heap every figure in this repository was measured at" in {
    runBySbt()
    // The argument and not `Runtime.maxMemory`, which reports the heap less one survivor space and
    // so is not the number anybody wrote.
    val arguments = ManagementFactory.getRuntimeMXBean.getInputArguments.asScala.toVector
    arguments.filter(_.startsWith("-Xmx")).lastOption shouldBe Some("-Xmx1024m")
  }

  it should "run in the build's root, where the suites read `docs/` and the sources from" in {
    runBySbt()
    new File("build.sbt").isFile shouldBe true
  }
}
