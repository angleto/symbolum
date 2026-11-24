import java.io.File
import javax.xml.parsers.DocumentBuilderFactory

import sbt.*

/**
 * The verdict of a forked test run, read from the reports ScalaTest writes rather than only from
 * the events sbt counts.
 *
 * WHY, measured on 2026-11-24, Mycelium card f0016ec8, on sbt 2.0.9 with `Test / fork := true`. A
 * test failing with an exception whose message is longer than somewhere between 60 000 and 70 000
 * characters reaches sbt's result as no failure at all: ScalaTest prints `failed 1`, and sbt prints
 * `[success]` and exits 0. Perturbing one assertion of `scan`'s `CommentsSpec` into a `throw`: a
 * short message and one of 60 000 characters exited 1 under `scan/testOnly`; 70 000 and 100 000
 * exited 0; and 100 001 exited 0 under `scan/test`, which is what `tools/sbt test` and CI run. The
 * message "the standard chain does not build", which prints whole terms, is over that length as a
 * rule, so a broken derivation, the commonest defect here, was the one the gate could not see. An
 * audit of the 40 latest green CI runs found no failed test hidden that way.
 *
 * WHERE IT IS LOST is not located. The fork sends each event as one JSON line (`ForkTestMain`: Gson,
 * then `println`); `sbt.ForkTests` parses each line inside `catch case NonFatal(_) => ()`, which
 * would drop an event without a word, and computes the overall result from the events it kept.
 * `java.util.Scanner`, which splits the lines, was seen reading a line of 100 008 characters whole,
 * and `writeUTF`'s 65 535-byte limit is not on the path. So this does not repair the channel: it
 * stops the verdict depending on it alone.
 *
 * WHAT IT DOES. ScalaTest's JUnit XML reporter, `-u`, writes one file per suite. A `Tests.Setup`
 * empties the directory before the fork starts, so every file read was written by this run. After
 * `Test / testFull` has returned, [[verdict]] reads them, prints what it read, refuses naming each
 * suite with a failure or an error, and refuses when the set of reports is not the set of suites sbt
 * discovered. The long-message failure above, perturbed again with this in place, wrote
 * `failures="1"` into its report while sbt's own result said it passed: the report is the half that
 * survives.
 *
 * WHY AFTER `testFull` AND NOT IN A `Tests.Cleanup`, which runs for `testOnly` too and was the first
 * version. Measured the same day: a cleanup ran before the reports existed, every time, reading 0
 * suites on a passing run, a short failure and a long one, while the report was on disk a fraction
 * of a second later; after `testFull` returns it is there. Why sbt runs the cleanup first was not
 * established, and a cleanup that waited for the file would be guessing at a deadline.
 *
 * WHAT IT DOES NOT COVER. `testOnly` and `testQuick` do not go through `testFull`, so they keep
 * sbt's verdict alone and a long-message failure still reads green there: read ScalaTest's summary
 * in their log, which is what `tools/verify/` already says to do. And it reads what ScalaTest says,
 * so a suite ScalaTest itself mis-reports is out of its reach, as it was before.
 */
object ForkedVerdict {

  /** Where ScalaTest writes one JUnit XML file per suite, under the module's `target`. */
  def directory(target: File): File = target / "scalatest-verdict"

  def options(target: File): Seq[TestOption] = {
    val reports = directory(target)
    Seq(
      Tests.Setup { () =>
        IO.delete(reports)
        IO.createDirectory(reports)
      },
      Tests.Argument(TestFrameworks.ScalaTest, "-u", reports.getAbsolutePath)
    )
  }

  /** One suite as its report states it. */
  final case class Report(suite: String, tests: Int, failures: Int, errors: Int)

  def reports(reportDirectory: File): Seq[Report] = {
    val files = Option(reportDirectory.listFiles()).toSeq.flatten
      .filter(file => file.getName.startsWith("TEST-") && file.getName.endsWith(".xml"))
      .sortBy(_.getName)
    files.map { file =>
      val root = DocumentBuilderFactory.newInstance().newDocumentBuilder().parse(file).getDocumentElement
      def count(attribute: String): Int =
        Option(root.getAttribute(attribute)).filter(_.nonEmpty).map(_.toInt).getOrElse {
          throw new IllegalStateException(s"$file: a <testsuite> without `$attribute`")
        }
      Report(root.getAttribute("name"), count("tests"), count("failures"), count("errors"))
    }
  }

  /**
   * Refuse a run whose reports name a failure or an error, or whose reports are not exactly one per
   * suite sbt discovered. The second half is what keeps an absent report from reading as a pass,
   * which is the absence this file exists to stop being read as a verdict.
   */
  def verdict(reportDirectory: File, discovered: Seq[String], log: Logger): Unit = {
    val read = reports(reportDirectory)
    // Printed whatever it finds, so that a run shows the reports were read: a verdict that says
    // nothing when it passes cannot be told apart from one that never ran.
    log.info(
      s"the fork's own reports: ${read.size} suites, ${read.map(_.tests).sum} tests, " +
        s"${read.map(r => r.failures + r.errors).sum} failed or in error, in $reportDirectory")

    val failed = read.filter(report => report.failures + report.errors > 0)
    if (failed.nonEmpty)
      throw new MessageOnlyException(
        failed
          .map(report =>
            s"${report.suite}: ${report.failures} failed and ${report.errors} in error of ${report.tests}")
          .mkString(
            "ScalaTest's own reports say these suites did not pass, whatever sbt reported above:\n  ",
            "\n  ",
            s"\nread from $reportDirectory; Mycelium card f0016ec8 is why sbt's verdict is not trusted alone"
          )
      )

    val written = read.map(_.suite).toSet
    val expected = discovered.toSet
    val missing = expected -- written
    val unexpected = written -- expected
    if (missing.nonEmpty || unexpected.nonEmpty)
      throw new MessageOnlyException(
        s"the reports in $reportDirectory are not one per suite discovered: " +
          s"no report from [${missing.toSeq.sorted.mkString(", ")}]; " +
          s"a report from no discovered suite: [${unexpected.toSeq.sorted.mkString(", ")}]"
      )
  }
}
