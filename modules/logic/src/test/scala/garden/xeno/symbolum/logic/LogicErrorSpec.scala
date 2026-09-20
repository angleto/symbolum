package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * What a refusal's standing lets a caller conclude, and the two questions every standing answers.
 *
 * `LogicError.Standing` exists because a consumer read an exhausted search as a refutation and
 * published it. Until 2026-09-16 the enumeration protected one direction and not the other: the
 * abstract `standing` on the trait means a **refusal** added to that file does not compile until it
 * says which of the three it carries, and nothing at all said what a **standing** added to the enum
 * means. Its four readers were equality comparisons, so a fourth case would have compiled in
 * silence and every one of them would have answered `false` about it.
 *
 * [[LogicError.Standing.answersTheGoal]] and [[LogicError.Standing.stoppedShort]] are the repair
 * and the compiler is what enforces it. That part is **not** asserted here, and the reason is worth
 * a line rather than a silence: what would have to be tested is that adding a case fails to compile,
 * and a suite cannot add a case to an enum it compiles against. It was measured by hand instead, by
 * adding a fourth case in a worktree and reading the two errors the compiler gave, and the
 * measurement is in the commit that added this file and on card `db03f949`. It is not restated here,
 * where it would be prose claiming a check nobody runs.
 *
 * What this file does assert is the table those two matches hold, in both directions, and the
 * thing that would make the table meaningless.
 */
class LogicErrorSpec extends AnyFlatSpec with Matchers {

  import LogicError.Standing

  "A standing" should "answer the two questions the readers ask, one row per case" in {
    // The table, written out rather than summarised, because it is what a fourth case has to extend
    // and a reader comparing this file with the enum should be able to do it line by line.
    Standing.Decided.answersTheGoal shouldBe true
    Standing.Decided.stoppedShort shouldBe false

    Standing.Exhausted.answersTheGoal shouldBe false
    Standing.Exhausted.stoppedShort shouldBe true

    Standing.Unread.answersTheGoal shouldBe false
    Standing.Unread.stoppedShort shouldBe false
  }

  it should "be read by two questions that are not one question, which is what a single flag lost" in {
    // What makes the table above worth asserting. Both predicates written as `_ => false` satisfy
    // four of its six lines, and the two that are left are the only thing separating a real pair of
    // questions from a pair of constants. So they are asserted as a pair here: each is true
    // somewhere, they are nowhere true together, and there is a case where both are false.
    //
    // The last of those three is the one that says a single boolean would not have done. `Unread`
    // is neither an answer nor a stop, and a `decided` flag alone cannot say which of the two a
    // caller is looking at.
    Standing.values.count(_.answersTheGoal) should be > 0
    Standing.values.count(_.stoppedShort) should be > 0
    Standing.values.filter(standing => standing.answersTheGoal && standing.stoppedShort) shouldBe empty
    Standing.values.filter(standing => !standing.answersTheGoal && !standing.stoppedShort) should not be empty
  }

  it should "be the reading `decided` is written in terms of, at every case rather than at one" in {
    // `LogicError.decided` used to compare against `Standing.Decided` itself, so the enum had a
    // reader of its own that a new case would not have reached. It goes through the match now, and
    // this asserts the two agree over real refusals rather than over the case somebody remembered.
    //
    // Real refusals and not a stand-in: `LogicError` is sealed, so a suite cannot invent one
    // carrying a chosen standing, and the three below are the ones the file gives.
    val goal = Term.variable("x", Type.Bool)
    val samples: Vector[LogicError] = Vector(
      DoesNotFollow(goal, "a procedure that searched to the end"),
      BoundReached("a limit", 1, 0, goal),
      SyntaxError("a text that does not read", 0)
    )

    samples.foreach { refusal =>
      withClue(s"${refusal.standing}: ") {
        LogicError.decided(Left(refusal)) shouldBe refusal.standing.answersTheGoal
      }
    }

    // And the guard that keeps the loop above from shrinking without anybody noticing: the samples
    // cover the enumeration. A case added to `Standing` is caught twice over -- once by the
    // compiler, at the two matches, and once here, because no sample carries it and this is what
    // says the agreement was checked at every kind of refusal rather than at one.
    samples.map(_.standing).distinct should contain theSameElementsAs Standing.values.toSeq
  }

  it should "rest on a build setting, which is therefore asserted rather than assumed" in {
    // The whole mechanism is one compiler diagnostic, and it is a WARNING. Measured on 2026-09-16
    // against Scala 3.3.5 with a three-case enum and a two-case match: without `-Xfatal-warnings`
    // the compiler says "match may not be exhaustive ... It would fail on pattern case: Blue" and
    // compiles the file; with it, the same diagnostic is `[E029] Pattern Match Exhaustivity Error`
    // and the build stops. So the guard the two matches above give is held by a line in `build.sbt`,
    // and removing that line would take it away without failing anything -- which is the silence
    // this file exists against, one level down.
    //
    // Asserted here rather than in a style spec because this is the only guard in the repository
    // that is nothing but the flag: everything else `-Xfatal-warnings` catches is caught the day
    // somebody reads the warning, and an omitted case is caught by nobody.
    //
    // WHAT THIS TEST DOES NOT COVER, said here since 2026-09-18 rather than left to be assumed. It
    // reads text, so what it establishes is that the flag is WRITTEN. It is silent on whether the
    // flag ARRIVES at the compiler, and those came apart in this repository already: `sbt doc`
    // takes none of these options, its own log says `Skipping unused scalacOptions: -Werror`, and
    // 57 unresolved scaladoc links were reported as warnings under an exit 0 while this assertion
    // was green throughout. A scope, a later `scalacOptions :=` in place of a `++=`, or a plugin
    // that replaces the list would each do the same to the compiler.
    //
    // WHO COVERS IT: the `fatalWarnings` task in `build.sbt`, which reads the effective options of
    // every project holding sources and then compiles a source that has to fail because of the
    // flag, against a control compiling the same source without it. It is not a command somebody
    // remembers: `Test / test` on the root depends on it, so it runs under `tools/sbt test` and in
    // CI. A test in this suite cannot be that check -- nothing a compiled program reads at runtime
    // says which diagnostics were emitted when it was compiled -- which is why the strong half
    // lives in the build and this half stays here, beside the guard it is about.
    val build = new String(
      java.nio.file.Files.readAllBytes(java.nio.file.Paths.get("build.sbt")),
      "UTF-8"
    )

    // Not vacuous on an empty read: a wrong working directory gives the empty string, which
    // contains nothing, so the assertion below would fail rather than pass. Said out loud because
    // the opposite arrangement -- asserting an absence -- would have passed.
    withClue(
      s"build.sbt is read from the repository root, and the working directory is " +
        s"${java.nio.file.Paths.get("").toAbsolutePath}\n"
    ) {
      build should not be empty
    }

    // Either spelling, and the reason is a measurement rather than tolerance: run directly on
    // 2026-09-18, the 3.3.5 compiler turns this file's own diagnostic into an error and writes no
    // class file under `-Xfatal-warnings` and under `-Werror` alike, where under neither it warns
    // and writes seven. A test that insisted on the spelling this build happens to use would go
    // red on a rename that changes nothing, and a gate red for the wrong reason is repaired by
    // loosening it.
    withClue("neither spelling of the option is in build.sbt: ") {
      Vector("-Xfatal-warnings", "-Werror").exists(build.contains) shouldBe true
    }

    // And that the strong check is wired to something that runs. The task can say the flag is
    // dead; it cannot say that nobody invokes it, and a gate nothing calls is the failure this
    // file's own subject is about moved one step along. This is text again, and deliberately: what
    // it guards is a line rather than a value reaching a tool, so the failure that defeated the
    // assertion above has no counterpart here.
    withClue("`fatalWarnings` is defined and something runs it: ") {
      build should include("lazy val fatalWarnings = taskKey[Unit]")
      build should include("Test / test := (Test / test).dependsOn(fatalWarnings).value")
    }
  }

  it should "say no about a result that is not a refusal at all" in {
    // The half of `decided` that has nothing to do with the enum, and the one its own documentation
    // calls out: a proof is not a decision that something does not follow.
    LogicError.decided(Right(())) shouldBe false
  }
  /**
   * The two counts of the partial-instance refusal, at one and elsewhere.
   *
   * `logic` sits below `theories`, so it cannot see the counter the rest of the repository uses
   * and carries its own in `Plural`. Both numbers here reach one independently: a theorem with one
   * leading quantifier is the ordinary case, and a call that supplied one argument is what the
   * refusal is usually about.
   *
   * The same pair of numbers is written a second time by `Remedy` one module up, which reaches
   * `Prose.count` instead. Two messages about one refusal is the arrangement here, not a defect.
   */
  "The refusal about a partial instance" should "take the singular at one and the plural elsewhere" in {
    val subject = Term.variable("p", Type.Bool)

    def message(quantifiers: Int, arguments: Int): String =
      PartialInstance(quantifiers, arguments, subject).message

    message(1, 1) should startWith("this theorem has 1 leading quantifier and 1 argument were given")
    message(3, 2) should startWith("this theorem has 3 leading quantifiers and 2 arguments were given")
  }
}
