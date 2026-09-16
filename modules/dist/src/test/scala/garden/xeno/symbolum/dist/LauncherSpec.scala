package garden.xeno.symbolum.dist

import java.io.{ByteArrayOutputStream, PrintStream}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import garden.xeno.symbolum.examples.WhatAClaimCosts
import garden.xeno.symbolum.tactics.Find

/**
 * Every launcher the tarball ships is entered by something, which the allowlist did not say.
 *
 * `build.sbt` names five main classes for `JavaAppPackaging`, and `DocumentationSpec` asserts the
 * five appear in that file. Nothing asserted that any of them WORKS. That is the repository's own
 * rule about what counts as built, unapplied to the file it cites as the first demonstration of the
 * proof half: a tactic is built when it has proved something end to end, not when it compiles and
 * its unit tests pass.
 *
 * == The count this file was opened on was too small, and the criterion is why ==
 *
 * The card that asked for this counted a launcher as exercised when a spec named its object, and
 * got two uncovered of five. That criterion answers a different question from the one the tarball
 * asks. A tarball runs `main`, and `main` is where a launcher's own work lives: `Find.main` joins
 * its arguments with spaces, because `sbt` and a shell both hand them over already split, and
 * prints a usage line when there are none. `FindSpec` drives `Find.of`, which is downstream of
 * both. Counted again on 2026-09-16 by looking for `<Launcher>.main(` rather than for the name:
 *
 *   - `Ask`, entered by `AskSpec`;
 *   - `Find`, entered by nothing until this file;
 *   - `Notebook`, entered by nothing, and it cannot be entered (below);
 *   - `examples.WhatAClaimCosts`, entered by nothing until this file;
 *   - `dist.Repl`, entered by nothing, and it cannot be entered (below).
 *
 * Four of five rather than two. The looser criterion also over-counts in a way worth naming,
 * because it is how it produced the smaller number: `Notebook` matches in `StyleSpec` and in
 * `RealSpec`, and both are the string `"Notebook.scala"` in a list of file paths, not a call.
 *
 * == Two of them cannot be entered, and that is said rather than forced ==
 *
 * `Notebook.main` blocks on a latch so that `sbt runMain` does not take the server down with it,
 * and `Repl.main` delegates to the Scala REPL, which reads stdin. A spec that called either would
 * hang the suite. [[CannotBeEntered]] is the list, each with the reason, and what is checked for
 * those two is everything except the delegation.
 *
 * == Why the file is here, which the module graph decides rather than a preference ==
 *
 * `examples` and `dist` had no test sources at all, and the alternative considered first was to
 * keep this beside `DocumentationSpec` in `tactics` and point it at the two modules. It cannot
 * work, and the reason is the direction of the graph: `examples` depends on `tactics`, so nothing
 * in `tactics` can name `WhatAClaimCosts`, and a test there could only assert about its text, which
 * is the defect rather than the repair. `dist` depends on `tactics` **and** `examples`, so it is
 * the one module that can name every launcher it ships: one test source set instead of two, in the
 * module that owns the tarball.
 */
final class LauncherSpec extends AnyFlatSpec with Matchers {

  /**
   * The launchers whose `main` does not return, with why.
   *
   * A list rather than a silence, and the reasons are long because a one-word reason is how an
   * exemption outlives what justified it. Anything not here owes a spec that enters `main`.
   */
  private val CannotBeEntered: Map[String, String] = Map(
    "garden.xeno.symbolum.tactics.Notebook" ->
      ("`main` blocks on a CountDownLatch after starting the server, deliberately, because " +
        "`HttpServer.start` returns as soon as it is listening and a `main` that ended there would " +
        "have `sbt runMain` report success and take the server down with it"),
    "garden.xeno.symbolum.dist.Repl" ->
      ("`main` delegates to the Scala REPL, which reads stdin and does not return, so a spec that " +
        "called it would hang the suite rather than fail it")
  )

  private def read(relative: String): String = {
    val path = Paths.get(relative)
    withClue(
      s"$relative is read from the repository root, and the working directory is " +
        s"${Paths.get("").toAbsolutePath}\n"
    ) {
      Files.exists(path) shouldBe true
    }
    new String(Files.readAllBytes(path), StandardCharsets.UTF_8)
  }

  /**
   * What a launcher printed.
   *
   * `Console.withOut` and not `System.setOut`, which was the first version and captured nothing.
   * `Predef.println` goes to `Console.out`, which holds the value `System.out` had when `Console`
   * was first touched, so replacing `System.out` afterwards redirects a stream nobody is writing
   * to. The failure is silent in the dangerous direction: every assertion below was made against
   * an empty string and reported as "did not include", which reads like the launcher printing the
   * wrong thing rather than like the harness reading the wrong stream.
   */
  private def capturing(body: => Unit): String = {
    val captured = new ByteArrayOutputStream()
    Console.withOut(new PrintStream(captured, true, StandardCharsets.UTF_8))(body)
    new String(captured.toByteArray, StandardCharsets.UTF_8)
  }

  /**
   * The allowlist as `build.sbt` holds it, parsed rather than copied.
   *
   * A second hand-written list here would be the thing this file exists against: it would agree
   * with the build on the day it was written and be the only thing still saying five when the
   * build said six.
   */
  private lazy val shipped: Vector[String] = {
    val build = read("build.sbt")
    val at = build.indexOf("Compile / discoveredMainClasses := Seq(")

    withClue("build.sbt no longer assigns `Compile / discoveredMainClasses`: ") {
      at should be >= 0
    }

    val block = build.substring(at, build.indexOf(")", at))
    """"([a-zA-Z0-9_.]+)"""".r.findAllMatchIn(block).map(_.group(1)).toVector
  }

  /**
   * The text of every spec in the repository, which is where "entered by something" is looked for.
   *
   * A walk rather than a list, for the reason `StyleSpec` gives about its own: a list is right on
   * the day it is written, and a module added later is invisible to it. The suffix is the file name
   * and not the class, so this reads every suite exactly as long as every suite lives in a file
   * named after it, which is not an assumption made here but an assertion made there: `StyleSpec`
   * fails when a class the framework will run sits in a file that does not carry its name and end
   * in `Spec`. A count of suites pinned here instead would be a second site for that one invariant.
   * And if a suite ever does escape that clause, this walk misses it in the safe direction: a spec
   * it does not read cannot make the gate pass wrongly, only fail wrongly.
   *
   * This paragraph said the repository held one suite outside the convention and that the walk
   * therefore under-read by one. The number was **zero on the day the sentence was written**, not
   * made zero afterwards: the file it meant, `NegativeFractionTestSimple.scala`, had been renamed
   * nine minutes earlier by `13992fe`, which is the commit that added the `StyleSpec` clause above
   * and is an ancestor of the one that wrote this. A sentence born false is not caught by asking
   * when it stopped being true.
   */
  private lazy val specs: Vector[String] = {
    val stream = Files.walk(Paths.get("modules"))
    try
      stream
        .filter(path => path.getFileName.toString.endsWith("Spec.scala"))
        .map[String](path => new String(Files.readAllBytes(path), StandardCharsets.UTF_8))
        .toArray(size => new Array[String](size))
        .toVector
    finally stream.close()
  }

  /**
   * Which of `launchers` no spec enters through `main`, excusing the ones named.
   *
   * A function rather than a block inside the assertion, so that it can be put to an input whose
   * answer is known. The test below does that, and it is what separates "nothing is unentered" from
   * "the scan found nothing", which a green run cannot tell apart.
   */
  private def unentered(launchers: Vector[String], excused: Set[String]): Vector[String] =
    launchers.filterNot { entry =>
      val simple = entry.split('.').last
      excused.contains(entry) || specs.exists(_.contains(s"$simple.main("))
    }

  "The distribution's allowlist" should "be read from the build, and be the launchers rather than everything" in {
    // What would make every assertion below vacuous is an empty parse: a rename of the setting or a
    // reformatting that moves the closing parenthesis, and this file passes while checking nothing.
    // So the parse is asserted to have found something, and asserted NOT to have found the mains
    // that regenerate documents, which `DocumentationSpec` names as what must stay out. An empty
    // result fails the first; a parse that swallowed the file fails the second.
    shipped should not be empty
    shipped should contain("garden.xeno.symbolum.dist.Repl")
    shipped should not contain "garden.xeno.symbolum.theories.Lemmas"
  }

  it should "be a list of obligations: every launcher's `main` is entered, or is excused by name" in {
    // The half the allowlist did not carry. `DocumentationSpec` says what MAY ship; this says what
    // ships must be entered where it can be, and the criterion is `<Launcher>.main(` rather than
    // the launcher's name, for the reason the class comment gives.
    val missing = unentered(shipped, CannotBeEntered.keySet)

    withClue(
      "these ship in the tarball and no spec calls their `main`; write one, or add the launcher " +
        "to `CannotBeEntered` with the reason it cannot return:\n  " + missing.mkString("\n  ") + "\n"
    ) {
      missing shouldBe empty
    }
  }

  it should "report a launcher nobody enters, which is what makes the test above worth running" in {
    // The assertion above is `shouldBe empty`, and an empty answer is what a broken scan returns
    // too: a walk that found no files, a criterion that matches nothing, a parse that yielded no
    // launchers. Each of those makes it pass while checking nothing, and none of them is visible in
    // a green run. So the same function is put to an input whose answer is known.
    val ghost = "garden.xeno.symbolum.nowhere.NoSuchLauncher"

    unentered(Vector(ghost), Set.empty) shouldBe Vector(ghost)

    // And the excuse is what takes it off the list, rather than the scan finding it after all.
    unentered(Vector(ghost), Set(ghost)) shouldBe empty

    // And a launcher that IS entered is not reported, which is the third way the function could be
    // wrong: one that always answers "unentered" would pass the two assertions above.
    unentered(Vector("garden.xeno.symbolum.tactics.Ask"), Set.empty) shouldBe empty
  }

  it should "excuse only launchers it ships, so a stale excuse fails rather than sits" in {
    // The other direction, and the one an exemption list loses first. An entry here for a launcher
    // the build no longer names is an excuse for nothing, and it would keep passing for ever.
    CannotBeEntered.keys.toVector.diff(shipped) shouldBe empty

    // And the reason has to be a reason. `StyleSpec` makes the same demand of its own exemptions,
    // for the same cause: a one-word excuse outlives whatever justified it.
    CannotBeEntered.values.foreach(reason => reason.length should be > 60)
  }

  /* ------------------------------------------------------------- the demonstration, run */

  private lazy val demonstration: String = capturing(WhatAClaimCosts.main(Array.empty))

  "`WhatAClaimCosts`" should "run end to end and report on every claim it makes" in {
    // Running it is the point. The class builds `Cost.construct(Chain.standard)` and puts four
    // claims to the whole tactic surface, so this is the one gate that fails when the demonstration
    // a reader is pointed at stops demonstrating.
    demonstration should include("WHAT A CLAIM COSTS")

    // Named rather than counted, because a count says four arrived and not which four.
    demonstration should include("a ring identity over the reals")
    demonstration should include("an order fact")
    demonstration should include("a claim about the naturals")
    demonstration should include("the decision procedures still do not decide")
  }

  it should "still carry the one it cannot settle, which is what the page is for" in {
    // The assertion a gate written to check that the demonstration "works" would not have. Its own
    // documentation says a page made only of successes teaches that the tool answers, which is the
    // one thing about it that is not true, and the fourth claim is true and unproved on purpose. A
    // change that quietly started proving it, or dropped it, changes what the page teaches.
    demonstration should include("?y:real. y * y = x")
  }

  /* ------------------------------------------------------------------ the one nobody had entered */

  "`Find`" should "be entered through `main`, where the argument joining lives" in {
    // `FindSpec` drives `Find.of`, which is downstream of everything `main` does. What `main` adds
    // is the join: `sbt` and a shell both split a query into words before this sees it, so a shape
    // written `x:real + y:real = y + x` arrives as seven arguments and has to be put back. Calling
    // `of` with the joined string never exercised that, and it is the one thing a caller of the
    // launcher gets wrong.
    //
    // Asserted as an equality against `of` on the joined text rather than on the wording of the
    // answer, and the first version of this test is why. It asserted that the output held a `+` and
    // did not say "nothing to look for", and BOTH survive a `main` that dropped the join: the query
    // would be `x:real`, which is a name search that answers rather than an empty one, so neither
    // assertion could tell the two apart. What separates them is only that the two calls agree.
    val words = Array("x:real", "+", "y:real", "=", "y", "+", "x")
    val found = capturing(Find.main(words))

    found.trim shouldBe Find.of(words.mkString(" ")).trim

    // And not vacuously, which an equality between two empty strings would be: `of` is asked three
    // questions and prints a heading for each, including the empty ones.
    found should not be empty
    found.linesIterator.size should be > 1
  }

  it should "say what to do when it is given nothing, rather than answering about nothing" in {
    // The empty path, which is the other half of `main` and prints usage. Without this the branch
    // is unentered and the sentence a caller meets first is whatever it has decayed into.
    val empty = capturing(Find.main(Array.empty))

    empty should include("nothing to look for")
    empty should include(Find.Annotated)
  }

  /* ------------------------------------------------------------------ the one that cannot run */

  "`Repl`" should "pass the process's own classpath, under the flag the REPL reads" in {
    // Everything except the delegation. `Repl.arguments` was split out of `main` for this: the
    // launcher's documentation makes three claims about what it starts the REPL with, and none of
    // them could be checked while they were inside a call that does not return.
    val built = Repl.arguments(Array("-usejavacp"))

    built.head shouldBe "-classpath"
    built(1) shouldBe System.getProperty("java.class.path")

    // Appended and not prepended, which the class documents as what lets a caller override: the
    // REPL reads the LAST `-classpath` it is given.
    built.last shouldBe "-usejavacp"
  }

  it should "be named the same thing by the launcher, the README and the release notes" in {
    // Three hand-written copies of `bin/symbolum-repl` with nothing comparing them. `Repl.Command`
    // is the declaration; these two are citations, and they go red together when it moves.
    read("README.md") should include(Repl.Command)
    read(".github/workflows/publish.yml") should include(Repl.Command)
  }

  it should "carry the prefix the build's own renaming adds, so a rename on either side stops matching" in {
    // What `Repl.Command` is worth depends on it naming the script that exists. Packaging derives
    // `bin/repl` from the simple name of the main class and `build.sbt` rewrites every `bin/` entry
    // by prefixing `symbolum-`. Neither step is reproduced here: what is asserted is that the two
    // ends agree.
    Repl.Command shouldBe s"bin/symbolum-${"Repl".toLowerCase}"
    read("build.sbt") should include("s\"symbolum-$name\"")
  }
}
