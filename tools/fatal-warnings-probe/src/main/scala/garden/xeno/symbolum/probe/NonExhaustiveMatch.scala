package garden.xeno.symbolum.probe

/**
 * A source that MUST NOT compile under this build's options, and that must compile without one of
 * them. It is the positive control for `-Xfatal-warnings`: an instrument that reports an absence is
 * worth nothing until it has been seen finding something known to be present, and "no warning was
 * turned into an error" is exactly such an absence.
 *
 * == Why a file and not an assertion ==
 *
 * `LogicErrorSpec` asserts that `-Xfatal-warnings` is WRITTEN in `build.sbt`, which is a different
 * claim from its arriving at the compiler, and this repository already holds a case where the two
 * came apart: `sbt doc` takes none of these options, the log says `Skipping unused scalacOptions:
 * -Werror`, and 57 unresolved scaladoc links were reported as warnings under an exit 0. Scope is
 * the easiest of the three ways to lose the flag without noticing; the other two are a later
 * `scalacOptions :=` in place of a `++=`, and a plugin that replaces them.
 *
 * Nothing a test can read at runtime says a diagnostic was emitted when this repository was
 * compiled, so the only instrument that sees the flag do its work is a compilation that has to
 * fail. `fatalWarnings` in `build.sbt` is what runs it.
 *
 * == Why it is here and not under `modules/` ==
 *
 * A file that must not compile cannot live in a source set the build compiles: `sbt compile` and
 * `sbt test` would be red on every tree. So this sits outside `modules/`, in a project the root
 * does not aggregate, and it is reached only by the task that expects it to fail. The cost is that
 * the scans over `modules/` -- the style scan, the language scan, the comment census -- do not read
 * this file, which is stated here rather than discovered: what protects it is that it is fifteen
 * lines and that the gate reads it twice, once expecting a failure and once expecting a success.
 *
 * == Why this warning ==
 *
 * The exhaustivity of a match is the one guard in this repository that is nothing but the flag.
 * Everything else `-Xfatal-warnings` catches is caught the day somebody reads the warning; an
 * omitted case in a match over a closed set is caught by nobody, and `LogicError.decided` is the
 * site that rests on it. So the probe is the shape of that site rather than any warning that
 * happens to be convenient: a closed set of three and a match over two of them.
 *
 * Measured against Scala 3.3.5 on 2026-09-18, both halves in one run of `tools/sbt fatalWarnings`:
 * the control reports `[E029] Pattern Match Exhaustivity Warning ... It would fail on pattern case:
 * Far` and compiles, and the probe reports the same diagnostic as `[E029] Pattern Match
 * Exhaustivity Error`, `one error found`, and compiles nothing.
 */
enum Shade:
  case Near, Middle, Far

/** The match that omits `Far`. See [[Shade]] for what this file is and why it may not compile. */
object NonExhaustiveMatch:

  /** Total on two of the three cases, which is the diagnostic this file exists to provoke. */
  def distance(shade: Shade): Int = shade match
    case Shade.Near   => 0
    case Shade.Middle => 1
