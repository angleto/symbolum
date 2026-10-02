package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.Term
import garden.xeno.symbolum.theories.{Chain, Signature}

/**
 * Put a claim to the whole tactic surface from a command line, and read what it cost.
 *
 * The smallest useful version of a request surface, and deliberately the smallest. Until this
 * existed the only way to ask this system anything was to write Scala and run `sbt`, so the price
 * of one question was a compilation: every measurement in this session began by writing a file into
 * `scratch/`, compiling it against the build's classpath and running it, to ask something `Cost`
 * answers in one call.
 *
 * {{{
 *   sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:real. x + 0 = x"
 *   sbt "tactics/runMain garden.xeno.symbolum.tactics.Ask !x:real. x + 0 = x | !n:num. 0 <= real_of_num n"
 * }}}
 *
 * **The claim is not quoted and the arguments are joined**, which is a fact about `sbt` rather than
 * a choice. Everything after the class name reaches `main` split on whitespace, and the quotes a
 * shell would have honoured are gone by then: quoting the claim produces a first argument of
 * `'!x:real.` and a parse error about a type variable. So the arguments are put back together and
 * `|` separates one claim from the next, `;` being unavailable because `sbt` reads it as the end of
 * a command.
 *
 * == What it is not, and the card that asked for it says why ==
 *
 * Not a server, not a protocol and not a session. The adversarial review advised against chasing
 * LeanDojo or Pantograph, which exist for a library this repository does not have, and what it
 * asked for instead was exactly this: take a statement and give back the report as data, without
 * the caller compiling. A protocol becomes worth building when something outside drives the
 * generator, and nothing does yet.
 *
 * == Why every claim is answered rather than the first failure stopping it ==
 *
 * A caller asking three things wants the two that read. A claim the theory cannot state comes back
 * as a line saying so, in its place in the list, and the others are answered around it. That is the
 * same choice `Argument` makes for a conclusion with no certificate, and for the same reason: the
 * half that can be answered is worth more than the consistency of refusing everything.
 */
object Ask {

  /** How a caller runs this. The claim is unquoted; see the note above about why. */
  val Command: String = "sbt \"tactics/runMain garden.xeno.symbolum.tactics.Ask <claim>\""

  /** What separates one claim from the next on a command line. */
  val Separator: String = "|"

  /** Everything the standard chain assembles, which is the widest thing there is to ask. */
  private lazy val chain: Chain = Chain.standard

  private lazy val cost: Cost =
    Cost
      .construct(chain)
      .fold(error => throw new IllegalStateException(s"the standard cost does not build: ${error.message}"),
        identity)

  /**
   * The page for one claim, or the reason it could not be put.
   *
   * A claim that does not read gets the reader's message and, where the text says something the
   * reader could not, what to write instead: `!n:num. n + 0 = n` is the first claim anybody makes
   * about the naturals, and "real and num cannot be the same type" names neither the owner of `+`
   * nor `NUM_ADD`. `Counterpart` is the table, and `Peano`'s **No notation** heading is the
   * decision it exists to pay for rather than to reopen.
   *
   * A claim that reads gets [[asAsked]] under the report wherever the report prints it differently.
   * That is what `docs/adr/0002` costs and the ADR now says so: a bound name is not part of a term,
   * so somebody who asks about `budget` is answered about `x`.
   */
  def of(claim: String): String = of(chain.widest, cost, claim)

  /**
   * The page for one claim against a signature and a cost report of one's own.
   *
   * Taken rather than read off the chain this object holds, for the reason [[Find.of]] gives about
   * the library: a caller working in a development it extended itself is asking about that one, and
   * answering out of `Chain.standard` would put an answer about a different theory where the answer
   * belongs. A `Session` holds both of these and no chain.
   */
  def of(signature: Signature, cost: Cost, claim: String): String =
    signature.proposition(claim) match {
      case Left(refusal) =>
        (Vector(s"unreadable: $claim", s"  ${refusal.render(signature.show)}") ++
          Remedy.spelling(signature, claim, refusal).map(remedy => s"  ${remedy.message}"))
          .mkString("\n")

      case Right(term) =>
        (Vector(page(cost, term)) ++ asAsked(signature, claim, term)).mkString("\n")
    }

  /**
   * The claim as the caller wrote it, where the report does not print it that way.
   *
   * Only where the two differ, and that is the line's whole content: a report already printing the
   * caller's own text gains nothing by printing it twice, and one that is not has made its own
   * answer un-checkable against the informal claim it translates, which is what a formal statement
   * is for. A reader who wrote `budget` and is answered about `x` has to reconstruct the
   * correspondence before the answer means anything, and nothing on the page says there is one.
   *
   * The comparison is against `Readback`'s text rather than against the head of the page, because
   * `Cost.page` builds that head out of exactly this. From a command line the caller's own string
   * has already been rejoined on single spaces by [[claimsIn]], so what survives the comparison is
   * a difference of names or of spelling and not one of whitespace.
   *
   * **This is the cheap half and the expensive one is not built.** A name hint carried beside the
   * term from the reader through `Cost` to the renderer would cover a claim whose text is gone by
   * the time a report is printed, and the count of consumers needing that was taken on 2026-09-12:
   * one, `Argument`, which holds the caller's text one method above its own renderer, so the same
   * cheap move covers it. Everything else that renders a report — `Propose`, `Sweep`, `Novelty` —
   * is handed claims a generator built out of theorems, where there is no author's name to lose.
   */
  private def asAsked(signature: Signature, text: String, claim: Term): Option[String] =
    if (Readback.of(signature, claim).toOption.contains(text)) None
    else
      Some(
        s"  as asked: $text (a bound name is not part of a term; the names above are the printer's)"
      )

  /** The same for a claim already read, which is what a caller holding a `Term` wants. */
  def page(claim: Term): String = page(cost, claim)

  /** The same against a cost report of one's own, which carries its own signature already. */
  def page(cost: Cost, claim: Term): String =
    (for {
      report <- cost.of(claim)
      rendered <- cost.render(report)
    } yield rendered).fold(refusal => s"refused: ${refusal.render(cost.reals.show)}", identity)

  /** The pages for a list of claims, one after another. */
  def report(claims: Vector[String]): String = claims.map(of).mkString("\n")

  /** The claims a command line carries, put back together and split where the caller meant. */
  def claimsIn(arguments: Vector[String]): Vector[String] =
    arguments
      .mkString(" ")
      .split(java.util.regex.Pattern.quote(Separator))
      .toVector
      .map(_.trim)
      .filter(_.nonEmpty)

  def main(arguments: Array[String]): Unit = {
    val claims = claimsIn(arguments.toVector)
    if (claims.isEmpty) println(s"nothing to ask. Usage:\n  $Command")
    else println(report(claims))
  }
}
