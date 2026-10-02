package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.FVar
import garden.xeno.symbolum.theories.{Chain, Library, Signature}

/**
 * Look for a lemma from a command line, by name or by shape, without writing Scala.
 *
 * The other half of what [[Ask]] does for a claim. `Library` has answered both of these questions
 * since it was written, and `docs/lemmas.md` lists every name, but reaching either from outside
 * meant a file in `scratch/`, a classpath and a compilation. The card that asks for this puts it
 * plainly: to use a lemma you had to know its `String` key in a `Map`, and there was no `exact?`,
 * no Loogle, and for a while not even a listing.
 *
 * {{{
 *   sbt "tactics/runMain garden.xeno.symbolum.tactics.Find SUM"
 *   sbt "tactics/runMain garden.xeno.symbolum.tactics.Find x:real + y:real = y + x"
 *   sbt "tactics/runMain garden.xeno.symbolum.tactics.Find Sum"
 * }}}
 *
 * == Both questions are answered, and never guessed between ==
 *
 * HOL Light's `search` takes name fragments and conclusion patterns in one list, and the two are
 * different questions: somebody who half remembers a name asks the first, somebody who knows the
 * shape and not the name asks the second. A single argument cannot be read as one or the other
 * without a rule, and every rule available here is wrong somewhere: `x` is a plausible name
 * fragment and a readable term, `SUM_ZERO` is a name and not a term, and a caller should not have
 * to know which branch it took.
 *
 * So it takes neither branch. The query is put to all three questions and each answer is reported
 * under its own heading, including the heading that is empty. Where the text does not read as a
 * proposition, or reads as one that asks nothing, the shape section says which rather than
 * disappearing, and [[byShape]] carries the measurement that made the second case worth a branch.
 *
 * == The three questions ==
 *
 *   - **by name**, `Library.whose`, a case-insensitive substring, because a caller half remembering
 *     a name does not remember its case;
 *   - **by shape**, `Library.matching`, first-order matching under the pattern's own free
 *     variables, so `x:real + y:real = y + x` finds commutativity and `0 + 1 = 1 + 0` finds nothing;
 *   - **about a constant**, `Library.about`, which is the question a reader actually asks first and
 *     is neither of the other two: what do I have about `Sum`.
 *
 * The matching is first order, so a lemma quantifying over a predicate is not found by shape. That
 * is `Matching.matchTerm`'s limit and it is recorded here rather than worked around.
 *
 * A shape **at a type** does not find a lemma stated over a type variable, for the same reason and
 * in the same direction: the query is the pattern, and matching solves the pattern's type variables
 * rather than the library's. `FST (PAIR x:num y:num) = x` finds nothing and
 * `FST (PAIR x:'a y:'b) = x` finds `FST_PAIR`. Asking `Ask` the first of those does prove it, which
 * is not a contradiction: `Prove` asks the library whether a lemma instantiates TO the goal, which
 * is the match the other way round.
 *
 * The argument is **not quoted**, for the reason [[Ask]] gives about `sbt` handing the arguments
 * over already split, and it is joined back the same way.
 */
object Find {

  /** How a caller runs this. The query is unquoted; see the note above about why. */
  val Command: String = "sbt \"tactics/runMain garden.xeno.symbolum.tactics.Find <name or shape>\""

  /** Everything the standard chain assembles, which is the widest library there is to search. */
  private lazy val chain: Chain = Chain.standard

  private lazy val held: Library = Library.of(chain)

  /** The page for one query against the standard chain, which is what a command line wants. */
  def of(query: String): String = of(chain.widest, held, query)

  /**
   * The page for one query against a library of one's own.
   *
   * The signature and the library are taken rather than read off a chain this object holds,
   * because a caller that has built its own is asking about **that** one: a session extends the
   * theory as it runs, and a search that quietly answered out of `Chain.standard` would report
   * about a different development than the one the reader is working in. That is the failure this
   * repository refuses everywhere else, an answer to a question nobody asked printed where the
   * answer belongs, and until 2026-09-13 this object could only give it.
   *
   * The two are separate arguments rather than one `Chain` because what is used is exactly a
   * signature to read and print with and a library to search, and `Session` has both without
   * having a chain of its own.
   */
  def of(signature: Signature, held: Library, query: String): String =
    Vector(
      section(signature, s"by name, containing ${quoted(query)}", held.whose(query)),
      section(signature, s"about the constant ${quoted(query)}", held.about(query)),
      byShape(signature, held, query)
    ).mkString("\n\n")

  /**
   * The shape answer, or the reason there is none.
   *
   * Two ways there is none, and they are different things a reader needs told apart. The text may
   * not read as a proposition at all, and then the parser's own sentence is what to show. Or it may
   * read as **a bare variable**, and that is the case this section exists for.
   *
   * A proposition has to be boolean, so a lone identifier like `SUM_TELESCOPES` reads perfectly
   * well as a boolean variable, and a pattern that is a variable matches everything: asked that
   * way, the first version of this file answered `SUM_TELESCOPES` with 126 lemmas, which is the
   * whole library. Nothing was wrong with the matching. What was wrong is that an answer meaning
   * "every lemma there is" was printed in the place where an answer to a question belongs, and a
   * reader who did not look closely would have read it as a result.
   *
   * So a bare variable is refused by name here rather than answered, which is the rule the tactics
   * follow about a question a procedure cannot settle.
   */
  private def byShape(signature: Signature, held: Library, query: String): String =
    signature.proposition(query) match {
      case Left(refusal) =>
        s"by shape: not a proposition of this theory, so nothing was asked\n  ${refusal.render(signature.show)}"

      case Right(_: FVar) =>
        "by shape: that reads as a bare variable, which matches every lemma there is, " +
          s"so nothing was asked\n  ${Annotated}"

      case Right(pattern) =>
        section(signature, s"by shape, matching ${signature.show(pattern)}", held.matching(pattern))
    }

  private def quoted(text: String): String = s"`$text`"

  /**
   * One answer, with its entries, or the sentence that says it is empty.
   *
   * An empty heading is printed rather than dropped, because a reader who asked three questions and
   * is shown two answers cannot tell which of the three was empty and which was never asked.
   */
  private def section(signature: Signature, heading: String, found: Vector[Library.Entry]): String =
    if (found.isEmpty) s"$heading: nothing"
    else
      (s"$heading: ${found.size}" +: found.sortBy(entry => (entry.name, entry.development)).map {
        entry =>
          s"  ${entry.development}.${entry.name}  ${signature.show(entry.theorem.conclusion)}"
      }).mkString("\n")

  /** The shape a pattern has to have to be read, which is the one thing a caller gets wrong. */
  val Annotated: String =
    "a bare variable carries no type and this reader refuses to guess one, so a shape is written " +
      "with its first occurrence annotated: x:real + y:real = y + x"

  def main(arguments: Array[String]): Unit = {
    val query = arguments.mkString(" ").trim

    if (query.isEmpty) println(s"nothing to look for. Usage:\n  $Command\n  $Annotated")
    else println(of(query))
  }
}
