package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * One theorem as a page: what it says, what it rests on, how it was derived, and what it cost.
 *
 * The three pieces this assembles existed separately and nobody had put them together, which is why
 * the thing they add up to was easy to describe and impossible to show. `Signature.readable` sets a
 * statement in print beside the text that reads back; `Script` holds the derivation at the size it
 * was written in rather than at the kernel's; `Derivation` answers what a proof is believed on and
 * what it cost. A page is those three and no fourth thing, and in particular **nothing here decides
 * anything**: every line is a rendering of something the code already held.
 *
 * == Why it is here and not in `modules/tactics` ==
 *
 * The plan this comes from said `tactics`, because `Cost` and `Provenance` live there and a page
 * about a **claim a session asked** wants both: what the claim charges, where it fails, what would
 * have to be assumed. A page about a **theorem the library holds** wants neither, and everything it
 * does want is in `theories`. Putting it here is what lets a generated document use it, which is
 * the first consumer there will be; a session's page is this page with `Cost`'s fields added, and
 * that belongs where `Cost` is.
 *
 * == What is checked on the page, and what a reader must not assume ==
 *
 * Every formula is rendered from the term, every citation is resolved by comparing sequents, the
 * axioms come from walking the derivation and the counts are computed. So a reader may take all of
 * those as facts about the object, in the strong sense: they cannot be stale, because there is no
 * copy of them.
 *
 * What a reader must not take from the page is that the theorem is **worth** anything, that the
 * spelling of a constant is the right one, or that the informal claim in somebody's head is what
 * the statement says. The first is mathematics, the second is a reading recorded in
 * `docs/reading-register.md`, and the third is what the legible form under the statement is printed
 * for. The page says so of itself, in a section that is part of the output rather than of this
 * comment, because a reader of the page does not read this file.
 *
 * **There is no authored prose in what this produces.** That is a property worth keeping: a page
 * that mixes generated lines with sentences somebody wrote has to mark which is which, and the
 * cheapest way to be sure is to have none of the second. A document that wants prose puts this page
 * inside it, under a heading of its own.
 */
object Essay {

  /** How a page refers to the rendering that is set for reading rather than for checking. */
  val PrintedNotice: String =
    "The formula above is set for reading and **does not read back**. The line under it is the " +
      "text the page was generated from: that is the one to compare against a source, or to paste " +
      "into `Ask`."

  /** What a statement no form of which reads back is marked with, as in the lemma listing. */
  val NotReadable: String = Library.NotReadable

  /**
   * The page for one named theorem.
   *
   * `script` is optional and its absence is reported rather than hidden: a theorem nobody has
   * recorded the derivation of still has a statement, a foundation and a cost, and a page that
   * quietly omitted the derivation would read as a proof with nothing in it.
   */
  def of(
    signature: Signature,
    library: Library,
    name: String,
    theorem: Kernel.Thm,
    script: Option[Script]
  ): String = {
    val sections = Vector(
      statement(signature, name, theorem),
      restsOn(signature, library, theorem),
      derivation(signature, library, script),
      cost(theorem),
      reproduce(signature, library, name, theorem),
      checked(script)
    )

    sections.mkString("\n\n")
  }

  /** The page for a lemma the library holds, with its account if the development recorded one. */
  def of(chain: Chain, name: String): Either[String, String] = {
    val library = Library.of(chain)

    library.named(name).headOption match {
      case None => Left(s"no lemma named $name")
      case Some(entry) =>
        Right(of(chain.widest, library, name, entry.theorem, chain.magnitude.scripts.get(name)))
    }
  }

  /* ------------------------------------------------------------------ the sections */

  private def statement(signature: Signature, name: String, theorem: Kernel.Thm): String = {
    val heading = s"# $name"

    signature.readable(theorem.conclusion) match {
      case Some(pair) =>
        s"""$heading
           |
           |$$$$${pair.printed}$$$$
           |
           |```
           |${pair.legible}
           |```
           |
           |*$PrintedNotice*""".stripMargin

      case None =>
        // The one case where the page shows no formula set in print: a statement that does not read
        // back is not published in a form a reader cannot check against anything.
        s"""$heading
           |
           |```
           |$NotReadable ${signature.show(theorem.conclusion)}
           |```""".stripMargin
    }
  }

  /**
   * How to get this theorem back, which is the section a reader asks for first.
   *
   * Three routes and they answer different questions: put the claim to the whole tactic surface and
   * watch it be settled, look the lemma up by name, or reach it from Scala. The first is the one
   * that matters, because it is the only one where the reader's own machine does the work rather
   * than being told what somebody else's did.
   *
   * **The claim printed here is the legible form and not the set one**, and that is the whole
   * reason this section costs nothing: every statement in the library is printed and read back
   * through the same signature, and `NotationRoundTripSpec` asserts it of all of them. So the line
   * below is generated rather than transcribed, and a reader who pastes it gets the same term.
   * A statement that does **not** read back is the one case where the route is withheld instead of
   * printed wrong.
   *
   * **The two commands are string literals here and cannot be anything else**, because `Ask` and
   * `Find` live in `modules/tactics` and this file is in `modules/theories`, which is below it.
   * A literal naming another module's entry point is exactly the kind of copy that goes stale, so
   * `EssayCommandSpec` in `tactics` asserts these two against `Ask.Command` and `Find.Command`:
   * the agreement is checked from the one module that can see both.
   */
  private def reproduce(
    signature: Signature,
    library: Library,
    name: String,
    theorem: Kernel.Thm
  ): String = {
    val heading = "## How to get it"

    val held = library.named(name).headOption.map(_.development)
    val fromScala = held match {
      case Some(development) =>
        s"From Scala it is `$development`'s, under the name `$name`. Specialise it with " +
          "`Rules.specTo`, which takes the instance wanted and finds the instantiation by " +
          "matching: the order the binders were written in is not part of any contract here."
      case None =>
        "It is in no development this page can name, which is a defect in the page rather than " +
          "in the theorem."
    }

    signature.readable(theorem.conclusion) match {
      case Some(pair) =>
        s"""$heading
           |
           |Put the claim to the prover, which settles it from the whole tactic surface:
           |
           |```
           |$AskCommand ${pair.legible}"
           |```
           |
           |The claim is **not** quoted: `sbt` hands the arguments over already split, so the
           |shell's quotes are gone before the command sees them.
           |
           |Look it up instead, by name or by shape:
           |
           |```
           |$FindCommand $name"
           |```
           |
           |$fromScala""".stripMargin

      case None =>
        s"""$heading
           |
           |This statement does not read back through the signature it is printed in, so no line
           |that a reader could paste is published for it. `$FindCommand $name"` reaches it by name.
           |
           |$fromScala""".stripMargin
    }
  }

  /**
   * How `Ask` is invoked, as this page prints it.
   *
   * A copy of `Ask.Command` with the placeholder dropped, because `modules/theories` is below
   * `modules/tactics` and cannot read the real one. `EssayCommandSpec` asserts the agreement.
   */
  val AskCommand: String = "sbt \"tactics/runMain garden.xeno.symbolum.tactics.Ask"

  /** How `Find` is invoked, on the same terms and checked by the same spec. */
  val FindCommand: String = "sbt \"tactics/runMain garden.xeno.symbolum.tactics.Find"

  private def restsOn(signature: Signature, library: Library, theorem: Kernel.Thm): String = {
    val axioms = Derivation.axiomsOf(theorem)

    // The theorem itself is in its own walk, so it comes back as something it rests on, which is
    // true and useless and reads as circular. Dropped by the sequent, which is how the library
    // compares anything: a lemma re-derived on the way is the same fact and is still not a premise
    // of itself. The instance measurement of this morning made the same mistake, which is why the
    // line is here rather than being noticed a third time.
    val named = library.restingOn(theorem).filterNot(_.theorem.conclusion == theorem.conclusion)
    val namedAxioms = named.filter(entry => axioms.contains(entry.theorem.conclusion))
    val unnamed = axioms.size - namedAxioms.map(_.theorem.conclusion).distinct.size

    val rows = named
      .sortBy(entry => (entry.development, entry.name))
      .map(entry => s"| `${entry.name}` | ${entry.development} |")

    val table =
      if (rows.isEmpty) Vector("It rests on no named fact, which means the inference rules alone.")
      else Vector("| what | where |", "|---|---|") ++ rows

    val unnamed_ =
      if (unnamed == 0) Vector.empty
      else
        Vector(
          "",
          s"${count(unnamed, "axiom")} it reaches ${if (unnamed == 1) "is" else "are"} not named " +
            "above: `Library.of` holds no classical axiom, and says in its own comment why."
        )

    (Vector(
      "## What it rests on",
      "",
      s"${count(axioms.size, "axiom")} reached, ${namedAxioms.size} of them named below, and " +
        s"${named.size} named facts in all.",
      ""
    ) ++ table ++ unnamed_).mkString("\n")
  }

  /** A number and its noun, with the plural where the number needs one. */
  private def count(howMany: Int, noun: String): String =
    if (howMany == 1) s"1 $noun" else s"$howMany ${noun}s"

  private def derivation(
    signature: Signature,
    library: Library,
    script: Option[Script]
  ): String = script match {
    case None =>
      """## The derivation
        |
        |Not recorded. The development that proved this has not been converted to record its steps,
        |so the page can say what the theorem rests on and what it cost and cannot say how it was
        |obtained.""".stripMargin

    case Some(account) =>
      val names = Script.names(
        Vector(library.entries.map(entry => (entry.name, entry.theorem)).toMap)
      )

      val lines = account
        .lines(names, sequent(signature, _))
        .map(line => s"${line.number}. ${line.head}\n   $$${line.sequent}$$")

      s"""## The derivation
         |
         |${account.size} steps, recorded as the derivation was written.
         |
         |${lines.mkString("\n")}""".stripMargin
  }

  private def cost(theorem: Kernel.Thm): String = {
    val size = Derivation.size(theorem)
    val census = Derivation.census(theorem).toVector.sortBy(-_._2)
    val rows = census.map { case (rule, howMany) =>
      f"| $rule | $howMany | ${100.0 * howMany / size}%.1f%% |"
    }

    // Built as lines rather than with `stripMargin`, because a markdown table's rows begin with the
    // character `stripMargin` strips: the first page this produced had every row of both tables
    // missing its first `|`, and rendered as text.
    (Vector(
      "## The proof the kernel holds",
      "",
      s"$size inferences. The account above describes them and is not a second proof: what the " +
        "kernel checked is this, and its shape is",
      "",
      "| rule | inferences | share |",
      "|---|---|---|"
    ) ++ rows).mkString("\n")
  }

  private def checked(script: Option[Script]): String =
    s"""## What on this page is checked
       |
       |- The statement, in both forms, is rendered from the theorem. The second form was read back
       |  and gave the same term, which is what `Signature.readable` returns a pair for.
       |- What it rests on is a walk over the derivation, and a name appears against a fact only
       |  where the sequents agree.
       |- The inferences and their shape are counted from the same walk.
       |${if (script.isEmpty) "" else "- Each step is one operation as it was recorded, and a step citing a name cites a fact whose\n  statement is that name's.\n"}
       |Not checked, and not claimed: that the statement says what somebody meant, which is what the
       |readable form is printed for; that a constant is spelled the way the literature spells it,
       |which is a reading and is recorded in `docs/reading-register.md`; and that the theorem is
       |worth proving.""".stripMargin

  private def sequent(signature: Signature, theorem: Kernel.Thm): String = {
    val printed = Spellings.standard.show(signature.notation, theorem.conclusion)
    val hypotheses = theorem.hypotheses.map(Spellings.standard.show(signature.notation, _))

    if (hypotheses.isEmpty) s"\\vdash $printed"
    else s"${hypotheses.mkString(", ")} \\vdash $printed"
  }

  /** The command that prints one page, written here so the message and the command cannot drift. */
  val Command: String = "sbt \"theories/runMain garden.xeno.symbolum.theories.Essay <LEMMA>\""

  def main(arguments: Array[String]): Unit =
    arguments.toList match {
      case name :: Nil =>
        of(Chain.standard, name) match {
          case Right(page) => println(page)
          case Left(reason) => println(s"$reason. The command is $Command")
        }

      case _ => println(s"one lemma at a time: $Command")
    }
}
