package garden.xeno.symbolum.theories

/**
 * The showcase: the results worth reading, each as the page `Essay` renders for it.
 *
 * `docs/lemmas.md` is the **listing** and holds every one of them, which is what you search. This
 * is the **showcase**, and the difference is the question each answers: the listing answers "is
 * there already a lemma about this", and a showcase answers "what can this system actually do". A
 * reader who has never opened this repository gets the second question answered here and would
 * drown in the first.
 *
 * == What decides whether a theorem belongs here ==
 *
 * A criterion rather than a list, because a list is what goes stale: **a theorem is here if a
 * reader who does not know this repository can tell from its statement why it is worth having**.
 * Everything else stays in the listing. That rules out the infrastructure a development needs to
 * reach its results, which is most of the library and is not a lesser kind of lemma.
 *
 * Each entry carries one sentence saying what that reason is, because "notable" is not visible in
 * a name: `NUM_SQUARE_NOT_DOUBLE` is the arithmetic content of the irrationality of the square root
 * of two, and nothing about the name says so.
 *
 * == Why this file does not render anything ==
 *
 * `Essay` already does, and it was already complete: statement, what it rests on, the derivation,
 * the proof the kernel holds, how to get it back, and what on the page is checked. What was missing
 * was a document that calls it -- the renderer had two consumers, `Session` and `Notebook`, and
 * neither leaves anything behind that a reader arrives at. So this is a selection and a splice, and
 * a page grows on its own the day the development behind it records its derivation.
 *
 * == The one transformation, and the hazard in it ==
 *
 * `Essay` renders a page whose own title is a level-one heading, which is right for a page and
 * wrong for twelve of them inside one document. So every heading is pushed down one level, and the
 * shift is **fence-aware**: a line inside a fenced block is left alone whatever it starts with. The
 * pages carry fenced blocks holding statements and shell commands, and a shifter that did not
 * count fences would rewrite a line of somebody's command on the day one begins with a comment.
 */
object Theorems {

  /** Where the showcase goes, relative to the repository root. */
  val Document: String = "docs/theorems.md"

  /** The command that writes it, held here so that the marker and the message cannot drift. */
  val Command: String = "sbt \"theories/runMain garden.xeno.symbolum.theories.Theorems\""

  /** The one generated region of the document, and the markers that delimit it. */
  val Section: Generated = Generated("theorems", Document, Command)

  /** The line above the generated pages, in the document. */
  val Start: String = Section.start

  /** The line below them. */
  val End: String = Section.end

  /**
   * The showcase, in reading order rather than alphabetical, with why each one is here.
   *
   * The order is a reading: what the logic costs, then what the naturals are, then arithmetic that
   * a reader recognises from school, then the two that are about this system rather than about
   * mathematics. A reader going top to bottom meets the foundations before the results that rest
   * on them.
   *
   * `TheoremsSpec` asserts that every name here is one the library holds, so an entry that survives
   * a rename fails the build rather than producing a document with a hole in it.
   */
  val Showcase: Vector[(String, String)] = Vector(
    // The step count is deliberately not in this sentence, and the reason is measured rather than
    // stylistic. The page this generates prints it from `Derivation.size`, under "The proof the
    // kernel holds"; until 2026-09-22 this literal repeated that count in words, so one
    // generated page carried the measurement and a hand copy of it twenty-eight lines apart with
    // nothing comparing them. `TheoremsSpec`'s comparison cannot: it compares the document with
    // this generator, and the generator embeds this literal, so both sides move together and a
    // derivation that got cheaper would have left the page disagreeing with itself.
    "EXCLUDED_MIDDLE" ->
      ("Every proposition is true or false. It is an **axiom** in most systems and a **theorem** " +
        "here, derived from the choice operator alone, which is Diaconescu's argument; what it " +
        "cost the kernel is counted further down this page. Three places in this repository said " +
        "the opposite until `docs/adr/0009` measured it."),
    "NUM_INDUCTION" ->
      ("Proof by induction over the naturals. Peano assumed it; here the type `num` is **carved " +
        "out** of an infinite one as the smallest inductive subset, and induction is what falls out " +
        "of that definition rather than something asked for. So are the other Peano axioms and the " +
        "recursion theorem."),
    "NUM_ARCHIMEDES" ->
      ("No real number is above every natural. It is the only thing in this repository that spends " +
        "the sixteenth axiom of the reals, completeness: fifteen of the sixteen were worked and the " +
        "one that separates an ordered field from the reals was not, until this."),
    "ABS_TRIANGLE" ->
      ("The triangle inequality. It is here for the page rather than for the result: it is the one " +
        "theorem whose derivation is **recorded step by step**, seventy of them, each naming the " +
        "operation and the fact it used, so it is where to look to see what a proof in this system " +
        "is made of."),
    "SUM_TELESCOPES" ->
      ("A sum of differences collapses to its ends. The first result about finite sums, built on " +
        "the recursion theorem rather than on a primitive."),
    "SUM_BY_PARTS" ->
      ("Summation by parts, which is the discrete integration by parts and is what makes a sum of " +
        "a product tractable."),
    "NUM_BEZOUT" ->
      ("Two numbers' greatest common divisor is a combination of them. The fact every argument " +
        "about divisibility eventually reaches."),
    "NUM_EUCLID" ->
      ("A prime dividing a product divides one of the factors. The step that makes factorisation " +
        "unique, and the reason `NUM_GCD` had to exist before the primes could."),
    "NUM_FACTORISATION" ->
      ("Every number above one is a product of primes, and the family can be taken " +
        "**non-decreasing**. The sorting is what makes the uniqueness below an equation between " +
        "two families rather than a statement about rearranging one, which this system could not " +
        "make: it has no permutations, no finite sets and no multisets."),
    "NUM_FACTORISATION_UNIQUE" ->
      ("And there is only one such product. Two non-decreasing families of primes with the same " +
        "product have the same length and the same entries, index for index, which is the " +
        "fundamental theorem of arithmetic said in a language with no multiset in it."),
    "NUM_CRT" ->
      ("The Chinese remainder theorem, over **n** moduli and not only two. It exists because the " +
        "beta function needs it: coding a sequence of any length as two numbers is what lets a " +
        "theory that cannot say `sequence` talk about sequences."),
    "NUM_PRIME_UNBOUNDED" ->
      ("There is a prime above every number. That is what \"there are infinitely many primes\" says " +
        "in a logic with no notion of an infinite set, and the route runs through `n! + 1` exactly " +
        "as Euclid's does."),
    "NUM_SQUARE_NOT_DOUBLE" ->
      ("No square is twice a square at a positive denominator. It is the arithmetic content of the " +
        "irrationality of the square root of two and is deliberately **not** that sentence: there " +
        "is no square root on the reals here, so the classical statement cannot be written and the " +
        "name does not pretend otherwise."),
    "NUM_PROV_DEDUCTION" ->
      ("The deduction theorem, for **Peano arithmetic as this system encodes it inside itself**. " +
        "Not a fact about the logic these pages are written in: a fact about an arithmetic whose " +
        "formulas are numbers, which is the machinery Goedel's theorems are built on and the " +
        "direction `docs/adr/0013` sets.")
  )

  /**
   * The pages as the document carries them, or the names that are not in the library.
   *
   * An `Either` rather than a page saying "no lemma named X", because a showcase with a hole in it
   * is a document somebody publishes without reading, and the failure a reader of it meets is at
   * the wrong end. The caller prints the names and stops.
   */
  def listing(): Either[String, String] = {
    val chain = Chain.standard

    val pages = Showcase.map { case (name, why) =>
      Essay.of(chain, name).map(page => withLead(demoted(page), why))
    }

    val missing = pages.collect { case Left(why) => why }
    if (missing.nonEmpty) Left(missing.mkString("\n"))
    else Right(pages.collect { case Right(page) => page }.mkString("\n\n---\n\n"))
  }

  /**
   * Every heading pushed down one level, leaving fenced blocks alone.
   *
   * `Essay` writes a page, so its title is `#`; a document holding twelve of them wants them at
   * `##`. The fence counting is not caution for its own sake: the pages carry fenced blocks with
   * shell commands in them, and a line inside one that began with `#` would be rewritten into
   * something that is not the command any more.
   */
  def demoted(page: String): String =
    page.linesIterator
      .foldLeft((Vector.empty[String], false)) { case ((kept, inFence), line) =>
        if (line.trim.startsWith("```")) (kept :+ line, !inFence)
        else if (!inFence && line.startsWith("#")) (kept :+ s"#$line", inFence)
        else (kept :+ line, inFence)
      }
      ._1
      .mkString("\n")

  /** The reason a theorem is in the showcase, under its heading and above its statement. */
  private def withLead(page: String, why: String): String =
    page.split("\n", 2) match {
      case Array(heading, rest) => s"$heading\n\n$why\n$rest"
      case _ => page
    }

  /** The document with its generated part replaced, or why it could not be. */
  def spliced(document: String, generated: String): Either[String, String] =
    Section.spliced(document, generated)

  /** What the generated part of a document currently holds, for a caller comparing the two. */
  def generatedPartOf(document: String): Either[String, String] = Section.partOf(document)

  def main(arguments: Array[String]): Unit =
    listing() match {
      case Left(why) =>
        System.err.println(s"$why\nThe showcase names a lemma the library does not hold.")
        sys.exit(1)
      case Right(pages) => Generated.run(arguments, Document, Vector(Section -> pages))
    }
}
