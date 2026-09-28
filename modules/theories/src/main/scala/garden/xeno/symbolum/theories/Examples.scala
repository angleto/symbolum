package garden.xeno.symbolum.theories

/**
 * The command that writes the theorem pages in `docs/examples.md`.
 *
 * `Essay` has produced a page for a theorem since it was written and **no document consumed one**,
 * which made the thing it adds up to easy to describe and impossible to show. This is the first
 * consumer: a chosen set of results, each printed as its own page, with the statement rendered from
 * the term, what it rests on resolved by comparing sequents, and the cost computed by walking the
 * derivation. Nothing on a page is a copy of anything, so nothing on a page can go stale.
 *
 * == Why the list is written by hand and the pages are not ==
 *
 * [[Chosen]] is a curated list and has to be: `docs/lemmas.md` already prints every entry the
 * library holds, and a document with a page for each would be that listing many times over. What
 * belongs here is the handful somebody would show a reader who asked what the system can do, which
 * is a judgement and is therefore written down where it can be argued with rather than derived from
 * a rule nobody agreed.
 *
 * A name that is not in the library is **refused by name** rather than skipped. A showcase that
 * quietly dropped an entry would go on looking complete while shrinking, which is the failure mode
 * of every hand-maintained list of examples.
 *
 * == What a reader must not take from this document ==
 *
 * That the list is the best of what is here, that the areas covered are the areas a reader cares
 * about, or that a theorem missing from it is missing from the system. The document's own prose
 * says what is not here and why, and that part is written by hand because it is an argument rather
 * than a rendering.
 */
object Examples {

  /** Where the pages go, relative to the repository root. */
  val Document: String = "docs/examples.md"

  /** The command that runs this, written here so that the marker and the message cannot drift. */
  val Command: String = "sbt \"theories/runMain garden.xeno.symbolum.theories.Examples\""

  /** The one generated region of the document. */
  val Section: Generated = Generated("examples", Document, Command)

  /**
   * The results the document shows, grouped by what a reader would call them.
   *
   * Each group's heading is prose and each entry is a name the library holds. The order inside a
   * group is the order a reader should meet them in, which is not alphabetical and is not the order
   * they were proved.
   */
  val Chosen: Vector[(String, Vector[String])] = Vector(
    "Number theory" -> Vector(
      "NUM_PRIME_UNBOUNDED",
      "NUM_SQUARE_NOT_DOUBLE",
      "NUM_PRIME_TWO",
      "NUM_PRIME_FACTOR",
      "NUM_BEZOUT",
      "NUM_EUCLID",
      "NUM_PRIME_DIVISOR",
      "NUM_FACTORISATION",
      "NUM_FACTORISATION_UNIQUE",
      "NUM_CRT",
      "NUM_FACT_DIVIDES",
      "NUM_WILSON"
    ),
    "The naturals, and what separates the reals from an ordered field" -> Vector(
      "NUM_STRONG_INDUCTION",
      "NUM_ARCHIMEDES",
      "ABS_TRIANGLE"
    ),
    "Analysis" -> Vector(
      "SQRT_TWO_IRRATIONAL",
      "EXP_ONE_IRRATIONAL",
      "EXP_ADD",
      "SIN_COS_SQUARED",
      "INTERMEDIATE_VALUE_WITHIN",
      "CONTINUOUS_ATTAINS_MAX_WITHIN",
      "ROLLE_WITHIN",
      "MEAN_VALUE_WITHIN",
      "INTEGRAL_DERIVATIVE_WITHIN",
      "DERIVATIVE_INTEGRAL_WITHIN"
    ),
    "Towards the incompleteness theorems" -> Vector(
      "NUM_BETA_SEQUENCE",
      "NUM_PA_FORM",
      "NUM_PROV_MP",
      "NUM_PROV_SELF"
    )
  )

  /** Every page, in the order [[Chosen]] gives, or the first name the library does not hold. */
  def pages(): Either[String, String] = {
    val chain = Chain.standard

    Chosen.foldLeft(Right(Vector.empty): Either[String, Vector[String]]) {
      case (carried, (heading, names)) =>
        for {
          collected <- carried
          rendered <- names.foldLeft(Right(Vector.empty): Either[String, Vector[String]]) {
            (inner, name) =>
              for {
                held <- inner
                page <- Essay.of(chain, name)
              } yield held :+ page
          }
        } yield collected :+ s"## $heading\n\n${rendered.mkString("\n\n---\n\n")}"
    }.map(_.mkString("\n\n---\n\n"))
  }

  /** The document with its generated part replaced, or why it could not be. */
  def spliced(document: String, generated: String): Either[String, String] =
    Section.spliced(document, generated)

  /** What the generated part of a document currently holds, for a caller comparing the two. */
  def generatedPartOf(document: String): Either[String, String] = Section.partOf(document)

  def main(arguments: Array[String]): Unit =
    pages() match {
      case Left(reason) =>
        System.err.println(s"$Document was not written: $reason")
        sys.exit(1)
      case Right(body) =>
        Generated.run(arguments, Document, Vector(Section -> body))
    }
}
