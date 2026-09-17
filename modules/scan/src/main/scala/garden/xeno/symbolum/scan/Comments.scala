package garden.xeno.symbolum.scan

/**
 * What in a source of this repository is a comment, decided in one place.
 *
 * Six gates decided it separately until 2026-09-16, in two shapes that did not agree, and each of
 * the six decides whether a check is green. Three cleaned the text with the same pair of
 * substitutions (`Sources.code` in `theories`, `RemedySpec` in `tactics`, `LauncherSpec` in
 * `dist`); three filtered whole lines with a block-state scanner (`StyleSpec`,
 * `SourceLanguageSpec`, `DocumentationSpec`, all in `tactics`). The three inputs that separate
 * them, and what each shape answered:
 *
 *   - `foo(); // note`: the first kept `foo();` and dropped the note; the second kept the **whole
 *     line**, because it does not *begin* with a slash, so the note was scanned as code.
 *   - a doc comment opened and closed on one line with code after it: the first kept the code;
 *     the second dropped the whole line, code included.
 *   - `"http://x"` inside a string literal: the first dropped from the slashes to the end of the
 *     line, **code included**; the second kept it.
 *
 * Two questions, not one implementation written twice: "the text with its comments off" and "which
 * lines are code and which are comment" are different functions and both are wanted. [[split]]
 * answers both by answering neither: it gives, per line, the part that is code and the part that is
 * comment, and everything else here is a projection of it.
 *
 * == Why this is a module of its own ==
 *
 * The three text-cleaning sites sit in three modules' test scopes, which do not see each other, and
 * sharing along the existing edges means `theories % "test->test"` on `tactics`: that puts 75 test
 * files and 21 097 lines into the compile graph of every `tactics/testOnly`, to remove two copies
 * of one function. Measured on 2026-09-16, and the inner loop is not the place to spend it.
 *
 * So this depends on nothing and is reached at `test->compile`, which costs each of the three the
 * compilation of this one file. It is the argument `mark` already carries one floor down: a check
 * over the repository's own text should not wait for the prover, because the days the prover is
 * broken are exactly the days the check is worth running.
 *
 * == The limits, which are the part worth reading ==
 *
 * This is a lexer for comments and **not** a Scala parser, and three things it does that the two
 * shapes above did not are the three that were wrong in this tree rather than in principle:
 *
 *   - **A string literal is code.** Three lines of `Notebook.scala` carry a double slash inside one,
 *     the address the server prints and the two the KaTeX tags load, and the substituting shape cut
 *     each of them there: the `println` lost the rest of itself. What reads that shape includes a
 *     census over the one operation that can make the trusted base grow, so its failure is a line
 *     declaring an axiom that the census does not see. The operation is not named here on purpose:
 *     a file that names it owes an entry in a hand-kept list in `theories`, and this module depends
 *     on nothing and should not be pointing upwards. The concrete version of this sentence is in
 *     `Sources.code`, which is the caller and may say it.
 *   - **A triple-quoted string is a string**, which quote parity is not enough to know. The one in
 *     `Mark.scala` that opens with an SVG tag has three quotes, a tag and an attribute in quotes of
 *     its own before its own double slash, so the number of quotes before those slashes is even and
 *     a parity rule reads the rest of that header as English prose. It was the one line in this tree
 *     where parity gave the wrong answer, and nothing named it.
 *
 * **Neither of those two names a line number, and that is the repair rather than a preference.** The
 * first said "line 77", which was true when it was written and stopped being true at `4b96fe1`, a
 * commit of somebody else's card that rewrote `Notebook.scala` and left the `println` at 107 with a
 * blank docstring line at 77. That is worse than naming a file that is gone: the reader arrives
 * somewhere that exists and says nothing. `Sources.code` carries the concrete version of the same
 * explanation, has never carried a number, and survived that commit for exactly that reason. The
 * same sentence also said `http://` of all three lines, where one is `http://` and two are the
 * `https://` of the CDN; what the lexer is about is the double slash, so that is what it now says.
 *   - **A block comment nests.** Scala nests them, this repository has been bitten twice by writing
 *     an opening marker inside a docstring, and the non-greedy substitution the three text-cleaning
 *     sites used closes at the first closing marker it meets rather than at the matching one.
 *
 * What it still does not know: an interpolation holding a comment, which is absent here and would
 * be read as string; and a `#` inside a nested quote in the shell family, where [[hashLines]]
 * counts both kinds of quote and says why below.
 */
object Comments {

  /**
   * One line, split into the part that is code and the part that is comment.
   *
   * Both parts, rather than the one a caller wants, because a caller wants different ones: the
   * style census reads the code and reports the **original** line to the person, and the language
   * census reads the comment. A projection that threw the other half away would put the choice back
   * in three places.
   *
   * `number` is 1-based, which is how a test names a line to a reader, and `text` is the line as it
   * was written. The line is carried rather than reassembled from the two parts because they do not
   * reassemble: `object Foo { /* a */ def bar` puts two pieces in `code` and one between them in
   * `comment`, so concatenating the halves gives a line nobody wrote. What survives instead is the
   * count, and [[CommentsSpec]] asserts it: every character of `text` goes to exactly one part.
   */
  final case class Line(number: Int, text: String, code: String, comment: String) {

    /** Whether anything but whitespace is left once the comments come off. */
    def isCode: Boolean = code.trim.nonEmpty

    /** Whether this line carries a comment, wholly or after code. */
    def isComment: Boolean = comment.trim.nonEmpty
  }

  /** What the scanner is in the middle of when a line ends. */
  private sealed trait Carried
  private case object Plain extends Carried
  private final case class Block(depth: Int) extends Carried
  private case object Triple extends Carried

  /**
   * Every line of `text`, each split into its code and its comment.
   *
   * The state carried across a line boundary is only these three, and that is a fact about the
   * language rather than a simplification: a line comment ends at the newline, and a single-quoted
   * string literal cannot hold one, so neither can be open when a line ends.
   */
  def split(text: String): Vector[Line] =
    text.linesIterator.toVector.zipWithIndex
      .foldLeft((Vector.empty[Line], Plain: Carried)) { case ((lines, carried), (line, index)) =>
        val (code, comment, next) = scan(line, carried)
        (lines :+ Line(index + 1, line, code, comment), next)
      }
      ._1

  /**
   * The text with its comments removed, line structure intact.
   *
   * The pair of substitutions this replaces put a single space where a block comment had been,
   * **including its newlines**, so a docstring of four lines merged the line above it with the line
   * below and every line number after it moved. Nothing read the numbers, so nothing failed; a
   * caller that folds over lines was reading a file whose shape depended on how its prose was
   * wrapped.
   */
  def withoutComments(text: String): String =
    split(text).map(_.code).mkString("\n")

  /** The lines that carry code, with the comment off each of them. */
  def codeLines(text: String): Vector[Line] = split(text).filter(_.isCode)

  /** The lines that carry a comment, with the code off each of them. */
  def commentLines(text: String): Vector[Line] = split(text).filter(_.isComment)

  /**
   * The lines that carry a comment, for a language whose comment opens with `#` and has no block
   * form: shell, YAML and `.properties` alike.
   *
   * A second reader and not a second census, for the reason `SourceLanguageSpec` gave when it held
   * this: comment syntax is shared and file extensions are not.
   *
   * **Both kinds of quote count here and only one counts in Scala**, and the asymmetry is
   * measured rather than tidy. `echo '### The libraries'` is in this tree, so ignoring the single
   * quote reads it as a comment; in Scala a `'` is a character literal and passes in and out of
   * prose as an apostrophe, so the same rule there would drop a real comment on
   * `val s = "don't" // note`. A dropped comment is never scanned and makes a census greener, which
   * is the failure these checks exist against; a kept literal can at worst be flagged.
   */
  def hashLines(text: String): Vector[Line] =
    text.linesIterator.toVector.zipWithIndex
      .map { case (line, index) =>
        val at = hashOutsideQuotes(line, 0, quote = None)
        val split = at.getOrElse(line.length)
        Line(index + 1, line, line.take(split), line.drop(split))
      }
      .filter(_.isComment)

  /** Where the comment of a `#` line begins, skipping the quotes of either kind. */
  private def hashOutsideQuotes(line: String, at: Int, quote: Option[Char]): Option[Int] =
    if (at >= line.length) None
    else
      (quote, line.charAt(at)) match {
        case (Some(open), character) if character == open => hashOutsideQuotes(line, at + 1, None)
        case (Some(_), _) => hashOutsideQuotes(line, at + 1, quote)
        case (None, '#') => Some(at)
        case (None, character) if character == '"' || character == '\'' =>
          hashOutsideQuotes(line, at + 1, Some(character))
        case _ => hashOutsideQuotes(line, at + 1, None)
      }

  /* -------------------------------------------------------------------- the Scala scanner */

  /**
   * One line, from the state the line before it left open.
   *
   * Segments rather than two strings being built up, because code and comment interleave on a line
   * that opens and closes a block in the middle of an expression, and because a builder is mutable
   * state that would owe `StyleSpec` an entry in its excused list for no gain: a line of this
   * repository is a few hundred characters and the segments per line are one or two.
   */
  private def scan(line: String, entry: Carried): (String, String, Carried) = {
    def walk(
        at: Int,
        from: Int,
        state: Carried,
        code: Vector[String],
        comment: Vector[String]
    ): (String, String, Carried) =
      if (at >= line.length)
        state match {
          case Plain => (code.mkString + line.substring(from), comment.mkString, Plain)
          case Triple => (code.mkString + line.substring(from), comment.mkString, Triple)
          case block: Block => (code.mkString, comment.mkString + line.substring(from), block)
        }
      else
        state match {
          case Block(depth) =>
            if (line.startsWith("/*", at)) walk(at + 2, from, Block(depth + 1), code, comment)
            else if (line.startsWith("*/", at) && depth > 1)
              walk(at + 2, from, Block(depth - 1), code, comment)
            else if (line.startsWith("*/", at))
              walk(at + 2, at + 2, Plain, code, comment :+ line.substring(from, at + 2))
            else walk(at + 1, from, state, code, comment)

          case Triple =>
            if (line.startsWith("\"\"\"", at)) walk(at + 3, from, Plain, code, comment)
            else walk(at + 1, from, state, code, comment)

          case Plain =>
            if (line.startsWith("//", at))
              (code.mkString + line.substring(from, at), comment.mkString + line.substring(at), Plain)
            else if (line.startsWith("/*", at))
              walk(at + 2, at, Block(1), code :+ line.substring(from, at), comment)
            else if (line.startsWith("\"\"\"", at)) walk(at + 3, from, Triple, code, comment)
            else if (line.charAt(at) == '"') walk(stringEnd(line, at + 1), from, Plain, code, comment)
            else if (line.charAt(at) == '\'')
              walk(characterEnd(line, at), from, Plain, code, comment)
            else walk(at + 1, from, state, code, comment)
        }

    walk(0, 0, entry, Vector.empty, Vector.empty)
  }

  /**
   * The index just past a single-quoted string literal that opened at `at - 1`.
   *
   * Interpolation is why this is not a search for the next quote, and `NotationBoundarySpec` found
   * that out the expensive way one module over: `s"... ${xs.mkString(", ")}"` holds a quote inside
   * the interpolation, and a scanner that ends the literal there leaves the rest of the expression
   * outside any string. Here that would put a `//` of a URL back in the open.
   *
   * An unterminated literal ends at the end of the line, which is not a Scala source and is the
   * only answer that keeps this total.
   */
  private def stringEnd(line: String, at: Int): Int =
    if (at >= line.length) line.length
    else if (line.charAt(at) == '\\') stringEnd(line, at + 2)
    else if (line.startsWith("${", at)) stringEnd(line, braceEnd(line, at + 1, 0))
    else if (line.charAt(at) == '"') at + 1
    else stringEnd(line, at + 1)

  /** The index just past the brace group opening at `at`, skipping the literals inside it. */
  private def braceEnd(line: String, at: Int, depth: Int): Int =
    if (at >= line.length) line.length
    else
      line.charAt(at) match {
        case '"' => braceEnd(line, stringEnd(line, at + 1), depth)
        case '{' => braceEnd(line, at + 1, depth + 1)
        case '}' if depth == 1 => at + 1
        case '}' => braceEnd(line, at + 1, depth - 1)
        case _ => braceEnd(line, at + 1, depth)
      }

  /**
   * The index just past a character literal opening at `at`, or `at + 1` where there is none.
   *
   * A quote is not always an opening: `'a` is how a type variable is written in the texts this
   * repository parses, and Scala 3 spells a quoted expression `'{`. So the shape is recognised
   * rather than assumed, and what makes recognising it necessary is `'"'`, which occurs in two
   * specs here: read as an ordinary character it opens a string literal that never closes, and
   * every comment after it on the line disappears.
   */
  private def characterEnd(line: String, at: Int): Int =
    if (line.startsWith("'\\", at) && at + 3 < line.length && line.charAt(at + 3) == '\'') at + 4
    else if (at + 2 < line.length && line.charAt(at + 2) == '\'') at + 3
    else at + 1
}
