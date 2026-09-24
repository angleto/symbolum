package garden.xeno.symbolum.scan

import org.scalatest.Inspectors
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The answers this repository's gates get when they ask what a comment is.
 *
 * Six sites asked it separately and two of them are pinned here by the three inputs that separated
 * them, because "they agree now" is a claim about six files and this is the one place where the
 * agreement is a property of one function instead.
 *
 * The three findings below the table are the ones the two old shapes got wrong on this tree rather
 * than in principle, and each is written as the line that produced it: a `println` of a URL, an SVG
 * header opened with three quotes, and a block comment inside a block comment. A test written from
 * the general rule instead of from the line would have passed on all three before the repair.
 */
class CommentsSpec extends AnyFlatSpec with Matchers with Inspectors {

  /* ------------------------------------------------------ the three inputs of the census */

  "A trailing comment" should "leave the code and go to the comment" in {
    val line = Comments.split("foo(); // note").head

    line.code shouldBe "foo(); "
    line.comment shouldBe "// note"
    line.isCode shouldBe true
    line.isComment shouldBe true
  }

  "A block comment closed on its own line" should "leave the code that follows it" in {
    val line = Comments.split("/** doc */ code").head

    line.code shouldBe " code"
    line.comment shouldBe "/** doc */"
  }

  "A line comment marker inside a string literal" should "not be a comment" in {
    val text = """println(s"open http://$Host:${server.getAddress.getPort}")"""
    val line = Comments.split(text).head

    line.code shouldBe text
    line.comment shouldBe ""
    line.isComment shouldBe false
  }

  /* ------------------------------------------------------ what the two old shapes got wrong */

  "A triple-quoted string" should "hold its quotes and its slashes" in {
    // The SVG header in `Mark.scala`, copied below rather than cited by line. Quote parity answers
    // "outside a string" here, because the three opening quotes and the attribute's pair are an
    // even number before the slashes, so the rule the language census used would have read the
    // rest of this header as English prose.
    val text = "    s\"\"\"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 1 1\">"
    val line = Comments.split(text).head

    line.comment shouldBe ""
    line.code shouldBe text
  }

  "A block comment" should "close at the marker that matches it and not at the first one" in {
    val lines = Comments.split("/* outer /* inner */ still comment */ code")

    lines.head.code shouldBe " code"
    lines.head.comment shouldBe "/* outer /* inner */ still comment */"
  }

  "A character literal holding a quote" should "not open a string" in {
    // `'"'` occurs in this tree, in the scanners themselves. Read as an ordinary character it opens
    // a literal that never closes, and every comment after it on the line disappears; this is a
    // line of one of the scanners this module replaced, kept as it was written.
    val lines = Comments.split("""trailing(line, "//", Set('"')) // the marker""")

    lines.head.comment shouldBe "// the marker"
    lines.head.code shouldBe """trailing(line, "//", Set('"')) """
  }

  /* ------------------------------------------------------ inside a literal, where it is easy to fall out */

  "An interpolation" should "keep the quotes inside it from ending the literal" in {
    // The case `NotationBoundarySpec` paid for one module over: a scanner that ends the literal at
    // the first quote inside `${...}` leaves the rest of the expression in the open, and here that
    // would hand the slashes of the inner separator to the comment reader. On 2026-09-16 four sites
    // in this tree were shaped like this one.
    val lines = Comments.split("""val s = s"a ${xs.mkString("//")} b" // the only comment""")

    lines.head.comment shouldBe "// the only comment"
    lines.head.code shouldBe """val s = s"a ${xs.mkString("//")} b" """

    // And the braces nest, so the closing one that ends the interpolation is the matching one and
    // not the first. Same shape as a block comment, one syntax over.
    val nested = Comments.split("""val t = s"${ if (b) { "//" } else { "x" } } end" // the comment""")
    nested.head.comment shouldBe "// the comment"
  }

  "An escaped quote" should "not end the literal it is inside" in {
    val lines = Comments.split("""val s = "a \" // still the string" // the only comment""")

    lines.head.comment shouldBe "// the only comment"
  }

  "An escaped character literal" should "be read to its closing quote" in {
    val lines = Comments.split("""val newline = '\n' // the only comment""")

    lines.head.comment shouldBe "// the only comment"
    lines.head.code shouldBe """val newline = '\n' """
  }

  "A quote that opens no character literal" should "be passed over" in {
    // Scala 3 spells a quoted expression `'{`, and `'a` is how a type variable is written in the
    // texts this repository parses. Neither is a literal, so neither may swallow the line.
    val lines = Comments.split("val q = '{ x } // the only comment")

    lines.head.comment shouldBe "// the only comment"
  }

  "An unterminated literal" should "end with the line rather than the scan" in {
    // Not a Scala source, and the reader still has to be total: a census that threw on one bad file
    // would report nothing about every other file, which is a worse answer than a wrong one.
    val lines = Comments.split("val s = \"abc // not a comment\nval after = 1 // a comment")

    lines.head.comment shouldBe ""
    lines(1).comment shouldBe "// a comment"

    // The same guard one level in: an interpolation whose brace group never closes. Tested beside
    // its sibling rather than left as the one totality case nothing reaches, because which of a
    // pair is covered would then be an accident of which malformed line somebody happened to write.
    Comments.split("""val s = s"${ x""").head.comment shouldBe ""
  }

  /* ------------------------------------------------------ across lines */

  "A block comment spanning lines" should "put every one of them in the comment" in {
    val sample =
      """/** A docstring that says var and while and null.
        |  * A continuation line that says return.
        |  */
        |// A line comment that says asInstanceOf.
        |val kept = 1
        |/* a one-line block that says var */
        |val alsoKept = 2""".stripMargin

    Comments.codeLines(sample).map(_.code.trim) shouldBe Vector("val kept = 1", "val alsoKept = 2")
    Comments.commentLines(sample).map(_.number) shouldBe Vector(1, 2, 3, 4, 6)
  }

  "A triple-quoted string spanning lines" should "stay code to its closing quotes" in {
    val sample =
      "val page = \"\"\"<a href=\"http://x\">\n" +
        "  // not a comment\n" +
        "\"\"\"\n" +
        "val after = 1 // a comment"

    Comments.commentLines(sample).map(_.number) shouldBe Vector(4)
    Comments.commentLines(sample).head.comment shouldBe "// a comment"
  }

  "The text without its comments" should "keep one line per line" in {
    val sample =
      """object Foo {
        |  /** doc
        |    * more
        |    */
        |  def bar = 1
        |}""".stripMargin

    // The pair of substitutions this replaces put a single space where the three lines of that
    // docstring had been, newlines included, so the file lost two lines and every number after it
    // moved. A caller that folds over lines read a shape that depended on how the prose was wrapped.
    Comments.withoutComments(sample).linesIterator.size shouldBe 6
    Comments.withoutComments(sample) should include("def bar = 1")
    Comments.withoutComments(sample) should not include "more"
  }

  /* ------------------------------------------------------ the `#` languages */

  "A hash comment" should "be found after code and inside no quote" in {
    val sample =
      """key: value # a trailing comment
        |echo '### The libraries'
        |# a whole line
        |echo "no # comment here" && true
        |""".stripMargin

    Comments.hashLines(sample).map(_.number) shouldBe Vector(1, 3)
    Comments.hashLines(sample).head.comment shouldBe "# a trailing comment"
  }

  /* ------------------------------------------------------ what makes the assertions above empty */

  "The split" should "lose no character, which is what says neither half is quietly dropping" in {
    // Every assertion above is about one half, and a scanner that dropped the other half would
    // satisfy most of them. This is the guard against that, and it is a count rather than a
    // reassembly because the halves do not reassemble: the first line below puts two pieces in
    // `code` with one between them in `comment`, so concatenating them gives a line nobody wrote.
    val sample =
      """object Foo { /* a */ def bar = "x // y" // z
        |  /** doc */ val c = '"'
        |}""".stripMargin

    val lines = Comments.split(sample)
    lines.map(_.text) shouldBe sample.linesIterator.toVector
    forAll(lines) { line => line.code.length + line.comment.length shouldBe line.text.length }

    // And the split is where a reader would put it, on the line that has both halves twice over.
    lines.head.comment shouldBe "/* a */// z"
    lines.head.code shouldBe """object Foo {  def bar = "x // y" """
  }

  it should "answer for a text with no comment at all, which is the input that makes it vacuous" in {
    val sample = "val a = 1\nval b = 2"

    Comments.commentLines(sample) shouldBe empty
    Comments.codeLines(sample).map(_.number) shouldBe Vector(1, 2)
    Comments.withoutComments(sample) shouldBe sample
  }
}
