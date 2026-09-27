package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Every binder of the printed library is named from its type's list, read off the page itself.
 *
 * Until 2026-09-26 the printer named binders x, y, z by position, and the mean value theorem read
 * `!x:real -> real. !y:real. !z:real. ...`. `Show.binderName` now offers a function `f`, `g`, `h`,
 * a proposition `p`, `q`, `r`, a natural `n`, `m`, `k`, `i`, `j`, and anything else `x` to `w`,
 * each with a digit once the list is spent. The pinned texts across the specs move if that rule
 * moves, but none of them says what the rule is, and a regression that named one kind of binder
 * positionally again would be repaired by re-pinning the texts. This reads the whole listing the
 * way a reader does and asserts the rule over every binder on it.
 *
 * Two things keep it from being vacuous, and both are assertions rather than hopes:
 *
 *   - **The page is read completely.** The number of function-typed binders found in the printed
 *     text equals the number of function-typed abstractions in the statements' terms, counted on
 *     the terms without printing them. A reader of the text that skipped a binder shape would come
 *     up short and fail here rather than report nothing wrong.
 *   - **Each class is populated.** A class with no binders would pass any rule.
 *
 * Written for the verification of Mycelium card `14b83bac`, 2026-09-27.
 */
class BinderNamesByTypeSpec extends AnyFlatSpec with Matchers {

  private lazy val chain = Chain.standard
  private lazy val library = Library.of(chain)
  private lazy val listing: String = library.listing(chain.widest)

  private val Entry = """^  (\S+)\s+(\S.*)$""".r
  private val Binder = """([!?\\@])([A-Za-z][A-Za-z0-9_]*):""".r

  /** The entries of the listing, name and printed statement. */
  private lazy val entries: Vector[(String, String)] =
    listing.linesIterator.collect { case Entry(name, statement) => (name, statement) }.toVector

  /** The type text after a binder's colon, up to the `.` that closes the binder at depth zero. */
  private def typeText(statement: String, from: Int): String = {
    var depth = 0
    var index = from
    while (index < statement.length && !(statement(index) == '.' && depth == 0)) {
      if (statement(index) == '(') depth += 1
      if (statement(index) == ')') depth -= 1
      index += 1
    }
    statement.substring(from, index).trim
  }

  private def arrowAtTop(text: String): Boolean = {
    var depth = 0
    text.indices.exists { index =>
      if (text(index) == '(') depth += 1
      if (text(index) == ')') depth -= 1
      depth == 0 && text.startsWith("->", index)
    }
  }

  private def classOf(text: String): String =
    if (arrowAtTop(text)) "function"
    else if (text == "bool") "proposition"
    else if (text == "num") "natural"
    else "value"

  private val offered: Map[String, Set[String]] = Map(
    "function" -> Set("f", "g", "h"),
    "proposition" -> Set("p", "q", "r"),
    "natural" -> Set("n", "m", "k", "i", "j"),
    "value" -> Set("x", "y", "z", "u", "v", "w"))

  private def stem(name: String): String = name.reverse.dropWhile(_.isDigit).reverse

  /** (entry, binder name, class) for every binder printed on the page. */
  private lazy val binders: Vector[(String, String, String)] = entries.flatMap { case (entry, statement) =>
    Binder.findAllMatchIn(statement).map(m => (entry, m.group(2), classOf(typeText(statement, m.end)))).toVector
  }

  private def functionAbstractions(term: Term): Int = term match {
    case App(fn, arg) => functionAbstractions(fn) + functionAbstractions(arg)
    case Abs(binderType, body) =>
      (if (Type.destFun(binderType).isDefined) 1 else 0) + functionAbstractions(body)
    case _ => 0
  }

  "The printed library" should "be read whole: every function-typed abstraction in the terms is a binder found on the page" in {
    entries.size shouldBe library.entries.size
    val onPage = binders.count(_._3 == "function")
    val inTerms = library.entries.map(entry => functionAbstractions(entry.theorem.conclusion)).sum
    onPage should be > 0
    onPage shouldBe inTerms
  }

  it should "name every binder from its type's list, and every list is used" in {
    val misnamed = binders.filterNot { case (_, name, kind) => offered(kind).contains(stem(name)) }
    withClue(misnamed.take(10).mkString("\n")) { misnamed shouldBe empty }
    for (kind <- offered.keys) withClue(kind) { binders.count(_._3 == kind) should be > 0 }
  }

  it should "print the mean value theorem about f, as the card that asked for this measured it" in {
    val meanValue = entries.collectFirst { case ("MEAN_VALUE", statement) => statement }.getOrElse(fail("no MEAN_VALUE"))
    meanValue should startWith("!f:real -> real. !x:real. !y:real. x < y ==> ")
  }

  "Show.binderName" should "offer each class its own first name, whatever the position" in {
    val reals = TyApp(Real.TypeName, Nil)
    val never: String => Boolean = _ => false
    Show.binderName(Type.fun(reals, reals), never) shouldBe "f"
    Show.binderName(Type.fun(TyApp(Natural.TypeName, Nil), Type.fun(reals, reals)), never) shouldBe "f"
    Show.binderName(Type.Bool, never) shouldBe "p"
    Show.binderName(TyApp(Natural.TypeName, Nil), never) shouldBe "n"
    Show.binderName(reals, never) shouldBe "x"
    Show.binderName(Type.fun(reals, reals), Set("f", "g", "h")) shouldBe "f1"
  }
}
