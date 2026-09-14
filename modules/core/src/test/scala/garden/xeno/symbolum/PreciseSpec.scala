package garden.xeno.symbolum

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * An expression evaluated to fifty digits, and the one candidate that shows why it was needed.
 *
 * The precision corpus has a pair that agrees to nine digits and is not an identity:
 * `x + x/1000000000` against `x`. It survives the `Double` screen, whose tolerance is `1e-8`, and
 * the kernel refuses it afterwards. Nothing calls that a discovery today because nothing reports
 * the survivors of the screen, and a loop that proposed at volume would.
 *
 * Both halves of that are asserted here: that the `Double` screen passes it, and that fifty digits
 * do not. A test of the second alone would not say what the second is for.
 */
class PreciseSpec extends AnyFlatSpec with Matchers {

  private val fifty = Precise.to(50)
  private val x = Var("x")
  private val at7 = Map("x" -> BigDecimal(7))

  /* ---------------------------------------------------------- the reason for the file */

  "The pair the Double screen lets through" should "not survive fifty digits" in {
    val nudged = Add(Vector(x, Div(Vector(x, Num(1000000000)))))

    // The first stage says yes, which is the fact this file is a response to.
    val doublePoint = Map("x" -> 7.0)
    math.abs(nudged.eval(doublePoint) - x.eval(doublePoint)) should be <= 1e-8 * 7.0

    // The second says how far the agreement went, which is a different and more useful answer than
    // "they differ": nine digits is what a sixteen-digit screen would have called agreement.
    fifty.agreement(nudged, x, at7) shouldBe Some(9)
  }

  it should "be told apart from a pair that agrees all the way down" in {
    // The comparison this file exists to make. Both pairs pass the `Double` screen; only one of
    // them is an identity, and the number of digits is what separates them.
    val identity = Add(Vector(Pow(Sin(x), Num(2)), Pow(Cos(x), Num(2))))

    fifty.agreement(identity, Num(1), at7) shouldBe None
  }

  it should "count the digits a round trip actually costs" in {
    // `exp(log x)` is `x` and comes back agreeing to forty-nine of fifty digits, not fifty. That is
    // the honest reading of an expression whose every step rounds, and it is why the comparison
    // takes a slack rather than asking about the last digit.
    fifty.agreement(Exp(Log(x)), x, at7) shouldBe Some(49)
  }

  /* -------------------------------------------------------------------- what it reads */

  "A literal" should "be exact when it is a fraction and no better than it came when it is not" in {
    // A third to fifty digits, because `Num` holds a fraction and this divides it here.
    fifty.at(Div(Vector(Num(1), Num(3))), at7).map(_.toString) shouldBe
      Some("0.33333333333333333333333333333333333333333333333333")

    // And `Dsl.e`, which is `Num(math.E)`, with the sixteen digits a `Double` had. No arithmetic
    // recovers a seventeenth, which is the whole reason `Arbitrary.e` exists.
    fifty.at(Dsl.e, at7) shouldBe Some(BigDecimal("2.718281828459045"))
  }

  "A variable" should "be read from the point and nowhere else" in {
    // `Dsl.pi` is `Var("pi")` and nothing in this module gives that name a meaning, so neither does
    // this: a point that does not bind it gets no answer rather than an answer about a number the
    // caller did not ask for.
    fifty.at(Dsl.pi, at7) shouldBe None
    fifty.at(Var("y"), at7) shouldBe None

    val supplied = at7 ++ fifty.named
    fifty.at(Dsl.pi, supplied) shouldBe Some(fifty.arithmetic.pi)

    // The sine of that pi is the tail of pi rather than zero, which is the right answer about a
    // fifty-digit decimal and not about the constant.
    fifty.at(Sin(Dsl.pi), supplied).get.abs should be < BigDecimal("1e-50")
  }

  "Every node with an arithmetic meaning" should "have a value" in {
    val point = Map("x" -> BigDecimal(2), "y" -> BigDecimal(3))

    fifty.at(Add(Vector(x, Var("y"))), point) shouldBe Some(BigDecimal(5))
    fifty.at(Sub(Vector(Var("y"), x)), point) shouldBe Some(BigDecimal(1))
    fifty.at(Mul(Vector(x, Var("y"))), point) shouldBe Some(BigDecimal(6))
    fifty.at(Div(Vector(Var("y"), x)), point) shouldBe Some(BigDecimal("1.5"))
    fifty.at(Neg(x), point) shouldBe Some(BigDecimal(-2))
    fifty.at(Pow(x, Var("y")), point) shouldBe Some(BigDecimal(8))
    fifty.at(Num(5), point) shouldBe Some(BigDecimal(5))
    fifty.at(Exp(Num(0)), point) shouldBe Some(BigDecimal(1))
    fifty.at(Log(Num(1)), point) shouldBe Some(BigDecimal(0))
    fifty.at(Sin(Num(0)), point) shouldBe Some(BigDecimal(0))
    fifty.at(Cos(Num(0)), point) shouldBe Some(BigDecimal(1))
    fifty.at(Tan(Num(0)), point) shouldBe Some(BigDecimal(0))
  }

  "A place where the question has no answer" should "give nothing, and never throw" in {
    // `Expr.eval` throws at three of these. A screening loop asks this of thousands of points and
    // wants a value it can skip rather than a control transfer it has to catch.
    fifty.at(Div(Vector(x, Num(0))), at7) shouldBe None
    fifty.at(Log(Neg(x)), at7) shouldBe None
    fifty.at(Var("nobody"), at7) shouldBe None
    fifty.at(Pow(Neg(x), Div(Vector(Num(1), Num(2)))), at7) shouldBe None

    // And the same through a wrapper, so that one missing leaf loses the whole answer rather than
    // being counted as zero.
    fifty.at(Add(Vector(x, Var("nobody"))), at7) shouldBe None
    fifty.at(Mul(Vector(x, Div(Vector(x, Num(0))))), at7) shouldBe None
    fifty.agreement(Var("nobody"), x, at7) shouldBe None
  }

  /* ------------------------------------------------------------------- the census */

  "Every node type this module defines" should "be evaluated or be named as declined" in {
    // The catch-all at the bottom of the traversal returns nothing, which is the safe answer and
    // also a silent one: a node type added next year would fall through it and be refused at every
    // point without anybody noticing. This reads the module's own sources, so adding one fails
    // here until somebody decides which list it belongs in.
    val declared = Files
      .list(PreciseSpec.sources)
      .iterator
      .asScala
      .toVector
      .filter(path => path.getFileName.toString.endsWith(".scala"))
      .filter(path => PreciseSpec.extendsExpr(Files.readString(path)))
      .map(path => path.getFileName.toString.stripSuffix(".scala"))
      .sorted

    declared should not be empty
    withClue(s"declared in the module: ${declared.mkString(", ")}\n") {
      declared shouldBe (Precise.Handled ++ Precise.Declined).sorted
    }
  }

  "The two that are declined" should "give nothing rather than fifty digits of a step size" in {
    // Both are approximations in the `Double` evaluator as well, and their error is a property of
    // the step rather than of the arithmetic. Fifty digits of a five-point finite difference is
    // fifty digits of which six are about the derivative.
    fifty.at(Derivative(Mul(Vector(x, x)), "x"), at7) shouldBe None
    fifty.at(Integral(Mul(Vector(x, x)), "x", Some(Num(0)), Some(Num(1))), at7) shouldBe None
  }

  /* --------------------------------------------------------------- the instances */

  "The precision" should "be the one asked for, and the standard one the screen's" in {
    Precise.to(12).digits shouldBe 12
    Precise.standard.digits shouldBe Arbitrary.standard.digits
    Precise.over(Arbitrary.to(7)).digits shouldBe 7
  }
}

private object PreciseSpec {

  /** Where this module's sources are, found from wherever the tests were started. */
  val sources: Path = {
    def search(from: Path, left: Int): Path = {
      val candidate = from.resolve("modules/core/src/main/scala/garden/xeno/symbolum")
      if (Files.isDirectory(candidate)) candidate
      else if (left == 0) throw new IllegalStateException(s"no module sources above $from")
      else search(from.getParent, left - 1)
    }
    search(Paths.get("").toAbsolutePath, 5)
  }

  /**
   * Whether a source file declares a subtype of `Expr`.
   *
   * `extends Expr` and not `extends Expr`-anything: `ExpressionError` starts with the same seven
   * letters and is not a node.
   */
  def extendsExpr(source: String): Boolean =
    source.linesIterator.exists { line =>
      val trimmed = line.trim
      trimmed.endsWith("extends Expr") || trimmed.endsWith("extends Expr {")
    }
}
