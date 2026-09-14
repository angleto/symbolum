package garden.xeno.symbolum.kernel

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The properties the inference rules rely on and therefore do not re-check.
 *
 * Two of these are the reason for the representation and are worth more than the rest: that terms
 * differing only in the name of a bound variable are one value, and that substitution cannot
 * capture. If either stops holding, every rule in the kernel is unsound and nothing else in the
 * suite would notice.
 */
class TermSpec extends AnyFlatSpec with Matchers {


  /**
   * Abstraction, forced.
   *
   * `Term.abs` refuses a body that is not locally closed, since 2026-09-10, so it returns a
   * refusal like `app` and `eq` do. Every body below is built out of variables and constants a
   * line or two above and none of them can be open, so forcing here is reading the signature and
   * not ignoring it. A test that meant to hand it an open body says so by calling `Term.abs`
   * directly and looking at the `Left`.
   */
  private def lam(variable: FVar, body: Term): Term =
    Term.abs(variable, body).fold(error => fail(s"unexpected refusal: $error"), identity)

  private val A = TyVar("A")
  private val B = TyVar("B")
  private val x = Term.variable("x", A)
  private val y = Term.variable("y", A)

  "A lambda" should "not record the name of the variable it binds" in {
    lam(x, x) shouldBe lam(y, y)
  }

  it should "keep a free variable of the same name at another type distinct" in {
    val other = Term.variable("x", B)
    lam(x, other) should not be lam(x, x)
  }

  it should "have a function type" in {
    Term.typeOf(lam(x, x)) shouldBe Type.fun(A, A)
  }

  "Substitution" should "not capture the variable it moves under a binder" in {
    // In a representation carrying names, `(\x. y)[y := x]` reads as `\x. x` unless the binder is
    // renamed first. Here the binder holds an index, so the x that arrives stays free.
    val body = lam(x, y)
    val substituted = Term.substitute(Map(y -> x), body)

    substituted.map(Term.freeVariables) shouldBe Right(Set(x))
    substituted should not be Right(lam(x, x))
  }

  it should "refuse a replacement of the wrong type" in {
    val wrongType = Term.variable("z", B)
    Term.substitute(Map(x -> wrongType), x).left.map(_.getClass) shouldBe
      Left(classOf[TypeMismatch])
  }

  it should "leave a variable it was not given alone" in {
    Term.substitute(Map(x -> y), y) shouldBe Right(y)
  }

  "Type instantiation" should "identify two variables that differed only in their type" in {
    val xa = Term.variable("x", A)
    val xb = Term.variable("x", B)
    xa should not be xb

    Term.substituteTypes(Map("A" -> B), xa) shouldBe xb
  }

  "Application" should "refuse an argument of the wrong type" in {
    val identity = lam(x, x)
    val wrongType = Term.variable("z", B)

    Term.app(identity, wrongType).left.map(_.getClass) shouldBe Left(classOf[TypeMismatch])
  }

  it should "refuse a term that is not a function" in {
    Term.app(x, y).left.map(_.getClass) shouldBe Left(classOf[NotAFunction])
  }

  it should "take the codomain as its type" in {
    val applied = Term.app(lam(x, x), y)
    applied.map(Term.typeOf) shouldBe Right(A)
  }

  "An equation" should "be taken apart into the sides it was built from" in {
    val equation = Term.eq(x, y)
    equation.map(Term.destEq) shouldBe Right(Some((x, y)))
  }

  it should "be a proposition whatever the type of its sides" in {
    Term.eq(x, y).map(Term.typeOf) shouldBe Right(Type.Bool)
  }

  it should "be refused between terms of different types" in {
    Term.eq(x, Term.variable("z", B)).left.map(_.getClass) shouldBe Left(classOf[TypeMismatch])
  }

  "Beta reduction" should "substitute the argument for the bound variable" in {
    val applied = Term.app(lam(x, x), y).getOrElse(fail("the application should type check"))
    Term.betaReduce(applied) shouldBe Some(y)
  }

  it should "leave a term that is not a redex alone" in {
    Term.betaReduce(x) shouldBe None
  }

  "Free variables" should "not include the one a lambda binds" in {
    Term.freeVariables(lam(x, x)) shouldBe empty
    Term.freeVariables(lam(x, y)) shouldBe Set(y)
  }

  /* ------------------------------ the invariant, and where it is established */

  "The operations that admit a term from outside" should "each refuse one that is not locally closed" in {
    // `typeOf` is total, and may be, only because these four establish the premise it assumes.
    // The list is written out so that a fifth builder cannot be added without joining it: that is
    // exactly how `Term.abs` came to be the one that did not check, from 2026-09-03 until an
    // adversarial review on 2026-09-10 read the file for a different reason and noticed.
    val loose = lam(x, x) match {
      case Abs(_, body) => body
      case other => fail(s"expected an abstraction, got $other")
    }

    Term.isLocallyClosed(loose) shouldBe false

    Term.abs(x, loose).left.map(_.getClass) shouldBe Left(classOf[NotLocallyClosed])
    Term.app(loose, x).left.map(_.getClass) shouldBe Left(classOf[NotLocallyClosed])
    Term.eq(loose, loose).left.map(_.getClass) shouldBe Left(classOf[NotLocallyClosed])
    Term.substitute(Map(x -> loose), x).left.map(_.getClass) shouldBe Left(classOf[NotLocallyClosed])
  }

}
