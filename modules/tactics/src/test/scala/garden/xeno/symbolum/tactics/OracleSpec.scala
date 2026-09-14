package garden.xeno.symbolum.tactics

import org.scalacheck.Gen
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks
import garden.xeno.symbolum.{Add, Cos, Div, Expr, Mul, Num, Pow, Var}
import garden.xeno.symbolum.kernel.*

/**
 * The computer algebra system proposing and the kernel checking.
 *
 * The test that matters most is the one where the oracle is wrong on purpose. Everything else here
 * shows the bridge working; that one shows it cannot be talked into anything, which is the only
 * reason the arrangement is worth having.
 */
class OracleSpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {

  /**
   * Fewer cases than elsewhere: every one of them runs a full ring normalisation, where the other
   * property tests run a substitution. Twenty-five random polynomials take a few seconds.
   */
  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 25)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val oracle = Oracle.standard
  private val reals = oracle.reals

  /** The widest signature the repository assembles, which is the only one that has `real_of_num`. */
  private val chain: garden.xeno.symbolum.theories.Signature = garden.xeno.symbolum.theories.Chain.standard.widest

  private val x = Var("x")
  private val y = Var("y")

  "The oracle" should "have its expansion certified" in {
    val expression = Mul(Vector(Add(Vector(x, Num(1))), Add(Vector(x, Num(1)))))
    val certified = force(oracle.certifyExpansion(expression))

    certified.theorem.hypotheses shouldBe empty
    Term.destEq(certified.theorem.conclusion) should not be None
    // The theorem is about the expression that went in and the one that came out, not about
    // something the translation invented on the way.
    Term.destEq(certified.theorem.conclusion).map(_._1) shouldBe
      Some(force(Translate.toTerm(reals, expression)))
    Term.destEq(certified.theorem.conclusion).map(_._2) shouldBe
      Some(force(Translate.toTerm(reals, certified.proposal)))
  }

  it should "have a simplification certified" in {
    val expression = Add(Vector(x, x, y))
    val certified = force(oracle.certifySimplification(expression))

    certified.theorem.hypotheses shouldBe empty
    reals.show(certified.theorem.conclusion) should include("=")
  }

  "An identity" should "be certified when it holds" in {
    val left = Mul(Vector(x, Add(Vector(y, Num(1)))))
    val right = Add(Vector(Mul(Vector(x, y)), x))

    force(oracle.certifyIdentity(left, right)).hypotheses shouldBe empty
  }

  it should "be refused when it does not hold" in {
    // The oracle is trusted for nothing, and this is what that means: an identity that is simply
    // false gets no theorem, however it was proposed.
    val result = oracle.certifyIdentity(Add(Vector(x, x)), Mul(Vector(Num(3), x)))

    result.left.map(_.getClass) shouldBe Left(classOf[NotCertified])
  }

  it should "be refused when it is true but outside what the tactic can see" in {
    // `x * x = x^2` is true and the translation expands the power, so this one passes; the refusal
    // below is the shape that does not.
    force(oracle.certifyIdentity(Mul(Vector(x, x)), Pow(x, Num(2))))

    // `x * 2 = x * 4 / 2` was the witness here and is certified since 2026-09-09: a numeral
    // denominator is a coefficient now. What still refuses is a SYMBOLIC one: `(2 * x) / x = 2`
    // needs `x * inv x` to become `1`, which costs the hypothesis `~(x = 0)` that this tactic has
    // nowhere to put. The refusal comes from the tactic and not from the reader, which is the more
    // informative place for it to come from.
    oracle
      .certifyIdentity(Div(Vector(Mul(Vector(Num(2), x)), x)), Num(2))
      .left
      .map(_.getClass) shouldBe Left(classOf[NotCertified])
  }

  "The fragment" should "refuse what the theory cannot state" in {
    Translate.toTerm(reals, Cos(x)).left.map(_.getClass) shouldBe Left(classOf[OutsideFragment])
    // A fractional literal and a root stay out, and for a reason that is now stated as their own
    // rather than borrowed from division: the numerals of this theory are integers, and there is
    // no constant for a root.
    Translate.toTerm(reals, Num(1, 2)).left.map(_.getClass) shouldBe Left(classOf[OutsideFragment])
    Translate.toTerm(reals, Pow(x, Num(1, 2))).left.map(_.getClass) shouldBe
      Left(classOf[OutsideFragment])
  }

  it should "read a quotient, which it used to refuse" in {
    // `x / y` abbreviates `x * inv y`, and unfolding an abbreviation asks for nothing. What asks
    // for `~(y = 0)` is cancelling, which belongs to the tactic. Seven of the ten refusals in the
    // RING corpus were quotients held out by a sentence that was about the cancellation.
    Translate.toTerm(reals, Div(Vector(x, y))) should matchPattern { case Right(_) => }
    reals.show(force(Translate.toTerm(reals, Div(Vector(x, y))))) shouldBe "x / y"
  }

  /* ------------------------------------------------------ the fragment at the naturals */

  "The naturals" should "enter through the embedding rather than as reals with a different name" in {
    // What a statement about whole numbers becomes. The variable is of type `num` and the term is
    // of type `real`, which is the whole arrangement: the claim is about the image of the naturals,
    // so the procedures that decide the reals are the ones that see it, and the embedding is
    // written into the term where a reader can see it rather than taken silently.
    val term = force(Translate.toTerm(chain, Add(Vector(x, Num(3))), Translate.Target.Naturals))

    chain.show(term) shouldBe "real_of_num x + 3"
    Term.typeOf(term) shouldBe TyApp(garden.xeno.symbolum.theories.Real.TypeName, Nil)
  }

  it should "refuse the operators that are not the reals' operators at that type" in {
    // The three the naturals do not share with the reals. Subtraction there is truncated and
    // division is the floor, so reading either as the reals' would state something other than what
    // was written; a negation is not a natural number at all.
    //
    // The witness is not invented: miniF2F's `mathd_algebra_314` is
    // `(n : ℕ) (h₀ : n = 11) : (1 / 4)^(n + 1) * 2^(2 * n) = 1 / 4`, where every literal is a
    // natural, `1 / 4` is zero, and what Lean holds is `0 = 0`. Reading those quotients as the
    // reals' would hand the kernel a statement about fourths that nobody wrote, and it is the kind
    // of statement a prover then goes on to certify.
    def refused(expression: Expr): String =
      Translate.toTerm(chain, expression, Translate.Target.Naturals) match {
        case Right(term) => fail(s"$expression was read as ${chain.show(term)}")
        case Left(error) => error.message
      }

    refused(garden.xeno.symbolum.Sub(Vector(x, y))) should include("truncated at zero")
    refused(Div(Vector(Num(1), Num(4)))) should include("the floor of the quotient")
    refused(garden.xeno.symbolum.Neg(x)) should include("no negation")
  }

  it should "still read what the two types share" in {
    // Addition, multiplication, a whole exponent and the numerals, which is what makes the target
    // worth having: `real_of_num` is a homomorphism for the first two, so the statement that comes
    // out is the statement that went in.
    val squared = force(Translate.toTerm(chain, Pow(x, Num(2)), Translate.Target.Naturals))

    chain.show(squared) shouldBe "real_of_num x * real_of_num x"
  }

  it should "refuse a target the signature has no embedding for" in {
    // `Real.standard` has no `num` and no `real_of_num`, so asking for the naturals there is a
    // refusal rather than a term built out of a constant nobody declared. The target says what the
    // caller meant; the signature says what can be said.
    Translate.toTerm(reals, x, Translate.Target.Naturals) should matchPattern { case Left(_) => }
  }

  it should "read a closed exponent as the number it is" in {
    // An exponent is a number and not a spelling, so `x ^ (2 + 2)` and `x ^ 4` are the same claim
    // and the border may not treat them differently. Independent of any corpus on purpose: this
    // is the rule, and the benchmark that motivated it is a separate artifact that must be free
    // to move.
    force(oracle.certifyIdentity(Pow(x, Add(Vector(Num(2), Num(2)))), Pow(x, Num(4))))

    // Nested, because the exponent's own exponent is closed too, and this is the shape that
    // appears in the wild as `X^2^3`.
    force(oracle.certifyIdentity(Pow(x, Pow(Num(2), Num(3))), Pow(x, Num(8))))
  }

  it should "read a zero exponent as the empty product, and show what it proved" in {
    // The border expands a power into a product, so a zero exponent leaves the product of nothing,
    // which is the numeral 1 whatever the base was. That holds at zero too, and the theory agrees
    // with HOL Light and Mathlib in having no side condition on it.
    val certified = force(oracle.certifyIdentity(Pow(x, Num(0)), Num(1)))
    force(oracle.certifyIdentity(Pow(Num(0), Num(0)), Num(1)))

    // And the theorem says `1 = 1`, not `x^0 = 1`, because the theory has no exponentiation
    // constant for the second to be about. That is worth pinning rather than leaving implicit: a
    // reader who takes this as a theorem about `x^0` is reading the border's convention, not the
    // kernel's derivation, and the two are only the same while the convention is the algebraic one.
    reals.show(certified.conclusion) shouldBe "1 = 1"
  }

  it should "still refuse the exponents that are not a whole number in range" in {
    def refusal(expression: Expr): String =
      Translate.toTerm(reals, expression) match {
        case Left(error: OutsideFragment) => error.reason
        case other => fail(s"expected a refusal by name, got $other")
      }

    // Each says which of the four it is, because they suggest different next steps: a symbolic
    // exponent waits on the naturals, a root and an inverse wait on theorems the theory does not
    // have, and a large one is a bound this file chose.
    refusal(Pow(x, y)) should include("not closed arithmetic")
    refusal(Pow(x, Num(1, 2))) should include("a root")
    refusal(Pow(x, Num(-1))) should include("a negative exponent is an inverse")
    refusal(Pow(x, Mul(Vector(Num(3), Num(6))))) should include("above 16")
  }

  it should "accept a negative literal" in {
    val certified = force(oracle.certifyIdentity(Add(Vector(x, Num(-1))), Add(Vector(Num(-1), x))))

    certified.hypotheses shouldBe empty
  }

  it should "translate a term to itself when it is already a term" in {
    reals.show(force(Translate.toTerm(reals, Add(Vector(x, Num(2)))))) shouldBe "x + 2"
  }

  /* ------------------------------------------------------------- the property */

  private val atom: Gen[Expr] =
    Gen.oneOf(Gen.choose(0, 3).map(n => Num(n): Expr), Gen.oneOf(x, y))

  private def polynomial(depth: Int): Gen[Expr] =
    if (depth <= 0) atom
    else {
      val child = polynomial(depth - 1)
      Gen.oneOf(
        atom,
        Gen.listOfN(2, child).map(parts => Add(parts.toVector): Expr),
        Gen.listOfN(2, child).map(parts => Mul(parts.toVector): Expr),
        child.flatMap(base => Gen.choose(0, 2).map(exponent => Pow(base, Num(exponent)): Expr))
      )
    }

  "Every expansion the oracle proposes" should "be provable, over generated polynomials" in {
    // This is the arrangement used as a test harness: the computer algebra system runs on random
    // input and every answer it gives is proved. A defect in its polynomial handling shows up here
    // as a refusal, with the expression that caused it.
    forAll(polynomial(3)) { expression =>
      whenever(Translate.isTranslatable(reals, expression)) {
        val result = oracle.certifyExpansion(expression)

        withClue(s"$expression  ->  ${expression.expand()}\n") {
          result.isRight shouldBe true
        }
      }
    }
  }
}
