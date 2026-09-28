package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Integration by parts and the change of variables with derivatives relative to `[a, b]`, and the
 * tangent extension they are carried by.
 *
 * `IntegralSpec` compares every statement `Integral` publishes with its text. What is asserted here
 * is what it cannot see: that each relative rule detaches, with nothing assumed, at `abs` on
 * `[0, 1]`, which has slope `1` relative to the interval everywhere and no derivative at `0`, so the
 * two-sided rules cannot be detached there; that the tangent extension of `abs` has a two-sided
 * derivative at `0`, which is the whole of what the lemma adds; and that each relative rule costs
 * what its two-sided form costs and rests on it through the extension.
 */
class IntegralRulesWithinSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val integral = chain.integral
  private def logic: Logic = integral.logic
  private def rules: Rules = logic.rules
  private val reals: Type = TyApp(Real.TypeName, Nil)
  private val functions: Type = Type.fun(reals, reals)

  private def fact(name: String): Kernel.Thm = force(integral.fact(name))
  private def slope(name: String): Kernel.Thm = force(chain.derivative.fact(name))
  private def real(text: String): Term = force(integral.term(text, reals))
  private def function(text: String): Term = force(integral.term(text, functions))
  private def proposition(text: String): Term = force(integral.proposition(text))
  private lazy val linarith: Linarith = force(Linarith.construct(chain.order))
  private def lemma(text: String): Kernel.Thm = force(linarith.prove(text))
  private def opened(theorem: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(theorem.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, theorem))))
  private def at(theorem: Kernel.Thm, arguments: Term*): Kernel.Thm =
    opened(force(rules.specAll(theorem, arguments.toList)))
  private def mp(theorem: Kernel.Thm, premises: Kernel.Thm*): Kernel.Thm =
    premises.foldLeft(theorem)((acc, premise) => force(rules.mp(acc, premise)))

  private lazy val witness = new AbsoluteAtAnEnd(chain)
  private val zero = "0:real"
  private val one = "1:real"

  /** `|- !x. 0 <= x /\ x <= 1 ==> derivative_within (\z. 1) 0 1 x 0`: a constant's slope, relative. */
  private lazy val constantRelative: Kernel.Thm = {
    val x = Term.variable("x", reals)
    val constant = mp(at(slope(Derivative.Constant), real(one), x))
    val relative = mp(at(slope(Derivative.WithinOfDerivative), function("\\z:real. (1:real)"), real(zero), real(one), x, real(zero)), constant)
    force(rules.disch(proposition("(0:real) <= x:real /\\ x <= 1"), relative).flatMap(rules.gen(x, _)))
  }

  /** `|- has_integral (\x. 1 * 1) 0 1 (abs 1 - abs 0)`, the change of variables at `g = abs`. */
  private lazy val substituted: Kernel.Thm =
    mp(at(fact(Integral.HasSubstitutionWithin), function("\\y:real. y"), function("\\y:real. (1:real)"),
      function("abs"), function("\\x:real. (1:real)"), real(zero), real(one)),
      lemma("(0:real) <= 1"), slope(Derivative.Identity), witness.relative)

  "The tangent extension" should "give abs a two-sided slope at 0, where abs itself has none" in {
    witness.noSlopeAtZero.hypotheses shouldBe empty
    val extended = mp(at(fact(Integral.TangentSlope), function("abs"), function("\\x:real. (1:real)"),
      real(zero), real(one), real(zero)), lemma("(0:real) <= 1"), witness.relative, lemma("(0:real) <= 0"), lemma("(0:real) <= 1"))
    extended.hypotheses shouldBe empty
    extended.conclusion shouldBe proposition(
      "derivative (\\y:real. COND (y < 0) (abs 0 + 1 * (y - 0)) (COND (1 < y) (abs 1 + 1 * (y - 1)) (abs y))) 0 1")
  }

  /**
   * The change of variables at `g = abs` on `[0, 1]`. Its two-sided form asks `derivative abs 0 1`,
   * which `AbsoluteAtAnEnd` refutes, so only the relative form detaches here.
   */
  "The relative rules" should "detach the change of variables at abs on [0, 1] with nothing assumed" in {
    substituted.hypotheses shouldBe empty
    substituted.conclusion shouldBe proposition("has_integral (\\x:real. 1 * 1) 0 1 (abs 1 - abs 0)")

    val named = mp(at(fact(Integral.SubstitutionWithin), function("\\y:real. y"), function("\\y:real. (1:real)"),
      function("abs"), function("\\x:real. (1:real)"), real(zero), real(one)),
      lemma("(0:real) <= 1"), slope(Derivative.Identity), witness.relative)
    named.hypotheses shouldBe empty
    named.conclusion shouldBe proposition("integral (\\x:real. 1 * 1) 0 1 = abs 1 - abs 0")

    // and the two-sided hypothesis is false there, at 0
    val twoSided = proposition("!x:real. 0 <= x /\\ x <= 1 ==> derivative abs x 1")
    val assumed = force(LogicError.lift(Kernel.assume(twoSided)))
    val atZero = mp(at(assumed, real(zero)), force(rules.conjIntro(lemma("(0:real) <= 0"), lemma("(0:real) <= 1"))))
    val refused = force(rules.notElim(witness.noSlopeAtZero, atZero).flatMap(rules.notIntro(twoSided, _)))
    refused.hypotheses shouldBe empty
  }

  /**
   * Integration by parts at `f = 1`, `g = abs`: the integrand `f * dg` is `1 * 1`, whose integral the
   * change of variables above supplies, so the whole detachment rests on the relative rules alone.
   */
  it should "detach integration by parts at a constant and abs on [0, 1] with nothing assumed" in {
    val arguments = Vector(function("\\z:real. (1:real)"), function("abs"), function("\\x:real. (0:real)"),
      function("\\x:real. (1:real)"), real(zero), real(one), real("abs 1 - abs 0"))
    val has = mp(at(fact(Integral.HasPartsWithin), arguments*),
      lemma("(0:real) <= 1"), constantRelative, witness.relative, substituted)
    has.hypotheses shouldBe empty
    has.conclusion shouldBe proposition(
      "has_integral (\\x:real. 0 * abs x) 0 1 (1 * abs 1 - 1 * abs 0 - (abs 1 - abs 0))")
    val named = mp(at(fact(Integral.PartsWithin), arguments*),
      lemma("(0:real) <= 1"), constantRelative, witness.relative, substituted)
    named.hypotheses shouldBe empty
  }

  it should "cost what the two-sided rules cost" in {
    for ((relative, twoSided) <- Vector(
        Integral.HasPartsWithin -> Integral.HasParts,
        Integral.PartsWithin -> Integral.Parts,
        Integral.HasSubstitutionWithin -> Integral.HasSubstitution,
        Integral.SubstitutionWithin -> Integral.Substitution
      )) withClue(s"$relative: ") {
      Derivation.axiomsOf(fact(relative)) shouldBe Derivation.axiomsOf(fact(twoSided))
    }
  }

  it should "carry the two-sided rules to the relative ones through the tangent extension" in {
    val tangent = fact(Integral.TangentSlope).conclusion
    val parts = Set(tangent, fact(Integral.HasParts).conclusion, fact(Integral.HasCongruence).conclusion)
    Derivation.restingOn(fact(Integral.HasPartsWithin), parts) shouldBe parts
    val substitution = Set(tangent, fact(Integral.HasSubstitution).conclusion)
    Derivation.restingOn(fact(Integral.HasSubstitutionWithin), substitution) shouldBe substitution
  }
}
