package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The logarithm's first facts: what they cost, the route they take, and that they say something.
 *
 * **What it cost.** Nothing declared: the development hands on the theory it was given, constant
 * for constant, which is what `Deduction` asserts of itself for the same reason.
 *
 * **The route.** `EXP_ONTO` is the intermediate value theorem at the exponential, so it rests on
 * `INTERMEDIATE_VALUE` and on `EXP_CONTINUOUS`, and continuity rests on the one estimate,
 * `EXP_NEAR_ONE`, carried by the addition theorem. A proof of the same statements by another
 * route would read the same, so the route is what is asserted.
 *
 * **What keeps it from saying nothing.** A logarithm of a negative number is a choice nothing
 * constrains, so every fact about `ln` carries `0 < y` and is detached here at `2` with nothing
 * assumed. And the estimate's radius is not decoration: at `h = 8` the unconditional statement is
 * refuted, because `exp 8 = (exp 2)^4 >= 81`.
 */
class LogarithmSpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val logarithm = chain.logarithm
  private def rules: Rules = logarithm.logic.rules
  private val reals: Type = TyApp(Real.TypeName, Nil)

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def fact(name: String): Kernel.Thm = force(logarithm.fact(name))
  private def real(text: String): Term = force(logarithm.term(text, reals))
  private def proposition(text: String): Term = force(logarithm.proposition(text))
  private lazy val linarith: Linarith = force(Linarith.construct(chain.order))
  private def lemma(text: String): Kernel.Thm = force(linarith.prove(text))
  private def mp(theorem: Kernel.Thm, premises: Kernel.Thm*): Kernel.Thm =
    premises.foldLeft(theorem)((acc, premise) => force(rules.mp(acc, premise)))

  "The logarithm" should "declare nothing, and hand on the theory it was given" in {
    logarithm.theory.constants shouldBe chain.continuity.theory.constants
    logarithm.theory.axioms shouldBe chain.continuity.theory.axioms
    logarithm.theory.typeOperators shouldBe chain.continuity.theory.typeOperators
    chain.widest shouldBe chain.continuity
  }

  it should "state every fact as it is written, with nothing assumed" in {
    Logarithm.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe proposition(text)
        fact(name).hypotheses shouldBe empty
      }
    }
    logarithm.facts.keySet shouldBe Logarithm.Statements.map(_._1).toSet
  }

  it should "reach the exponential's range through the intermediate value theorem and continuity" in {
    val onto = fact(Logarithm.Onto)
    val route = Set(
      force(chain.continuity.fact(Continuity.IntermediateValue)).conclusion,
      fact(Logarithm.Continuous).conclusion,
      fact(Logarithm.AboveLine).conclusion)
    Derivation.restingOn(onto, route) shouldBe route

    val continuous = fact(Logarithm.Continuous)
    val underIt = Set(
      fact(Logarithm.NearOne).conclusion,
      force(chain.transcendental.fact(Transcendental.Addition)).conclusion)
    Derivation.restingOn(continuous, underIt) shouldBe underIt

    // And the logarithm's facts reach the exponential's range, which is what the choice in `ln`'s
    // definition was silent without.
    Derivation.restingOn(fact(Logarithm.LnOfExp), Set(onto.conclusion)) shouldBe Set(onto.conclusion)

    // The range spends completeness, which the rationals could not pay: `exp` restricted to them
    // misses every value whose logarithm is irrational.
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion
    Derivation.axiomsOf(onto) should contain(completeness)
  }

  it should "detach at two, so that its hypotheses are ones something satisfies" in {
    val two = real("2:real")
    val positive = lemma("(0:real) < 2")
    val found = mp(force(rules.spec(two, fact(Logarithm.Onto))), positive)
    found.hypotheses shouldBe empty
    logarithm.show(found.conclusion) shouldBe "?x:real. exp x = 2"

    val value = mp(force(rules.spec(two, fact(Logarithm.ExpOfLn))), positive)
    value.hypotheses shouldBe empty
    logarithm.show(value.conclusion) shouldBe "exp (ln 2) = 2"

    val doubled = mp(force(rules.specAll(fact(Logarithm.Multiplicative), List(two, two))), positive, positive)
    doubled.hypotheses shouldBe empty
    logarithm.show(doubled.conclusion) shouldBe "ln (2 * 2) = ln 2 + ln 2"
  }

  it should "need the estimate's radius, which is shown by refuting the estimate without it" in {
    // `exp 2 >= 3` from the line, so `exp 4 = exp 2 * exp 2 >= 9` and `exp 8 >= 81`, and
    // `abs (exp 8 - 1) <= 16` is false. The unconditional statement is refuted at that one point.
    val unconditional = proposition("!h:real. abs (exp h - 1) <= 2 * abs h")
    val assumed = force(LogicError.lift(Kernel.assume(unconditional)))
    val atEight = force(rules.spec(real("8:real"), assumed))

    def product(a: String, b: String): Kernel.Thm = {
      val addition = force(rules.specAll(force(chain.transcendental.fact(Transcendental.Addition)), List(real(a), real(a))))
      val sum = force(LogicError.lift(Term.eq(real(s"($a) + ($a)"), real(b))).flatMap(chain.ring.prove))
      val exp = force(logarithm.term("exp", Type.fun(reals, reals)))
      force(Conv.apTerm(exp, sum).flatMap(Conv.sym).flatMap(Conv.trans(_, addition)))
    }
    val line = mp(force(rules.spec(real("2:real"), fact(Logarithm.AboveLine))), lemma("(0:real) < 2"))
    val four = mp(force(rules.specAll(lemma("!p:real q:real. p = q * q ==> 1 + 2 <= q ==> 9 <= p"),
      List(real("exp 4"), real("exp 2")))), product("2", "4"), line)
    val eight = mp(force(rules.specAll(lemma("!p:real q:real. p = q * q ==> 9 <= q ==> 81 <= p"),
      List(real("exp 8"), real("exp 4")))), product("4", "8"), four)
    val above = force(chain.limit.magnitude.fact(Magnitude.AbsAbove).flatMap(rules.spec(real("exp 8 - 1"), _)))
    val eightIs = mp(force(chain.limit.magnitude.fact(Magnitude.OfNonNegative).flatMap(rules.spec(real("8:real"), _))),
      lemma("(0:real) <= 8"))
    val absurd = mp(force(rules.specAll(
      lemma("!e:real d:real m:real. 81 <= e ==> e - 1 <= d ==> m = 8 ==> d <= 2 * m ==> F"),
      List(real("exp 8"), real("abs (exp 8 - 1)"), real("abs 8")))), eight, above, eightIs, atEight)
    val refused = force(rules.notIntro(unconditional, absurd))

    refused.hypotheses shouldBe empty
  }
}
