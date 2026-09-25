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
 * refuted, because `exp 8 = (exp 2)^4 >= 81`. The same point refutes `EXP_SMALL_ABOVE` without its
 * radius, and `EXP_LN` and `LN_MUL` are refuted with a positivity dropped, at `0` and at `(0, 2)`.
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
    // That the three constants it is about are reachable from the chain's end, which is what this
    // line is for. It said `chain.widest shouldBe chain.continuity` until 2026-09-25, when
    // `Resolving` became a link above it; which link is last is `ChainSpec`'s to pin.
    chain.widest.theory.constants.keySet should contain allElementsOf chain.continuity.theory.constants.keySet
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

  /** `|- exp (2 * a) = exp a * exp a`, spelt through the addition theorem at `(a, a)`. */
  private def doubled(a: String, b: String): Kernel.Thm = {
    val addition = force(rules.specAll(force(chain.transcendental.fact(Transcendental.Addition)), List(real(a), real(a))))
    val sum = force(LogicError.lift(Term.eq(real(s"($a) + ($a)"), real(b))).flatMap(chain.ring.prove))
    val exp = force(logarithm.term("exp", Type.fun(reals, reals)))
    force(Conv.apTerm(exp, sum).flatMap(Conv.sym).flatMap(Conv.trans(_, addition)))
  }

  /** `|- 81 <= exp 8`: `exp 2 >= 3` from the line, then squared twice through the addition theorem. */
  private lazy val eightAbove: Kernel.Thm = {
    val line = mp(force(rules.spec(real("2:real"), fact(Logarithm.AboveLine))), lemma("(0:real) < 2"))
    val four = mp(force(rules.specAll(lemma("!p:real q:real. p = q * q ==> 1 + 2 <= q ==> 9 <= p"),
      List(real("exp 4"), real("exp 2")))), doubled("2", "4"), line)
    mp(force(rules.specAll(lemma("!p:real q:real. p = q * q ==> 9 <= q ==> 81 <= p"),
      List(real("exp 8"), real("exp 4")))), doubled("4", "8"), four)
  }

  it should "need the estimate's radius, which is shown by refuting the estimate without it" in {
    // `exp 8 >= 81`, and `abs (exp 8 - 1) <= 16` is false. The unconditional statement is refuted
    // at that one point.
    val unconditional = proposition("!h:real. abs (exp h - 1) <= 2 * abs h")
    val assumed = force(LogicError.lift(Kernel.assume(unconditional)))
    val atEight = force(rules.spec(real("8:real"), assumed))
    val above = force(chain.limit.magnitude.fact(Magnitude.AbsAbove).flatMap(rules.spec(real("exp 8 - 1"), _)))
    val eightIs = mp(force(chain.limit.magnitude.fact(Magnitude.OfNonNegative).flatMap(rules.spec(real("8:real"), _))),
      lemma("(0:real) <= 8"))
    val absurd = mp(force(rules.specAll(
      lemma("!e:real d:real m:real. 81 <= e ==> e - 1 <= d ==> m = 8 ==> d <= 2 * m ==> F"),
      List(real("exp 8"), real("abs (exp 8 - 1)"), real("abs 8")))), eightAbove, above, eightIs, atEight)
    val refused = force(rules.notIntro(unconditional, absurd))

    refused.hypotheses shouldBe empty
  }

  // The three below were written by the verification of card 7f6ac0d3, which found that the file
  // asserted one hypothesis carrying weight and the published facts carry four. Each drops one
  // hypothesis from a published statement and derives the negation of what is left, so a later
  // edit that loosened a statement to the dropped form would be publishing a falsity rather than a
  // generalisation. `EXP_ABOVE_LINE`'s `0 < x` is absent from the list on purpose: `1 + x <= exp x`
  // holds at every real, so that hypothesis narrows a true statement and no derivation refutes it.

  /**
   * The negation of `dropped`, from an absurdity that rests on it and on nothing else: a refutation
   * whose absurdity did not read the dropped statement would be a derivation of `F`, and one resting
   * on something more would refute that instead.
   */
  private def refute(dropped: Term, absurd: Kernel.Thm): Unit = {
    absurd.hypotheses shouldBe List(dropped)
    val refused = force(rules.notIntro(dropped, absurd))
    refused.hypotheses shouldBe empty
    logarithm.show(refused.conclusion) shouldBe s"~(${logarithm.show(dropped)})"
  }

  it should "need the upper bound's radius, refuted at the same point as the estimate's" in {
    val unbounded = proposition("!x:real. 0 < x ==> exp x <= 1 + 2 * x")
    val atEight = mp(force(rules.spec(real("8:real"), force(LogicError.lift(Kernel.assume(unbounded))))),
      lemma("(0:real) < 8"))
    val absurd = mp(force(rules.specAll(lemma("!e:real. 81 <= e ==> e <= 1 + 2 * 8 ==> F"), List(real("exp 8")))),
      eightAbove, atEight)
    refute(unbounded, absurd)
  }

  it should "need the positivity in EXP_LN, since the exponential is never zero" in {
    // At `0` the dropped form says `exp (ln 0) = 0`, and `EXP_POSITIVE` at `ln 0` says it is above.
    val everywhere = proposition("!x:real. exp (ln x) = x")
    val atZero = force(rules.spec(real("0:real"), force(LogicError.lift(Kernel.assume(everywhere)))))
    val positive = force(rules.spec(real("ln 0"), fact(Logarithm.Positive)))
    val absurd = mp(force(rules.specAll(lemma("!p:real. p = 0 ==> 0 < p ==> F"), List(real("exp (ln 0)")))),
      atZero, positive)
    refute(everywhere, absurd)
  }

  it should "need the positivity of the first factor in LN_MUL, or ln 2 would be zero" in {
    // At `(0, 2)` the dropped form says `ln (0 * 2) = ln 0 + ln 2`, and `0 * 2` is `0`, so `ln 2 = 0`;
    // then `2 = exp (ln 2) = exp 0 = 1`. What is refuted is the statement with only `0 < y` kept,
    // which is the sharper of the two: the other factor alone is not enough.
    val oneSided = proposition("!x:real y:real. 0 < y ==> ln (x * y) = ln x + ln y")
    val two = lemma("(0:real) < 2")
    val instance = mp(force(rules.specAll(force(LogicError.lift(Kernel.assume(oneSided))),
      List(real("0:real"), real("2:real")))), two)
    val ln = force(logarithm.term("ln", Type.fun(reals, reals)))
    val exp = force(logarithm.term("exp", Type.fun(reals, reals)))
    val zeroTimes = force(LogicError.lift(Term.eq(real("0 * 2"), real("0:real"))).flatMap(chain.ring.prove))
    val lnZeroTimes = force(Conv.apTerm(ln, zeroTimes))
    val lnTwoIsZero = mp(force(rules.specAll(lemma("!a:real b:real c:real. a = b ==> a = b + c ==> c = 0"),
      List(real("ln (0 * 2)"), real("ln 0"), real("ln 2")))), lnZeroTimes, instance)
    val sameExp = force(Conv.apTerm(exp, lnTwoIsZero))
    val expLnTwo = mp(force(rules.spec(real("2:real"), fact(Logarithm.ExpOfLn))), two)
    val expZero = force(chain.transcendental.fact(Transcendental.ExponentialAtZero))
    val absurd = mp(force(rules.specAll(lemma("!p:real q:real. p = q ==> p = 2 ==> q = 1 ==> F"),
      List(real("exp (ln 2)"), real("exp 0")))), sameExp, expLnTwo, expZero)
    refute(oneSided, absurd)
  }
}
