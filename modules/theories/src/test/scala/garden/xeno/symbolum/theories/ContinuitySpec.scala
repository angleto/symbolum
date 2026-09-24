package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Continuity and the intermediate value theorem: what they cost, what they rest on, and that what
 * they say is not vacuous.
 *
 * **What it cost.** One defined constant and no axiom, asserted as a difference against the theory
 * below it rather than as a count.
 *
 * **What it rests on.** The intermediate value theorem is false over the rationals, so a derivation
 * of it that did not reach `COMPLETENESS` would be a derivation of something else; and past the
 * axioms of the reals it reaches exactly one, the choice `abs` is defined by. That one is the
 * definition's and not the argument's: every fact `Magnitude` publishes about `abs` spends it,
 * measured on 2026-09-24, and `converges` pays it for the same reason. The two facts about
 * particular functions reach no completeness at all.
 *
 * **What keeps it from being a theorem about nothing, and there are two ways it could be.** A
 * definition nothing satisfies would make every statement with `continuous f x` in a hypothesis
 * true and empty, so the theorem is detached at the identity on `[0, 1]` with nothing assumed. And a
 * definition everything satisfies would make the hypothesis decoration, so a step function is shown
 * **not** continuous at zero, and the same step function refutes the theorem with its continuity
 * hypothesis dropped: it is `0` at `-1` and `1` at `1` and takes no value in between.
 */
class ContinuitySpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val continuity = chain.continuity
  private def logic: Logic = continuity.logic
  private def rules: Rules = logic.rules
  private val reals: Type = TyApp(Real.TypeName, Nil)

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def fact(name: String): Kernel.Thm = force(continuity.fact(name))
  private def real(text: String): Term = force(continuity.term(text, reals))
  private def proposition(text: String): Term = force(continuity.proposition(text))
  private lazy val linarith: Linarith = force(Linarith.construct(chain.order))
  private def lemma(text: String): Kernel.Thm = force(linarith.prove(text))
  private def opened(theorem: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(theorem.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, theorem))))

  private val realAxioms: Set[Term] = chain.reals.axioms.values.map(_.conclusion).toSet

  /* --------------------------------------------------------------- what it cost */

  "Continuity" should "add one constant and no axiom to the theory below it" in {
    val below = chain.root.theory
    continuity.theory.axioms shouldBe below.axioms
    (continuity.theory.constants.keySet -- below.constants.keySet) shouldBe Set(Continuity.Continuous)
    continuity.theory.typeOperators.keySet shouldBe below.typeOperators.keySet
  }

  it should "state every fact as it is written, with nothing assumed" in {
    Continuity.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe proposition(text)
        fact(name).hypotheses shouldBe empty
      }
    }
    continuity.facts.keySet shouldBe Continuity.Statements.map(_._1).toSet
  }

  /* ---------------------------------------------------------- what it rests on */

  it should "prove the intermediate value theorem from the reals alone, completeness among them" in {
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion
    val spent = Derivation.axiomsOf(fact(Continuity.IntermediateValue))

    spent should contain(completeness)
    // An equality and not a ceiling: the choice arrives through `abs` in the definition, and a
    // derivation that began to spend infinity or eta as well would fail here rather than pass.
    // Written first as `empty`, from a probe that compared against the reals' THEORY, whose axioms
    // include the logic's; this spec, comparing against the sixteen, is what said otherwise.
    val select = force(chain.classical.axiom("SELECT")).conclusion
    withClue(s"it reaches: ${(spent -- realAxioms).map(continuity.show).mkString("; ")}\n") {
      (spent -- realAxioms) shouldBe Set(select)
    }

    // The facts about a particular function spend no supremum: they pick a radius by hand.
    Derivation.axiomsOf(fact(Continuity.Constant)) should not contain completeness
    Derivation.axiomsOf(fact(Continuity.Identity)) shouldBe empty
  }

  /* ------------------------------------------------------------- what it says */

  it should "detach at the identity on [0, 1], so that its hypothesis is one something satisfies" in {
    val identity = force(continuity.term("\\y:real. y", Type.fun(reals, reals)))
    val instance = opened(force(rules.specAll(
      fact(Continuity.IntermediateValue),
      List(identity, real("0:real"), real("1:real"), real("(1:real) / 2")))))

    val everywhere = {
      val x = Term.variable("x", reals)
      val inside = proposition("(0:real) <= x /\\ x <= 1")
      val continuous = force(rules.spec(x, fact(Continuity.Identity)))
      force(rules.disch(inside, continuous).flatMap(rules.gen(x, _)))
    }
    val detached = Vector(
      lemma("(0:real) <= 1"),
      everywhere,
      lemma("(0:real) <= (1:real) / 2"),
      lemma("(1:real) / 2 <= 1")
    ).foldLeft(instance)((theorem, premise) => force(rules.mp(theorem, premise)))

    detached.hypotheses shouldBe empty
    continuity.show(detached.conclusion) shouldBe "?x:real. 0 <= x /\\ x <= 1 /\\ x = 1 / 2"
  }

  /** The step `COND (0 < y) 1 0`, which both negative guards below spend. */
  private val step: Term =
    force(continuity.term("\\y:real. COND (0 < y) (1:real) 0", Type.fun(reals, reals)))

  /** `|- COND (0 < at) 1 0 = 1` or `= 0`, from the evidence for the guard or against it. */
  private def stepValue(at: String, evidence: Kernel.Thm, positive: Boolean): Kernel.Thm = {
    val name = if (positive) Classical.CondTrue else Classical.CondFalse
    val conditional =
      Kernel.instType(Map(Classical.TypeVariable -> reals), force(chain.classical.fact(name)))
    val guard = proposition(s"(0:real) < $at")
    force(rules.specAll(conditional, List(guard, real("1:real"), real("0:real"))).flatMap(rules.mp(_, evidence)))
  }

  it should "refuse a step, so that the definition is not satisfied by everything" in {
    // `COND (0 < y) 1 0` jumps at zero. At tolerance one half, every radius `d` holds `d / 2`, where
    // the step is one while it is zero at zero, and one is not within a half of zero.
    val continuous = force(continuity.term(Continuity.Continuous))
    val claim = force(LogicError.lift(Term.app(continuous, step).flatMap(Term.app(_, real("0:real")))))
    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val unfolded = force(Conv.unfold(force(continuity.definition(Continuity.Continuous)), List(step, real("0:real"))))
    val body = opened(force(LogicError.lift(Kernel.eqMp(unfolded, assumed))))
    val near = force(rules.spec(real("(1:real) / 2"), body).flatMap(rules.mp(_, lemma("(0:real) < (1:real) / 2"))))

    val d = Term.variable("d", reals)
    val radius = force(LogicError.lift(Kernel.assume(proposition(
      "0 < d:real /\\ (!y:real. abs (y - 0) < d ==> " +
        "abs (COND (0 < y) (1:real) 0 - COND ((0:real) < 0) 1 0) < (1:real) / 2)"))))
    val dPositive = force(rules.conjElim1(radius))
    val inside = force(rules.conjElim2(radius))

    val magnitude = force(chain.limit.magnitude.fact(Magnitude.OfNonNegative)
      .flatMap(rules.spec(real("d / 2 - 0"), _))
      .flatMap(rules.mp(_, force(rules.spec(d, lemma("!d:real. 0 < d ==> 0 <= d / 2 - 0")).flatMap(rules.mp(_, dPositive))))))
    val close = force(rules.specAll(lemma("!m:real d:real. m = d / 2 - 0 ==> 0 < d ==> m < d"), List(real("abs (d / 2 - 0)"), d))
      .flatMap(rules.mp(_, magnitude)).flatMap(rules.mp(_, dPositive)))
    val jump = force(rules.spec(real("d / 2"), inside).flatMap(rules.mp(_, close)))

    val halfPositive = force(rules.spec(d, lemma("!d:real. 0 < d ==> 0 < d / 2")).flatMap(rules.mp(_, dPositive)))
    val afterJump = stepValue("d / 2", halfPositive, positive = true)
    val atJump = stepValue("0", lemma("~((0:real) < 0)"), positive = false)
    val difference = "COND (0 < d / 2) (1:real) 0 - COND ((0:real) < 0) 1 0"
    val above = force(chain.limit.magnitude.fact(Magnitude.AbsAbove).flatMap(rules.spec(real(difference), _)))
    val absurd = force(rules
      .specAll(
        lemma("!p:real q:real m:real. p = 1 ==> q = 0 ==> p - q <= m ==> m < 1 / 2 ==> F"),
        List(real("COND (0 < d / 2) (1:real) 0"), real("COND ((0:real) < 0) (1:real) 0"), real(s"abs ($difference)")))
      .flatMap(rules.mp(_, afterJump)).flatMap(rules.mp(_, atJump))
      .flatMap(rules.mp(_, above)).flatMap(rules.mp(_, jump)))

    val eliminated = force(rules.existsElim(near, d, absurd))
    val refused = force(rules.notIntro(claim, eliminated))
    refused.hypotheses shouldBe empty
    continuity.show(refused.conclusion) shouldBe "~(continuous (\\x:real. COND (0 < x) 1 0) 0)"
  }

  it should "need its continuity hypothesis, which is shown by refuting the theorem without it" in {
    // Without continuity the statement is false at the same step on `[-1, 1]`: it is `0` at `-1`
    // and `1` at `1`, and it takes the value one half nowhere, since at every point it is one of
    // the two. So the unconditional statement is refuted by the very function the definition
    // refused above, which is the pairing that says the hypothesis is doing the work.
    val unconditional = proposition(
      "!f:real -> real. !a:real. !b:real. !y:real. a <= b ==> f a <= y ==> y <= f b ==> " +
        "?x:real. a <= x /\\ x <= b /\\ f x = y")
    val assumed = force(LogicError.lift(Kernel.assume(unconditional)))
    val instance = opened(force(rules.specAll(assumed, List(step, real("0 - 1"), real("1:real"), real("(1:real) / 2")))))
    val atStart = stepValue("0 - 1", lemma("~((0:real) < 0 - 1)"), positive = false)
    val atEnd = stepValue("1", lemma("(0:real) < 1"), positive = true)
    val startBelow = force(rules.specAll(lemma("!p:real. p = 0 ==> p <= 1 / 2"), List(real("COND (0 < 0 - 1) (1:real) 0"))).flatMap(rules.mp(_, atStart)))
    val endAbove = force(rules.specAll(lemma("!p:real. p = 1 ==> 1 / 2 <= p"), List(real("COND ((0:real) < 1) (1:real) 0"))).flatMap(rules.mp(_, atEnd)))
    val somewhere = Vector(lemma("(0:real) - 1 <= 1"), startBelow, endAbove)
      .foldLeft(instance)((theorem, premise) => force(rules.mp(theorem, premise)))

    val x = Term.variable("x", reals)
    val witness = force(LogicError.lift(Kernel.assume(proposition(
      "0 - 1 <= x:real /\\ x <= 1 /\\ COND (0 < x) (1:real) 0 = 1 / 2"))))
    val hit = force(rules.conjElim2(witness).flatMap(rules.conjElim2))
    val value = real("COND (0 < x:real) (1:real) 0")
    val positiveCase = {
      val guard = force(LogicError.lift(Kernel.assume(proposition("(0:real) < x"))))
      val one = stepValue("x", guard, positive = true)
      force(rules.specAll(lemma("!p:real. p = 1 ==> p = 1 / 2 ==> F"), List(value)).flatMap(rules.mp(_, one)).flatMap(rules.mp(_, hit)))
    }
    val otherCase = {
      val guard = force(LogicError.lift(Kernel.assume(proposition("~((0:real) < x)"))))
      val zero = stepValue("x", guard, positive = false)
      force(rules.specAll(lemma("!p:real. p = 0 ==> p = 1 / 2 ==> F"), List(value)).flatMap(rules.mp(_, zero)).flatMap(rules.mp(_, hit)))
    }
    val middle = force(chain.classical.fact(Classical.ExcludedMiddle).flatMap(rules.spec(proposition("(0:real) < x"), _)))
    val absurd = force(rules.disjElim(middle, positiveCase, otherCase))
    val eliminated = force(rules.existsElim(somewhere, x, absurd))
    val refused = force(rules.notIntro(unconditional, eliminated))

    refused.hypotheses shouldBe empty
  }

  it should "be the chain's end, so that every development above the reals can name it" in {
    chain.widest shouldBe continuity
    chain.widest.theory.constants.keySet should contain(Continuity.Continuous)
  }
}
