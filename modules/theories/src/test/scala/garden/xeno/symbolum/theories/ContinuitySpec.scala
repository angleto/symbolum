package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Continuity, the intermediate value theorem and the extreme value theorem: what they cost, what
 * they rest on, and that what they say is not vacuous.
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

  "Continuity" should "add its constant and no axiom to the theory below it" in {
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

  /* ------------------------------------------------------- the extreme value theorem */

  it should "prove the extreme value theorem from the reals alone, and through the gluing" in {
    // The same equality as the intermediate value theorem's, for each of the four that take a
    // supremum: all sixteen axioms of the reals, `COMPLETENESS` among them, and the choice that
    // `abs`, `min`, `max` and the excluded middle are paid for with. Measured on 2026-09-25 before it
    // was written here, at seventeen for each.
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion
    val select = force(chain.classical.axiom("SELECT")).conclusion
    for (name <- List(Continuity.IntervalGluing, Continuity.Bounded, Continuity.AttainsMaximum, Continuity.AttainsMinimum)) {
      val spent = Derivation.axiomsOf(fact(name))
      withClue(s"$name reaches: ${(spent -- realAxioms).map(continuity.show).mkString("; ")}\n") {
        spent should contain(completeness)
        (spent -- realAxioms) shouldBe Set(select)
      }
    }
    // The negation picks its radius by hand and takes no supremum.
    Derivation.axiomsOf(fact(Continuity.Negation)) should not contain completeness

    // The route, which is the design and not a detail: both halves of the theorem are the gluing,
    // and the minimum is the maximum of the negation. A derivation that took the textbook's second
    // supremum argument instead would state the same theorem and fail here.
    def published(names: String*): Set[Term] = names.map(fact(_).conclusion).toSet
    Derivation.restingOn(fact(Continuity.AttainsMaximum), published(Continuity.IntervalGluing, Continuity.Bounded)) shouldBe
      published(Continuity.IntervalGluing, Continuity.Bounded)
    Derivation.restingOn(fact(Continuity.AttainsMinimum), published(Continuity.AttainsMaximum, Continuity.Negation)) shouldBe
      published(Continuity.AttainsMaximum, Continuity.Negation)
  }

  /** `!x. 0 <= x /\ x <= 1 ==> continuous (\y. y) x`, the hypothesis both detachments discharge. */
  private lazy val identityOnUnit: Kernel.Thm = {
    val x = Term.variable("x", reals)
    val inside = proposition("(0:real) <= x /\\ x <= 1")
    val continuous = force(rules.spec(x, fact(Continuity.Identity)))
    force(rules.disch(inside, continuous).flatMap(rules.gen(x, _)))
  }

  it should "detach the maximum and the minimum at the identity on [0, 1], with nothing assumed" in {
    // The two hypotheses are ones something satisfies, and what comes out is the statement about
    // that function rather than a consequence of an unsatisfiable premise.
    val identity = force(continuity.term("\\y:real. y", Type.fun(reals, reals)))
    def detached(name: String): Kernel.Thm = {
      val instance = opened(force(rules.specAll(fact(name), List(identity, real("0:real"), real("1:real")))))
      Vector(lemma("(0:real) <= 1"), identityOnUnit).foldLeft(instance)((theorem, premise) => force(rules.mp(theorem, premise)))
    }
    val highest = detached(Continuity.AttainsMaximum)
    val lowest = detached(Continuity.AttainsMinimum)
    highest.hypotheses shouldBe empty
    lowest.hypotheses shouldBe empty
    continuity.show(highest.conclusion) shouldBe "?x:real. 0 <= x /\\ x <= 1 /\\ (!y:real. 0 <= y /\\ y <= 1 ==> y <= x)"
    continuity.show(lowest.conclusion) shouldBe "?x:real. 0 <= x /\\ x <= 1 /\\ (!y:real. 0 <= y /\\ y <= 1 ==> x <= y)"
  }

  /** `|- COND (at < 1) at 0 = at` or `= 0`, from the evidence for the guard or against it. */
  private def sawValue(at: String, evidence: Kernel.Thm, below: Boolean): Kernel.Thm = {
    val name = if (below) Classical.CondTrue else Classical.CondFalse
    val conditional =
      Kernel.instType(Map(Classical.TypeVariable -> reals), force(chain.classical.fact(name)))
    val guard = proposition(s"$at < (1:real)")
    force(rules.specAll(conditional, List(guard, real(at), real("0:real"))).flatMap(rules.mp(_, evidence)))
  }

  it should "need its continuity hypothesis, which is shown by refuting the maximum without it" in {
    // `COND (y < 1) y 0` on `[0, 1]` climbs to one and drops to zero at one, so the least upper bound
    // of its values is one and no point has it. Without continuity the maximum statement would hand
    // back an `m`; below one the midpoint of `m` and one is higher, and at one the value is zero,
    // which one half beats.
    val saw = force(continuity.term("\\y:real. COND (y < 1) y (0:real)", Type.fun(reals, reals)))
    val unconditional = proposition(
      "!f:real -> real. !a:real. !b:real. a <= b ==> " +
        "?m:real. a <= m /\\ m <= b /\\ (!x:real. a <= x /\\ x <= b ==> f x <= f m)")
    val assumed = force(LogicError.lift(Kernel.assume(unconditional)))
    val instance = opened(force(rules.specAll(assumed, List(saw, real("0:real"), real("1:real")))))
    val somewhere = force(rules.mp(instance, lemma("(0:real) <= 1")))

    val m = Term.variable("m", reals)
    val witness = force(LogicError.lift(Kernel.assume(proposition(
      "0 <= m:real /\\ m <= 1 /\\ (!x:real. 0 <= x /\\ x <= 1 ==> COND (x < 1) x (0:real) <= COND (m < 1) m 0)"))))
    val mAbove = force(rules.conjElim1(witness))
    val highest = force(rules.conjElim2(witness).flatMap(rules.conjElim2))
    def higherThanAt(point: String, inside: Kernel.Thm): Kernel.Thm =
      force(rules.spec(real(point), highest).flatMap(rules.mp(_, inside)))

    val belowOne = {
      val guard = force(LogicError.lift(Kernel.assume(proposition("m:real < 1"))))
      val atM = sawValue("m:real", guard, below = true)
      val middle = "(m + 1) / 2"
      val inside = force(rules.conjIntro(
        force(rules.spec(m, lemma("!m:real. 0 <= m ==> 0 <= (m + 1) / 2")).flatMap(rules.mp(_, mAbove))),
        force(rules.spec(m, lemma("!m:real. m < 1 ==> (m + 1) / 2 <= 1")).flatMap(rules.mp(_, guard)))))
      val atMiddle = sawValue(middle, force(rules.spec(m, lemma("!m:real. m < 1 ==> (m + 1) / 2 < 1")).flatMap(rules.mp(_, guard))), below = true)
      force(rules
        .specAll(lemma("!p:real q:real m:real. p = (m + 1) / 2 ==> q = m ==> p <= q ==> m < 1 ==> F"),
          List(real(s"COND ($middle < 1) ($middle) (0:real)"), real("COND (m < 1) m (0:real)"), m))
        .flatMap(rules.mp(_, atMiddle)).flatMap(rules.mp(_, atM))
        .flatMap(rules.mp(_, higherThanAt(middle, inside))).flatMap(rules.mp(_, guard)))
    }
    val atOne = {
      val guard = force(LogicError.lift(Kernel.assume(proposition("~(m:real < 1)"))))
      val atM = sawValue("m:real", guard, below = false)
      val atHalf = sawValue("(1:real) / 2", lemma("(1:real) / 2 < 1"), below = true)
      val inside = lemma("(0:real) <= (1:real) / 2 /\\ (1:real) / 2 <= 1")
      force(rules
        .specAll(lemma("!p:real q:real. p = 1 / 2 ==> q = 0 ==> p <= q ==> F"),
          List(real("COND ((1:real) / 2 < 1) ((1:real) / 2) (0:real)"), real("COND (m < 1) m (0:real)")))
        .flatMap(rules.mp(_, atHalf)).flatMap(rules.mp(_, atM))
        .flatMap(rules.mp(_, higherThanAt("(1:real) / 2", inside))))
    }
    val middle = force(chain.classical.fact(Classical.ExcludedMiddle).flatMap(rules.spec(proposition("m:real < 1"), _)))
    val absurd = force(rules.disjElim(middle, belowOne, atOne))
    val refused = force(rules.existsElim(somewhere, m, absurd).flatMap(rules.notIntro(unconditional, _)))
    refused.hypotheses shouldBe empty
  }

  it should "need the gluing hypothesis of the gluing, which is shown by refuting it without it" in {
    // "Shorter than one" holds on every interval shorter than one, so it satisfies the local
    // hypothesis at radius one everywhere, and it does not glue: `[0, 2]` is not shorter than one.
    // So the statement with the gluing hypothesis dropped is false, and that hypothesis is where the
    // content is.
    val short = force(continuity.term("\\u:real. \\v:real. v - u < 1", Type.fun(reals, Type.fun(reals, Type.Bool))))
    val unglued = proposition(
      "!P:real -> real -> bool. !a:real. !b:real. a <= b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> ?d:real. 0 < d /\\ " +
        "(!u:real. !v:real. a <= u /\\ u <= x /\\ x <= v /\\ v <= b /\\ v - u < d ==> P u v)) ==> P a b")
    val assumed = force(LogicError.lift(Kernel.assume(unglued)))
    val instance = opened(force(rules.specAll(assumed, List(short, real("0:real"), real("2:real")))))

    val x = Term.variable("x", reals)
    val u = Term.variable("u", reals)
    val v = Term.variable("v", reals)
    val smallText = "(0:real) <= u /\\ u <= x /\\ x <= v /\\ v <= 2 /\\ v - u < 1"
    val small = proposition(smallText)
    val shortEnough = force(rules.conjElim2(force(LogicError.lift(Kernel.assume(small))))
      .flatMap(rules.conjElim2).flatMap(rules.conjElim2).flatMap(rules.conjElim2))
    val everyInterval = force(rules.disch(small, shortEnough).flatMap(rules.genAll(_, List(u, v))))
    val radius = force(rules.conjIntro(lemma("(0:real) < 1"), everyInterval))
    val existential = proposition(
      "?d:real. 0 < d /\\ (!u:real. !v:real. (0:real) <= u /\\ u <= x /\\ x <= v /\\ v <= 2 /\\ v - u < d ==> v - u < 1)")
    val predicate = force(logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential)))
    val witnessed = force(rules.existsIntro(predicate, real("1:real"), radius))
    val point = proposition("(0:real) <= x /\\ x <= 2")
    val local = force(rules.disch(point, witnessed).flatMap(rules.gen(x, _)))

    val concluded = force(rules.mp(instance, lemma("(0:real) <= 2")).flatMap(rules.mp(_, local)))
    val absurd = force(rules.notElim(lemma("~((2:real) - 0 < 1)"), concluded))
    val refused = force(rules.notIntro(unglued, absurd))
    refused.hypotheses shouldBe empty
  }

  it should "be reachable from the chain's end, so that every development above the reals can name it" in {
    // It WAS the end until 2026-09-25, and this asserted the identity; `Resolving` is above it since.
    // What the test is for is the visibility, and which link is last is `ChainSpec`'s to pin.
    chain.widest.theory.constants.keySet should contain(Continuity.Continuous)
    chain.widest.theory.constants(Continuity.Continuous) shouldBe continuity.theory.constants(Continuity.Continuous)
  }
}
