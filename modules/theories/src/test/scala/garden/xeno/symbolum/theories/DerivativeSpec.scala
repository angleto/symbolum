package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The derivative, the interior extremum lemma, Rolle's theorem and the mean value theorem: what
 * they cost, what they rest on, and that what they say is not vacuous.
 *
 * **What it cost.** One defined constant and no axiom, asserted as a difference against the theory
 * below it rather than as a count.
 *
 * **What it rests on.** Rolle's theorem spends exactly what the extreme value theorem spends, the
 * sixteen axioms of the reals and the choice `abs` is defined by, and it spends it through that
 * theorem and the interior lemma: a derivation that reached the maximum some other way would state
 * the same theorem and fail the route assertion. The interior lemma and the negation spend no
 * `COMPLETENESS`, since a derivative at one point is a statement about one point.
 *
 * **What keeps it from being a theorem about nothing, and there are two ways it could be.** A
 * definition nothing satisfies would make Rolle's theorem true and empty, so it is detached at a
 * constant function on `[0, 1]` with nothing assumed. And a definition everything satisfies would
 * make the conclusion decoration, so the identity is shown to have derivative zero **nowhere**,
 * and with that the theorem with `f a = f b` dropped is refuted at the identity on `[0, 1]`, where
 * every other hypothesis holds.
 */
class DerivativeSpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val derivative = chain.derivative
  private def logic: Logic = derivative.logic
  private def rules: Rules = logic.rules
  private val reals: Type = TyApp(Real.TypeName, Nil)
  private val functions: Type = Type.fun(reals, reals)

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def fact(name: String): Kernel.Thm = force(derivative.fact(name))
  private def real(text: String): Term = force(derivative.term(text, reals))
  private def proposition(text: String): Term = force(derivative.proposition(text))
  private lazy val linarith: Linarith = force(Linarith.construct(chain.order))
  private def lemma(text: String): Kernel.Thm = force(linarith.prove(text))
  private def opened(theorem: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(theorem.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, theorem))))

  private val realAxioms: Set[Term] = chain.reals.axioms.values.map(_.conclusion).toSet
  private val completeness: Term = force(chain.reals.axiom("COMPLETENESS")).conclusion
  private val select: Term = force(chain.classical.axiom("SELECT")).conclusion

  /* --------------------------------------------------------------- what it cost */

  "The derivative" should "add its constant and no axiom to the theory below it" in {
    // The theory it extends is the chain's end when it is built, which is `Resolving`'s, and not
    // `Continuity`'s, whose constants it reads.
    val below = chain.resolving.theory
    derivative.theory.axioms shouldBe below.axioms
    (derivative.theory.constants.keySet -- below.constants.keySet) shouldBe Set(Derivative.DerivativeName)
    derivative.theory.typeOperators.keySet shouldBe below.typeOperators.keySet
  }

  it should "state every fact as it is written, with nothing assumed" in {
    Derivative.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe proposition(text)
        fact(name).hypotheses shouldBe empty
      }
    }
    derivative.facts.keySet shouldBe Derivative.Statements.map(_._1).toSet
  }

  /* ---------------------------------------------------------- what it rests on */

  it should "prove Rolle's theorem at exactly the price of the extreme value theorem" in {
    // An equality and not a ceiling, measured on 2026-09-25 before it was written here: seventeen,
    // the sixteen and the choice. A Rolle that reached completeness by a road of its own, or began
    // to spend eta or infinity, would fail here rather than pass.
    val spent = Derivation.axiomsOf(fact(Derivative.Rolle))
    spent shouldBe Derivation.axiomsOf(force(chain.continuity.fact(Continuity.AttainsMaximum)))
    spent should contain(completeness)
    (spent -- realAxioms) shouldBe Set(select)

    // The mean value theorem is Rolle at a combination, and costs what Rolle costs.
    Derivation.axiomsOf(fact(Derivative.MeanValue)) shouldBe spent

    // Everything else is about one point, and takes no supremum; past the reals they spend the
    // choice `abs` is paid for with and nothing else.
    for (name <- Derivative.Statements.map(_._1)
        if name != Derivative.Rolle && name != Derivative.MeanValue && name != Derivative.Exponential) {
      val other = Derivation.axiomsOf(fact(name))
      withClue(s"$name reaches: ${(other -- realAxioms).map(derivative.show).mkString("; ")}\n") {
        other should not contain completeness
        (other -- realAxioms) shouldBe Set(select)
      }
    }
  }

  it should "price the exponential's slope at exactly what its second-order estimate costs" in {
    // `DERIVATIVE_EXP` is one point too, and the one fact here that is not only about the reals: the
    // estimate under it is a statement about a series, which spends the supremum through
    // `MONOTONE_CONVERGES` and the naturals' axioms through the factorial. What the slope adds on
    // top of the estimate is the addition theorem and the definition, which cost nothing more.
    val nearLine = force(chain.logarithm.fact(Logarithm.NearLine))
    val spent = Derivation.axiomsOf(fact(Derivative.Exponential))
    spent shouldBe Derivation.axiomsOf(nearLine)
    spent should contain(completeness)
    val route = Set(nearLine.conclusion, force(chain.transcendental.fact(Transcendental.Addition)).conclusion)
    Derivation.restingOn(fact(Derivative.Exponential), route) shouldBe route
  }

  it should "reach Rolle's theorem through the extreme value theorem and the interior lemma" in {
    // The route is the design: the extremes come from the extreme value theorem, the interior ones
    // are settled by Fermat's lemma, and the minimum's lemma is the maximum's at the negation.
    def published(names: String*): Set[Term] = names.map(fact(_).conclusion).toSet
    val extremes = Set(
      force(chain.continuity.fact(Continuity.AttainsMaximum)).conclusion,
      force(chain.continuity.fact(Continuity.AttainsMinimum)).conclusion
    )
    val wanted = extremes ++ published(Derivative.InteriorMaximum, Derivative.InteriorMinimum, Derivative.Negation)
    Derivation.restingOn(fact(Derivative.Rolle), wanted) shouldBe wanted
    Derivation.restingOn(fact(Derivative.InteriorMinimum), published(Derivative.InteriorMaximum, Derivative.Negation)) shouldBe
      published(Derivative.InteriorMaximum, Derivative.Negation)

    // And the mean value theorem is Rolle at a combination: its continuity from `Continuity`'s
    // linearity, its derivative from this file's, and the zero carried back by uniqueness.
    val combination = published(Derivative.Rolle, Derivative.Linear, Derivative.Unique) +
      force(chain.continuity.fact(Continuity.Linear)).conclusion
    Derivation.restingOn(fact(Derivative.MeanValue), combination) shouldBe combination

    // And the product rule keeps `g (x + h)` in hand through the continuity of a differentiable
    // function, which is why that fact is published beside it.
    val bridge = published(Derivative.Continuous)
    Derivation.restingOn(fact(Derivative.ProductRule), bridge) shouldBe bridge
    // And so does the chain rule, which needs `g (x + h)` inside `f`'s radius.
    Derivation.restingOn(fact(Derivative.ChainRule), bridge) shouldBe bridge
  }

  /* ------------------------------------------------------------- what it says */

  it should "detach Rolle's theorem at a constant function on [0, 1], with nothing assumed" in {
    val one = force(derivative.term("\\y:real. (1:real)", functions))
    val instance = opened(force(rules.specAll(fact(Derivative.Rolle), List(one, real("0:real"), real("1:real")))))

    val x = Term.variable("x", reals)
    val continuousEverywhere = {
      val inside = proposition("(0:real) <= x /\\ x <= 1")
      val continuous = force(chain.continuity.fact(Continuity.Constant).flatMap(rules.specAll(_, List(real("1:real"), x))))
      force(rules.disch(inside, continuous).flatMap(rules.gen(x, _)))
    }
    val differentiableInside = {
      val inside = proposition("(0:real) < x /\\ x < 1")
      val slope = force(rules.specAll(fact(Derivative.Constant), List(real("1:real"), x)))
      val exists = force(derivative.proposition("?m:real. derivative (\\y:real. (1:real)) x m")
        .flatMap(statement => logic.destExistsPredicate(statement).toRight(NotOfForm("an existential", statement)))
        .flatMap(rules.existsIntro(_, real("0:real"), slope)))
      force(rules.disch(inside, exists).flatMap(rules.gen(x, _)))
    }
    val level = Kernel.refl(real("1:real"))
    val detached = Vector(lemma("(0:real) < 1"), continuousEverywhere, differentiableInside, level)
      .foldLeft(instance)((theorem, premise) => force(rules.mp(theorem, premise)))

    detached.hypotheses shouldBe empty
    derivative.show(detached.conclusion) shouldBe "?x:real. 0 < x /\\ x < 1 /\\ derivative (\\y:real. 1) x 0"
  }

  /** `|- ~(derivative (\y. y) x 0)`: the identity's slope is one, and one is not within a half of zero. */
  private lazy val identityNotFlat: Kernel.Thm = {
    val identity = force(derivative.term("\\y:real. y", functions))
    val x = Term.variable("x", reals)
    val d = Term.variable("d", reals)
    val constant = force(derivative.term(Derivative.DerivativeName))
    val claim = force(LogicError.lift(
      Term.app(constant, identity).flatMap(Term.app(_, x)).flatMap(Term.app(_, real("0:real")))))
    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val unfolded = force(Conv.unfold(force(derivative.definition(Derivative.DerivativeName)), List(identity, x, real("0:real"))))
    val body = opened(force(LogicError.lift(Kernel.eqMp(unfolded, assumed))))
    val near = force(rules.spec(real("(1:real) / 2"), body).flatMap(rules.mp(_, lemma("(0:real) < (1:real) / 2"))))

    val radius = force(LogicError.lift(Kernel.assume(proposition(
      "0 < d:real /\\ (!h:real. 0 < abs h /\\ abs h < d ==> abs (x:real + h - x - 0 * h) < (1:real) / 2 * abs h)"))))
    val dPositive = force(rules.conjElim1(radius))
    val inside = force(rules.conjElim2(radius))

    val magnitude = chain.magnitude
    val halfIs = force(magnitude.fact(Magnitude.OfNonNegative).flatMap(rules.spec(real("d / 2"), _))
      .flatMap(rules.mp(_, force(rules.spec(d, lemma("!d:real. 0 < d ==> 0 <= d / 2")).flatMap(rules.mp(_, dPositive))))))
    val admissible = force(rules.specAll(lemma("!B:real d:real. B = d / 2 ==> 0 < d ==> 0 < B /\\ B < d"), List(real("abs (d / 2)"), d))
      .flatMap(rules.mp(_, halfIs)).flatMap(rules.mp(_, dPositive)))
    val bound = force(rules.spec(real("d / 2"), inside).flatMap(rules.mp(_, admissible)))

    val increment = "x:real + d / 2 - x - 0 * (d / 2)"
    val incrementIs = force(magnitude.fact(Magnitude.OfNonNegative).flatMap(rules.spec(real(increment), _))
      .flatMap(rules.mp(_, force(rules.specAll(lemma("!x:real d:real. 0 < d ==> 0 <= x + d / 2 - x - 0 * (d / 2)"), List(x, d))
        .flatMap(rules.mp(_, dPositive))))))
    val absurd = force(rules
      .specAll(
        lemma("!A:real B:real x:real d:real. A = x + d / 2 - x - 0 * (d / 2) ==> B = d / 2 ==> 0 < d ==> A < 1 / 2 * B ==> F"),
        List(real(s"abs ($increment)"), real("abs (d / 2)"), x, d))
      .flatMap(rules.mp(_, incrementIs)).flatMap(rules.mp(_, halfIs))
      .flatMap(rules.mp(_, dPositive)).flatMap(rules.mp(_, bound)))

    val eliminated = force(rules.existsElim(near, d, absurd))
    force(rules.notIntro(claim, eliminated))
  }

  it should "refuse a slope of zero to the identity, so that the definition is not satisfied by everything" in {
    identityNotFlat.hypotheses shouldBe empty
    derivative.show(identityNotFlat.conclusion) shouldBe "~(derivative (\\y:real. y) x 0)"
  }

  it should "refuse it a second way, by uniqueness, and the two refusals agree" in {
    // `DERIVATIVE_UNIQUE` at the identity's slope one and a supposed slope zero gives `1 = 0`. The
    // hand derivation above does not use uniqueness, so this is a second road to the same
    // statement, and a uniqueness that held vacuously, or a slope the identity did not have, would
    // make the two disagree.
    val x = Term.variable("x", reals)
    val identity = force(derivative.term("\\y:real. y", functions))
    val claim = proposition("derivative (\\y:real. y) x 0")
    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val one = force(rules.spec(x, fact(Derivative.Identity)))
    val same = force(rules.specAll(fact(Derivative.Unique), List(identity, x, real("1:real"), real("0:real")))
      .flatMap(rules.mp(_, one)).flatMap(rules.mp(_, assumed)))
    val absurd = force(rules.notElim(lemma("~((1:real) = 0)"), same))
    val refused = force(rules.notIntro(claim, absurd))
    refused.hypotheses shouldBe empty
    refused.conclusion shouldBe identityNotFlat.conclusion
  }

  it should "refuse the exponential a slope of zero at zero, by uniqueness against its value there" in {
    // `DERIVATIVE_EXP` asks nothing, so there is no hypothesis to detach; what could make it empty is
    // a slope the definition grants to anything. Uniqueness turns a second slope into `exp 0 = 0`,
    // which `EXP_0` contradicts.
    val zero = real("0:real")
    val exp = force(derivative.term("exp", functions))
    val claim = proposition("derivative exp 0 0")
    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val own = force(rules.spec(zero, fact(Derivative.Exponential)))
    val same = force(rules.specAll(fact(Derivative.Unique), List(exp, zero, real("exp 0"), zero))
      .flatMap(rules.mp(_, own)).flatMap(rules.mp(_, assumed)))
    val atZero = force(chain.transcendental.fact(Transcendental.ExponentialAtZero))
    val one = force(Conv.sym(same).flatMap(Conv.trans(_, atZero)))
    val absurd = force(rules.notElim(lemma("~((0:real) = 1)"), one))
    val refused = force(rules.notIntro(claim, absurd))
    refused.hypotheses shouldBe empty
    derivative.show(refused.conclusion) shouldBe "~(derivative exp 0 0)"
  }

  it should "detach the product rule at the identity times itself, with nothing assumed" in {
    // Both hypotheses are `DERIVATIVE_ID` at the same point, and what comes out is the slope of
    // `\y. y * y` at `x`, written as the rule writes it.
    val x = Term.variable("x", reals)
    val identity = force(derivative.term("\\y:real. y", functions))
    val slope = force(rules.spec(x, fact(Derivative.Identity)))
    val detached = opened(force(rules.specAll(fact(Derivative.ProductRule), List(identity, identity, x, real("1:real"), real("1:real")))
      .flatMap(rules.mp(_, slope)).flatMap(rules.mp(_, slope))))
    detached.hypotheses shouldBe empty
    derivative.show(detached.conclusion) shouldBe "derivative (\\y:real. y * y) x (1 * x + x * 1)"

    // And the bridge at the same function: a differentiable identity is continuous, the fact
    // `Continuity` proves directly, reached here the other way.
    val continuous = force(rules.specAll(fact(Derivative.Continuous), List(identity, x, real("1:real"))).flatMap(rules.mp(_, slope)))
    continuous.hypotheses shouldBe empty
    continuous.conclusion shouldBe force(chain.continuity.fact(Continuity.Identity).flatMap(rules.spec(x, _))).conclusion
  }

  it should "detach the chain rule at the identity after itself, and after a constant" in {
    val x = Term.variable("x", reals)
    val identity = force(derivative.term("\\y:real. y", functions))
    val atX = force(rules.spec(x, fact(Derivative.Identity)))
    val twice = opened(force(rules.specAll(fact(Derivative.ChainRule), List(identity, identity, x, real("1:real"), real("1:real")))))
    val composed = force(rules.mp(twice, atX).flatMap(rules.mp(_, atX)))
    composed.hypotheses shouldBe empty
    derivative.show(composed.conclusion) shouldBe "derivative (\\y:real. y) x (1 * 1)"

    // After a constant, `g (x + h) - g x` is zero for every `h`, which is the case the textbook's
    // quotient cannot reach: the rule has to hold there without ever dividing by the increment.
    val five = force(derivative.term("\\y:real. (5:real)", functions))
    val flat = force(rules.specAll(fact(Derivative.Constant), List(real("5:real"), x)))
    val outerAtFive = force(rules.spec(real("5:real"), fact(Derivative.Identity)))
    val afterConstant = opened(force(rules.specAll(fact(Derivative.ChainRule), List(identity, five, x, real("1:real"), real("0:real")))))
    val still = force(rules.mp(afterConstant, flat).flatMap(rules.mp(_, outerAtFive)))
    still.hypotheses shouldBe empty
    derivative.show(still.conclusion) shouldBe "derivative (\\y:real. 5) x (1 * 0)"
  }

  it should "detach the mean value theorem at the identity on [0, 1], where the ends differ" in {
    // Not Rolle in disguise: the identity takes different values at the two ends, so what comes out
    // is a slope times the length of the interval equal to the change, with nothing assumed.
    val identity = force(derivative.term("\\y:real. y", functions))
    val instance = opened(force(rules.specAll(fact(Derivative.MeanValue), List(identity, real("0:real"), real("1:real")))))
    val x = Term.variable("x", reals)
    val continuousEverywhere = {
      val inside = proposition("(0:real) <= x /\\ x <= 1")
      val continuous = force(chain.continuity.fact(Continuity.Identity).flatMap(rules.spec(x, _)))
      force(rules.disch(inside, continuous).flatMap(rules.gen(x, _)))
    }
    val differentiableInside = {
      val inside = proposition("(0:real) < x /\\ x < 1")
      val slope = force(rules.spec(x, fact(Derivative.Identity)))
      val exists = force(derivative.proposition("?m:real. derivative (\\y:real. y) x m")
        .flatMap(statement => logic.destExistsPredicate(statement).toRight(NotOfForm("an existential", statement)))
        .flatMap(rules.existsIntro(_, real("1:real"), slope)))
      force(rules.disch(inside, exists).flatMap(rules.gen(x, _)))
    }
    val detached = Vector(lemma("(0:real) < 1"), continuousEverywhere, differentiableInside)
      .foldLeft(instance)((theorem, premise) => force(rules.mp(theorem, premise)))
    detached.hypotheses shouldBe empty
    derivative.show(detached.conclusion) shouldBe
      "?x:real. ?y:real. 0 < x /\\ x < 1 /\\ derivative (\\z:real. z) x y /\\ 1 - 0 = y * (1 - 0)"
  }

  it should "need f a = f b, which is shown by refuting the theorem without it at the identity" in {
    // Dropped, the hypothesis leaves a statement every other premise of which the identity on
    // [0, 1] meets, and whose conclusion is a point where the identity is flat: there is none.
    val unconditional = proposition(
      "!f:real -> real. !a:real. !b:real. a < b ==> (!x:real. a <= x /\\ x <= b ==> continuous f x) ==> " +
        "(!x:real. a < x /\\ x < b ==> ?m:real. derivative f x m) ==> ?c:real. a < c /\\ c < b /\\ derivative f c 0")
    val assumed = force(LogicError.lift(Kernel.assume(unconditional)))
    val identity = force(derivative.term("\\y:real. y", functions))
    val instance = opened(force(rules.specAll(assumed, List(identity, real("0:real"), real("1:real")))))

    val x = Term.variable("x", reals)
    val continuousEverywhere = {
      val inside = proposition("(0:real) <= x /\\ x <= 1")
      val continuous = force(chain.continuity.fact(Continuity.Identity).flatMap(rules.spec(x, _)))
      force(rules.disch(inside, continuous).flatMap(rules.gen(x, _)))
    }
    val differentiableInside = {
      val inside = proposition("(0:real) < x /\\ x < 1")
      val slope = force(rules.spec(x, fact(Derivative.Identity)))
      val exists = force(derivative.proposition("?m:real. derivative (\\y:real. y) x m")
        .flatMap(statement => logic.destExistsPredicate(statement).toRight(NotOfForm("an existential", statement)))
        .flatMap(rules.existsIntro(_, real("1:real"), slope)))
      force(rules.disch(inside, exists).flatMap(rules.gen(x, _)))
    }
    val somewhere = Vector(lemma("(0:real) < 1"), continuousEverywhere, differentiableInside)
      .foldLeft(instance)((theorem, premise) => force(rules.mp(theorem, premise)))

    val c = Term.variable("c", reals)
    val witness = force(LogicError.lift(Kernel.assume(proposition("0 < c:real /\\ c < 1 /\\ derivative (\\y:real. y) c 0"))))
    val flat = force(rules.conjElim2(witness).flatMap(rules.conjElim2))
    val notFlat = force(rules.gen(Term.variable("x", reals), identityNotFlat).flatMap(rules.spec(c, _)))
    val absurd = force(rules.notElim(notFlat, flat))
    val eliminated = force(rules.existsElim(somewhere, c, absurd))
    val refused = force(rules.notIntro(unconditional, eliminated))

    refused.hypotheses shouldBe empty
  }
}
