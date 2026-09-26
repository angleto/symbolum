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

  /** The facts about a whole interval rather than a point, which rest on the mean value theorem. */
  private val onInterval: Set[String] = Set(Derivative.Flat, Derivative.NonDecreasing, Derivative.Increasing)

  /** The textbook forms of the interval theorems, which `DerivativeWithin` carries across the extension. */
  private val withinInterval: Set[String] = Set(
    Derivative.RolleWithin, Derivative.MeanValueWithin, Derivative.FlatWithin,
    Derivative.NonDecreasingWithin, Derivative.IncreasingWithin)

  private val realAxioms: Set[Term] = chain.reals.axioms.values.map(_.conclusion).toSet
  private val completeness: Term = force(chain.reals.axiom("COMPLETENESS")).conclusion
  private val select: Term = force(chain.classical.axiom("SELECT")).conclusion

  /* --------------------------------------------------------------- what it cost */

  "The derivative" should "add its constants and no axiom to the theory below it" in {
    // The theory it extends is the chain's end when it is built, which is `Resolving`'s, and not
    // `Continuity`'s, whose constants it reads.
    val below = chain.resolving.theory
    derivative.theory.axioms shouldBe below.axioms
    (derivative.theory.constants.keySet -- below.constants.keySet) shouldBe
      Set(Derivative.DerivativeName, Derivative.WithinName)
    derivative.definitions.keySet shouldBe Set(Derivative.DerivativeName, Derivative.WithinName)
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

    // The mean value theorem is Rolle at a combination, and costs what Rolle costs, and so do the
    // three facts about the sign of a derivative on an interval, which are it and uniqueness.
    Derivation.axiomsOf(fact(Derivative.MeanValue)) shouldBe spent
    for (name <- onInterval) withClue(name) { Derivation.axiomsOf(fact(name)) shouldBe spent }

    // Their textbook forms, with continuity relative to [a, b], cost the same and nothing more: the
    // extension they are carried by is built from the reals' order and `COND`, which the choice
    // already pays for.
    for (name <- withinInterval) withClue(name) { Derivation.axiomsOf(fact(name)) shouldBe spent }

    // That a derivative is a relative one reads no fact about the reals at all: the radius is handed
    // across unchanged, and the extra conjuncts of the increment are dropped.
    Derivation.axiomsOf(fact(Derivative.WithinOfDerivative)) shouldBe empty

    // Everything else is about one point, and takes no supremum; past the reals they spend the
    // choice `abs` is paid for with and nothing else.
    for (name <- Derivative.Statements.map(_._1)
        if !(Set(Derivative.Rolle, Derivative.MeanValue, Derivative.Exponential, Derivative.Sine, Derivative.Cosine, Derivative.NaturalLog,
          Derivative.WithinOfDerivative) ++ onInterval ++ withinInterval).contains(name)) {
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
    // `MONOTONE_CONVERGES`, the naturals' axioms through the factorial, and eta, which this comment
    // left out until 2026-09-25: all nineteen of the chain. What the slope adds on
    // top of the estimate is the addition theorem and the definition, which cost nothing more.
    val nearLine = force(chain.logarithm.fact(Logarithm.NearLine))
    val spent = Derivation.axiomsOf(fact(Derivative.Exponential))
    spent shouldBe Derivation.axiomsOf(nearLine)
    spent should contain(completeness)
    val route = Set(nearLine.conclusion, force(chain.transcendental.fact(Transcendental.Addition)).conclusion)
    Derivation.restingOn(fact(Derivative.Exponential), route) shouldBe route

    // Written by the verification of card a7214946, which asked for this price to be the addition
    // theorem's. The equality above is with the estimate, and the two would move together: an
    // estimate that began to spend a twentieth axiom would take the slope with it and nothing here
    // would go red. The addition theorem is proved in another file by another route, so this pins
    // the price to something the slope does not own. Measured on 2026-09-25 at `87175842`: both
    // are the chain's nineteen, eta included.
    spent shouldBe Derivation.axiomsOf(force(chain.transcendental.fact(Transcendental.Addition)))
  }

  it should "price the product rule, the chain rule and their bridge at the fifteen and the choice, exactly" in {
    // Written by the verification of cards d83a54d3 and 513a27d9, which asked for these prices as
    // equalities. The loop above asserts that past the reals they spend the choice alone and that
    // completeness is not among the reals they spend, which leaves the other fifteen unpinned; this
    // pins all of it, measured on 2026-09-25 at `87175842`. A derivation that stopped reaching an
    // axiom of the field would be a proof of the same statement by another road and is worth a look
    // rather than a silent pass.
    for (name <- List(Derivative.Continuous, Derivative.ProductRule, Derivative.ChainRule)) withClue(name) {
      Derivation.axiomsOf(fact(name)) shouldBe (realAxioms - completeness) + select
    }
  }

  it should "price the sine's and the cosine's slopes at what their estimates cost, through the addition formulas" in {
    // Measured on 2026-09-25 before it was written here: the two slopes spend what `COS_NEAR_ONE`
    // spends, which is a series and so the supremum and the naturals. The route is the design: the
    // addition formula splits the error, the two estimates bound its brackets and the square keeps
    // its coefficients at most one.
    val nearOne = force(chain.logarithm.fact(Logarithm.CosineNearOne))
    val nearLine = force(chain.logarithm.fact(Logarithm.SineNearLine))
    val squared = force(chain.transcendental.fact(Transcendental.Pythagoras))
    for ((name, addition) <- List(Derivative.Sine -> Transcendental.SineAddition, Derivative.Cosine -> Transcendental.CosineAddition))
      withClue(name) {
        val spent = Derivation.axiomsOf(fact(name))
        spent shouldBe Derivation.axiomsOf(nearOne)
        spent should contain(completeness)
        val route = Set(force(chain.transcendental.fact(addition)).conclusion, nearOne.conclusion, nearLine.conclusion, squared.conclusion)
        Derivation.restingOn(fact(name), route) shouldBe route
      }
  }

  it should "refuse the sine a slope of zero at zero and the cosine a slope of one, by uniqueness" in {
    // Uniqueness turns a second slope into an equation with `cos 0` or `sin 0`, and `COS_ZERO` and
    // `SIN_ZERO` contradict it: the published slopes are the only ones.
    val zero = real("0:real")
    val atZero = Map(
      Derivative.Sine -> force(chain.transcendental.fact(Transcendental.CosineAtZero)),
      Derivative.Cosine -> force(chain.transcendental.fact(Transcendental.SineAtZero)))
    for ((name, function, wrong, contradiction) <- List(
        (Derivative.Sine, "sin", "0:real", "!c:real. c = 0 ==> c = 1 ==> F"),
        (Derivative.Cosine, "cos", "1:real", "!s:real. 0 - s = 1 ==> s = 0 ==> F"))) withClue(name) {
      val f = force(derivative.term(function, functions))
      val claim = proposition(s"derivative $function 0 $wrong")
      val assumed = force(LogicError.lift(Kernel.assume(claim)))
      val own = force(rules.spec(zero, fact(name)))
      val slope = own.conclusion match {
        case App(_, argument) => argument
        case other            => fail(s"not a derivative: $other")
      }
      val same = force(rules.specAll(fact(Derivative.Unique), List(f, zero, slope, real(wrong)))
        .flatMap(rules.mp(_, own)).flatMap(rules.mp(_, assumed)))
      val value = force(Term.destEq(atZero(name).conclusion).map(_._1).toRight(NotOfForm("an equation", atZero(name).conclusion)))
      val absurd = force(rules.specAll(lemma(contradiction), List(value))
        .flatMap(rules.mp(_, same)).flatMap(rules.mp(_, atZero(name))))
      val refused = force(rules.notIntro(claim, absurd))
      refused.hypotheses shouldBe empty
    }
  }

  it should "price the logarithm's slope at the exponential's, through its estimate, its monotonicity and ln's product" in {
    // Measured on 2026-09-26 before it was written here: the same axioms as `DERIVATIVE_EXP`, since
    // what it spends past the reals is the exponential's series. The route is the design: `LN_MUL`
    // splits `ln (x + h)`, the monotonicity keeps `ln (1 + t)` small, and the estimate does the rest.
    val slope = fact(Derivative.NaturalLog)
    Derivation.axiomsOf(slope) shouldBe Derivation.axiomsOf(fact(Derivative.Exponential))
    val route = Set(
      force(chain.logarithm.fact(Logarithm.NearLine)).conclusion,
      force(chain.logarithm.fact(Logarithm.Multiplicative)).conclusion,
      force(chain.logarithm.fact(Logarithm.ExpOfLn)).conclusion,
      force(chain.logarithm.fact(Logarithm.StrictlyIncreasing)).conclusion)
    Derivation.restingOn(slope, route) shouldBe route
  }

  it should "refuse the logarithm a slope of zero at one, by uniqueness against inv 1" in {
    // `inv 1 = 1` is `MUL_INVERSE` at one, and uniqueness turns a second slope into `inv 1 = 0`.
    // The hypothesis `0 < x` is not refuted here and cannot be: at a point that is not positive
    // `ln` is a choice nothing constrains, so no derivation says the slope there is or is not `inv x`.
    val one = real("1:real")
    val ln = force(derivative.term("ln", functions))
    val claim = proposition("derivative ln 1 0")
    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val own = force(rules.spec(one, fact(Derivative.NaturalLog)).flatMap(rules.mp(_, lemma("(0:real) < 1"))))
    val same = force(rules.specAll(fact(Derivative.Unique), List(ln, one, real("inv 1"), real("0:real")))
      .flatMap(rules.mp(_, own)).flatMap(rules.mp(_, assumed)))
    val inverse = force(chain.reals.axiom("MUL_INVERSE").flatMap(rules.spec(one, _))
      .flatMap(rules.mp(_, lemma("~((1:real) = 0)"))))
    val absurd = force(rules.specAll(lemma("!v:real. 1 * v = 1 ==> v = 0 ==> F"), List(real("inv 1")))
      .flatMap(rules.mp(_, inverse)).flatMap(rules.mp(_, same)))
    val refused = force(rules.notIntro(claim, absurd))
    refused.hypotheses shouldBe empty
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

  it should "detach linearity at the identity and a constant, with nothing assumed" in {
    // The mean value card asked each of its three facts for a guard of its own. Uniqueness has two,
    // the refusals above, and `CONTINUOUS_LINEAR` is detached in `ContinuitySpec`; this one was
    // reached only inside `MEAN_VALUE`, whose derivation discharges its hypotheses from hypotheses
    // of its own, so nothing showed that the two it asks for are met by any pair of functions.
    // Added by the verification of 2026-09-25 at `87175842`. Specialised by the instance rather
    // than by position: five of the binders are reals, and a swap would be a different theorem.
    val x = Term.variable("x", reals)
    val target = proposition(
      "derivative (\\y:real. y) x 1 ==> derivative (\\y:real. (2:real)) x 0 ==> " +
        "derivative (\\y:real. 3 * y + (0 - 1) * 2) x (3 * 1 + (0 - 1) * 0)")
    val instance = force(rules.specToReduced(fact(Derivative.Linear), target))
    val detached = force(rules.mp(instance, force(rules.spec(x, fact(Derivative.Identity))))
      .flatMap(rules.mp(_, force(rules.specAll(fact(Derivative.Constant), List(real("2:real"), x))))))
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition("derivative (\\y:real. 3 * y + (0 - 1) * 2) x (3 * 1 + (0 - 1) * 0)")
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

  it should "compose the exponential's slope through the chain rule, with nothing assumed" in {
    // Written by the verification of card a7214946, which asked for `DERIVATIVE_EXP` to be detached
    // through the chain rule at `exp (2 * x)` or the like, to say that it composes. Two such: the
    // exponential after itself, where the outer slope is read at `exp x` rather than at `x`, and the
    // exponential after `1 * y + 1 * y`, which is `2 * y` as `DERIVATIVE_LINEAR` writes it. A slope
    // of `exp` that held only at the points `DerivativeSpec` happened to name, or a chain rule whose
    // outer hypothesis was read at `x` rather than at `g x`, fails the first.
    val x = Term.variable("x", reals)
    val exp = force(derivative.term("exp", functions))
    val inner = force(rules.spec(x, fact(Derivative.Exponential)))
    val outer = force(rules.spec(real("exp x"), fact(Derivative.Exponential)))
    val twice = opened(force(rules.specAll(fact(Derivative.ChainRule), List(exp, exp, x, real("exp (exp x)"), real("exp x")))))
    val composed = force(rules.mp(twice, inner).flatMap(rules.mp(_, outer)))
    composed.hypotheses shouldBe empty
    derivative.show(composed.conclusion) shouldBe "derivative (\\y:real. exp (exp y)) x (exp (exp x) * exp x)"

    val identity = force(derivative.term("\\y:real. y", functions))
    val one = force(rules.spec(x, fact(Derivative.Identity)))
    val doubled = opened(force(rules.specAll(fact(Derivative.Linear),
      List(identity, identity, x, real("1:real"), real("1:real"), real("1:real"), real("1:real")))
      .flatMap(rules.mp(_, one)).flatMap(rules.mp(_, one))))
    derivative.show(doubled.conclusion) shouldBe "derivative (\\y:real. 1 * y + 1 * y) x (1 * 1 + 1 * 1)"
    val double = force(derivative.term("\\y:real. 1 * y + 1 * y", functions))
    val atDouble = force(rules.spec(real("1 * x + 1 * x"), fact(Derivative.Exponential)))
    val instance = opened(force(rules.specAll(fact(Derivative.ChainRule),
      List(exp, double, x, real("exp (1 * x + 1 * x)"), real("1 * 1 + 1 * 1")))))
    val afterDouble = force(rules.mp(instance, doubled).flatMap(rules.mp(_, atDouble)))
    afterDouble.hypotheses shouldBe empty
    derivative.show(afterDouble.conclusion) shouldBe
      "derivative (\\y:real. exp (1 * y + 1 * y)) x (exp (1 * x + 1 * x) * (1 * 1 + 1 * 1))"
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

  it should "reach the sign of a derivative on an interval through the mean value theorem and uniqueness" in {
    val route = Set(fact(Derivative.MeanValue).conclusion, fact(Derivative.Unique).conclusion)
    for (name <- onInterval) withClue(name) { Derivation.restingOn(fact(name), route) shouldBe route }
  }

  /** `\y. y * y`, and at each `x` its slope `1 * x + x * 1` by the product rule at the identity twice. */
  private val square: Term = force(derivative.term("\\y:real. y * y", functions))
  private def squareSlope(x: Term): Kernel.Thm = {
    val identity = force(derivative.term("\\y:real. y", functions))
    val slope = force(rules.spec(x, fact(Derivative.Identity)))
    opened(force(rules.specAll(fact(Derivative.ProductRule), List(identity, identity, x, real("1:real"), real("1:real")))
      .flatMap(rules.mp(_, slope)).flatMap(rules.mp(_, slope))))
  }

  /**
   * The two hypotheses of the monotonicity facts at `\y. y * y` on `[0, 1]`: continuous there because
   * it has a derivative there, and inside a slope whose sign `relation` states, from `0 < x`.
   */
  private def squareHypotheses(relation: String): Vector[Kernel.Thm] = {
    val x = Term.variable("x", reals)
    val m = real("1 * x:real + x * 1")
    val continuousEverywhere = {
      val inside = proposition("(0:real) <= x /\\ x <= 1")
      val continuous = force(rules.specAll(fact(Derivative.Continuous), List(square, x, m)).flatMap(rules.mp(_, squareSlope(x))))
      force(rules.disch(inside, continuous).flatMap(rules.gen(x, _)))
    }
    val signedInside = {
      val insideText = "(0:real) < x /\\ x < 1"
      val inside = proposition(insideText)
      val assumed = force(LogicError.lift(Kernel.assume(inside)))
      val positive = force(rules.conjElim1(assumed))
      val signed = force(rules.mp(force(rules.spec(x, lemma(s"!x:real. 0 < x ==> 0 $relation 1 * x + x * 1"))), positive))
      val both = force(rules.conjIntro(squareSlope(x), signed))
      val exists = force(derivative.proposition(s"?m:real. derivative (\\y:real. y * y) x m /\\ 0 $relation m")
        .flatMap(statement => logic.destExistsPredicate(statement).toRight(NotOfForm("an existential", statement)))
        .flatMap(rules.existsIntro(_, m, both)))
      force(rules.disch(inside, exists).flatMap(rules.gen(x, _)))
    }
    Vector(continuousEverywhere, signedInside)
  }

  it should "detach monotonicity at the square on [0, 1], where it says something the order does not" in {
    // The slope `x + x` is positive strictly inside and zero at the left end, so the hypotheses hold
    // only because they ask nothing at the ends; and `u * u < v * v` is not a fact about the order
    // alone, which is what makes the conclusion worth reading.
    val ends = List(real("0:real"), real("1:real"))
    for ((name, relation, conclusion) <- Vector(
        (Derivative.Increasing, "<", "!u:real. !v:real. 0 <= u /\\ u < v /\\ v <= 1 ==> u * u < v * v"),
        (Derivative.NonDecreasing, "<=", "!u:real. !v:real. 0 <= u /\\ u <= v /\\ v <= 1 ==> u * u <= v * v"))) withClue(name) {
      val instance = opened(force(rules.specAll(fact(name), square :: ends)))
      val detached = squareHypotheses(relation).foldLeft(instance)((theorem, premise) => force(rules.mp(theorem, premise)))
      detached.hypotheses shouldBe empty
      detached.conclusion shouldBe proposition(conclusion)
    }
  }

  it should "detach the zero derivative at a constant function on [0, 1], with nothing assumed" in {
    val one = force(derivative.term("\\y:real. (1:real)", functions))
    val instance = opened(force(rules.specAll(fact(Derivative.Flat), List(one, real("0:real"), real("1:real")))))
    val x = Term.variable("x", reals)
    val continuousEverywhere = {
      val inside = proposition("(0:real) <= x /\\ x <= 1")
      val continuous = force(chain.continuity.fact(Continuity.Constant).flatMap(rules.specAll(_, List(real("1:real"), x))))
      force(rules.disch(inside, continuous).flatMap(rules.gen(x, _)))
    }
    val flatInside = {
      val inside = proposition("(0:real) < x /\\ x < 1")
      val slope = force(rules.specAll(fact(Derivative.Constant), List(real("1:real"), x)))
      force(rules.disch(inside, slope).flatMap(rules.gen(x, _)))
    }
    val detached = Vector(continuousEverywhere, flatInside).foldLeft(instance)((theorem, premise) => force(rules.mp(theorem, premise)))
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition("!x:real. 0 <= x /\\ x <= 1 ==> (1:real) = 1")
  }

  it should "need a positive slope for a strict increase, refuted at a constant function without it" in {
    // A constant has slope zero everywhere, which is non-negative, so the strict conclusion with the
    // non-strict hypothesis says `1 < 1` at the two ends of [0, 1].
    val weakened = proposition(
      "!f:real -> real. !a:real. !b:real. (!x:real. a <= x /\\ x <= b ==> continuous f x) ==> " +
        "(!x:real. a < x /\\ x < b ==> ?m:real. derivative f x m /\\ 0 <= m) ==> " +
        "!u:real. !v:real. a <= u /\\ u < v /\\ v <= b ==> f u < f v")
    val assumed = force(LogicError.lift(Kernel.assume(weakened)))
    val one = force(derivative.term("\\y:real. (1:real)", functions))
    val instance = opened(force(rules.specAll(assumed, List(one, real("0:real"), real("1:real")))))
    val x = Term.variable("x", reals)
    val continuousEverywhere = {
      val inside = proposition("(0:real) <= x /\\ x <= 1")
      val continuous = force(chain.continuity.fact(Continuity.Constant).flatMap(rules.specAll(_, List(real("1:real"), x))))
      force(rules.disch(inside, continuous).flatMap(rules.gen(x, _)))
    }
    val signedInside = {
      val inside = proposition("(0:real) < x /\\ x < 1")
      val slope = force(rules.specAll(fact(Derivative.Constant), List(real("1:real"), x)))
      val both = force(rules.conjIntro(slope, lemma("(0:real) <= 0")))
      val exists = force(derivative.proposition("?m:real. derivative (\\y:real. (1:real)) x m /\\ 0 <= m")
        .flatMap(statement => logic.destExistsPredicate(statement).toRight(NotOfForm("an existential", statement)))
        .flatMap(rules.existsIntro(_, real("0:real"), both)))
      force(rules.disch(inside, exists).flatMap(rules.gen(x, _)))
    }
    val everyPair = Vector(continuousEverywhere, signedInside).foldLeft(instance)((theorem, premise) => force(rules.mp(theorem, premise)))
    val ends = force(rules.conjIntro(lemma("(0:real) <= 0"),
      force(rules.conjIntro(lemma("(0:real) < 1"), lemma("(1:real) <= 1")))))
    val strictlyAbove = force(rules.specAll(everyPair, List(real("0:real"), real("1:real"))).flatMap(rules.mp(_, ends)))
    derivative.show(strictlyAbove.conclusion) shouldBe "1 < 1"
    val absurd = force(rules.notElim(lemma("~((1:real) < 1)"), strictlyAbove))
    val refused = force(rules.notIntro(weakened, absurd))
    refused.hypotheses shouldBe empty
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

  /**
   * `abs` at the left end of `[0, 1]` has slope `1` relative to the interval and no derivative, which
   * `AbsoluteAtAnEnd` derives. So [[Derivative.WithinInterior]] detaches strictly inside, at `1/2`,
   * and without its `a < x` it would carry that relative slope at `0` to a derivative there: the
   * statement with the hypothesis dropped is refuted with nothing assumed.
   */
  "The relative derivative" should "be the derivative strictly inside, and need a < x for it" in {
    val witness = new AbsoluteAtAnEnd(chain)
    val absolute = force(derivative.term("abs", Type.fun(reals, reals)))
    def point(text: String) = force(derivative.term(text, reals))
    def inside(x: String) = force(rules.conjIntro(
      force(linarith.prove(s"(0:real) <= $x")), force(linarith.prove(s"$x <= (1:real)"))))

    val half = "1 / (2:real)"
    val relativeAtHalf = force(rules.spec(point(half), witness.relative).flatMap(rules.mp(_, inside(half))))
    val interior = force(rules.specAll(fact(Derivative.WithinInterior),
      List(absolute, point("0:real"), point("1:real"), point(half), point("1:real")))
      .flatMap(rules.mp(_, force(linarith.prove(s"(0:real) < $half"))))
      .flatMap(rules.mp(_, force(linarith.prove(s"$half < (1:real)"))))
      .flatMap(rules.mp(_, relativeAtHalf)))
    interior.hypotheses shouldBe empty
    interior.conclusion shouldBe force(derivative.proposition(s"derivative abs ($half) 1"))

    val dropped = force(derivative.proposition(
      "!f:real -> real. !a:real. !b:real. !x:real. !m:real. x < b ==> derivative_within f a b x m ==> derivative f x m"))
    val relativeAtZero = force(rules.spec(point("0:real"), witness.relative).flatMap(rules.mp(_, inside("0:real"))))
    val absurd = force(LogicError.lift(Kernel.assume(dropped))
      .flatMap(rules.specAll(_, List(absolute, point("0:real"), point("1:real"), point("0:real"), point("1:real"))))
      .flatMap(rules.mp(_, force(linarith.prove("(0:real) < 1"))))
      .flatMap(rules.mp(_, relativeAtZero))
      .flatMap(rules.notElim(witness.noSlopeAtZero, _)))
    absurd.hypotheses shouldBe List(dropped)
    force(rules.notIntro(dropped, absurd)).hypotheses shouldBe empty
  }
}
