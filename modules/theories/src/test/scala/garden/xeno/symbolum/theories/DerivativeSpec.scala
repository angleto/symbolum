package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The derivative, the interior extremum lemma and Rolle's theorem: what they cost, what they rest
 * on, and that what they say is not vacuous.
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

    // Everything else is about one point, and takes no supremum; past the reals they spend the
    // choice `abs` is paid for with and nothing else.
    for (name <- Derivative.Statements.map(_._1) if name != Derivative.Rolle) {
      val other = Derivation.axiomsOf(fact(name))
      withClue(s"$name reaches: ${(other -- realAxioms).map(derivative.show).mkString("; ")}\n") {
        other should not contain completeness
        (other -- realAxioms) shouldBe Set(select)
      }
    }
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
