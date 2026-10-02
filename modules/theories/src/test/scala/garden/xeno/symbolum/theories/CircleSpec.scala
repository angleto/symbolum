package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * `pi`, its periods and `acos`, checked as published and then spent the way a consumer spends them.
 *
 * Statements that match their text say the right thing was proved; they do not say it can be used.
 * So two values a reader knows are derived here from the published facts alone, `acos 0 = pi / 2`
 * and `sin (2 * pi) = 0`, and the textbook's definition of `pi` is stated in its own words, and the differentiator the bounds rest on is shown refusing, once for a
 * wrong slope and once for a function outside its grammar, beside the same call that succeeds.
 */
class CircleSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private lazy val circle = chain.circle
  private lazy val rules = circle.logic.rules
  private lazy val linarith = force(Linarith.construct(chain.magnitude.order))
  private val Reals = TyApp(Real.TypeName, Nil)

  private def fact(name: String): Kernel.Thm = force(circle.fact(name))
  private def real(text: String): Term = force(circle.term(text, Reals))
  private def proposition(text: String): Term = force(circle.proposition(text))

  "Every fact of the development" should "prove the statement it is published as" in {
    Circle.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe proposition(text)
        fact(name).hypotheses shouldBe empty
      }
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    circle.facts.keySet shouldBe Circle.Statements.map(_._1).toSet
  }

  /**
   * Choice, eta and infinity, measured on 2026-09-27 over every fact: choice for `pi` and `acos`,
   * which are chosen, and for the reals, which are built from cuts since `docs/adr/0053`; eta for
   * the extensionality `Slope` carries each derivative across; infinity with the naturals under the
   * series. No axiom of the reals, because since that record the reals have none.
   */
  it should "rest on choice, eta and infinity, and add no axiom" in {
    val expected = Set(
      force(chain.classical.axiom(Classical.Choice)).conclusion,
      force(chain.classical.axiom(Classical.Eta)).conclusion,
      force(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    circle.facts.values.map(Derivation.axiomsOf).reduce(_ ++ _) shouldBe expected
    circle.theory.axioms shouldBe chain.integral.theory.axioms
  }

  /** `goal` from `facts`, as one implication `Linarith` settles and the facts detach. */
  private def conclude(facts: Seq[Kernel.Thm], goal: Term): Kernel.Thm = {
    val implication = facts.reverse.foldLeft(goal)((g, f) => force(circle.logic.mkImp(f.conclusion, g)))
    facts.foldLeft(force(linarith.prove(implication)))((thm, f) => force(rules.mp(thm, f)))
  }

  /** The zero `pi / 2` is the one `acos` finds at `0`: `ACOS_SPEC` and `COS_INJECTIVE` together. */
  "The inverse of cos" should "answer pi / 2 at zero, from the published facts alone" in {
    val inRange = conclude(Nil, proposition("(0:real) - 1 <= 0 /\\ (0:real) <= 1"))
    val spec = force(rules.spec(real("0"), fact(Circle.AcosSpec)).flatMap(rules.mp(_, inRange)))
    val injective = force(rules.specAll(fact(Circle.CosInjective), List(real("acos 0"), real("pi / 2"))))
    val wanted = force(circle.logic.destImp(injective.conclusion).map(_._1).toRight(NotOfForm("an implication", injective.conclusion)))
    val premise = conclude(Seq(spec, fact(Circle.PiBounds), fact(Circle.CosPiHalf)), wanted)
    val answered = force(rules.mp(injective, premise))
    answered.hypotheses shouldBe empty
    answered.conclusion shouldBe proposition("acos 0 = pi / 2")
  }

  /**
   * The textbook defines `pi` as twice the least positive zero of `cos`, and this file chooses the
   * zero in `[0, 2]` instead. The two agree, and that is checked here in the textbook's words from
   * the published facts alone: `pi / 2` is positive, is a zero, and no positive zero is below it.
   * The bound is attained at `pi / 2` itself, so `PI_HALF_LEAST_ZERO` is not true of an empty set.
   */
  "pi / 2" should "be the least positive zero of cos, which is how a textbook defines pi" in {
    val positive = conclude(Seq(fact(Circle.PiBounds)), proposition("(0:real) < pi / 2"))
    val stated = force(rules.conjIntro(fact(Circle.CosPiHalf), fact(Circle.PiHalfLeastZero)).flatMap(rules.conjIntro(positive, _)))
    stated.hypotheses shouldBe empty
    stated.conclusion shouldBe proposition("0 < pi / 2 /\\ cos (pi / 2) = 0 /\\ (!x:real. 0 < x /\\ cos x = 0 ==> pi / 2 <= x)")
  }

  "The period" should "carry sin 0 to sin (2 * pi)" in {
    val atZero = force(rules.spec(real("0"), fact(Circle.SinPeriodic)))
    val shifted = force(chain.ring.prove(proposition("(0:real) + 2 * pi = 2 * pi")))
    val sine = force(LogicError.lift(circle.theory.constant(Transcendental.Sine, Type.fun(Reals, Reals))))
    val moved = force(Conv.apTerm(sine, shifted))
    val result = conclude(Seq(atZero, moved, force(chain.transcendental.fact("SIN_ZERO"))), proposition("sin (2 * pi) = 0"))
    result.hypotheses shouldBe empty
  }

  private lazy val slope = Slope(
    circle.logic, chain.classical, chain.ring, circle.theory, circle.notation,
    name => chain.derivative.fact(name).orElse(chain.transcendental.fact(name))
  )
  private val x = Term.variable("x", Reals)
  private def function(text: String): Term = force(circle.term(text, Type.fun(Reals, Reals)))

  /**
   * The slope is checked rather than trusted: the same function at its derivative and at a wrong
   * one. A differentiator that accepted every slope would pass the first and fail the second.
   */
  "The differentiator" should "prove the slope it is given only when it is the slope" in {
    val proved = force(slope.at(function("\\t:real. t * sin t"), x, real("sin x + x * cos x")))
    proved.hypotheses shouldBe empty
    proved.conclusion shouldBe proposition("derivative (\\t:real. t * sin t) x (sin x + x * cos x)")
    slope.at(function("\\t:real. t * sin t"), x, real("x * cos x")).isLeft shouldBe true
  }

  it should "refuse a function outside its grammar by name, rather than guess" in {
    slope.at(function("\\t:real. exp t"), x, real("exp x")).isLeft shouldBe true
    slope.at(function("\\t:real. sin (t * t)"), x, real("2 * x * cos (x * x)")).isLeft shouldBe true
  }
}
