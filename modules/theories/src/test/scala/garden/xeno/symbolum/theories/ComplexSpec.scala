package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The complex numbers, checked as published and then spent the way a consumer spends them.
 *
 * A statement matching its text says the right thing was proved; it does not say the hypotheses
 * can ever be met. So every published implication whose antecedent is not trivially true is
 * discharged here at a value somebody can name: the inverse at `ii`, `cis` away from one at `pi`,
 * a root of unity of order one, both sums of the square roots of unity, and a square root of `ii`.
 * And the driver every identity is proved with is shown refusing two false ones beside a true one
 * that nothing published states.
 */
class ComplexSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private lazy val complex = chain.complex
  private lazy val rules = complex.logic.rules
  private lazy val linarith = force(Linarith.construct(chain.magnitude.order))
  private val Reals = TyApp(Real.TypeName, Nil)
  private val Numbers = TyApp(Natural.TypeName, Nil)

  private def fact(name: String): Kernel.Thm = force(complex.fact(name))
  private def lemma(name: String): Kernel.Thm =
    force(Library.of(chain).named(name).headOption.map(_.theorem).toRight(MissingDefinition(name)))
  private def term(text: String, ty: Type): Term = force(complex.term(text, ty))
  private def proposition(text: String): Term = force(complex.proposition(text))

  /** `goal` from `facts`, as one implication `Linarith` settles and the facts detach. */
  private def conclude(facts: Seq[Kernel.Thm], goal: Term): Kernel.Thm = {
    val implication = facts.reverse.foldLeft(goal)((g, f) => force(complex.logic.mkImp(f.conclusion, g)))
    facts.foldLeft(force(linarith.prove(implication)))((thm, f) => force(rules.mp(thm, f)))
  }

  "Every fact of the development" should "prove the statement it is published as" in {
    Complex.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe proposition(text)
        fact(name).hypotheses shouldBe empty
      }
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    complex.facts.keySet shouldBe Complex.Statements.map(_._1).toSet
  }

  /**
   * Choice, eta and infinity, measured on 2026-10-05 over every fact, and the theory asserts nothing
   * the circle's did not: the type is defined, and so is every operation on it.
   */
  it should "rest on choice, eta and infinity, and add no axiom" in {
    val expected = Set(
      force(chain.classical.axiom(Classical.Choice)).conclusion,
      force(chain.classical.axiom(Classical.Eta)).conclusion,
      force(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    complex.facts.values.map(Derivation.axiomsOf).reduce(_ ++ _) shouldBe expected
    complex.theory.axioms shouldBe chain.circle.theory.axioms
  }

  "The chain" should "end at the complex numbers, so that every constant they declare can be stated" in {
    chain.widest shouldBe complex
    Complex.Bodies.map(_._1).foreach { name =>
      withClue(s"$name: ")(chain.widest.theory.constants.contains(name) shouldBe true)
    }
  }

  /**
   * The three operators read at all three types in one signature, picked by what the operands are.
   * The constant each one lands on is read off the term rather than off the printed form, because
   * the printer gives `complex_add` and `real_add` the same symbol.
   */
  "The overloaded operators" should "read at complex, at real and at num, by their operands" in {
    def operator(text: String): String = force(chain.widest.proposition(text).flatMap(Logic.stripForall))._2 match {
      case App(App(Const(_, _), App(App(Const(name, _), _), _)), _) => name
      case other => fail(s"not an equation between applications: $other")
    }
    operator("!z:complex. !w:complex. z + w = w") shouldBe Complex.Add
    operator("!z:complex. !w:complex. z * w = w") shouldBe Complex.Multiplication
    operator("!z:complex. !w:complex. z - w = w") shouldBe Complex.Subtraction
    operator("!x:real. !y:real. x + y = y") shouldBe Real.Addition
    operator("!x:real. !y:real. x - y = y") shouldBe Real.Subtraction
    operator("!n:num. !m:num. n * m = m") shouldBe Peano.Multiplication
  }

  /**
   * What the overload costs, pinned: `-` had one candidate before this link, so a text whose only
   * typing was that candidate read at `real`, and now it has two and is refused for saying nothing
   * about which. The same text with a typed operand reads at both signatures.
   */
  it should "refuse a subtraction nothing types, which the circle's signature read at real" in {
    chain.circle.proposition("0 - 1 < 0").isRight shouldBe true
    chain.widest.proposition("0 - 1 < 0").isLeft shouldBe true
    chain.widest.proposition("(0:real) - 1 < 0").isRight shouldBe true
  }

  /**
   * A false identity is refused and a true one nothing publishes is proved. The first false one
   * differs from a true one by a constant and the second by a sign, the two ways a slip in a
   * component would show.
   */
  "The driver" should "prove an identity of the field it was not written for, and refuse two false ones" in {
    val proved = force(complex.prove("!z:complex. !w:complex. (z + w) * (z - w) = z * z - w * w"))
    proved.hypotheses shouldBe empty
    complex.prove("!z:complex. !w:complex. z * w = w * z + complex_of_real 1").isLeft shouldBe true
    complex.prove("!z:complex. cnj (z * ii) = cnj z * ii").isLeft shouldBe true
  }

  /** `~(ii = 0)`, from its imaginary part, and then the inverse law at it. */
  "The inverse" should "be one at ii, whose hypothesis holds" in {
    val ii = term("ii", Complex.Complexes)
    val zero = term("complex_of_real 0", Complex.Complexes)
    val same = proposition("ii = complex_of_real 0")
    val assumed = force(LogicError.lift(Kernel.assume(same)))
    val parts = force(rules.specAll(fact(Complex.Extensional), List(ii, zero)).flatMap(e => LogicError.lift(Kernel.eqMp(e, assumed))))
    val imaginary = force(rules.conjElim2(parts))
    val imaginaryOfZero = force(rules.spec(term("0", Reals), fact("IM_OF_REAL")))
    val absurd = conclude(Seq(imaginary, fact("IM_II"), imaginaryOfZero), proposition("F"))
    val notZero = force(rules.notIntro(same, absurd))
    val inverse = force(rules.spec(ii, fact("COMPLEX_MUL_INVERSE")).flatMap(rules.mp(_, notZero)))
    inverse.hypotheses shouldBe empty
    inverse.conclusion shouldBe proposition("ii * complex_inv ii = complex_of_real 1")
  }

  "cis" should "not be one at pi, where the hypothesis holds" in {
    val pi = term("pi", Reals)
    val range = conclude(Seq(lemma("PI_BOUNDS")), proposition("0 < pi /\\ pi < 2 * pi"))
    val notOne = force(rules.spec(pi, fact("CIS_NOT_ONE")).flatMap(rules.mp(_, range)))
    notOne.conclusion shouldBe proposition("~(cis pi = complex_of_real 1)")
  }

  private val one = "SUC 0"
  private val two = "SUC (SUC 0)"
  private def number(text: String): Term = term(text, Numbers)
  private def positive(text: String): Kernel.Thm = text match {
    case "SUC 0" => force(rules.spec(number("0"), lemma("NUM_ZERO_LT_SUC")))
    case _ => force(rules.spec(number("SUC 0"), lemma("NUM_ZERO_LT_SUC")))
  }

  "A root of unity" should "be one at its order, for an order that is positive" in {
    val unity = force(rules.spec(number(one), fact("ROOT_OF_UNITY")).flatMap(rules.mp(_, positive(one))))
    unity.conclusion shouldBe proposition(s"complex_pow (cis (2 * pi / real_of_num ($one))) ($one) = complex_of_real 1")
  }

  /** `0` is a multiple of two, so the two square roots of unity sum to two at it. */
  "The sum of the powers of a root of unity" should "be its order at a multiple of it" in {
    val divides = force(rules.spec(number(two), lemma("NUM_DIVIDES_ZERO")))
    val both = force(rules.conjIntro(positive(two), divides))
    val sum = force(rules.specAll(fact("ROOTS_OF_UNITY_SUM_DIVIDES"), List(number(two), number("0"))).flatMap(rules.mp(_, both)))
    sum.hypotheses shouldBe empty
  }

  /**
   * `1` is not a multiple of two, which is `NUM_DIVIDES_LE` and two facts of the order, so the
   * square roots of unity, `1` and `-1`, sum to zero. This is the hypothesis that would be empty if
   * the not-dividing case were stated wrongly, and it is met.
   */
  it should "be zero away from a multiple of it" in {
    val dividesT = proposition(s"NUM_DIVIDES ($two) ($one)")
    val dividing = force(LogicError.lift(Kernel.assume(dividesT)))
    val bounded = force(rules.specAll(lemma("NUM_DIVIDES_LE"), List(number(two), number(one))).flatMap(rules.mp(_, dividing)))
    val (tooLarge, vanishes) = force(complex.logic.destDisj(bounded.conclusion).toRight(NotOfForm("a disjunction", bounded.conclusion)))
    val f = proposition("F")
    val less = force(rules.spec(number(one), lemma("NUM_LT_SUC")))
    val notLarger = force(rules.specAll(lemma("NUM_LT_NOT_LE"), List(number(one), number(two))).flatMap(rules.mp(_, less)))
    val firstCase = force(LogicError.lift(Kernel.assume(tooLarge)).flatMap(rules.notElim(notLarger, _)))
    val secondCase = force(for {
      e <- LogicError.lift(Kernel.assume(vanishes))
      lt <- rules.spec(number("0"), lemma("NUM_ZERO_LT_SUC"))
      moved <- Limit.rewriteInProposition(e, lt)
      out <- rules.spec(number("0"), lemma("NUM_LT_IRREFL")).flatMap(rules.notElim(_, moved))
    } yield out)
    val absurd = force(rules.disjElim(bounded, firstCase, secondCase))
    absurd.conclusion shouldBe f
    val notDividing = force(rules.notIntro(dividesT, absurd))
    val both = force(rules.conjIntro(positive(two), notDividing))
    val sum = force(rules.specAll(fact("ROOTS_OF_UNITY_SUM_NOT_DIVIDES"), List(number(two), number(one))).flatMap(rules.mp(_, both)))
    sum.hypotheses shouldBe empty
    sum.conclusion shouldBe proposition(
      s"complex_sum (\\r:num. complex_pow (cis (2 * pi / real_of_num ($two))) (($one) * r)) ($two) = complex_of_real 0")
  }

  "A square root" should "exist for ii" in {
    val root = force(rules.specAll(fact("COMPLEX_ROOT"), List(term("ii", Complex.Complexes), number(two))).flatMap(rules.mp(_, positive(two))))
    root.hypotheses shouldBe empty
    root.conclusion shouldBe proposition(s"?w:complex. complex_pow w ($two) = ii")
  }
}
