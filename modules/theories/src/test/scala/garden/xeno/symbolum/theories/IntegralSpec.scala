package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The gauge integral, Cousin's lemma and the fundamental theorem of calculus: what they cost, what
 * they rest on, and that what they say is not vacuous. `docs/adr/0049` is the decision.
 *
 * **What it cost.** Three defined constants and no axiom, asserted as a difference against the
 * theory below.
 *
 * **What it rests on, and the one figure worth reading.** Cousin's lemma is the gluing, and spends
 * what the gluing spends: the sixteen axioms of the reals and the choice `abs` is defined by. So do
 * uniqueness and the value `integral`. The fundamental theorem stated with `has_integral` spends
 * **no** `COMPLETENESS`: it says every fine sum is close, which needs no division to exist. It is
 * naming the integral, through uniqueness and so through Cousin, that spends the supremum.
 *
 * **What keeps it from being a theorem about nothing.** A relation of sums that held of nothing
 * would make every number an integral of everything, and the definition would still read well. So
 * Cousin's lemma is detached at a concrete gauge with nothing assumed, the fundamental theorem is
 * detached at `y * y` on `[0, 1]`, a wrong value is refused, and the ordering hypothesis of
 * uniqueness is shown to carry weight by the empty interval `[1, 0]`, over which there are no fine
 * sums and every number is an integral.
 */
class IntegralSpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val integral = chain.integral
  private def logic: Logic = integral.logic
  private def rules: Rules = logic.rules
  private val reals: Type = TyApp(Real.TypeName, Nil)
  private val functions: Type = Type.fun(reals, reals)

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def fact(name: String): Kernel.Thm = force(integral.fact(name))
  private def real(text: String): Term = force(integral.term(text, reals))
  private def function(text: String): Term = force(integral.term(text, functions))
  private def proposition(text: String): Term = force(integral.proposition(text))
  private lazy val linarith: Linarith = force(Linarith.construct(chain.order))
  private def lemma(text: String): Kernel.Thm = force(linarith.prove(text))
  private def opened(theorem: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(theorem.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, theorem))))
  private def assume(text: String): Kernel.Thm = force(LogicError.lift(Kernel.assume(proposition(text))))

  /** A proof of the beta normal form of `target` as a proof of `target`. */
  private def shaped(target: Term, theorem: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(target).flatMap(Conv.sym).flatMap(e => LogicError.lift(Kernel.eqMp(e, theorem))))

  private val realAxioms: Set[Term] = chain.reals.axioms.values.map(_.conclusion).toSet
  private val completeness: Term = force(chain.reals.axiom("COMPLETENESS")).conclusion
  private val select: Term = force(chain.classical.axiom("SELECT")).conclusion

  /* --------------------------------------------------------------- what it cost */

  "The integral" should "add its constants and no axiom to the theory below it" in {
    val below = chain.derivative.theory
    integral.theory.axioms shouldBe below.axioms
    (integral.theory.constants.keySet -- below.constants.keySet) shouldBe
      Set(Integral.FineSumName, Integral.HasIntegralName, Integral.IntegralName)
    integral.theory.typeOperators.keySet shouldBe below.typeOperators.keySet
  }

  it should "state every fact as it is written, with nothing assumed" in {
    for ((name, text) <- Integral.Statements) withClue(name) {
      fact(name).hypotheses shouldBe empty
      fact(name).conclusion shouldBe proposition(text)
    }
  }

  it should "spend the gluing's price for Cousin, uniqueness and the value, and no completeness for the theorem itself" in {
    // Measured on 2026-09-25 before it was written here. The two rules of the relation spend
    // nothing; the price of the supremum arrives with Cousin's lemma and nowhere earlier.
    Real.spent(fact(Integral.Piece)) shouldBe empty
    Real.spent(fact(Integral.Join)) shouldBe empty

    val gluing = Real.spent(force(chain.continuity.fact(Continuity.IntervalGluing)))
    gluing shouldBe realAxioms + select
    for (name <- List(Integral.Exists, Integral.HasUnique, Integral.Unique, Integral.Fundamental, Integral.FundamentalWithin))
      withClue(name) {
      Real.spent(fact(name)) shouldBe gluing
    }

    // Every fine sum close to `F b - F a` is a statement about the sums there are, and needs none
    // to exist: the fundamental theorem as `has_integral` is the fifteen and the choice.
    // The textbook form, relative to [a, b], is the same argument and costs the same; the two-sided
    // form is derived from it through a fact that costs nothing.
    Real.spent(fact(Integral.HasFundamental)) shouldBe (realAxioms - completeness) + select
    Real.spent(fact(Integral.HasFundamentalWithin)) shouldBe (realAxioms - completeness) + select
  }

  it should "reach Cousin through the gluing, and the value through uniqueness" in {
    val gluing = force(chain.continuity.fact(Continuity.IntervalGluing)).conclusion
    Derivation.restingOn(fact(Integral.Exists), Set(gluing)) shouldBe Set(gluing)

    val underUniqueness = Set(fact(Integral.Exists).conclusion, fact(Integral.Gauge).conclusion)
    Derivation.restingOn(fact(Integral.HasUnique), underUniqueness) shouldBe underUniqueness

    val underTheorem = Set(fact(Integral.HasFundamental).conclusion, fact(Integral.Unique).conclusion)
    Derivation.restingOn(fact(Integral.Fundamental), underTheorem) shouldBe underTheorem

    // The two-sided theorem is the textbook one at a derivative read as a relative one, and not a
    // second copy of the argument, which would read the same word for word.
    val underTwoSided = Set(fact(Integral.HasFundamentalWithin).conclusion,
      force(chain.derivative.fact(Derivative.WithinOfDerivative)).conclusion)
    Derivation.restingOn(fact(Integral.HasFundamental), underTwoSided) shouldBe underTwoSided
  }

  /* ------------------------------------------------------ what keeps it from being empty */

  it should "detach Cousin's lemma at a constant gauge on [0, 1], with nothing assumed" in {
    val f = function("\\y:real. y")
    val gauge = function("\\y:real. (1:real)")
    val instance = opened(force(rules.specAll(fact(Integral.Exists), List(f, gauge, real("0:real"), real("1:real")))))
    val x = Term.variable("x", reals)
    val positive = force(rules.disch(proposition("(0:real) <= x /\\ x <= 1"), lemma("(0:real) < 1")).flatMap(rules.gen(x, _)))
    val detached = force(rules.mp(instance, lemma("(0:real) <= 1")).flatMap(rules.mp(_, positive)))
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition("?s:real. fine_sum (\\y:real. y) (\\y:real. (1:real)) 0 1 s")
  }

  /** `\y. y * y`, and at each `x` its slope `1 * x + x * 1`, by the product rule at the identity twice. */
  private val square: Term = function("\\y:real. y * y")
  private def squareSlope(x: Term): Kernel.Thm = {
    val identity = function("\\y:real. y")
    val slope = force(rules.spec(x, force(chain.derivative.fact(Derivative.Identity))))
    opened(force(rules.specAll(force(chain.derivative.fact(Derivative.ProductRule)),
      List(identity, identity, x, real("1:real"), real("1:real")))
      .flatMap(rules.mp(_, slope)).flatMap(rules.mp(_, slope))))
  }

  it should "detach the fundamental theorem at the square on [0, 1]" in {
    // The integral of `1 * y + y * 1` over [0, 1] is `1 * 1 - 0 * 0`: a value, with nothing assumed,
    // for a function no step of the argument names.
    val derivativeOfSquare = function("\\y:real. 1 * y + y * 1")
    val instance = opened(force(rules.specAll(fact(Integral.Fundamental),
      List(square, derivativeOfSquare, real("0:real"), real("1:real")))))
    val x = Term.variable("x", reals)
    val slopes = force(rules.disch(proposition("(0:real) <= x /\\ x <= 1"), squareSlope(x)).flatMap(rules.gen(x, _)))
    val detached = force(rules.mp(instance, lemma("(0:real) <= 1")).flatMap(rules.mp(_, slopes)))
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition("integral (\\y:real. 1 * y + y * 1) 0 1 = 1 * 1 - 0 * 0")
  }

  /**
   * The textbook form covers what the two-sided one does not, and `abs` on `[0, 1]` is the witness:
   * relative to the interval its slope is `1` everywhere, so the textbook form detaches with nothing
   * assumed, and at `0` it has no derivative at all, so the two-sided form's hypothesis is refuted
   * there, also with nothing assumed. `AbsoluteAtAnEnd` derives both.
   */
  it should "detach the textbook form at abs on [0, 1], where the two-sided form's hypothesis is false" in {
    val witness = new AbsoluteAtAnEnd(chain)
    val absolute = function("abs")
    val one = function("\\y:real. (1:real)")
    val arguments = List(absolute, one, real("0:real"), real("1:real"))

    val textbook = opened(force(rules.specAll(fact(Integral.HasFundamentalWithin), arguments)))
    val detached = force(rules.mp(textbook, lemma("(0:real) <= 1")).flatMap(rules.mp(_, witness.relative)))
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition("has_integral (\\y:real. (1:real)) 0 1 (abs 1 - abs 0)")

    val twoSided = opened(force(rules.specAll(fact(Integral.HasFundamental), arguments)))
    val slopes = force(rules.mp(twoSided, lemma("(0:real) <= 1")).flatMap(t =>
      logic.destImp(t.conclusion).map(_._1).toRight(NotOfForm("an implication", t.conclusion))))
    val supposed = force(LogicError.lift(Kernel.assume(slopes)))
    val atZero = force(rules.spec(real("0:real"), supposed)
      .flatMap(rules.mp(_, force(rules.conjIntro(lemma("(0:real) <= 0"), lemma("(0:real) <= 1"))))))
    val refuted = force(rules.notElim(witness.noSlopeAtZero, atZero).flatMap(rules.notIntro(slopes, _)))
    refuted.hypotheses shouldBe empty
  }

  /** `|- has_integral (\y. 1) 0 1 (1 - 0)`: the fundamental theorem at the identity. */
  private lazy val oneOverUnit: Kernel.Thm = {
    val identity = function("\\y:real. y")
    val one = function("\\y:real. (1:real)")
    val instance = opened(force(rules.specAll(fact(Integral.HasFundamental), List(identity, one, real("0:real"), real("1:real")))))
    val x = Term.variable("x", reals)
    val slope = force(rules.spec(x, force(chain.derivative.fact(Derivative.Identity))))
    val slopes = force(rules.disch(proposition("(0:real) <= x /\\ x <= 1"), slope).flatMap(rules.gen(x, _)))
    force(rules.mp(instance, lemma("(0:real) <= 1")).flatMap(rules.mp(_, slopes)))
  }

  it should "combine linearly at the theorem's price, and name the combination's integral at uniqueness's" in {
    // Measured on 2026-09-26: the statement about `has_integral` needs no division to exist, so it
    // spends what the fundamental theorem as `has_integral` spends and not the supremum; the value
    // `integral` goes through uniqueness and so through Cousin.
    Real.spent(fact(Integral.HasLinear)) shouldBe (realAxioms - completeness) + select
    Real.spent(fact(Integral.Linear)) shouldBe Real.spent(fact(Integral.HasUnique))
    Real.spent(fact(Integral.SumLinear)) should not contain completeness
    val route = Set(fact(Integral.SumLinear).conclusion, fact(Integral.Gauge).conclusion)
    Derivation.restingOn(fact(Integral.HasLinear), route) shouldBe route
  }

  /**
   * `|- has_integral (\x. 3 * 1 + 5 * (1 * x + x * 1)) 0 1 (3 * (1 - 0) + 5 * (1 * 1 - 0 * 0))`:
   * linearity at one and at the square's derivative, from the two integrals the fundamental theorem gives.
   */
  private lazy val combination: Kernel.Thm = {
    val derivativeOfSquare = function("\\y:real. 1 * y + y * 1")
    val x = Term.variable("x", reals)
    val squareSlopes = force(rules.disch(proposition("(0:real) <= x /\\ x <= 1"), squareSlope(x)).flatMap(rules.gen(x, _)))
    val squareIntegral = opened(force(rules.specAll(fact(Integral.HasFundamental),
      List(square, derivativeOfSquare, real("0:real"), real("1:real")))
      .flatMap(rules.mp(_, lemma("(0:real) <= 1"))).flatMap(rules.mp(_, squareSlopes))))
    val one = function("\\y:real. (1:real)")
    val combined = opened(force(rules.specAll(fact(Integral.HasLinear),
      List(one, derivativeOfSquare, real("0:real"), real("1:real"), real("1 - 0:real"), real("1 * 1 - 0 * 0:real"), real("3:real"), real("5:real")))
      .flatMap(rules.mp(_, oneOverUnit)).flatMap(rules.mp(_, squareIntegral))))
    combined
  }

  it should "detach linearity at one and at the square's derivative on [0, 1], to a value neither has alone" in {
    // `3 * 1 + 5 * (1 * x + x * 1)` has integral `3 * (1 - 0) + 5 * (1 * 1 - 0 * 0)`, which is eight,
    // from the two integrals the fundamental theorem gives, with nothing assumed.
    combination.hypotheses shouldBe empty
    combination.conclusion shouldBe
      proposition("has_integral (\\x:real. 3 * 1 + 5 * (1 * x + x * 1)) 0 1 (3 * (1 - 0) + 5 * (1 * 1 - 0 * 0))")
  }

  it should "refuse the combination the integral of its first part alone, so the detached value carries weight" in {
    // Written by the verification of card 61b8b2f1. A linearity that held because `has_integral` at
    // this function held of every number would pass the test above; uniqueness on [0, 1] against the
    // value three, which is what `3 * 1` alone integrates to, shows it does not.
    val combined = function("\\x:real. 3 * 1 + 5 * (1 * x + x * 1)")
    val wrong = proposition("has_integral (\\x:real. 3 * 1 + 5 * (1 * x + x * 1)) 0 1 3")
    val assumed = force(LogicError.lift(Kernel.assume(wrong)))
    val same = force(rules.specAll(fact(Integral.HasUnique),
      List(combined, real("0:real"), real("1:real"), real("3 * (1 - 0) + 5 * (1 * 1 - 0 * 0)"), real("3:real")))
      .flatMap(rules.mp(_, lemma("(0:real) <= 1"))).flatMap(rules.mp(_, combination)).flatMap(rules.mp(_, assumed)))
    val absurd = force(rules.notElim(lemma("~((3:real) * (1 - 0) + 5 * (1 * 1 - 0 * 0) = 3)"), same))
    val refused = force(rules.notIntro(wrong, absurd))
    refused.hypotheses shouldBe empty
  }

  it should "cost, for the combination's fine sums, no more than the fundamental theorem as has_integral" in {
    // Written by the verification of card 61b8b2f1. The test above asserts the price of
    // `HAS_INTEGRAL_LINEAR` exactly and of `FINE_SUM_LINEAR` only that it holds no `COMPLETENESS`.
    // Measured on 2026-09-26 at 1bcad72b: twelve against sixteen, so the sums cost strictly less than
    // the theorem, which a sentence saying the two cost the same gets wrong.
    val sums = Real.spent(fact(Integral.SumLinear))
    val theorem = Real.spent(fact(Integral.HasFundamental))
    info(s"FINE_SUM_LINEAR rests on ${sums.size} axioms, HAS_INTEGRAL_DERIVATIVE on ${theorem.size}")
    sums.subsetOf(theorem) shouldBe true
    sums should not be theorem
  }

  it should "integrate by parts and by substitution at the fundamental theorem's price, through the two rules" in {
    // Measured on 2026-09-26: both `has_integral` forms spend what the fundamental theorem as
    // `has_integral` spends, and both `integral` forms what uniqueness spends. The routes are the
    // design: the product rule, the theorem and linearity for parts; the chain rule and the theorem
    // for the substitution.
    val theorem = Real.spent(fact(Integral.HasFundamental))
    Real.spent(fact(Integral.HasParts)) shouldBe theorem
    Real.spent(fact(Integral.HasSubstitution)) shouldBe theorem
    Real.spent(fact(Integral.Parts)) shouldBe Real.spent(fact(Integral.HasUnique))
    Real.spent(fact(Integral.Substitution)) shouldBe Real.spent(fact(Integral.HasUnique))
    val partsRoute = Set(
      force(chain.derivative.fact(Derivative.ProductRule)).conclusion,
      fact(Integral.HasFundamental).conclusion,
      fact(Integral.HasLinear).conclusion)
    Derivation.restingOn(fact(Integral.HasParts), partsRoute) shouldBe partsRoute
    val substitutionRoute = Set(force(chain.derivative.fact(Derivative.ChainRule)).conclusion, fact(Integral.HasFundamental).conclusion)
    Derivation.restingOn(fact(Integral.HasSubstitution), substitutionRoute) shouldBe substitutionRoute
  }

  it should "detach the substitution at the square composed with itself on [0, 1]" in {
    // `F` and `g` are both `\y. y * y`, with slope `1 * y + y * 1` by the product rule, so the
    // integrand is `(1 * (x * x) + x * x * 1) * (1 * x + x * 1)` and its integral is
    // `(1 * 1) * (1 * 1) - (0 * 0) * (0 * 0)`, with nothing assumed.
    val slope = function("\\y:real. 1 * y + y * 1")
    val y = Term.variable("y", reals)
    val x = Term.variable("x", reals)
    val everywhere = force(rules.gen(y, squareSlope(y)))
    val inside = force(rules.disch(proposition("(0:real) <= x /\\ x <= 1"), squareSlope(x)).flatMap(rules.gen(x, _)))
    val detached = opened(force(rules.specAll(fact(Integral.HasSubstitution), List(square, slope, square, slope, real("0:real"), real("1:real")))
      .flatMap(rules.mp(_, lemma("(0:real) <= 1"))).flatMap(rules.mp(_, everywhere)).flatMap(rules.mp(_, inside))))
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition(
      "has_integral (\\x:real. (1 * (x * x) + x * x * 1) * (1 * x + x * 1)) 0 1 (1 * 1 * (1 * 1) - 0 * 0 * (0 * 0))")
  }

  it should "detach integration by parts at a constant and the identity on [0, 1]" in {
    // `f = \x. 1` has slope `0` and `g = \x. x` has slope `1`, so the given integral is of `1 * 1`,
    // which is the fundamental theorem's `1` over [0, 1] written under the lambda, and parts gives
    // `0 * x` the integral `1 * 1 - 1 * 0 - (1 - 0)`.
    val one = function("\\x:real. (1:real)")
    val zero = function("\\x:real. (0:real)")
    val identity = function("\\x:real. x")
    val x = Term.variable("x", reals)
    val constantSlope = force(rules.specAll(force(chain.derivative.fact(Derivative.Constant)), List(real("1:real"), x)))
    val identitySlope = force(rules.spec(x, force(chain.derivative.fact(Derivative.Identity))))
    val member = proposition("(0:real) <= x /\\ x <= 1")
    val slopesF = force(rules.disch(member, constantSlope).flatMap(rules.gen(x, _)))
    val slopesG = force(rules.disch(member, identitySlope).flatMap(rules.gen(x, _)))
    val product = force(LogicError.lift(Kernel.abs(x, lemma("(1:real) * 1 = 1"))))
    val hasConstant = force(integral.term("has_integral", Type.fun(functions, Type.fun(reals, Type.fun(reals, Type.fun(reals, Type.Bool))))))
    val rewritten = force(Conv.apTerm(hasConstant, product).flatMap(Conv.apThm(_, real("0:real"))).flatMap(Conv.apThm(_, real("1:real")))
      .flatMap(Conv.apThm(_, real("1 - 0:real"))).flatMap(Conv.sym).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, oneOverUnit))))
    val detached = opened(force(rules.specAll(fact(Integral.HasParts), List(one, identity, zero, one, real("0:real"), real("1:real"), real("1 - 0:real")))
      .flatMap(rules.mp(_, lemma("(0:real) <= 1"))).flatMap(rules.mp(_, slopesF)).flatMap(rules.mp(_, slopesG)).flatMap(rules.mp(_, rewritten))))
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition("has_integral (\\x:real. 0 * x) 0 1 (1 * 1 - 1 * 0 - (1 - 0))")
  }

  it should "refuse a wrong value, so that the definition does not hold of every number" in {
    // Assumed, `has_integral (\y. 1) 0 1 0` meets the fundamental theorem's `1 - 0` in uniqueness,
    // and `0 = 1 - 0` is false.
    oneOverUnit.hypotheses shouldBe empty
    val wrong = proposition("has_integral (\\y:real. (1:real)) 0 1 0")
    val assumed = force(LogicError.lift(Kernel.assume(wrong)))
    val same = force(rules.specAll(fact(Integral.HasUnique),
      List(function("\\y:real. (1:real)"), real("0:real"), real("1:real"), real("0:real"), real("1 - 0:real")))
      .flatMap(rules.mp(_, lemma("(0:real) <= 1"))).flatMap(rules.mp(_, assumed)).flatMap(rules.mp(_, oneOverUnit)))
    val absurd = force(rules.notElim(lemma("~((0:real) = 1 - 0)"), same))
    val refused = force(rules.notIntro(wrong, absurd))
    refused.hypotheses shouldBe empty
  }

  /**
   * `|- has_integral f 1 0 i` for every `i`: over `[1, 0]` no fine sum exists, because every sum's
   * interval has its ends in order, so "every fine sum is close to `i`" holds of every `i`.
   */
  private def overTheEmptyInterval(value: String): Kernel.Thm = {
    val f = function("\\y:real. (0:real)")
    val gauge = function("\\y:real. (1:real)")
    val ordered = Parser.term(integral.theory, integral.notation, "\\u:real. \\v:real. \\s:real. u <= v",
      Type.fun(reals, Type.fun(reals, Type.fun(reals, Type.Bool))))
    val instance = opened(force(ordered.flatMap(p => rules.specAll(fact(Integral.Induction), List(f, gauge, p)))))
    val u = Term.variable("u", reals)
    val v = Term.variable("v", reals)
    val w = Term.variable("w", reals)
    val x = Term.variable("x", reals)
    val s = Term.variable("s", reals)
    val t = Term.variable("t", reals)
    val base = {
      val condition = proposition("u:real <= x:real /\\ x <= v:real /\\ v - u < 1")
      val assumed = force(LogicError.lift(Kernel.assume(condition)))
      val ux = force(rules.conjElim1(assumed))
      val xv = force(rules.conjElim2(assumed).flatMap(rules.conjElim1))
      val uv = force(rules.specAll(lemma("!u:real x:real v:real. u <= x ==> x <= v ==> u <= v"), List(u, x, v))
        .flatMap(rules.mp(_, ux)).flatMap(rules.mp(_, xv)))
      force(rules.disch(condition, uv).flatMap(rules.genAll(_, List(u, v, x))))
    }
    val step = force(rules.specAll(lemma("!u:real v:real w:real. u <= v ==> v <= w ==> u <= w"), List(u, v, w))
      .flatMap(rules.genAll(_, List(u, v, w, s, t))))
    val ends = force(rules.mp(instance, base).flatMap(rules.mp(_, step)))

    val e = Term.variable("e", reals)
    val sumTerm = proposition(s"fine_sum (\\y:real. (0:real)) (\\y:real. (1:real)) 1 0 s")
    val sum = force(LogicError.lift(Kernel.assume(sumTerm)))
    val backwards = force(rules.specAll(ends, List(real("1:real"), real("0:real"), s)).flatMap(rules.mp(_, sum)))
    val absurd = force(rules.notElim(lemma("~((1:real) <= 0)"), backwards))
    val close = force(rules.falsityElim(proposition(s"abs (s:real - $value) < e:real"), absurd))
    val everySum = force(rules.disch(sumTerm, close).flatMap(rules.gen(s, _)))
    val positive = force(rules.gen(x, lemma("(0:real) < 1")))
    val normal = force(rules.conjIntro(positive, everySum))

    val unfolded = force(integral.definition(Integral.HasIntegralName)
      .flatMap(d => Conv.unfold(d, List(f, real("1:real"), real("0:real"), real(value)))))
    val statement = force(Term.destEq(unfolded.conclusion).map(_._2).toRight(NotOfForm("an equation", unfolded.conclusion)))
    val atE = statement match {
      case App(_, predicate) => force(LogicError.lift(Term.app(predicate, e)).flatMap(Conv.betaRoot)
        .flatMap(eq => Term.destEq(eq.conclusion).map(_._2).toRight(NotOfForm("an equation", eq.conclusion))))
      case other => fail(s"not a quantification: $other")
    }
    val existential = force(logic.destImp(atE).map(_._2).toRight(NotOfForm("an implication", atE)))
    val predicate = force(logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential)))
    val target = force(LogicError.lift(Term.app(predicate, gauge)).flatMap(Conv.betaRoot)
      .flatMap(eq => Term.destEq(eq.conclusion).map(_._2).toRight(NotOfForm("an equation", eq.conclusion))))
    val witnessed = force(rules.existsIntro(predicate, gauge, shaped(target, normal)))
    val everyTolerance = force(rules.disch(proposition("0 < e:real"), witnessed).flatMap(rules.gen(e, _)))
    force(Conv.sym(unfolded).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, everyTolerance))))
  }

  it should "need a <= b for uniqueness, which the empty interval [1, 0] refutes without it" in {
    val zero = overTheEmptyInterval("0")
    val one = overTheEmptyInterval("1")
    zero.hypotheses shouldBe empty
    one.hypotheses shouldBe empty
    val unconditional = proposition(
      "!f:real -> real. !a:real. !b:real. !i:real. !j:real. has_integral f a b i ==> has_integral f a b j ==> i = j")
    val assumed = force(LogicError.lift(Kernel.assume(unconditional)))
    val same = force(rules.specAll(assumed,
      List(function("\\y:real. (0:real)"), real("1:real"), real("0:real"), real("0:real"), real("1:real")))
      .flatMap(rules.mp(_, zero)).flatMap(rules.mp(_, one)))
    val absurd = force(rules.notElim(lemma("~((0:real) = 1)"), same))
    val refused = force(rules.notIntro(unconditional, absurd))
    refused.hypotheses shouldBe empty
  }

  it should "need a <= b for the fundamental theorem, refuted on [1, 0] where its other hypothesis asks nothing" in {
    // Written by the verification of card 0abc40ca. Over `[1, 0]` no point is in the interval, so
    // "F has derivative f x at every point of it" holds of every `F`, and the statement with
    // `a <= b` dropped names one value for `integral f 1 0` as `F 0 - F 1` for all of them at once:
    // `0 - 0` at the zero function and `0 - 1` at the identity. So the hypothesis is what keeps the
    // theorem true, and a later edit loosening the published statement to this form would be
    // publishing a falsity.
    //
    // The same hypothesis is NOT load-bearing in `HAS_INTEGRAL_DERIVATIVE`, and no test here refutes
    // it there on purpose: over `[1, 0]` every number is an integral, which is what the uniqueness
    // test above derives, so that statement stays true without `a <= b` and the hypothesis narrows it.
    val dropped = proposition(
      "!F:real -> real. !f:real -> real. !a:real. !b:real. (!x:real. a <= x /\\ x <= b ==> derivative F x (f x)) ==> " +
        "integral f a b = F b - F a")
    val assumed = force(LogicError.lift(Kernel.assume(dropped)))
    val zero = function("\\y:real. (0:real)")
    val x = Term.variable("x", reals)
    def at(primitive: String, slope: String): Kernel.Thm = {
      val instance = opened(force(rules.specAll(assumed, List(function(primitive), zero, real("1:real"), real("0:real")))))
      val inside = proposition("(1:real) <= x /\\ x <= 0")
      val nowhere = force(rules.spec(x, lemma("!x:real. 1 <= x /\\ x <= 0 ==> F"))
        .flatMap(rules.mp(_, force(LogicError.lift(Kernel.assume(inside))))))
      val vacuous = force(rules.falsityElim(proposition(s"derivative ($primitive) x $slope"), nowhere)
        .flatMap(rules.disch(inside, _)).flatMap(rules.gen(x, _)))
      force(rules.mp(instance, vacuous))
    }
    val atZero = at("\\y:real. (0:real)", "0")
    val atIdentity = at("\\y:real. y", "0")
    // Compared as terms, where alpha-equivalence is equality: the printer names the binder `x` here,
    // because the `x` the vacuous hypothesis was generalised over is in scope when it prints.
    atZero.conclusion shouldBe proposition("integral (\\y:real. (0:real)) 1 0 = 0 - 0")
    atIdentity.conclusion shouldBe proposition("integral (\\y:real. (0:real)) 1 0 = 0 - 1")
    val same = force(Conv.sym(atZero).flatMap(Conv.trans(_, atIdentity)))
    val absurd = force(rules.notElim(lemma("~((0:real) - 0 = 0 - 1)"), same))
    absurd.hypotheses shouldBe List(dropped)
    val refused = force(rules.notIntro(dropped, absurd))
    refused.hypotheses shouldBe empty
  }

  it should "need a <= b for INTEGRAL_LINEAR, refuted on [1, 0] where HAS_INTEGRAL_LINEAR still holds" in {
    // Written by the verification of card 61b8b2f1. Over `[1, 0]` every number is an integral, so
    // `HAS_INTEGRAL_LINEAR` is true there without asking anything, and the statement about
    // `integral` with `a <= b` dropped would name one value for the combination as `1 * 0 + 1 * 0`
    // and as `1 * 1 + 1 * 0` at once.
    val dropped = proposition(
      "!f:real -> real. !g:real -> real. !a:real. !b:real. !i:real. !j:real. !p:real. !q:real. " +
        "has_integral f a b i ==> has_integral g a b j ==> integral (\\x:real. p * f x + q * g x) a b = p * i + q * j")
    val assumed = force(LogicError.lift(Kernel.assume(dropped)))
    val zero = function("\\y:real. (0:real)")
    val one = real("1:real")
    val nought = real("0:real")
    def at(value: String): Kernel.Thm =
      opened(force(rules.specAll(assumed, List(zero, zero, one, nought, real(value), nought, one, one))
        .flatMap(rules.mp(_, overTheEmptyInterval(value))).flatMap(rules.mp(_, overTheEmptyInterval("0")))))
    val same = force(Conv.sym(at("0")).flatMap(Conv.trans(_, at("1"))))
    val absurd = force(rules.notElim(lemma("~((1:real) * 0 + 1 * 0 = 1 * 1 + 1 * 0)"), same))
    val refused = force(rules.notIntro(dropped, absurd))
    refused.hypotheses shouldBe empty
  }

  /* --------------------------------------------------- a continuous function has one */

  it should "give every continuous function an integral at the gluing's price, through Cousin and the supremum" in {
    // Measured on 2026-09-25 before it was written here: the reals' sixteen and the choice, the
    // same as Cousin's lemma. `COMPLETENESS` is spent by the gluing and once more for the supremum.
    val gluing = force(chain.continuity.fact(Continuity.IntervalGluing)).conclusion
    for (name <- List(Integral.ContinuousHas, Integral.ContinuousIntegral)) withClue(name) {
      Real.spent(fact(name)) shouldBe realAxioms + select
    }
    // The route: the criterion glues, and the sums the supremum compares come from Cousin.
    val route = Set(gluing, fact(Integral.Exists).conclusion, fact(Integral.Gauge).conclusion)
    Derivation.restingOn(fact(Integral.ContinuousHas), route) shouldBe route
  }

  it should "detach at the constant one on [0, 1], and agree with the fundamental theorem there" in {
    // Two routes to one number: the existence names `integral (\y. 1) 0 1`, the fundamental theorem
    // at the identity says `1 - 0` is an integral of the same function, and uniqueness joins them.
    // A statement that held for a reason unrelated to integration could not be joined to the other.
    val one = function("\\y:real. (1:real)")
    val instance = opened(force(rules.specAll(fact(Integral.ContinuousIntegral), List(one, real("0:real"), real("1:real")))))
    val x = Term.variable("x", reals)
    val continuous = force(rules.specAll(force(chain.continuity.fact(Continuity.Constant)), List(real("1:real"), x)))
    val everywhere = force(rules.disch(proposition("(0:real) <= x /\\ x <= 1"), continuous).flatMap(rules.gen(x, _)))
    val named = force(rules.mp(instance, lemma("(0:real) <= 1")).flatMap(rules.mp(_, everywhere)))
    named.hypotheses shouldBe empty
    named.conclusion shouldBe proposition("has_integral (\\y:real. (1:real)) 0 1 (integral (\\y:real. (1:real)) 0 1)")

    val joined = opened(force(rules.specAll(fact(Integral.HasUnique),
      List(one, real("0:real"), real("1:real"), real("integral (\\y:real. (1:real)) 0 1"), real("1 - 0:real")))))
    val agreed = force(rules.mp(joined, lemma("(0:real) <= 1")).flatMap(rules.mp(_, named)).flatMap(rules.mp(_, oneOverUnit)))
    agreed.hypotheses shouldBe empty
    agreed.conclusion shouldBe proposition("integral (\\y:real. (1:real)) 0 1 = 1 - 0")
  }

  // What is not here, and why: a control refuting the existence without continuity. Dirichlet's
  // function is gauge integrable, so a counterexample has to be unbounded, like `1 / x` near zero,
  // and showing that no number is its integral is an argument about unbounded fine sums of its own.
  // The existence is kept from vacuity by the detachment above instead.

  /* ------------------------------------------ additivity and the second half of the theorem */

  it should "add integrals over adjacent intervals with no supremum, and differentiate one with the gluing's price" in {
    // Measured on 2026-09-26 before it was written here. Additivity takes one fine sum at a time and
    // needs none to exist, so it is the fifteen and the choice; the derivative names `integral`, and
    // so spends Cousin's lemma and the supremum.
    Real.spent(fact(Integral.HasJoin)) shouldBe (realAxioms - completeness) + select
    for (name <- List(Integral.DerivativeWithin, Integral.DerivativeOfIntegral)) withClue(name) {
      Real.spent(fact(name)) shouldBe realAxioms + select
    }
    // The route: additivity and uniqueness read the increment as an integral, the existence supplies
    // the integrals, and the two-sided form is the relative one strictly inside.
    val underWithin = Set(Integral.HasJoin, Integral.ContinuousIntegral, Integral.Unique).map(fact(_).conclusion)
    Derivation.restingOn(fact(Integral.DerivativeWithin), underWithin) shouldBe underWithin
    val underInterior = Set(fact(Integral.DerivativeWithin).conclusion,
      force(chain.derivative.fact(Derivative.WithinInterior)).conclusion)
    Derivation.restingOn(fact(Integral.DerivativeOfIntegral), underInterior) shouldBe underInterior
  }

  it should "detach the second half at the constant one on [0, 1], at one half, with nothing assumed" in {
    val one = function("\\y:real. (1:real)")
    val instance = opened(force(rules.specAll(fact(Integral.DerivativeOfIntegral),
      List(one, real("0:real"), real("1:real"), real("(1:real) / 2")))))
    val x = Term.variable("x", reals)
    val continuous = force(rules.specAll(force(chain.continuity.fact(Continuity.Constant)), List(real("1:real"), x)))
    val everywhere = force(rules.disch(proposition("(0:real) <= x /\\ x <= 1"), continuous).flatMap(rules.gen(x, _)))
    val detached = Vector(everywhere, lemma("(0:real) < (1:real) / 2"), lemma("(1:real) / 2 < 1"))
      .foldLeft(instance)((theorem, premise) => force(rules.mp(theorem, premise)))
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition("derivative (\\y:real. integral (\\y:real. (1:real)) 0 y) ((1:real) / 2) 1")
  }

  // What is not here, and why. The relative form's `a <= x` and `x <= b` carry no weight, which is
  // argued here and not derived in a test: outside `[a, b]` no increment small enough keeps `x + h` inside, so the
  // relative derivative holds there at every slope and the statement stays true without them. The
  // continuity hypothesis does carry weight, and a control refuting the theorem without it would
  // need the integral of a discontinuous function as a value, which no fact here supplies.
}
