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

  "The integral" should "add its three constants and no axiom to the theory below it" in {
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
    Derivation.axiomsOf(fact(Integral.Piece)) shouldBe empty
    Derivation.axiomsOf(fact(Integral.Join)) shouldBe empty

    val gluing = Derivation.axiomsOf(force(chain.continuity.fact(Continuity.IntervalGluing)))
    gluing shouldBe realAxioms + select
    for (name <- List(Integral.Exists, Integral.HasUnique, Integral.Unique, Integral.Fundamental)) withClue(name) {
      Derivation.axiomsOf(fact(name)) shouldBe gluing
    }

    // Every fine sum close to `F b - F a` is a statement about the sums there are, and needs none
    // to exist: the fundamental theorem as `has_integral` is the fifteen and the choice.
    Derivation.axiomsOf(fact(Integral.HasFundamental)) shouldBe (realAxioms - completeness) + select
  }

  it should "reach Cousin through the gluing, and the value through uniqueness" in {
    val gluing = force(chain.continuity.fact(Continuity.IntervalGluing)).conclusion
    Derivation.restingOn(fact(Integral.Exists), Set(gluing)) shouldBe Set(gluing)

    val underUniqueness = Set(fact(Integral.Exists).conclusion, fact(Integral.Gauge).conclusion)
    Derivation.restingOn(fact(Integral.HasUnique), underUniqueness) shouldBe underUniqueness

    val underTheorem = Set(fact(Integral.HasFundamental).conclusion, fact(Integral.Unique).conclusion)
    Derivation.restingOn(fact(Integral.Fundamental), underTheorem) shouldBe underTheorem
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
}
