package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Taylor's theorem detached at a family whose members are all different, and read at the point it
 * names.
 *
 * `DerivativeSpec` detaches `TAYLOR` at `\k. exp`, where every order of the family is the same
 * function, so the index shift between `D k` and `D (SUC k)` is never exercised there: a statement
 * that said `derivative (D k) x (D k x)` would detach at the exponential just as well. Here the
 * family is the cube and its first two derivatives, written with `COND` on the order, and the
 * order of the expansion is one. On `[0, 1]` the textbook remainder then reads
 * `1 = (1 / 2!) * 6c`, whose only solution is `c = 1 / 3`, and that is what the kernel is made to
 * say: the detached theorem, rewritten by the recurrences and settled by `Field`, becomes
 * `?c. 0 < c /\ c < 1 /\ 1 = c * 3` with nothing assumed.
 *
 * What that is and is not evidence of. The theorem is a theorem, so it cannot be false; what could
 * be wrong is that it states something other than the Lagrange form. A remainder with `n!` where the
 * textbook has `(n + 1)!` would still detach and would read `1 = 6c`, so the point would be `1 / 6`,
 * still inside the interval: the interval cannot tell the two apart, and the value of the point can.
 * So the last assertion is that `Field` REFUSES the `1 / 6` reading of the same remainder, which is
 * the check that the instrument separating the two readings is actually able to separate them.
 *
 * Written for the verification of Mycelium card `4942ffdb`, 2026-09-27.
 */
class TaylorAtACubeSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private lazy val chain = Chain.standard
  private lazy val derivative = chain.derivative
  private lazy val logic: Logic = derivative.logic
  private lazy val rules: Rules = logic.rules
  private val reals: Type = TyApp(Real.TypeName, Nil)
  private val functions: Type = Type.fun(reals, reals)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private lazy val library = Library.of(chain)

  private def lemma(name: String): Kernel.Thm =
    library.entries.find(_.name == name).map(_.theorem).getOrElse(fail(s"no lemma $name"))
  private def fact(name: String): Kernel.Thm = force(derivative.fact(name))
  private def real(text: String): Term = force(derivative.term(text, reals))
  private def natural(text: String): Term = force(derivative.term(text, numbers))
  private def proposition(text: String): Term = force(derivative.proposition(text))
  private def opened(theorem: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(theorem.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, theorem))))
  private def mp(implication: Kernel.Thm, premises: Kernel.Thm*): Kernel.Thm =
    premises.foldLeft(implication)((current, premise) => force(rules.mp(current, premise)))
  private def rightOf(theorem: Kernel.Thm): Term =
    Term.destEq(theorem.conclusion).map(_._2).getOrElse(fail("an equation"))
  private def leftOf(theorem: Kernel.Thm): Term =
    Term.destEq(theorem.conclusion).map(_._1).getOrElse(fail("an equation"))
  private def implication(term: Term): (Term, Term) = logic.destImp(term).getOrElse(fail("an implication"))
  private def assumed(term: Term): Kernel.Thm = force(LogicError.lift(Kernel.assume(term)))

  private val Three = "SUC (SUC (SUC 0))"
  private val Two = "SUC (SUC 0)"
  private val One = "SUC 0"

  // The cube, `D 0`, and its slope from the power rule at exponent three: `D 1`.
  private lazy val cubeSlope: Kernel.Thm =
    opened(force(rules.specAll(fact(Derivative.Power), List(real("x:real"), natural(Two)))))
  // `D 1 = \u. 3 * Power u 2` is a product of a constant and the square; its slope by the product
  // rule, with the square's slope from the power rule at exponent two, is `D 2`.
  private lazy val constant: Term = real(s"real_of_num ($Three)")
  private lazy val squareSlope: Kernel.Thm =
    opened(force(rules.specAll(fact(Derivative.Power), List(real("x:real"), natural(One)))))
  private lazy val secondSlope: Kernel.Thm = {
    val constantSlope = force(rules.specAll(fact(Derivative.Constant), List(constant, real("x:real"))))
    val f = force(derivative.term(s"\\z:real. real_of_num ($Three)", functions))
    val g = force(derivative.term(s"\\y:real. Power y ($Two)", functions))
    opened(mp(force(rules.specAll(fact(Derivative.ProductRule),
      List(f, g, real("x:real"), real("0:real"), rightOf0(squareSlope)))), constantSlope, squareSlope))
  }
  /** The slope a `derivative f x s` theorem states. */
  private def rightOf0(theorem: Kernel.Thm): Term = theorem.conclusion match {
    case App(_, slope) => slope
    case other => fail(s"a derivative: ${derivative.show(other)}")
  }
  private def functionOf(theorem: Kernel.Thm): Term = theorem.conclusion match {
    case App(App(App(_, function), _), _) => function
    case other => fail(s"a derivative: ${derivative.show(other)}")
  }

  private val cube = s"Power y ($Three)"
  private val first = s"real_of_num ($Three) * Power y ($Two)"
  private val second = s"0 * Power y ($Two) + real_of_num ($Three) * (real_of_num ($Two) * Power y ($One))"
  private lazy val family: Term = force(derivative.term(
    s"\\k:num. \\y:real. COND (k = 0) ($cube) (COND (k = $One) ($first) ($second))",
    Type.fun(numbers, functions)))

  /** `|- !a b:real. COND guard a b = a` or `= b`, the guard decided by `proof`. */
  private def decided(guard: String, proof: Kernel.Thm, holds: Boolean): Kernel.Thm = {
    val name = if (holds) Classical.CondTrue else Classical.CondFalse
    val schema = Kernel.instType(Map(Classical.TypeVariable -> reals), force(chain.classical.fact(name)))
    val a = Term.variable("a", reals)
    val b = Term.variable("b", reals)
    val instance = force(rules.specAll(schema, List(force(derivative.proposition(guard)), a, b)))
    force(rules.mp(instance, proof).flatMap(rules.genAll(_, List(a, b))))
  }
  private lazy val conditionals: Vector[Rewrite.Rule] = force(Rewrite.Rule.all(logic, conditionalsTheorems))

  /** `|- t = t'` with every decided conditional in `t` gone. */
  private def decide(term: Term): Kernel.Thm = force(Rewrite.rewrite(conditionals, term))

  /** `|- goal[k]` from `|- goal[c]` and `|- c = k`. */
  private def carried(equation: Kernel.Thm, variable: FVar, goal: Term, atValue: Kernel.Thm): Kernel.Thm = {
    val zz = Term.variable("zz", variable.ty)
    val lambda = force(LogicError.lift(Term.abs(zz, force(LogicError.lift(Term.substitute(Map(variable -> zz), goal))))))
    val across = force(Conv.apTerm(lambda, equation))
    val (from, to) = Term.destEq(across.conclusion).getOrElse(fail("an equation"))
    val joined = force(Conv.sym(force(Conv.betaRoot(from))).flatMap(Conv.trans(_, across)).flatMap(Conv.trans(_, force(Conv.betaRoot(to)))))
    force(LogicError.lift(Kernel.eqMp(joined, atValue)))
  }

  /**
   * `|- !k x. NUM_LE k 1 ==> I x ==> P k x`, from `P c x` at `c = 0` and `c = 1`: the order is at
   * most one, so it is zero or one, and each case is carried back to `k`.
   */
  private def forEachOrder(hypothesis: Term)(atOrder: (Int, Term) => Kernel.Thm): Kernel.Thm = {
    val k = Term.variable("k", numbers)
    val x = Term.variable("x", reals)
    def open(term: Term, variable: Term): Term = {
      val predicate = logic.destForallPredicate(term).getOrElse(fail("a universal"))
      rightOf(force(Conv.betaRoot(force(LogicError.lift(Term.app(predicate, variable))))))
    }
    val body = open(open(hypothesis, k), x)
    val (bound, rest) = implication(body)
    val (interval, goal) = implication(rest)
    val atMostOne = assumed(bound)
    val split = mp(force(rules.specAll(lemma("NUM_LE_CASES"), List(k, natural(One)))), atMostOne)
    def at(value: Int, equation: Kernel.Thm): Kernel.Thm = {
      val c = natural(if (value == 0) "0" else One)
      val atValue = force(LogicError.lift(Term.substitute(Map(k -> c), goal)))
      carried(force(Conv.sym(equation)), k, goal, atOrder(value, atValue))
    }
    val zero = {
      val below = assumed(proposition(s"NUM_LT k ($One)"))
      val atMostZero = mp(force(rules.specAll(lemma("NUM_LE_OF_LT_SUC"), List(natural("0"), k))), below)
      at(0, mp(force(rules.spec(k, lemma("NUM_LE_ZERO"))), atMostZero))
    }
    val one = at(1, assumed(proposition(s"k = $One")))
    val cases = force(rules.disjElim(split, zero, one))
    val proved = force(rules.disch(interval, cases).flatMap(rules.disch(bound, _)).flatMap(rules.genAll(_, List(k, x))))
    proved.conclusion shouldBe hypothesis
    proved
  }

  /** The slope theorem of `D c`, for `c` zero or one. */
  private def slopeOf(order: Int): Kernel.Thm = if (order == 0) cubeSlope else secondSlope

  private lazy val detached: Kernel.Thm = {
    val instance = opened(force(rules.specAll(fact(Derivative.Taylor),
      List(family, real("0:real"), real("1:real"), natural(One)))))
    val (inside, afterInside) = implication(instance.conclusion)
    val (continuityHypothesis, afterContinuity) = implication(afterInside)
    val (slopeHypothesis, _) = implication(afterContinuity)

    val ordered = force(Linarith.construct(chain.order).flatMap(_.prove("(0:real) < 1")))
    ordered.conclusion shouldBe inside

    // `continuous (\y. COND (c = 0) ...) x`: the conditional under the binder decides to `D c`,
    // which has a slope and so is continuous.
    val continuity = forEachOrder(continuityHypothesis) { (order, goal) =>
      val lambda = goal match {
        case App(App(_, function), _) => function
        case other => fail(s"a continuity claim: ${derivative.show(other)}")
      }
      val equation = decide(lambda)
      rightOf(equation) shouldBe functionOf(slopeOf(order))
      val continuous = mp(force(rules.specAll(fact(Derivative.Continuous),
        List(functionOf(slopeOf(order)), real("x:real"), rightOf0(slopeOf(order))))), slopeOf(order))
      val result = force(Limit.rewriteInProposition(force(Conv.sym(equation)), continuous))
      result.conclusion shouldBe goal
      result
    }

    // `derivative (\y. COND (c = 0) ...) x (COND (SUC c = 0) ...)`: the function decides to `D c`
    // and the slope to `D (SUC c) x`, which is exactly what the power rule and the product rule
    // state. This is the step the exponential cannot exercise.
    val slopes = forEachOrder(slopeHypothesis) { (order, goal) =>
      val (function, slope) = goal match {
        case App(App(App(_, function), _), slope) => (function, slope)
        case other => fail(s"a derivative claim: ${derivative.show(other)}")
      }
      val functionEquation = decide(function)
      val slopeEquation = decide(slope)
      rightOf(functionEquation) shouldBe functionOf(slopeOf(order))
      rightOf(slopeEquation) shouldBe rightOf0(slopeOf(order))
      val result = force(Limit.rewriteInProposition(force(Conv.sym(slopeEquation)),
        force(Limit.rewriteInProposition(force(Conv.sym(functionEquation)), slopeOf(order)))))
      result.conclusion shouldBe goal
      result
    }

    mp(instance, ordered, continuity, slopes)
  }

  "Taylor's theorem" should "detach at the cube, order one, on [0, 1], with nothing assumed" in {
    // The family's three members are what the rules say they are, read before anything else.
    functionOf(cubeSlope) shouldBe force(derivative.term(s"\\y:real. $cube", functions))
    functionOf(secondSlope) shouldBe force(derivative.term(s"\\y:real. $first", functions))
    rightOf0(secondSlope) shouldBe real(second.replace("y", "x"))
    detached.hypotheses shouldBe empty
  }

  /** The remainder equation at a witness `c`, recurrences written out: `lhs = rhs` in `+ * inv` of numerals and `c`. */
  private lazy val recurrences: Vector[Rewrite.Rule] = force(Rewrite.Rule.all(logic,
    conditionalsTheorems ++ Vector("SUM_SUC", "SUM_ZERO", "POWER_SUC", "POWER_ZERO", "NUM_FACT_SUC", "NUM_FACT_ZERO",
      "NUM_REAL_MUL", "NUM_REAL_SUC", "NUM_REAL_ZERO").map(lemma)))
  private lazy val conditionalsTheorems: Vector[Kernel.Thm] = Vector(
    decided("(0:num) = 0", Conv.refl(natural("0")), holds = true),
    decided(s"$One = $One", Conv.refl(natural(One)), holds = true),
    decided(s"$One = 0", force(rules.spec(natural("0"), lemma("NUM_SUC_NOT_ZERO"))), holds = false),
    decided(s"$Two = 0", force(rules.spec(natural(One), lemma("NUM_SUC_NOT_ZERO"))), holds = false),
    decided(s"$Two = $One", force(rules.spec(natural(One), lemma("NUM_SUC_NOT_SELF"))), holds = false))

  private lazy val field: Field = force(Field.construct(chain.arithmetic))

  it should "name the Lagrange point of the cube, c = 1 / 3, and not the 1 / 6 an n! remainder would give" in {
    val c = Term.variable("c", reals)
    val predicate = logic.destExistsPredicate(detached.conclusion).getOrElse(fail("an existential"))
    val inside = rightOf(force(Conv.betaRoot(force(LogicError.lift(Term.app(predicate, c))))))
    val witness = assumed(inside)
    val low = force(rules.conjElim1(witness))
    val high = force(rules.conjElim2(witness).flatMap(rules.conjElim1))
    val remainder = force(rules.conjElim2(witness).flatMap(rules.conjElim2))
    val (lhs, rhs) = Term.destEq(remainder.conclusion).getOrElse(fail("the remainder equation"))

    val left = force(Rewrite.rewrite(recurrences, lhs))
    val right = force(Rewrite.rewrite(recurrences, rhs))
    // `1 = lhs` by the ring, `rhs = c * 3` by the field with the numeral denominator settled free.
    val one = force(LogicError.lift(Term.eq(rightOf(left), real("1:real"))).flatMap(chain.ring.prove))
    val three = force(LogicError.lift(Term.eq(rightOf(right), real("(c:real) * (1 + 1 + 1)"))).flatMap(field.prove))
    three.hypotheses shouldBe empty
    val equation = force(for {
      a <- Conv.sym(one)
      b <- Conv.sym(left)
      ab <- Conv.trans(a, b)
      abc <- Conv.trans(ab, remainder)
      abcd <- Conv.trans(abc, right)
      all <- Conv.trans(abcd, three)
    } yield all)
    val claim = proposition("?c:real. 0 < c /\\ c < 1 /\\ 1 = c * (1 + 1 + 1)")
    val body = force(rules.conjIntro(high, equation).flatMap(rules.conjIntro(low, _)))
    val claimPredicate = logic.destExistsPredicate(claim).getOrElse(fail("an existential"))
    val introduced = force(rules.existsIntro(claimPredicate, c, body))
    val lagrange = force(rules.existsElim(detached, c, introduced))
    lagrange.hypotheses shouldBe empty
    lagrange.conclusion shouldBe claim

    // The same point computed outside the kernel: 1 = (1 / 2!) * 6c at c = 1 / 3, inside (0, 1).
    val point = 1.0 / 3.0
    (1.0 / 2.0) * 6.0 * point shouldBe 1.0 +- 1e-12
    point should (be > 0.0 and be < 1.0)

    // And the instrument that separates the textbook remainder from the n! one can: `rhs = c * 6`
    // is refused, so a statement carrying the other factorial would have failed the step above.
    field.prove(force(LogicError.lift(Term.eq(rightOf(right), real("(c:real) * (1 + 1 + 1 + 1 + 1 + 1)"))))) should matchPattern {
      case Left(_) =>
    }
  }
}
