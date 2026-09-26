package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The step `COND (0 < y) 1 0` on `[-1, 0]`, the function that separates continuity relative to an
 * interval from continuity: it is not continuous at `0`, where it jumps to the right, and it is
 * continuous relative to `[-1, 0]` at every point, being constant there.
 *
 * Two specs need the pair. `ContinuitySpec` spends it on `INTERMEDIATE_VALUE_WITHIN`, and
 * `IntegralWithinSpec` on the integral's relative forms, each detached where the two-sided form's
 * hypothesis is false. Written once here, as `AbsoluteAtAnEnd` is for the derivative, so that the
 * two cannot disagree about what was derived; it was inline in `ContinuitySpec` until the second
 * consumer arrived on 2026-09-26.
 */
private[theories] final class StepAtAnEnd(chain: Chain) {

  private val continuity = chain.continuity
  private def logic: Logic = continuity.logic
  private def rules: Rules = logic.rules
  private val reals: Type = TyApp(Real.TypeName, Nil)

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => throw new IllegalStateException(error.message), identity)

  private def real(text: String): Term = force(continuity.term(text, reals))
  private def proposition(text: String): Term = force(continuity.proposition(text))
  private lazy val linarith: Linarith = force(Linarith.construct(chain.order))
  private def lemma(text: String): Kernel.Thm = force(linarith.prove(text))
  private def opened(theorem: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(theorem.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, theorem))))

  /** The step `COND (0 < y) 1 0`, which both negative guards below spend. */
  val step: Term =
    force(continuity.term("\\y:real. COND (0 < y) (1:real) 0", Type.fun(reals, reals)))

  /** `|- COND (0 < at) 1 0 = 1` or `= 0`, from the evidence for the guard or against it. */
  def stepValue(at: String, evidence: Kernel.Thm, positive: Boolean): Kernel.Thm = {
    val name = if (positive) Classical.CondTrue else Classical.CondFalse
    val conditional =
      Kernel.instType(Map(Classical.TypeVariable -> reals), force(chain.classical.fact(name)))
    val guard = proposition(s"(0:real) < $at")
    force(rules.specAll(conditional, List(guard, real("1:real"), real("0:real"))).flatMap(rules.mp(_, evidence)))
  }

  /** `|- ~(continuous step 0)`: at tolerance one half, every radius holds a point where the step is one. */
  lazy val refused: Kernel.Thm = {
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
    refused
  }

  private lazy val steps = Continuity.Steps(logic, linarith, continuity.theory, continuity.notation,
    force(continuity.definition(Continuity.Continuous)))

  /** `|- COND (0 < t) 1 0 = 0` from `|- t <= 0`. */
  def flat(t: String, upper: Kernel.Thm): Kernel.Thm =
    stepValue(t, force(Within.notBelow(steps, chain.reals, "(0:real)", t, upper)), positive = false)

  /** `|- !x. -1 <= x /\ x <= 0 ==> continuous_within step (-1) 0 x`: constant on the interval. */
  lazy val relative: Kernel.Thm = {
    val within = force(continuity.definition(Continuity.ContinuousWithin))
    val x = Term.variable("x", reals)
    val y = Term.variable("y", reals)
    val e = Term.variable("e", reals)


    val inside = proposition("(0:real) - 1 <= x /\\ x <= 0")
    val assumedInside = force(LogicError.lift(Kernel.assume(inside)))
    val atX = flat("x:real", force(rules.conjElim2(assumedInside)))
    val positive = proposition("0 < e:real")
    val assumedPositive = force(LogicError.lift(Kernel.assume(positive)))
    val near = proposition("(0:real) - 1 <= y /\\ y <= 0 /\\ abs (y - x) < 1")
    val assumedNear = force(LogicError.lift(Kernel.assume(near)))
    val atY = flat("y:real", force(rules.conjElim2(assumedNear).flatMap(rules.conjElim1)))

    val zeroDistance = force(chain.limit.magnitude.fact(Magnitude.OfNonNegative)
      .flatMap(rules.spec(real("(0:real) - 0"), _)).flatMap(rules.mp(_, lemma("(0:real) <= 0 - 0"))))
    val same = force(rules.specAll(lemma("!m:real e:real. m = 0 - 0 ==> 0 < e ==> m < e"), List(real("abs ((0:real) - 0)"), e))
      .flatMap(rules.mp(_, zeroDistance)).flatMap(rules.mp(_, assumedPositive)))
    val target = proposition("abs (COND (0 < y:real) (1:real) 0 - COND (0 < x:real) (1:real) 0) < e:real")
    val rewritten = force(Rewrite.Rule.all(logic, Vector(atY, atX)).flatMap(Rewrite.rewrite(_, target)))
    val value = force(Conv.sym(rewritten).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, same))))

    val everyPoint = force(rules.disch(near, value).flatMap(rules.gen(y, _)))
    val pair = force(rules.conjIntro(lemma("(0:real) < 1"), everyPoint))
    val shape = force(logic.destExistsPredicate(proposition(
      "?d:real. 0 < d /\\ (!y:real. (0:real) - 1 <= y /\\ y <= 0 /\\ abs (y - x) < d ==> " +
        "abs (COND (0 < y) (1:real) 0 - COND (0 < x:real) (1:real) 0) < e:real)")).toRight(NotOfForm("an existential", x)))
    val witnessed = force(rules.existsIntro(shape, real("1:real"), pair))
    val statement = force(rules.disch(positive, witnessed).flatMap(rules.gen(e, _)))
    val unfolded = force(Conv.unfold(within, List(step, real("(0:real) - 1"), real("0:real"), x)))
    val normal = force(Conv.betaNormalise(force(Term.destEq(unfolded.conclusion).map(_._2).toRight(NotOfForm("an equation", x)))))
    val definition = force(Conv.trans(unfolded, normal))
    val relative = force(Conv.sym(definition).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, statement))))
    val everywhere = force(rules.disch(inside, relative).flatMap(rules.gen(x, _)))
    everywhere
  }
}
