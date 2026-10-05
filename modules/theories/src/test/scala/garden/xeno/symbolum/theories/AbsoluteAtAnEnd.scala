package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * `abs` on `[0, 1]`, the function that separates a derivative relative to an interval from a
 * derivative: at every point of `[0, 1]` it has slope `1` relative to the interval, and at `0` it
 * has no derivative at all, because to the left of `0` it falls.
 *
 * Two specs need the pair and for two different reasons. `DerivativeSpec` spends it on
 * `DERIVATIVE_WITHIN_INTERIOR`, whose hypothesis `a < x` is what the pair refutes when dropped;
 * `IntegralSpec` spends it on the fundamental theorem, whose textbook form it detaches where the
 * two-sided form's hypothesis is false. Written once here so that the two cannot disagree about
 * what was derived.
 */
private[theories] final class AbsoluteAtAnEnd(chain: Chain) {

  private val derivative = chain.derivative
  private val logic = derivative.logic
  private val rules = logic.rules
  private val magnitude = chain.magnitude
  private val reals: Type = TyApp(Real.TypeName, Nil)

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => throw new IllegalStateException(error.message), identity)

  private def proposition(text: String): Term = force(derivative.proposition(text))
  private def real(text: String): Term = force(derivative.term(text, reals))
  private def assume(text: String): Kernel.Thm = force(LogicError.lift(Kernel.assume(proposition(text))))
  private lazy val linarith: Linarith = force(Linarith.construct(chain.order))
  private def lemma(text: String): Kernel.Thm = force(linarith.prove(text))
  private def at(theorem: Kernel.Thm, arguments: String*): Kernel.Thm =
    force(rules.specAll(theorem, arguments.toList.map(real)))
  private def mp(implication: Kernel.Thm, premises: Kernel.Thm*): Kernel.Thm =
    premises.foldLeft(implication)((acc, premise) => force(rules.mp(acc, premise)))
  private def variable(name: String): FVar = Term.variable(name, reals)
  private def magnitudeFact(name: String): Kernel.Thm = force(magnitude.fact(name))

  /** `|- <name> args = <its statement>`, reduced. */
  private def unfolded(name: String, arguments: List[Term]): Kernel.Thm =
    force(
      for {
        definition <- derivative.definition(name)
        equation <- Conv.unfold(definition, arguments)
        right <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
        normal <- Conv.betaNormalise(right)
        joined <- Conv.trans(equation, normal)
      } yield joined)

  private val absolute: Term = force(derivative.term("abs", Type.fun(reals, reals)))

  /**
   * `|- !x. 0 <= x /\ x <= 1 ==> derivative_within abs 0 1 x 1`. Inside the interval `abs` is the
   * identity, so the error of every admissible increment is zero; the radius is `1`.
   */
  lazy val relative: Kernel.Thm = {
    val x = variable("x")
    val e = variable("e")
    val h = variable("h")
    val inside = assume("(0:real) <= x:real /\\ x <= 1")
    val positive = assume("0 < e:real")
    val increment = assume("0 < abs (h:real) /\\ abs h < 1 /\\ (0:real) <= x:real + h /\\ x + h <= 1")
    val nonZero = force(rules.conjElim1(increment))
    val landed = force(rules.conjElim2(increment).flatMap(rules.conjElim2).flatMap(rules.conjElim1))
    val start = force(rules.conjElim1(inside))

    val atLanding = mp(at(magnitudeFact(Magnitude.OfNonNegative), "x:real + h:real"), landed)
    val atStart = mp(at(magnitudeFact(Magnitude.OfNonNegative), "x:real"), start)
    val error = "abs (x:real + h:real) - abs x - 1 * h"
    val zero = mp(
      at(lemma("!A:real B:real x:real h:real. A = x + h ==> B = x ==> A - B - 1 * h = 0"),
        "abs (x:real + h:real)", "abs (x:real)", "x:real", "h:real"),
      atLanding, atStart)
    val itself = mp(at(magnitudeFact(Magnitude.OfNonNegative), error),
      mp(at(lemma("!E:real. E = 0 ==> 0 <= E"), error), zero))
    val bound = mp(
      at(lemma("!M:real E:real e:real H:real. M = E ==> E = 0 ==> 0 < e ==> 0 < H ==> M < e * H"),
        s"abs ($error)", error, "e:real", "abs (h:real)"),
      itself, zero, positive, nonZero)

    val everyIncrement = force(rules.disch(increment.conclusion, bound).flatMap(rules.gen(h, _)))
    val onePositive = lemma("(0:real) < 1")
    val pair = force(rules.conjIntro(onePositive, everyIncrement))
    val radius = proposition(
      "?d:real. 0 < d /\\ (!h:real. 0 < abs h /\\ abs h < d /\\ (0:real) <= x:real + h /\\ x + h <= 1 ==> " +
        "abs (abs (x + h) - abs x - 1 * h) < e:real * abs h)")
    val predicate = logic.destExistsPredicate(radius).getOrElse(throw new IllegalStateException("not an existential"))
    val witnessed = force(rules.existsIntro(predicate, real("1:real"), pair))
    val statement = force(rules.disch(positive.conclusion, witnessed).flatMap(rules.gen(e, _)))

    val definition = unfolded(Derivative.WithinName, List(absolute, real("0:real"), real("1:real"), x, real("1:real")))
    val folded = force(Conv.sym(definition).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, statement))))
    force(rules.disch(inside.conclusion, folded).flatMap(rules.gen(x, _)))
  }

  /**
   * `|- ~(derivative abs 0 1)`. At tolerance `1`, whatever the radius `d`, the increment `-(d / 2)`
   * has error `d` against a bound of `d / 2`: the left of `0` falls where slope `1` says it rises.
   */
  lazy val noSlopeAtZero: Kernel.Thm = {
    val d = variable("d")
    val claim = proposition("derivative abs (0:real) 1")
    val supposed = force(LogicError.lift(Kernel.assume(claim)))
    val opened = force(LogicError.lift(Kernel.eqMp(unfolded(Derivative.DerivativeName,
      List(absolute, real("0:real"), real("1:real"))), supposed)))
    val radii = force(rules.spec(real("1:real"), opened).flatMap(rules.mp(_, lemma("(0:real) < 1"))))

    val body = assume("0 < d:real /\\ (!h:real. 0 < abs h /\\ abs h < d ==> abs (abs (0 + h) - abs 0 - 1 * h) < 1 * abs h)")
    val dPositive = force(rules.conjElim1(body))
    val serves = force(rules.conjElim2(body))
    val step = "0 - d:real / 2"
    val stepNegative = mp(at(lemma("!d:real. 0 < d ==> 0 - d / 2 <= 0"), "d:real"), dPositive)
    val stepSize = mp(at(magnitudeFact(Magnitude.OfNonPositive), step), stepNegative)
    val away = mp(at(lemma("!H:real d:real. H = -(0 - d / 2) ==> 0 < d ==> 0 < H"), s"abs ($step)", "d:real"),
      stepSize, dPositive)
    val close = mp(at(lemma("!H:real d:real. H = -(0 - d / 2) ==> 0 < d ==> H < d"), s"abs ($step)", "d:real"),
      stepSize, dPositive)
    val claimed = force(rules.spec(real(step), serves).flatMap(rules.mp(_, force(rules.conjIntro(away, close)))))

    val landed = s"0 + ($step)"
    val landedNegative = mp(at(lemma("!d:real. 0 < d ==> 0 + (0 - d / 2) <= 0"), "d:real"), dPositive)
    val atLanding = mp(at(magnitudeFact(Magnitude.OfNonPositive), landed), landedNegative)
    val atZero = mp(at(magnitudeFact(Magnitude.OfNonNegative), "0:real"), lemma("(0:real) <= 0"))
    val error = s"abs ($landed) - abs (0:real) - 1 * ($step)"
    val errorValue = mp(
      at(lemma("!A:real Z:real d:real. A = -(0 + (0 - d / 2)) ==> Z = 0 ==> A - Z - 1 * (0 - d / 2) = d"),
        s"abs ($landed)", "abs (0:real)", "d:real"),
      atLanding, atZero)
    val errorSize = mp(at(magnitudeFact(Magnitude.OfNonNegative), error),
      mp(at(lemma("!E:real d:real. E = d ==> 0 < d ==> 0 <= E"), error, "d:real"), errorValue, dPositive))
    val above = mp(
      at(lemma("!M:real E:real H:real d:real. M = E ==> E = d ==> H = -(0 - d / 2) ==> 0 < d ==> 1 * H <= M"),
        s"abs ($error)", error, s"abs ($step)", "d:real"),
      errorSize, errorValue, stepSize, dPositive)
    val itself = mp(at(lemma("!M:real H:real. M < H ==> H <= M ==> M < M"), s"abs ($error)", s"1 * abs ($step)"),
      claimed, above)
    val irreflexive = force(chain.reals.law("LT_IRREFLEXIVE"))
    val absurd = force(rules.spec(real(s"abs ($error)"), irreflexive).flatMap(rules.notElim(_, itself)))

    // `absurd` rests on the body at this `d`, which is what eliminating the existential discharges.
    val falsity = force(rules.existsElim(radii, d, absurd))
    force(rules.notIntro(claim, falsity))
  }
}
