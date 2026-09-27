package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The integral's theorems with continuity relative to `[a, b]`, and the census that says no interval
 * theorem is left without its textbook form.
 *
 * `IntegralSpec` already compares every statement `Integral` publishes with its text. What is
 * asserted here is what it cannot see: that each relative form detaches, with nothing assumed, at a
 * function whose two-sided hypothesis is **false** at an end, which is the whole difference between
 * the two forms; that each costs what its two-sided form costs; and that the census of the library
 * finds no interval continuity hypothesis without a `_WITHIN` twin.
 */
class IntegralWithinSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val integral = chain.integral
  private def logic: Logic = integral.logic
  private def rules: Rules = logic.rules
  private val reals: Type = TyApp(Real.TypeName, Nil)

  private def fact(name: String): Kernel.Thm = force(integral.fact(name))
  private def real(text: String): Term = force(integral.term(text, reals))
  private def proposition(text: String): Term = force(integral.proposition(text))
  private lazy val linarith: Linarith = force(Linarith.construct(chain.order))
  private def lemma(text: String): Kernel.Thm = force(linarith.prove(text))
  private def opened(theorem: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(theorem.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, theorem))))
  private def at(theorem: Kernel.Thm, arguments: Term*): Kernel.Thm =
    opened(force(rules.specAll(theorem, arguments.toList)))
  private def mp(theorem: Kernel.Thm, premises: Kernel.Thm*): Kernel.Thm =
    premises.foldLeft(theorem)((acc, premise) => force(rules.mp(acc, premise)))

  private lazy val witness = new StepAtAnEnd(chain)
  private def step: Term = witness.step
  private val minusOne = "(0:real) - 1"

  /**
   * The step jumps at `0`, the right end of `[-1, 0]`, so `CONTINUOUS_INTEGRAL` cannot be detached at
   * it there, and `CONTINUOUS_INTEGRAL_WITHIN` is, with nothing left assumed. A relative hypothesis
   * that held only where the two-sided one does would make the new forms a renaming.
   */
  "The integral's relative forms" should "detach at a step on [-1, 0], where the two-sided hypothesis fails at 0" in {
    witness.refused.hypotheses shouldBe empty
    witness.refused.conclusion shouldBe proposition("~(continuous (\\y:real. COND (0 < y) (1:real) 0) 0)")

    val ordered = lemma(s"$minusOne <= 0")
    val exists = mp(at(fact(Integral.ContinuousHasWithin), step, real(minusOne), real("0:real")), ordered, witness.relative)
    exists.hypotheses shouldBe empty
    exists.conclusion shouldBe proposition(
      s"?i:real. has_integral (\\y:real. COND (0 < y) (1:real) 0) ($minusOne) 0 i")

    val named = mp(at(fact(Integral.ContinuousIntegralWithin), step, real(minusOne), real("0:real")), ordered, witness.relative)
    named.hypotheses shouldBe empty
    named.conclusion shouldBe proposition(
      s"has_integral (\\y:real. COND (0 < y) (1:real) 0) ($minusOne) 0 (integral (\\y:real. COND (0 < y) (1:real) 0) ($minusOne) 0)")
  }

  /**
   * At the jump itself: the integral from `-1` has, relative to `[-1, 0]`, the step's value `0` as its
   * slope at `0`. `DERIVATIVE_WITHIN_INTEGRAL` asks continuity at `0` and so says nothing there.
   */
  it should "give the integral its slope relative to [-1, 0] at the end where the step jumps" in {
    val slope = mp(
      at(fact(Integral.DerivativeWithinWithin), step, real(minusOne), real("0:real"), real("0:real")),
      witness.relative, lemma(s"$minusOne <= 0"), lemma("(0:real) <= 0"))
    slope.hypotheses shouldBe empty
    slope.conclusion shouldBe proposition(
      s"derivative_within (\\y:real. integral (\\y:real. COND (0 < y) (1:real) 0) ($minusOne) y) ($minusOne) 0 0 " +
        "(COND ((0:real) < 0) (1:real) 0)")

    val inside = mp(
      at(fact(Integral.DerivativeOfIntegralWithin), step, real(minusOne), real("0:real"), real("(0:real) - 1 / 2")),
      witness.relative, lemma(s"$minusOne < 0 - 1 / 2"), lemma("(0:real) - 1 / 2 < 0"))
    inside.hypotheses shouldBe empty
  }

  /**
   * Each relative form costs what its two-sided form costs: the extension is built from the order and
   * `COND`, which the choice under the integral already pays for, and the congruences read nothing
   * the definitions do not.
   */
  it should "cost what the two-sided forms cost" in {
    for ((relative, twoSided) <- Vector(
        Integral.ContinuousHasWithin -> Integral.ContinuousHas,
        Integral.ContinuousIntegralWithin -> Integral.ContinuousIntegral,
        Integral.DerivativeWithinWithin -> Integral.DerivativeWithin,
        Integral.DerivativeOfIntegralWithin -> Integral.DerivativeOfIntegral
      )) withClue(s"$relative: ") {
      Derivation.axiomsOf(fact(relative)) shouldBe Derivation.axiomsOf(fact(twoSided))
    }
  }

  /** The route, asserted rather than described: the extension, and the congruence that carries it back. */
  it should "carry the two-sided theorem back from the extension through the congruence" in {
    val extension = force(chain.continuity.fact(Continuity.Extension)).conclusion
    val carried = Set(extension, fact(Integral.HasCongruence).conclusion)
    Derivation.restingOn(fact(Integral.ContinuousHasWithin), carried) shouldBe carried
    val slopes = Set(extension, fact(Integral.WithinCongruence).conclusion)
    Derivation.restingOn(fact(Integral.DerivativeWithinWithin), slopes) shouldBe slopes
  }

  /**
   * The census the verification of card 6257d0da asked for, and it is structural rather than
   * textual: a fact is counted when one of its antecedents is `!x. p x ==> ... ==> continuous f x`,
   * a two-sided continuity hypothesis over a set of points, and for each such fact the library must
   * hold one named with `_WITHIN` appended whose statement names `continuous_within`. The chain of
   * implications inside the hypothesis is followed to its end: the first version looked at one
   * step and missed `TAYLOR`'s `!v w. v <= u ==> a <= w /\ w <= b ==> continuous (f v) w`, which
   * landed the night this was written. The textual
   * reading this replaces also counted `CONTINUOUS_LINEAR` and `DERIVATIVE_CONTINUOUS`, whose
   * continuity is at one point and asks nothing of an interval.
   *
   * What it does not count: a two-sided **derivative** over an interval, which is the same kind of
   * excess one notion over and has the census below, written for card 3caa8541.
   *
   * A fact without its twin is listed in `Pending` with the card that owes it, and the list is held
   * both ways: a pending entry that has its twin fails, so the entry is removed when the card lands.
   * Non-vacuity, asserted beside it: the census finds as many facts as the assertion below says, so a
   * selector that matched nothing could not pass it.
   */
  "Every interval theorem" should "have a textbook form, named with _WITHIN, stated with continuous_within" in {
    val library = Library.of(chain)
    val names = library.entries.map(_.name).toSet
    def strip(t: Term): Term = Logic.stripForall(t).map(_._2).getOrElse(t)
    def antecedents(t: Term): Vector[Term] = logic.destImp(t) match {
      case Some((first, rest)) => first +: antecedents(rest)
      case None => Vector.empty
    }
    def concludes(t: Term, name: String): Boolean = t match {
      case App(App(Const(`name`, _), _), _) => true
      case _ => false
    }
    def mentions(t: Term, name: String): Boolean = t match {
      case Const(`name`, _) => true
      case App(f, x) => mentions(f, name) || mentions(x, name)
      case Abs(_, body) => mentions(body, name)
      case _ => false
    }
    def conclusionOf(t: Term): Term = logic.destImp(t).map { case (_, rest) => conclusionOf(rest) }.getOrElse(t)
    def overAnInterval(hypothesis: Term): Boolean =
      Logic.stripForall(hypothesis).exists { case (bound, body) =>
        bound.nonEmpty && logic.destImp(body).isDefined && concludes(conclusionOf(body), Continuity.Continuous)
      }
    // Empty since 2026-09-27, when `TAYLOR_WITHIN` landed for card `3b7c74be`, the one entry there was.
    val Pending: Map[String, String] = Map.empty
    val twoSided = library.entries.filter(entry =>
      antecedents(strip(entry.theorem.conclusion)).exists(overAnInterval)).map(_.name).distinct

    // 16 since 2026-09-27: `CAUCHY_MEAN_VALUE` asks two-sided continuity on [a, b] of both functions,
    // and `CAUCHY_MEAN_VALUE_WITHIN` landed with it.
    twoSided.size shouldBe 16
    val missing = twoSided.filterNot(name => names.contains(s"${name}_WITHIN"))
    withClue(s"two-sided interval facts with no _WITHIN twin and no card owing one: ${missing.mkString(", ")}\n") {
      missing.toSet shouldBe Pending.keySet
    }
    twoSided.filterNot(Pending.contains).foreach { name =>
      val twin = library.entries.find(_.name == s"${name}_WITHIN").map(_.theorem.conclusion).getOrElse(fail(name))
      withClue(s"${name}_WITHIN: ") { mentions(twin, Continuity.ContinuousWithin) shouldBe true }
    }
  }

  /**
   * The same census one notion over, which card 3caa8541 asked for: a fact is counted when one of
   * its antecedents is `!x. a <= x /\ x <= b ==> ... ==> derivative f x m`, a two-sided derivative at
   * every point of a **closed** interval, which asks at the ends about points outside it. A derivative
   * asked only inside, `a < x /\ x < b`, is the textbook's already and is not counted: that is
   * `MEAN_VALUE`'s and `TAYLOR`'s. Each counted fact must have a `_WITHIN` twin naming
   * `derivative_within`, and the count is pinned so that a selector matching nothing fails.
   */
  "Every rule asking a derivative on a closed interval" should "have a _WITHIN twin stated with derivative_within" in {
    val library = Library.of(chain)
    val names = library.entries.map(_.name).toSet
    def strip(t: Term): Term = Logic.stripForall(t).map(_._2).getOrElse(t)
    def antecedents(t: Term): Vector[Term] = logic.destImp(t) match {
      case Some((first, rest)) => first +: antecedents(rest)
      case None => Vector.empty
    }
    def conclusionOf(t: Term): Term = logic.destImp(t).map { case (_, rest) => conclusionOf(rest) }.getOrElse(t)
    def isNonStrict(t: Term): Boolean = t match {
      case App(App(Const(Real.NonStrictOrder, _), _), _) => true
      case _ => false
    }
    def closed(premise: Term): Boolean = logic.destConj(premise).exists { case (l, r) => isNonStrict(l) && isNonStrict(r) }
    def slopeOnClosed(hypothesis: Term): Boolean =
      Logic.stripForall(hypothesis).exists { case (bound, body) =>
        bound.nonEmpty && logic.destImp(body).exists { case (premise, _) => closed(premise) } &&
          (conclusionOf(body) match {
            case App(App(App(Const(Derivative.DerivativeName, _), _), _), _) => true
            case _ => false
          })
      }
    def mentions(t: Term, name: String): Boolean = t match {
      case Const(`name`, _) => true
      case App(f, x) => mentions(f, name) || mentions(x, name)
      case Abs(_, body) => mentions(body, name)
      case _ => false
    }
    val counted = library.entries.filter(entry =>
      antecedents(strip(entry.theorem.conclusion)).exists(slopeOnClosed)).map(_.name).distinct

    withClue(s"counted: ${counted.mkString(", ")}\n") { counted.size shouldBe 6 }
    val missing = counted.filterNot(name => names.contains(s"${name}_WITHIN"))
    withClue(s"two-sided derivative facts on a closed interval with no _WITHIN twin: ${missing.mkString(", ")}\n") {
      missing shouldBe empty
    }
    counted.foreach { name =>
      val twin = library.entries.find(_.name == s"${name}_WITHIN").map(_.theorem.conclusion).getOrElse(fail(name))
      withClue(s"${name}_WITHIN: ") { mentions(twin, Derivative.WithinName) shouldBe true }
    }
  }
}
