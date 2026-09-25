package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A recurrence carried as a hypothesis, which is what induction is for before recursion exists.
 *
 * `2^t` is not **defined** here, although it could be: `Recursion` derives the recursion theorem
 * on the naturals and `Series` defines `Power` by it. This file declares the function instead, and what
 * it shows is that a missing definition need not block a development, which is the whole of it.
 *
 * A function from the naturals to the reals can be **declared**, which costs nothing to believe,
 * and its recurrence assumed. Every theorem then carries the recurrence on the left of the
 * turnstile, where a reader can see it and argue with it, which is what `docs/proving.md` says a
 * model's assumptions are for. Induction does the rest.
 *
 * == Why the chain runs naturals first and reals second ==
 *
 * The tactics are built over a `RealTheory`, so the reals have to be built over the naturals if
 * `Arithmetic`, `Ring` and `Order` are to see `num`. The other order builds a signature with both
 * types in it and tactics that cannot read half of it. `Chain` says the same of the whole chain, and
 * the reals are not its last link: every development after them is built over them in turn.
 */
class RecurrenceSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val num = TyApp("num", Nil)
  private val real = TyApp(Real.TypeName, Nil)

  private val classical = Classical.standard
  private val naturals = force(Natural.construct(classical))
  private val reals = force(
    force(Real.construct(classical.logic, naturals.theory))
      .extended(Vector.empty, Vector("pow" -> Type.fun(num, real)))
  )
  private val order = force(
    for {
      arithmetic <- Arithmetic.construct(reals)
      ring <- Ring.construct(arithmetic)
      built <- Order.construct(ring)
    } yield built
  )
  private val rules = reals.logic.rules

  "One signature" should "hold both types and the tactics that read them" in {
    reals.theory.typeOperators.keySet should contain allOf ("real", "num", "ind")
    // Nineteen since eta landed in `Classical.scala` on 2026-09-10.
    reals.theory.axioms.size shouldBe 19

    // Statable, which is the thing that was not true before the two developments could be chained.
    reals.show(force(reals.proposition("pow ZERO = 1"))) shouldBe "pow ZERO = 1"
    reals.show(force(reals.proposition("!t:num. pow (SUC t) = 2 * pow t"))) shouldBe
      "!x:num. pow (SUC x) = 2 * pow x"
  }

  "A claim about a function defined by a recurrence" should "be proved by induction from it" in {
    // The whole loop, with nothing defined by recursion and no axiom added. `pow` is declared, so
    // it says nothing; the two equations are assumed, so they travel; and induction turns them into
    // a statement about every `t`.
    val baseEquation = force(reals.proposition("pow ZERO = 1"))
    val stepEquation = force(reals.proposition("!t:num. pow (SUC t) = 2 * pow t"))
    val assumedBase = force(LogicError.lift(Kernel.assume(baseEquation)))
    val assumedStep = force(LogicError.lift(Kernel.assume(stepEquation)))

    val predicate = force(reals.term("\\t:num. 0 < pow t"))
    val instance = force(rules.spec(predicate, force(naturals.fact(Natural.Induction))))
    val opened = force(
      Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
    )

    val (premises, _) = reals.logic.destImp(opened.conclusion).get
    val (_, stepGoal) = reals.logic.destConj(premises).get

    // `0 <` as a term, so that a congruence can carry a proof of `0 < a` across `a = b`.
    val less = force(
      LogicError.lift(reals.theory.constant(Real.Order, Type.fun(real, Type.fun(real, Type.Bool))))
    )
    val positive = force(LogicError.lift(Term.app(less, force(reals.term("0")))))

    val base = force(
      Conv
        .sym(assumedBase)
        .flatMap(Conv.apTerm(positive, _))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, force(order.zeroLessOne))))
    )

    val stripped = force(Logic.stripForall(stepGoal))
    val t = stripped._1.head
    val (before, _) = reals.logic.destImp(stripped._2).get
    val assumedBefore = force(LogicError.lift(Kernel.assume(before)))

    val atT = force(
      LogicError.lift(
        Term.substitute(Map(Term.variable("t", num) -> t), force(reals.term("pow t:num")))
      )
    )
    val product = force(
      rules
        .specAll(force(reals.axiom("LT_MUL")), List(force(reals.term("2")), atT))
        .flatMap { instance =>
          rules.conjIntro(force(order.positive(2)), assumedBefore).flatMap(rules.mp(instance, _))
        }
    )
    val step = force(
      rules
        .spec(t, assumedStep)
        .flatMap(Conv.sym)
        .flatMap(Conv.apTerm(positive, _))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, product)))
    )
    val closed = force(rules.disch(before, step).flatMap(rules.gen(t, _)))

    val proved = force(rules.conjIntro(base, closed).flatMap(rules.mp(opened, _)))

    reals.show(proved.conclusion) shouldBe "!x:num. 0 < pow x"

    // And it rests on the recurrence and on nothing else. That is the point: the assumption is
    // visible in the theorem, which is what an axiom would not be.
    proved.hypotheses.map(reals.show).sorted shouldBe
      Vector("!x:num. pow (SUC x) = 2 * pow x", "pow ZERO = 1")
  }

  "The declared function" should "cost nothing to believe, which is why this is not an axiom" in {
    // Declaring is conservative: `pow` says exactly what its absence says, so the nineteen axioms
    // are still nineteen and the recurrence is a hypothesis rather than part of the theory.
    reals.theory.axioms.size shouldBe 19
    reals.theory.definitions.get("pow") shouldBe None
  }
}
