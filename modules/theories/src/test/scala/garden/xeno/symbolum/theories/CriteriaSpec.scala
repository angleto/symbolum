package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The convergence criteria in both directions, spent on series a reader can name.
 *
 * `LimitSpec` already asserts that every published fact proves the statement it is published as.
 * What it cannot say is whether the statements are **usable**: an implication nobody can detach
 * reads exactly like a fact. So every criterion here is detached at a concrete series with nothing
 * left assumed, and the one that decides the negative half is detached at the series whose
 * divergence nobody disputes.
 *
 * And a hypothesis a criterion carries is shown to be load-bearing where that costs one derivation:
 * `SUM_SCALE_DIVERGES` asks that the factor be non-zero, and at zero the scaled series converges
 * while the unscaled one diverges.
 */
class CriteriaSpec extends AnyFlatSpec with Matchers {

  private val chain: Chain = Chain.standard
  private val limit: Limit = chain.limit
  private val logic: Logic = chain.logic
  private val rules: Rules = logic.rules
  private val real: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val sequences: Type = Type.fun(numbers, real)

  private def force[A](result: Either[LogicError, A]): A =
    result.fold(error => fail(error.message), identity)

  private val linarith: Linarith = force(Linarith.construct(chain.order))

  private def term(text: String, ty: Type): Term = force(chain.widest.term(text, ty))
  private def proposition(text: String): Term = force(chain.widest.proposition(text))
  private def fact(name: String): Kernel.Thm = force(limit.fact(name))

  /** `predicate`, a lambda over the reals written as text, at `value`. */
  private def at(predicate: String, value: Term): Term =
    force(
      LogicError
        .lift(Term.app(term(predicate, Type.fun(real, Type.Bool)), value))
        .flatMap(Conv.betaNormalise)
        .flatMap(Limit.rightOf))

  /** `abs q = q` or `abs q = -q` for a numeral `q`, by its sign. */
  private def sizeOf(q: Term): Kernel.Thm =
    linarith.prove(at("\\x:real. 0 <= x", q)) match {
      case Right(nonNegative) =>
        force(rules.spec(q, force(chain.magnitude.fact(Magnitude.OfNonNegative))).flatMap(rules.mp(_, nonNegative)))
      case Left(_) =>
        val nonPositive = force(linarith.prove(at("\\x:real. x <= 0", q)))
        force(rules.spec(q, force(chain.magnitude.fact(Magnitude.OfNonPositive))).flatMap(rules.mp(_, nonPositive)))
    }

  /** A comparison about `abs q`, from its size, with `abs q` an atom to LINARITH. */
  private def aboutSize(q: Term, comparison: String): Kernel.Thm = {
    val size = sizeOf(q)
    val magnitude = force(Limit.destructEquation(size))._1
    force(
      logic
        .mkImp(size.conclusion, at(comparison, magnitude))
        .flatMap(linarith.prove)
        .flatMap(rules.mp(_, size)))
  }

  /**
   * `diverges (Sum (\i. 1))`, from the term test at `b = 1`: the negative control the whole half
   * needs. A `diverges` that held of nothing would satisfy every other assertion about it, and one
   * that held of everything would too; this is the series that must diverge.
   */
  "The term test" should "derive that the series of ones diverges, with nothing assumed" in {
    val one = term("1:real", real)
    val instance = force(
      rules
        .specAll(fact(Limit.TermTest), List(term("\\i:num. (1:real)", sequences), one, term("ZERO", numbers)))
        .flatMap(Limit.normalised))
    val n = Term.variable("n", numbers)
    val bound = force(
      linarith
        .prove("!a:real. a = 1 ==> 1 <= a")
        .flatMap(rules.spec(term("abs (1:real)", real), _))
        .flatMap(rules.mp(_, sizeOf(one)))
        .flatMap(rules.disch(proposition("NUM_LE ZERO (n:num)"), _))
        .flatMap(rules.gen(n, _)))

    val diverging = force(
      rules.mp(instance, force(linarith.prove("0 < (1:real)"))).flatMap(rules.mp(_, bound)))
    diverging.conclusion shouldBe proposition("diverges (Sum (\\i:num. (1:real)))")
    diverging.hypotheses shouldBe empty
  }

  it should "reach no supremum, because a divergence is read off the terms and not obtained" in {
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion
    Real.spent(fact(Limit.TermTest)) should not contain completeness
    Real.spent(fact(Limit.TermsVanish)) should not contain completeness

    // The convergence half does, through monotone convergence under the powers: the one place the
    // geometric series obtains a limit rather than carrying one it was handed.
    Real.spent(fact(Limit.GeometricConverges)) should contain(completeness)
  }

  /**
   * At one half the geometric series converges **to two**, by one specialisation and one step of
   * `Field`: the instance `LimitSpec` spent ninety lines of kernel calls on, and which named no
   * value.
   */
  "The geometric series" should "converge at one half to two" in {
    val half = term("(1:real) / 2", real)
    val converging = force(
      rules.spec(half, fact(Limit.GeometricConverges)).flatMap(rules.mp(_, aboutSize(half, "\\x:real. x < 1"))))
    val value = force(Limit.convergenceOf(converging))._2
    // `inv (1 - 1/2) = 2` is a cancellation, so `Field` proves it and charges `~(1 - 1/2 = 0)`,
    // which LINARITH discharges: the value is two with nothing assumed.
    val charged = force(
      Field
        .construct(chain.arithmetic)
        .flatMap(field => LogicError.lift(Term.eq(value, term("2:real", real))).flatMap(field.prove)))
    val two = charged.hypotheses.foldLeft(charged) { (theorem, condition) =>
      force(linarith.prove(condition).flatMap(met => rules.disch(condition, theorem).flatMap(rules.mp(_, met))))
    }
    two.hypotheses shouldBe empty

    val atTwo = force(Limit.rewriteWith(two, converging))
    atTwo.conclusion shouldBe proposition("converges (Sum (\\i:num. Power ((1:real) / 2) i)) 2")
    atTwo.hypotheses shouldBe empty
  }

  it should "diverge at two and at minus one, the second being a ratio of magnitude exactly one" in {
    Vector("2:real", "0 - (1:real)").foreach { written =>
      withClue(s"$written: ") {
        val q = term(written, real)
        val diverging = force(
          rules.spec(q, fact(Limit.GeometricDiverges)).flatMap(rules.mp(_, aboutSize(q, "\\x:real. 1 <= x"))))
        diverging.hypotheses shouldBe empty
        // Through the ratio test's other side, which is what the geometric divergence is published
        // as resting on.
        Derivation.restingOn(diverging, Set(fact(Limit.RatioDiverges).conclusion)) should have size 1
      }
    }
  }

  /**
   * The ratio test detached at the geometric series at one half, from index zero and at ratio one
   * half, with every hypothesis discharged: the ratio bound is an equation there, `POWER_SUC` and
   * `ABS_MUL` with the magnitude of one half.
   *
   * The instance is one the closed forms already settle, deliberately: what is under test is that
   * the lemma's three hypotheses can be met at once, which is what a hand derivation needs of it.
   * `Convergence` does not apply it, and `docs/adr/0041` says why.
   */
  "The ratio test" should "detach at a series with every hypothesis discharged" in {
    val half = term("(1:real) / 2", real)
    val terms = term("\\i:num. Power ((1:real) / 2) i", sequences)
    val instance = force(
      rules
        .specAll(fact(Limit.RatioTest), List(terms, half, term("ZERO", numbers)))
        .flatMap(Limit.normalised))

    val n = Term.variable("n", numbers)
    val powerAt = term("Power ((1:real) / 2) (n:num)", real)
    val next = force(rules.specAll(force(chain.series.fact(Series.PowerAtSuccessor)), List(half, n)))
    val product = force(rules.specAll(force(chain.magnitude.fact(Magnitude.Multiplicative)), List(half, powerAt)))
    val sized = force(Limit.rewriteInProposition(sizeOf(half), product))
    val opened = force(Conv.sym(next).flatMap(Limit.rewriteInProposition(_, sized)))
    val bound = force(
      Limit
        .destructEquation(opened)
        .flatMap(sides => rules.specAll(force(chain.order.fact(Order.LeOfEq)), List(sides._1, sides._2)))
        .flatMap(rules.mp(_, opened))
        .flatMap(rules.disch(proposition("NUM_LE ZERO (n:num)"), _))
        .flatMap(rules.gen(n, _)))

    val converging = force(
      rules
        .mp(instance, force(linarith.prove("0 <= (1:real) / 2")))
        .flatMap(rules.mp(_, force(linarith.prove("(1:real) / 2 < 1"))))
        .flatMap(rules.mp(_, bound)))
    converging.conclusion shouldBe proposition("?l:real. converges (Sum (\\i:num. Power ((1:real) / 2) i)) l")
    converging.hypotheses shouldBe empty
  }

  /**
   * `SUM_SCALE_DIVERGES` asks that the factor be non-zero, and at zero the claim without that
   * hypothesis is false: the geometric series at two diverges, and zero times it converges, to zero.
   * Both halves are derived, so the hypothesis is shown load-bearing rather than said to be.
   */
  "Scaling a divergence" should "need its non-zero factor, because at zero the scaled series converges" in {
    val two = term("2:real", real)
    val diverging = force(
      rules.spec(two, fact(Limit.GeometricDiverges)).flatMap(rules.mp(_, aboutSize(two, "\\x:real. 1 <= x"))))
    diverging.conclusion shouldBe proposition("diverges (Sum (\\i:num. Power (2:real) i))")

    // Zero times it: every partial sum is zero times one, so the partial sums are constantly zero.
    val zero = term("0:real", real)
    val n = Term.variable("n", numbers)
    val powers = term("\\i:num. Power (2:real) i", sequences)
    val scaled = force(
      rules.specAll(force(chain.series.fact(Series.Scaled)), List(zero, powers, n)).flatMap(Limit.normalised))
    val vanishes = force(
      Limit.rightOf(scaled).flatMap(right => LogicError.lift(Term.eq(right, zero))).flatMap(chain.ring.prove))
    val pointwise = force(Conv.trans(scaled, vanishes).flatMap(Conv.sym))
    val agree = force(rules.disch(proposition("NUM_LE ZERO (n:num)"), pointwise).flatMap(rules.gen(n, _)))
    val constant = force(rules.spec(zero, force(limit.constantSequence)))
    val series = term("Sum (\\i:num. 0 * Power (2:real) i)", sequences)
    val converging = force(
      rules
        .specAll(force(limit.eventually), List(force(Limit.convergenceOf(constant))._1, series, zero, term("ZERO", numbers)))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, agree))
        .flatMap(rules.mp(_, constant)))
    converging.conclusion shouldBe proposition("converges (Sum (\\i:num. 0 * Power (2:real) i)) 0")
    converging.hypotheses shouldBe empty
  }
}
