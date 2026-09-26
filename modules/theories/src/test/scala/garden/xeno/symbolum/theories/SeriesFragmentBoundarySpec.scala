package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The series procedure attacked at the edges of its fragment, for the verification of Mycelium card
 * `d3fd8018` on 2026-09-26.
 *
 * A decision procedure has two obligations and `ConvergenceSpec` states them from the inside: it
 * answers in the fragment and refuses outside it. This file states them from the outside, with
 * series chosen because they **look** like members: a summand one letter away from a closed form,
 * a divergent series whose terms stay bounded, a factor that is zero written as a difference, a
 * value equal to the true one written in another spelling, and a value whose truth the theory
 * leaves open. For each, what is asserted is the one thing a caller may rely on: an answer is a
 * kernel theorem of exactly the goal or of its denial, resting on the chain's axioms and nothing
 * else, and anything else is a refusal whose standing does not claim a decision.
 */
class SeriesFragmentBoundarySpec extends AnyFlatSpec with Matchers {

  private val chain: Chain = Chain.standard
  private val procedure: Convergence =
    Convergence.construct(chain).fold(error => fail(error.message), identity)
  private val believed: Set[Term] = chain.widest.theory.axioms.toSet

  private def proposition(text: String): Term =
    chain.widest.proposition(text).fold(error => fail(s"$text: ${error.message}"), identity)

  /** What the procedure says about `text`, checked against the discipline above whatever it is. */
  private def answer(text: String): Either[LogicError, Kernel.Thm] = {
    val result = procedure.prove(text)
    result match {
      case Right(theorem) =>
        withClue(s"$text was answered with ${theorem.conclusion}: ") {
          theorem.conclusion shouldBe proposition(text)
          theorem.hypotheses shouldBe empty
          Derivation.axiomsOf(theorem).diff(believed) shouldBe empty
        }
      case Left(denied: Denied) =>
        // A denial carries its theorem only as a term, so what is checked is that the term is the
        // other answer to the same series, which is what makes it a denial rather than a change of
        // subject.
        withClue(s"$text was denied with ${denied.proved}: ") {
          denied.goal shouldBe proposition(text)
        }
      case Left(_) => ()
    }
    result
  }

  private def notDecided(text: String): LogicError =
    answer(text) match {
      case Right(theorem) => fail(s"$text was proved: ${theorem.conclusion}")
      case Left(error) =>
        withClue(s"$text was refused as a decision: ${error.message}\n") {
          error.standing should not be LogicError.Standing.Decided
        }
        error
    }

  "A divergent series whose terms stay bounded" should "be denied convergence, not granted it" in {
    // `(-1)^i` has partial sums 1, 0, 1, 0, ... which never grow: bounded, and divergent. The
    // magnitude of the ratio is exactly one, the boundary the geometric decision turns on.
    Vector(
      "?l:real. converges (Sum (\\i:num. Power (0 - (1:real)) i)) l",
      "converges (Sum (\\i:num. Power (0 - (1:real)) i)) 0",
      "?l:real. converges (Sum (\\i:num. Power ((2:real) / 2) i)) l",
      "?l:real. converges (Sum (\\i:num. Power (1 - (0:real)) i)) l"
    ).foreach { text =>
      answer(text) match {
        case Left(denied: Denied) =>
          denied.standing shouldBe LogicError.Standing.Decided
          chain.widest.show(denied.proved) should include("diverges")
        case other => fail(s"$text: expected a denial, got $other")
      }
    }
  }

  "The harmonic series and its alternating twin" should "be refused, neither granted nor denied" in {
    // The harmonic series diverges and the alternating one converges, and neither is in the
    // fragment; the pair is what separates a refusal from a guess, since a guess would have to get
    // one of the two wrong. The first two are the rational-function class, and the refusal must
    // name that; the alternating one is not a rational function, because the sign is a power.
    Vector(
      "?l:real. converges (Sum (\\i:num. inv (real_of_num (SUC i)))) l",
      "diverges (Sum (\\i:num. inv (real_of_num (SUC i))))"
    ).foreach { text =>
      notDecided(text).message should include("tends to one")
    }
    Vector(
      "?l:real. converges (Sum (\\i:num. Power (0 - (1:real)) i * inv (real_of_num (SUC i)))) l",
      "diverges (Sum (\\i:num. Power (0 - (1:real)) i * inv (real_of_num (SUC i))))"
    ).foreach(text => notDecided(text))
  }

  "A summand one letter away from a closed form" should "be refused rather than read as that form" in {
    // Each of these has the syntax of a member with the index where a constant must be. The first
    // two diverge (`i^i / i!` grows like `e^i`, `(i/2)^i` without bound); a procedure that matched
    // the shape without checking that the parameter is free of the index would prove them
    // convergent.
    Vector(
      "?l:real. converges (Sum (\\i:num. Power (real_of_num i) i / real_of_num (NUM_FACT i))) l",
      "?l:real. converges (Sum (\\i:num. Power (real_of_num i) i * Power ((1:real) / 2) i)) l",
      "?l:real. converges (Sum (\\i:num. real_of_num i * Power ((1:real) / 2) (SUC i))) l",
      "?l:real. converges (Sum (\\i:num. Power ((1:real) / 2) (i + i))) l"
    ).foreach(text => notDecided(text))
  }

  "A zero written as a difference" should "not let a divergence be carried through it" in {
    // `(1 - 1) * 3^i` is the zero series, which converges; `1 - 1` as a constant summand is the
    // same. Both are divergences only if the zero is misread as something else.
    Vector(
      "diverges (Sum (\\i:num. (1 - (1:real)) * Power (3:real) i))",
      "diverges (Sum (\\i:num. (1 - (1:real))))",
      "diverges (Sum (\\i:num. (c:real) * Power (3:real) i))"
    ).foreach(text => notDecided(text))
  }

  "A value equal to the true one in another spelling" should "never be refused as a decision" in {
    // `Sum (\i. (1/2)^i)` converges to `inv (1 - 1/2)`, which is two. Every value below is two in
    // this theory, so a `NotEqualTo` of standing `Decided` on any of them would be a decision
    // against a true claim. Proved or refused undecided are both acceptable; which one each gets
    // is printed, because it says how far the comparison reaches.
    Vector(
      "(2:real)", "(4:real) / 2", "(1:real) + 1", "inv ((1:real) / 2)", "inv (inv (2:real))",
      "2 * ((3:real) / 3)", "(1:real) / inv 2", "2 * (inv (3:real) * 3)", "(inv (0:real) + 2) - inv 0",
      "2 + 0 * inv (0:real)"
    ).foreach { value =>
        val text = s"converges (Sum (\\i:num. Power ((1:real) / 2) i)) ($value)"
        answer(text) match {
          case Right(_) => info(s"$value: proved")
          case Left(error) =>
            info(s"$value: refused, ${error.standing}: ${error.message}")
            withClue(s"$text: ") { error.standing should not be LogicError.Standing.Decided }
        }
      }
  }

  "A value whose truth the theory leaves open" should "not be refused as a decision either" in {
    // `inv 0` is unconstrained by the reals' sixteen axioms, so whether the series converges to
    // `2 + inv 0` is neither provable nor refutable here. `numeric` counts `inv` among the field
    // operations, so this is the one input where "both values are numbers" does not make differing
    // normal forms two different numbers.
    //
    // Found by this file on 2026-09-26 at `1bcad72b`: the answer was `NotEqualTo`, standing
    // `Decided`, and the assertion was held pending. `Convergence.numeric` now counts a reciprocal
    // or a divisor as a number only where LINARITH places it strictly on one side of nought, so
    // this is `ValueUnidentified`; the wrapper came off in the change that repaired it.
    val text = "converges (Sum (\\i:num. Power ((1:real) / 2) i)) (2 + inv (0:real))"
    val result = answer(text)
    result match {
      case Right(theorem) => fail(s"$text was proved: ${theorem.conclusion}")
      case Left(error)    => info(s"refused, ${error.standing}: ${error.message}")
    }
    result.left.toOption.map(_.standing) should not be Some(LogicError.Standing.Decided)
  }

  "A value that differs, written as numbers" should "stay a decision, which is the control for the two above" in {
    Vector("3", "4 / 3", "0 - 2").foreach { value =>
      val text = s"converges (Sum (\\i:num. Power ((1:real) / 2) i)) ($value:real)"
      answer(text) match {
        case Left(error: NotEqualTo) => error.standing shouldBe LogicError.Standing.Decided
        case other                   => fail(s"$text: expected NotEqualTo, got $other")
      }
    }
  }
}
