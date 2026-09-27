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
 * value equal to the true one written in another spelling, and a value equal to it only through
 * `inv 0 = 0`, which the chain proves and the procedure does not hold. For each, what is asserted is the one thing a caller may rely on: an answer is a
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

  "A value equal to the true one only through inv 0 = 0" should "be proved or refused without a decision" in {
    // The series converges to `2`, and `2 + inv 0` is `2` since the reals were constructed:
    // `inv 0 = 0` is a theorem of `Cut`, so the claim is TRUE. What no procedure here holds is
    // that theorem, so the two values differ as forms over the atom `inv 0` while being equal, and
    // the one thing a caller may not be told is that the claim was decided against. A proof is
    // welcome and `answer` checks it is exactly the goal.
    //
    // Found by this file on 2026-09-26 at `1bcad72b`: the answer was `NotEqualTo`, standing
    // `Decided`. `Convergence.numeric` then learned to count a reciprocal as a number only where
    // LINARITH places it strictly on one side of nought. This test also failed a PROOF until
    // 2026-09-27, when the claim was still thought to be open; card `8fb6da8b` took that branch out
    // once the construction had made the claim true.
    val text = "converges (Sum (\\i:num. Power ((1:real) / 2) i)) (2 + inv (0:real))"
    answer(text) match {
      case Right(theorem) => info(s"proved: ${theorem.conclusion}")
      case Left(error) =>
        info(s"refused, ${error.standing}: ${error.message}")
        error.standing should not be LogicError.Standing.Decided
    }
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

  // Second round of the verification of card `d3fd8018`, 2026-09-27, over the repair in `ba68dcbc`:
  // `Convergence.numeric` counts a reciprocal or a divisor as a number only where LINARITH places it
  // strictly on one side of nought. The attack is on the neighbours of the one case the repair was
  // written for. Every value in the first group is 2 in the constructed reals, where `inv 0 = 0` is
  // a theorem (the last test of this file), so the only wrong answer there is a decision that it is
  // not; a proof is right and a refusal that claims no decision is sound.
  private def outcome(text: String): String = answer(text) match {
    case Right(_)    => "proved"
    case Left(error) => s"${error.getClass.getSimpleName}, ${error.standing}"
  }

  private def series(value: String): String = s"converges (Sum (\\i:num. Power ((1:real) / 2) i)) ($value)"

  private def neverDecided(value: String): Unit = {
    val text = series(value)
    val result = answer(text)
    info(s"$value: ${result.fold(e => s"${e.getClass.getSimpleName}, ${e.standing}", _ => "proved")}")
    result match {
      case Right(_)    => ()
      case Left(error) =>
        withClue(s"$text: ${error.message}\n") { error.standing should not be LogicError.Standing.Decided }
    }
  }

  "A value that is 2 once a reciprocal of nought is read" should "never be refused as a decision" in {
    Vector(
      "2 + 1 / (0:real)", "2 + inv (1 - (1:real))", "2 + inv (inv (0:real))",
      "2 + inv (inv (2:real) - inv 2)", "2 + inv (2 * inv (2:real) - 1)", "2 + 0 * inv (0:real)",
      "2 + (3:real) / (1 - 1)", "(1:real) + 1 + inv (0 * 3)"
    ).foreach(neverDecided)
  }

  "A value that is 2 with every divisor placed" should "never be refused as a decision, and the plain one be proved" in {
    Vector(
      "4 * inv ((1:real) + 1)", "inv (1 - inv (2:real))", "inv (inv (3:real) + inv 6)",
      "2 * inv (inv (2:real) * 2)", "inv (inv (inv (inv (2:real))))"
    ).foreach(neverDecided)
    answer(series("4 * inv ((1:real) + 1)")).isRight shouldBe true
  }

  "A value that is not 2 over a divisor LINARITH places" should "still be a decision" in {
    Vector("inv ((1:real) + 1)", "3 * inv ((1:real) + 1)").foreach { value =>
      val text = series(value)
      info(s"$value: ${outcome(text)}")
      answer(text) match {
        case Left(error: NotEqualTo) => error.standing shouldBe LogicError.Standing.Decided
        case other                   => fail(s"$text: expected a decided NotEqualTo, got $other")
      }
    }
  }

  "A value that differs only inside a reciprocal" should "be answered by the discipline, whatever it is" in {
    // Not 2 in any reading: 3 + inv 0 is 3 in the construction, and the others are 3, 7 and 8.
    // What is recorded is which of a decision and a refusal each gets; a proof would be a kernel
    // theorem of a false statement, and `answer` checks the conclusion.
    Vector("3 + inv (0:real)", "1 + inv (inv (3:real) + inv 6)", "1 + inv (inv (2:real) * inv 3)",
      "inv (inv (8:real))").foreach { value =>
      val text = series(value)
      info(s"$value: ${outcome(text)}")
      answer(text).isRight shouldBe false
    }
  }

  "inv 0 = 0" should "be a theorem of the reals as the chain builds them, so the case above is not open" in {
    // `docs/adr/0053`: `inv` is `CUT_INV` and `real_zero` is `CUT_OF_RAT RAT_ZERO` by definition, and
    // `CUT_INV_ZERO` is proved. Unfolding the two aliases, as `Real.construct` does for the sixteen,
    // carries that fact to the reals' own names.
    val reals = Real.standard
    val cuts = Real.constructed.cuts
    val derived = for {
      inverse <- reals.definition(Real.Inverse)
      zero <- reals.definition(Real.Zero)
      rules <- Rewrite.Rule.all(cuts.logic, Vector(inverse, zero))
      conversion = Rewrite.normaliser(rules, Vector.empty, Ordering.by[Term, String](_.toString))
      statement <- reals.proposition("inv (0:real) = 0")
      unfolded <- conversion(statement)
      fact <- cuts.fact(Cut.InverseZero)
      back <- Conv.sym(unfolded)
      theorem <- LogicError.lift(Kernel.eqMp(back, fact))
    } yield (statement, theorem)
    derived match {
      case Left(error) => fail(error.message)
      case Right((statement, theorem)) =>
        theorem.conclusion shouldBe statement
        theorem.hypotheses shouldBe empty
        Derivation.axiomsOf(theorem).diff(reals.theory.axioms.toSet) shouldBe empty
        info(s"derived: ${reals.show(theorem.conclusion)}")
    }
  }
}
