package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Finite distributions, the value of an experiment and Blackwell's easy direction, checked as
 * published and then spent.
 *
 * A statement matching its text says the right thing was proved and not that its hypotheses can be
 * met, so the two that are not trivially met are discharged here: `CHANNEL` at the identity garbling
 * on two signals, which turns `BLACKWELL_GARBLING` into an inequality with no hypothesis, and the
 * positive marginals of `VALUE_POSTERIOR` at a uniform experiment. `ARGMAX_UNIQUE` is discharged by
 * the essay's case, whose third value is the reader's rule at each of sixty-four signals. The facts
 * about distributions, marginals, channels, products and posteriors have every hypothesis met at
 * the uniform weight on two points, the posterior's positivity included.
 *
 * The essay's case E5 is the last test: three values, each a theorem with no hypothesis, and the
 * two comparisons the essay reads off them.
 */
class DecisionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private lazy val decision = chain.decision
  private lazy val steps = decision.steps

  private def published(name: String): Kernel.Thm = force(decision.fact(name))
  private def proposition(text: String): Term = force(decision.proposition(text))

  private lazy val threeAxioms = Set(
    force(chain.classical.axiom(Classical.Choice)).conclusion,
    force(chain.classical.axiom(Classical.Eta)).conclusion,
    force(chain.naturals.axiom(Natural.Infinity)).conclusion
  )

  "Every fact of the development" should "prove the statement it is published as" in {
    Decision.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        published(name).conclusion shouldBe proposition(text)
        published(name).hypotheses shouldBe empty
      }
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    decision.facts.keySet shouldBe Decision.Statements.map(_._1).toSet
  }

  it should "rest on choice, eta and infinity, and add no axiom" in {
    decision.facts.values.map(Derivation.axiomsOf).reduce(_ ++ _) shouldBe threeAxioms
    decision.theory.axioms shouldBe chain.complex.theory.axioms
  }

  it should "declare its six constants and no type" in {
    val declared = decision.theory.constants.keySet -- chain.complex.theory.constants.keySet
    declared shouldBe Set(Decision.MaximumName, Decision.ArgmaxName, Decision.DistributionName,
      Decision.ChannelName, Decision.ValueName, Decision.IndependentName)
    decision.theory.typeOperators shouldBe chain.complex.theory.typeOperators
  }

  /**
   * `CHANNEL 2 2 (\s t. COND (t = s) 1 0)`, the garbling that changes nothing: each row is the
   * indicator of its own signal, non-negative and summing to one by `SUM_COND_COUNT`.
   */
  private lazy val identityChannel: Kernel.Thm = {
    import steps.*
    import steps.kit.*
    val garbling = "(\\s:num. \\t:num. COND (t = s) (1:real) 0)"
    force(for {
      rows <- prop("!y:num. y < 2 ==> DISTRIBUTION 2 (\\t:num. COND (t = y) (1:real) 0)")
      each <- steps.every(rows) { (ys, yhs, _) =>
        val Y = v(ys(0))
        for {
          opened <- unfold(Decision.DistributionName, "2:num", s"\\t:num. COND (t = $Y) (1:real) 0")
          nonneg <- prop(s"!i:num. i < 2 ==> (0:real) <= COND (i = $Y) 1 0")
          signs <- steps.every(nonneg) { (is, _, g) =>
            val I = v(is(0))
            cases(s"$I = $Y")(
              on => at(fact("COND_TRUE"), s"$I = $Y ==> COND ($I = $Y) (1:real) 0 = 1").flatMap(mp(_, on))
                .flatMap(e => linAfter(Seq(e), Seq.empty, g)),
              off => at(fact("COND_FALSE"), s"~($I = $Y) ==> COND ($I = $Y) (1:real) 0 = 0").flatMap(mp(_, off))
                .flatMap(e => linAfter(Seq(e), Seq.empty, g))
            )
          }
          counted <- at(fact(Decision.SumCondCount),
            s"$Y < 2 ==> Sum (\\t:num. COND (t = $Y) (1:real) 0) 2 = 1 + (real_of_num 2 - 1) * 0").flatMap(mp(_, yhs(0)))
          total <- lin(Seq(counted), s"Sum (\\t:num. COND (t = $Y) (1:real) 0) 2 = 1")
          both <- conj(signs, total)
          back <- Conv.sym(opened)
          out <- LogicError.lift(Kernel.eqMp(back, both))
        } yield out
      }
      opened <- unfold(Decision.ChannelName, "2:num", "2:num", garbling)
      back <- Conv.sym(opened)
      out <- LogicError.lift(Kernel.eqMp(back, each))
    } yield out)
  }

  "Blackwell's easy direction" should "hold with nothing assumed at a garbling that is a channel" in {
    identityChannel.hypotheses shouldBe empty
    identityChannel.conclusion shouldBe proposition("CHANNEL 2 2 (\\s:num. \\t:num. COND (t = s) (1:real) 0)")
    val instance = force(steps.kit.at(published(Decision.Blackwell),
      "CHANNEL 2 2 (\\s:num. \\t:num. COND (t = s) (1:real) 0) ==> " +
        "VALUE (n:num) 2 (top:num) (prior:num->real) (\\y:num. \\t:num. Sum (\\s:num. (k:num->num->real) y s * " +
        "(\\s:num. \\t:num. COND (t = s) (1:real) 0) s t) 2) (u:num->num->real) <= VALUE n 2 top prior k u"))
    val detached = force(decision.logic.rules.mp(instance, identityChannel))
    detached.hypotheses shouldBe empty
    Derivation.axiomsOf(detached) shouldBe threeAxioms
  }

  "The posterior form" should "agree with the value at an experiment whose every signal has positive probability" in {
    import steps.*
    import steps.kit.*
    val positive = force(for {
      each <- prop("!s:num. s < 2 ==> 0 < Sum (\\y:num. (\\y:num. (1:real) / 2) y * (\\y:num. \\s:num. (1:real) / 2) y s) 2")
      out <- steps.every(each) { (_, _, g) =>
        for {
          constant <- at(fact("SUM_CONSTANT"), "Sum (\\y:num. (1:real) / 2 * (1 / 2)) 2 = real_of_num 2 * ((1:real) / 2 * (1 / 2))")
          b0 <- fact("NUM_REAL_BIT0")
          b1 <- fact("NUM_REAL_BIT1")
          one <- fact("NUM_REAL_ONE")
          out <- rewriting(Seq(constant), g)(h => rewriting(Seq(b0, b1, one), h)(linarith.prove))
        } yield out
      }
    } yield out)
    val instance = force(steps.kit.at(published(Decision.ValueByPosterior),
      "(!s:num. s < 2 ==> 0 < Sum (\\y:num. (\\y:num. (1:real) / 2) y * (\\y:num. \\s:num. (1:real) / 2) y s) 2) ==> " +
        "VALUE 2 2 (top:num) (\\y:num. (1:real) / 2) (\\y:num. \\s:num. (1:real) / 2) (u:num->num->real) = " +
        "Sum (\\s:num. Sum (\\y:num. (\\y:num. (1:real) / 2) y * (\\y:num. \\s:num. (1:real) / 2) y s) 2 * " +
        "Maximum (\\a:num. Sum (\\y:num. (\\y:num. (1:real) / 2) y * (\\y:num. \\s:num. (1:real) / 2) y s * " +
        "inv (Sum (\\z:num. (\\y:num. (1:real) / 2) z * (\\y:num. \\s:num. (1:real) / 2) z s) 2) * u a y) 2) top) 2"))
    val detached = force(decision.logic.rules.mp(instance, positive))
    detached.hypotheses shouldBe empty
  }

  private val Uniform = "(\\y:num. (1:real) / 2)"
  private val UniformRows = "(\\y:num. \\s:num. (1:real) / 2)"
  private val Identity = "(\\s:num. \\t:num. COND (t = s) (1:real) 0)"

  /** `DISTRIBUTION 2 (\y. 1/2)`: a half is non-negative, and two halves are one by `SUM_CONSTANT`. */
  private lazy val uniform: Kernel.Thm = {
    import steps.*
    import steps.kit.*
    force(for {
      opened <- unfold(Decision.DistributionName, "2:num", Uniform)
      nonneg <- prop("!i:num. i < 2 ==> (0:real) <= 1 / 2")
      signs <- steps.every(nonneg)((_, _, g) => linarith.prove(g))
      constant <- at(fact("SUM_CONSTANT"), s"Sum $Uniform 2 = real_of_num 2 * (1 / 2)")
      goal <- prop(s"Sum $Uniform 2 = 1")
      b0 <- fact("NUM_REAL_BIT0")
      b1 <- fact("NUM_REAL_BIT1")
      one <- fact("NUM_REAL_ONE")
      total <- rewriting(Seq(constant), goal)(h => rewriting(Seq(b0, b1, one), h)(linarith.prove))
      both <- conj(signs, total)
      back <- Conv.sym(opened)
      out <- LogicError.lift(Kernel.eqMp(back, both))
    } yield out)
  }

  /** `CHANNEL 2 2 (\y s. 1/2)`: every row is [[uniform]]. */
  private lazy val uniformChannel: Kernel.Thm = {
    import steps.*
    import steps.kit.*
    force(for {
      rows <- prop(s"!y:num. y < 2 ==> DISTRIBUTION 2 $Uniform")
      each <- steps.every(rows)((_, _, _) => Right(uniform))
      opened <- unfold(Decision.ChannelName, "2:num", "2:num", UniformRows)
      back <- Conv.sym(opened)
      out <- LogicError.lift(Kernel.eqMp(back, each))
    } yield out)
  }

  /** `published(name)` at `instance`, detached from each of `premises` in turn, with nothing left over. */
  private def discharged(name: String, instance: String, conclusion: String, premises: Kernel.Thm*): Unit =
    withClue(s"$name: ") {
      val specialised = force(steps.kit.at(published(name), instance))
      val out = premises.foldLeft(specialised)((thm, premise) => force(decision.logic.rules.mp(thm, premise)))
      // the kernel holds the instance beta-normal, so the text is read the way `at` reads it
      out.conclusion shouldBe force(steps.kit.prop(conclusion))
      out.hypotheses shouldBe empty
      Derivation.axiomsOf(out) shouldBe threeAxioms
    }

  "The facts about distributions" should "have every hypothesis met at the uniform weight on two points" in {
    import steps.*
    import steps.kit.*
    uniform.hypotheses shouldBe empty
    uniformChannel.hypotheses shouldBe empty
    val P = Uniform
    val K = UniformRows
    val order = force(prop("!i:num. i < 2 ==> (0:real) <= 1").flatMap(steps.every(_)((_, _, g) => linarith.prove(g))))
    val zeroBelowTwo = force(for {
      spelled <- nm("2").flatMap(chain.successor.spell)
      lt <- at(fact("NUM_ZERO_LT_SUC"), "0 < SUC (SUC 0)")
      back <- Conv.sym(spelled)
      out <- rw(back, lt)
    } yield out)
    zeroBelowTwo.conclusion shouldBe proposition("(0:num) < 2")
    val positive = force(for {
      goal <- prop(s"0 < Sum (\\y:num. $P y * $K y 0) 2")
      constant <- at(fact("SUM_CONSTANT"), "Sum (\\y:num. (1:real) / 2 * (1 / 2)) 2 = real_of_num 2 * ((1:real) / 2 * (1 / 2))")
      b0 <- fact("NUM_REAL_BIT0")
      b1 <- fact("NUM_REAL_BIT1")
      one <- fact("NUM_REAL_ONE")
      out <- rewriting(Seq(constant), goal)(h => rewriting(Seq(b0, b1, one), h)(linarith.prove))
    } yield out)

    val marginal = s"DISTRIBUTION 2 (\\s:num. Sum (\\y:num. $P y * $K y s) 2)"
    discharged(Decision.DistributionMarginal,
      s"DISTRIBUTION 2 $P ==> CHANNEL 2 2 $K ==> $marginal", marginal, uniform, uniformChannel)
    val composed = s"CHANNEL 2 2 (\\y:num. \\t:num. Sum (\\s:num. $K y s * $Identity s t) 2)"
    discharged(Decision.ChannelCompose,
      s"CHANNEL 2 2 $K ==> CHANNEL 2 2 $Identity ==> $composed", composed, uniformChannel, identityChannel)
    val monotone = s"Sum (\\i:num. $P i * (\\i:num. (0:real)) i) 2 <= Sum (\\i:num. $P i * (\\i:num. (1:real)) i) 2"
    discharged(Decision.ExpectationMonotone,
      s"DISTRIBUTION 2 $P ==> (!i:num. i < 2 ==> (\\i:num. (0:real)) i <= (\\i:num. (1:real)) i) ==> $monotone",
      monotone, uniform, order)
    val constant = s"Sum (\\i:num. $P i * (3:real)) 2 = 3"
    discharged(Decision.ExpectationConstant, s"DISTRIBUTION 2 $P ==> $constant", constant, uniform)
    val product = s"(\\t:num. $P (NUM_DIV t 2) * $P (NUM_MOD t 2))"
    discharged(Decision.DistributionProduct,
      s"DISTRIBUTION 2 $P ==> DISTRIBUTION 2 $P ==> DISTRIBUTION (2 * 2) $product",
      s"DISTRIBUTION (2 * 2) $product", uniform, uniform)
    discharged(Decision.ProductIndependent,
      s"DISTRIBUTION 2 $P ==> DISTRIBUTION 2 $P ==> INDEPENDENT 2 2 $product",
      s"INDEPENDENT 2 2 $product", uniform, uniform)
    val posterior = s"DISTRIBUTION 2 (\\y:num. $P y * $K y 0 * inv (Sum (\\z:num. $P z * $K z 0) 2))"
    discharged(Decision.PosteriorDistribution,
      s"DISTRIBUTION 2 $P ==> CHANNEL 2 2 $K ==> (0:num) < 2 ==> 0 < Sum (\\y:num. $P y * $K y 0) 2 ==> $posterior",
      posterior, uniform, uniformChannel, zeroBelowTwo, positive)
    val linear =
      s"Sum (\\i:num. $P i * ((2:real) * real_of_num i + 3 * (\\i:num. (1:real)) i)) 2 = " +
        s"2 * Sum (\\i:num. $P i * real_of_num i) 2 + 3 * Sum (\\i:num. $P i * (\\i:num. (1:real)) i) 2"
    discharged(Decision.ExpectationLinear, linear, linear)
  }

  /**
   * The essay's case E5, `docs/adr/0063`: `7/20` with the signal alone, `9/16` with the frame on
   * average, `1/8` for the same reader on new tasks. Recomputed outside the kernel on 2026-10-22 with
   * exact fractions, by the essay's `sim.py` and by a second script written from its description,
   * and the three agree; no tie for the optimal action at any of the sixty-four signals.
   */
  "The essay's case E5" should "have the three values it prints, each a theorem with nothing assumed" in {
    val values = force(EssayCase.derive(decision, chain.successor))
    Seq(values.empty -> EssayCase.Empty, values.average -> EssayCase.Average, values.newTask -> EssayCase.NewTask)
      .foreach { case (theorem, text) =>
        withClue(s"$text: ") {
          // read with its redexes contracted: the new-task value applies the model's lambdas to the
          // signal, and the theorem is stated as the kernel holds it, beta-normal
          theorem.conclusion shouldBe force(steps.kit.prop(text))
          theorem.hypotheses shouldBe empty
          Derivation.axiomsOf(theorem) shouldBe threeAxioms
        }
      }
    // what the essay reads off them: the frame helps on average, as Blackwell says, and hurts on new tasks
    val linarith = force(Linarith.construct(chain.magnitude.order))
    force(linarith.prove(proposition("(7:real) / 20 <= 9 / 16")))
    force(linarith.prove(proposition("(1:real) / 8 < 7 / 20")))
  }
}
