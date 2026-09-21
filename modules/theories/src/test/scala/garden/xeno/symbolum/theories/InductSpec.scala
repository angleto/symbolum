package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Induction where the step is not an equation.
 *
 * The driver could drive one shape: rewrite both halves and close with `Ring`, which decides
 * equations. An audit of the Collatz conversion reported that as a blocker in those words — "the
 * induction driver proves only EQUATIONS" — and it is a real one: a statement about growth is an
 * inequality, and every inequality anybody wants by induction was outside it.
 *
 * The asymmetry was never in the rewriting. It was in what the induction hypothesis is **for**.
 * `proveWith` hands it to the step as a rewrite rule, which is right for an equation and impossible
 * for anything else, because `Sum f n <= Sum g n` is not a rule and `Rule.of` says so.
 * `proveAssuming` hands it over as a **fact**: the step goal is rewritten, the hypothesis goes on
 * the left of an arrow in front of it, the caller's procedure is asked for that implication, and
 * modus ponens takes the hypothesis back off.
 */
class InductSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val linarith = force(Linarith.construct(chain.order))

  private val recurrences = Vector(
    force(chain.series.fact(Series.AtZero)),
    force(chain.series.fact(Series.AtSuccessor))
  )

  "A statement whose step is an inequality" should "be proved by induction, which it could not be" in {
    // Both sides are sums of a constant, so the step is `S n + 1 <= T n + 2` from `S n <= T n`,
    // which is linear in the two sums read as atoms. That is the smallest honest case: the
    // hypothesis is used, and it is used as a fact rather than as a rewrite.
    val statement = force(
      chain.series.proposition("!n:num. Sum (\\i:num. 1) n <= Sum (\\i:num. 2) n")
    )

    val theorem = force(chain.induct.proveAssuming(statement, recurrences)(linarith.prove))

    theorem.conclusion shouldBe statement
    theorem.hypotheses shouldBe empty

    info(s"${Derivation.size(theorem)} inferences over ${Derivation.axiomsOf(theorem).size} axioms")
  }

  "An equation" should "still go through the driver that closes with the ring" in {
    // The guard against the new path quietly replacing the old one: `proveWith` is what an equation
    // wants, because there the hypothesis really is a rewrite and rewriting with it is what closes
    // the step.
    val statement = force(chain.series.proposition("!n:num. Sum (\\i:num. 0) n = 0"))

    force(chain.induct.prove(statement, recurrences)).conclusion shouldBe statement
  }

  "The induction hypothesis" should "win the redex against a recurrence that would take it apart" in {
    // Found by a consumer on 2026-09-11 and reported as "the driver refuses what `proveBy` proves
    // from the same three rules in a different order". `Rewrite.stepConv` is a depth conversion
    // over `firstConv`, so on the node `Sum f (SUC k)` the first applicable rule wins: with
    // `SUM_SUC` ahead of the hypothesis, the redex the hypothesis was for is taken apart before it
    // is reached, and the goal keeps no link at all to the step before.
    //
    // The refusal that came back named a residue carrying `Sum f k` and `Sum g k` with nothing
    // between them, which is a true report of a false identity and a wrong account of what
    // happened. That is the shape this repository keeps finding: the message is about the merits
    // and the cause is the machinery.
    //
    // Summation by parts over a run-length form, which is the consumer's own goal rather than one
    // chosen here to make the point.
    val recurrence = force(
      chain.series.proposition("!i:num. (Z:num->real) (SUC i) = (P:num->real) i * (Y:num->real) i")
    )
    val statement = force(
      chain.series.proposition(
        "!k:num. Sum (\\i:num. (Z:num->real) i - (Y:num->real) i) (SUC k) = " +
          "(Z:num->real) ZERO - (Y:num->real) k + " +
          "Sum (\\i:num. (Y:num->real) i * ((P:num->real) i - 1)) k"
      )
    )
    val assumed = force(LogicError.lift(Kernel.assume(recurrence)))

    val theorem = force(chain.induct.prove(statement, recurrences :+ assumed))

    theorem.conclusion shouldBe statement
    theorem.hypotheses.toVector shouldBe Vector(recurrence)

    info(s"${Derivation.size(theorem)} inferences over ${Derivation.axiomsOf(theorem).size} axioms")
  }

  "The step" should "be told which variable the driver opened, since it cannot be guessed" in {
    // The second half of what a consumer met on 2026-09-11, reported as two problems because it
    // fails in two different places. `Logic.stripForall` freshens every bound variable against
    // what is free, so a statement written about `n` is opened about `x`, and a step that builds a
    // term with the letter the caller wrote builds a term that does not occur in the goal. Nothing
    // complains there: the refusal arrives later from whichever procedure was handed the result,
    // saying something true about the merits and nothing about what happened.
    //
    // Asserted both ways round, because the trap is the second half. The variable is in the goal
    // and the caller's own letter is not, and a step holding only the goal would have to dig the
    // first back out by matching on the goal's shape, which is what every step in this repository
    // did until the record existed.
    val statement = force(chain.series.proposition("!n:num. Sum (\\i:num. 0) n = 0"))

    var seen: Option[FVar] = None
    val theorem = force(
      chain.induct.proveBy(
        statement,
        goal => chain.induct.settle(recurrences.flatMap(Rewrite.Rule.of(chain.logic, _).toOption))(goal, Vector.empty),
        opened =>
          seen = Some(opened.variable)

          Term.freeVariables(opened.goal) should contain(opened.variable)
          Term.freeVariables(opened.goal).map(_.name) should not contain "n"

          Rewrite.Rule
            .of(chain.logic, opened.hypothesis)
            .flatMap(rule =>
              chain.induct.settle(recurrences.flatMap(Rewrite.Rule.of(chain.logic, _).toOption))(
                opened.goal,
                Vector(rule)
              )
            )
      )
    )

    theorem.conclusion shouldBe statement
    seen.map(_.name) should not be Some("n")
  }

  "A step the caller's procedure cannot close" should "be refused rather than reported as false" in {
    // The question `Induct.afterRewriting` asks after the closer refuses, at the place a driver
    // asks it: a rule set that does not settle makes the closer fail in a way indistinguishable
    // from the claim being false, and the two send a reader to different places.
    val statement = force(
      chain.series.proposition("!n:num. Sum (\\i:num. 2) n <= Sum (\\i:num. 1) n")
    )

    chain.induct.proveAssuming(statement, recurrences)(linarith.prove).isLeft shouldBe true
  }

  "A step whose rules multiply the term" should "be refused as a defect and not as a limit" in {
    // `docs/adr/0037` end to end, at the one call site that spends its third outcome. The two
    // refusals `Induct.afterRewriting` can raise both say the rewriting did not finish and their
    // remedies are opposites: `NotNormalised` is settled by raising the step limit, and this one
    // gets worse the higher that limit goes, because what stopped it is a rule set that multiplies
    // the term. Before 2026-09-22 this case did not stop at all -- it is the shape that killed a
    // suite after an hour, held a thread at 540 s of processor, and exhausted the heap in four and
    // a half minutes, on three separate days.
    //
    // The rule is `!f n. Sum f n = Sum f n + Sum f n`, which no guard in `Rewrite.Rule.of`
    // reaches: the pattern has variables in it, so `Rule.reproduces` is not asked, and the left
    // side is an application and not a bare variable, so the other refusal does not apply either.
    val quantified = force(
      chain.series.proposition("!f:num->real. !n:num. Sum f n = Sum f n + Sum f n")
    )
    val rule = force(
      Rewrite.Rule.of(chain.series.logic, force(LogicError.lift(Kernel.assume(quantified))))
    )

    val goal = force(chain.series.proposition("Sum (\\i:num. 1) ZERO = Sum (\\i:num. 1) ZERO"))

    val refusal = Induct
      .afterRewriting(Vector(rule), goal)(_ => Left(NotOfForm("a closer that settles this", goal)))
      .swap
      .getOrElse(fail("the rewriting was expected to be refused"))

    withClue(s"${refusal.message}\n") {
      refusal shouldBe a[GrewPastCeiling]
    }

    // And the width it names is past the ceiling rather than an arbitrary number, which is what a
    // reader compares against `Rewrite.DefaultCeiling` to tell a rule set that multiplies from a
    // corpus that has outgrown the number.
    refusal match {
      case GrewPastCeiling(_, reached, allowed) =>
        allowed shouldBe Rewrite.DefaultCeiling
        reached should be > Rewrite.DefaultCeiling
      case other => fail(s"not the ceiling's refusal: $other")
    }
  }

}
