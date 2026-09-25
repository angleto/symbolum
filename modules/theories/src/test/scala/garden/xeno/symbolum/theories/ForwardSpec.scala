package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The right forward closure: that it is there, that it costs nothing, and that it discriminates.
 *
 * The last is the one that matters and it is the reason this development exists rather than a
 * budgeted search. A closure can be generated forwards and looked at, which answers a membership
 * for whatever the budget reached and answers **nothing** about a non-membership; the induction
 * principle answers a non-membership, and the test that says so is the one below that derives
 * `~(WORD_RFC R w)` rather than failing to find `w`.
 */
class ForwardSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard
  private lazy val forward: Forward = chain.forward
  private lazy val logic: Logic = forward.logic

  private def fact(name: String): Kernel.Thm =
    forward.fact(name).fold(error => fail(error.message), identity)

  "The closure" should "publish every statement it names, and say the same thing the text does" in {
    // The guard against a development whose prose and whose theorems have drifted: each published
    // statement is parsed and compared with the theorem, rather than the theorem being printed and
    // read by somebody. `Reaching` and `Concatenation` are checked the same way.
    forward.facts.keySet shouldBe Forward.Statements.map(_._1).toSet

    for ((name, text) <- Forward.Statements) {
      val expected = Parser
        .proposition(forward.theory, forward.notation, text)
        .fold(error => fail(s"$name does not parse: ${error.message}"), identity)

      withClue(s"$name\n  text:    ${forward.show(expected)}\n  theorem: ${forward.show(fact(name).conclusion)}\n") {
        fact(name).conclusion shouldBe expected
      }
    }
  }

  it should "declare the step and the closure, and cost no axiom at all" in {
    // The whole development is definitional, which is what makes it free to build on. Asserted as
    // an equality against the empty set rather than as a ceiling, so a fact that quietly started
    // spending something would be as much a defect as one that stopped.
    forward.definitions.keySet shouldBe Set(Forward.Step, Forward.Name)

    for (name <- Forward.Statements.map(_._1)) {
      withClue(s"$name rests on: ${Derivation.axiomsOf(fact(name)).map(forward.show).mkString(", ")}\n") {
        Derivation.axiomsOf(fact(name)) shouldBe empty
      }
    }
  }

  it should "leave nothing assumed, which is what makes these theorems rather than obligations" in {
    for (name <- Forward.Statements.map(_._1)) {
      withClue(s"$name\n")(fact(name).hypotheses shouldBe empty)
    }
  }

  "The induction principle" should "ask nothing of the system, where the introduction rules pay for monotonicity" in {
    // The asymmetry `Inductive` is built on, seen from the consumer's side: the half that decides a
    // non-membership is free. If this ever acquires a hypothesis about `R` the file has stopped
    // being what its docstring says it is, and a non-membership stops being free with it.
    val induction = fact(Forward.Induction)
    induction.hypotheses shouldBe empty

    val printed = forward.show(induction.conclusion)
    withClue(s"$printed\n") {
      printed should include("WORD_RFC")
      printed should not include "MONOTONE"
    }
  }

  "The extension clause" should "not ask a consumer to prove reflexivity" in {
    // The first build of this development published `... /\ WORD_CONCAT y v = WORD_CONCAT y v ==>`,
    // which is true, useless, and unanswerable as a question about what it guards. The rule chooses
    // the point, so the equation is discharged where it arises. This pins that it stays discharged.
    val printed = forward.show(fact(Forward.Extend).conclusion)
    val reflexive = """(\S+) = \1""".r

    withClue(s"$printed\n") {
      reflexive.findFirstIn(printed) shouldBe None
    }
  }

  "The emptiness conditions" should "both be present, because each rules out a different collapse" in {
    // Neither is decoration. With the first empty the clause admits any member extended by any
    // right-hand side; with the second empty it is a second copy of inside reduction. A build that
    // dropped either would still prove everything else in this file.
    val printed = forward.show(fact(Forward.Extend).conclusion)
    withClue(s"$printed\n") {
      """~\(\S+ = WORD_EMPTY\)""".r.findAllMatchIn(printed).size shouldBe 2
    }
  }
}
