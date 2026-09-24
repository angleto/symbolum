package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A goal's own hypotheses as facts, and the two things that could go wrong with it.
 *
 * The capability is `Context` and `Prove.underHypotheses`, and `docs/adr/0025` is the decision. What
 * has to be seen together is the pair: that a goal needing its own premise is **proved**, and that
 * what comes back rests on **nothing**. The whole of what this route relaxes is that a candidate may
 * carry a hypothesis while the search is running, so the theorem at the end is where that is paid
 * for.
 *
 * == What would make this file vacuous, which is the question to ask of a guard ==
 *
 * A context carrying no facts. Every assertion here about a proof would then be an assertion about
 * the prover as it already was, and would pass unchanged: a goal settled some other way reads
 * exactly like a goal settled with a premise. So the facts are counted first, and the witnesses are
 * goals the prover refuses **without** them, which was measured rather than assumed.
 *
 * The measurement is the perturbation `kit/baseline/perturb.sh` exists to make, and it was made on
 * 2026-09-18 over `248a4c4` plus this change: the one line in `Prove.apply` that asks the route was
 * taken out, everything else left standing, and this file run again. **The three witnesses failed
 * and the other three passed**, which is the shape to want: the structural assertions and the
 * negative control are about `Context` and about the refusal, so a perturbation of the wiring must
 * not move them, and a guard that went red there would be a guard about something else.
 */
final class ContextSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val prove: Prove = Prove.standard
  private val logic: Logic = force(prove.reals.logic.over(prove.reals.theory))

  private def read(text: String): Term = force(prove.reals.proposition(text))

  /** The theorem, checked against the goal as asked, which is what the route promises. */
  private def proved(text: String): Kernel.Thm = {
    val goal = read(text)
    val theorem = force(prove(goal)).theorem

    withClue(s"$text came back as ${theorem.display}: ") {
      theorem.conclusion shouldBe goal
      theorem.hypotheses shouldBe empty
    }

    theorem
  }

  /* ------------------------------------------------------------ what a context is */

  "A goal with an antecedent" should "hand over its premises as theorems, conjunctions taken apart" in {
    val goal = read("!x:real. !y:real. 0 < x /\\ 0 < y ==> 0 < inv x")
    val context = Context.of(logic, goal).getOrElse(fail("this goal has an antecedent"))

    // One antecedent and three facts: the conjunction and both halves. This is the count that keeps
    // the witnesses below from being vacuous, since with no facts the prover is the prover it was.
    context.assumed should have size 1
    context.facts.map(_.conclusion) should have size 3
    logic.destConj(context.assumed.head) should not be None

    // Each fact rests on the antecedent it came from and on nothing else, which is what
    // `Context.discharge` is going to pay for.
    context.facts.flatMap(_.hypotheses).distinct shouldBe context.assumed

    // And what is left to prove is no longer an implication, which is the whole move.
    logic.destImp(context.conclusion) shouldBe None
    context.generalising should have size 2
  }

  "A goal with no antecedent" should "hand over nothing, which is not a failure" in {
    Context.of(logic, read("!x:real. 0 <= x * x")) shouldBe None
  }

  /* ------------------------------------------------------------------ the witnesses */

  "A goal whose obligation is its own premise" should "be proved, and rest on nothing" in {
    // Two uses of `INV_POSITIVE`, which is `!x. 0 < x ==> 0 < inv x`. The first owes `0 < inv x`,
    // the second owes `0 < x`, and that last obligation is the goal's own hypothesis: no lemma in
    // this library proves `0 < x` of an arbitrary `x`, and there had better not be one.
    // `ChainingSpec`'s depth bound is read against the same outer shape,
    // `0 < inv ((x * x) * (y * y) + 1)`, which its default bounds refuse: there the positivity
    // under `inv` costs the lemmas that build it from squares, and here the premise supplies it.
    val text = "!x:real. 0 < x ==> 0 < inv (inv x)"
    val theorem = proved(text)
    val context = Context.of(logic, read(text)).getOrElse(fail("this goal has an antecedent"))

    // The assumption is not something the theorem rests on, which is the difference between
    // "proved" and "proved under an assumption" and the one confusion this route could produce.
    // `Derivation.restingOn` only reads a node carrying no hypotheses, and an assumption carries
    // itself, so it cannot appear.
    //
    // Asked together with the goal rather than alone, because an instrument that answered nothing
    // at all would report the same empty set: the goal is known to be in this derivation for a
    // reason independent of the assumption, so finding it is what says the instrument read.
    Derivation.restingOn(theorem, context.allowed + theorem.conclusion) shouldBe
      Set(theorem.conclusion)
  }

  it should "take the premise it needs out of a conjunction" in {
    proved("!x:real. !y:real. 0 < x /\\ 0 < y ==> 0 < inv x")
  }

  it should "use a premise that is itself an implication, which is a lemma owing its antecedent" in {
    // Nothing here knows this hypothesis is special: it is a fact with an antecedent, so `Apply`
    // peels it and owes `0 < x`, and the second premise settles that.
    proved("!x:real. !y:real. (0 < x ==> 0 < y) ==> 0 < x ==> 0 < inv y")
  }

  /* -------------------------------------------------------------- the negative control */

  "A conclusion that does not follow from its premises" should "still be refused, with the refusal the shape chose" in {
    // True premise, false conclusion under it: a route that proved this would be unsound rather
    // than merely eager. It is the assertion that says relaxing the hypothesis test did not relax
    // what a proof is.
    val goal = read("!x:real. 0 < x ==> 0 < inv (0 - x)")

    prove(goal) match {
      case Right(outcome) => fail(s"this must not be provable: ${outcome.theorem.display}")

      // And it is the message the goal's address chose, not one this route invented. `directly` is
      // the prover before either search, so the two refusals agreeing is the rule "a search may add
      // a theorem and must never take a refusal away" asserted rather than described.
      case Left(refusal) =>
        refusal.message shouldBe force(prove.directly(goal).swap).message
    }
  }
}
