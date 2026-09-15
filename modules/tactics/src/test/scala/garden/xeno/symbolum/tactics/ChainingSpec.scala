package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.checker.Check
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.*

/**
 * Two lemmas put together, which the README said nothing here did.
 *
 * The assertion that carries this file is not that these goals are provable. It is **which lemmas
 * were used and how many**, because the claim being falsified is about the number: `Prove.held`
 * already uses one lemma, so a test that only checked a theorem came back would have passed for
 * months before this existed. `Chaining.Outcome.Proved` carries the names for exactly that reason,
 * and every assertion below reads them.
 *
 * == The witness, and where it came from ==
 *
 * `0 < inv (x * x + 1)` is `INV_POSITIVE` over `ADD_NONNEG_LT`, and the obligations at the bottom
 * are `0 <= x * x`, which is `SQUARE_NONNEG` through the scan, and `0 < 1`, which is LINARITH. So
 * every layer of the arrangement takes part: the search, the library, the scan and a decision
 * procedure.
 *
 * It is a constructed witness rather than one found by scanning, and the difference is worth
 * recording because the scan was tried first and came back empty. What it asked was every
 * conditional lemma's own conclusion with the hypothesis dropped, and **most of those are not
 * theorems**: `NUM_DIVIDES a b /\ NUM_DIVIDES b a ==> a = b` with the hypothesis dropped is `a = b`,
 * which is false. A population chosen because it was easy to enumerate answered a question nobody
 * had asked.
 *
 * == And the reason that empty answer was read twice ==
 *
 * It was empty for two reasons at once, and only one of them was the population. `Chaining` also
 * looked its goal up in the index **with the goal's universals still on**, so the head of
 * `!x. 0 < x * x + 1` was the quantifier, every quantified goal fell in an empty bucket, and nothing
 * was ever matched. `Chaining.Outcome.NoRoute` is also the honest answer when the library really
 * holds nothing, so the broken index and the empty library said the same thing.
 *
 * What separated them was this file's witness: a goal whose two-lemma route was known **before** it
 * was asked. That is why the witness is constructed, and it is why the first assertion below names
 * the two lemmas rather than counting them.
 */
class ChainingSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard
  private lazy val prove: Prove =
    Prove.construct(chain).fold(error => fail(s"the prover does not build: $error"), identity)

  private def read(text: String): Term =
    chain.widest.proposition(text).fold(error => fail(s"$text: ${error.message}"), identity)

  private def chained(text: String): (Kernel.Thm, Vector[String]) = {
    val goal = read(text)
    prove.searchFor(goal) match {
      case Some(Chaining.Outcome.Proved(theorem, used)) =>
        withClue(s"the theorem must be the goal and rest on nothing: ${theorem.display} ") {
          theorem.conclusion shouldBe goal
          theorem.hypotheses shouldBe empty
        }
        (theorem, used)
      case other => fail(s"expected a chained proof of $text, got $other")
    }
  }

  "Two lemmas" should "be put together, and the pair named" in {
    val (_, used) = chained("!x:real. 0 < inv (x * x + 1)")
    used shouldBe Vector("INV_POSITIVE", "ADD_NONNEG_LT")
  }

  it should "be put together for a goal whose shape is a denial rather than an order" in {
    val (_, used) = chained("!x:real. ~(x * x + 1 = 0)")
    used shouldBe Vector("POSITIVE_NOT_ZERO", "ADD_NONNEG_LT")
  }

  "One lemma with its obligations discharged" should "be reported as one and not as two" in {
    // The assertion that keeps the two above from being vacuous. This goal is one lemma whose
    // obligations a decision procedure closes, so a `used` list that counted subgoals rather than
    // lemmas would say two here, and then "two lemmas were chained" above would mean nothing.
    val (_, used) = chained("!x:real. 0 < x * x + 1")
    used shouldBe Vector("ADD_NONNEG_LT")

    val (_, alsoOne) = chained("!x:real. !y:real. 0 <= (x * x) * (y * y)")
    alsoOne shouldBe Vector("MUL_NONNEG_BOTH")
  }

  "The scan" should "still answer alone where it can, and report no lemma chained" in {
    // `go` tries the leaf before any candidate, so a goal `Prove.held` settles comes back with an
    // empty list. That is the boundary between this file's claim and the one that already held.
    prove.searchFor(read("!x:real. 0 <= x * x")) match {
      case Some(Chaining.Outcome.Proved(_, used)) => used shouldBe empty
      case other => fail(s"the scan must still reach this: $other")
    }
  }

  "The prover" should "reach a chained goal through its own entry point" in {
    // `searchFor` is the measurement's door and this is the one a caller uses. Without this the
    // file could pass while nothing but a test ever ran the search.
    prove(read("!x:real. 0 < inv (x * x + 1)")).isRight shouldBe true
  }

  "The depth bound" should "stop a goal that needs three, and say so" in {
    // `inv (inv (x * x + 1))` is one lemma deeper than the witness, so the default must not reach it.
    prove.searchFor(read("!x:real. 0 < inv (inv (x * x + 1))")) match {
      case Some(Chaining.Outcome.Depleted(_, _)) => succeed
      case other => fail(s"the default bounds must stop this: $other")
    }

    // And it must be the **depth** that stops it, not the budget, which is a different claim and the
    // one this test was written to make. Asked again with expansions no question here comes near, so
    // the only bound left is the depth, and the refusal names it.
    val patient = Chaining(chain.widest.logic, Library.of(chain), Chaining.Bounds(depth = 2, expansions = 500))
    patient.prove(read("!x:real. 0 < inv (inv (x * x + 1))"), target => prove.directly(target).toOption) match {
      case Chaining.Outcome.Depleted(bound, at) =>
        bound shouldBe Chaining.Bound.Lemmas
        at shouldBe 2
      case other => fail(s"the depth must be what stops it: $other")
    }
  }

  it should "be raised by a caller who wants the third step, which is what makes it a bound" in {
    // The other half: the goal above is not out of reach, it is out of budget. A bound no setting
    // could pass would be a limit wearing a bound's name.
    //
    // **The count is not asserted here and the first version of this test asserted it wrongly.** The
    // leaf handed over is `prove`, which chains on its own, so a step this search delegates is a
    // step it does not report: it came back naming one lemma for a route that takes three, and the
    // reading "only one lemma was used" was false. What a nested search reports is what **it** did,
    // and that is a property of the arrangement rather than of the proof.
    val deeper = Chaining(chain.widest.logic, Library.of(chain), Chaining.Bounds(depth = 3, expansions = 80))
    val goal = read("!x:real. 0 < inv (inv (x * x + 1))")

    deeper.prove(goal, target => prove.directly(target).toOption) match {
      case Chaining.Outcome.Proved(theorem, used) =>
        theorem.conclusion shouldBe goal
        theorem.hypotheses shouldBe empty
        used should not be empty
      case other =>
        fail(s"a raised bound must reach it, or the default is not a budget but a ceiling: $other")
    }
  }

  "The order candidates are tried in" should "put what shrinks the goal ahead of what grows it" in {
    // The measurement that chose it, kept as an assertion because the obvious order is the other
    // one and `Apply.candidates` offers it. `DOUBLE_NEGATION` matches every goal and owes `~~goal`,
    // which is one obligation and is larger than the goal; the lemma that settles the goal owes two
    // that are smaller. Ordered by count the first is tried first, and a budget spent from the front
    // buys nothing.
    //
    // Asserted through the budget rather than by reading the order: at ten expansions the witness is
    // reached under this order and was not under the other, which is the difference that matters and
    // the only one a reader can check.
    val tight = Chaining(chain.widest.logic, Library.of(chain), Chaining.Bounds(depth = 2, expansions = 10))
    tight.prove(read("!x:real. 0 < x * x + 1"), target => prove.directly(target).toOption) match {
      case Chaining.Outcome.Proved(_, used) => used shouldBe Vector("ADD_NONNEG_LT")
      case other => fail(s"ten expansions must be enough under this order: $other")
    }
  }

  "A chained theorem" should "be replayed by the second checker, which is what makes a search believable" in {
    // The half of the arrangement the rest of this file cannot assert. Everything above checks what
    // `Chaining` says about its own answer, and `Chaining` is a search: untrusted here by the same
    // argument that keeps `modules/sat` unable to see the kernel. What makes a chained proof worth
    // anything is that a second reader walks the derivation and reaches the same sequent from the
    // same theory, and until this was written nothing did: `Replayed` is the checker's own corpus
    // and holds no chained proof, and it cannot hold one, because it lives in `modules/checker`
    // and `Chaining` is two modules above it. The dependency goes the other way — `tactics` takes
    // `checker % "test->test"` — so the replay of a chained proof belongs here and nowhere else.
    val (chained2, used) = chained("!x:real. 0 < inv (x * x + 1)")
    used should have length 2

    val replayed = Check.proof(chained2, chain.widest.theory) match {
      case Check.Holds(counted, _) => counted
      // `RestsOnUnvouched` is the verdict worth naming separately in the failure, because it is the
      // one this test exists for: a search that reached the goal through an axiom the theory does
      // not assert is a proof of somebody else's theory, and it is not a failed step.
      case other => fail(s"the checker did not accept a chained proof: $other")
    }

    // And the count is asserted against the one-lemma proof rather than against a literal, which is
    // what keeps the assertion from passing on a stub. `ADD_NONNEG_LT` is the second lemma of the
    // pair above, so its proof is a part of the chained one: a replay that walked the derivation
    // sees strictly more steps, and a replay that stopped at the top sees the same or fewer.
    val (oneLemma, alone) = chained("!x:real. 0 < x * x + 1")
    alone shouldBe Vector("ADD_NONNEG_LT")

    Check.proof(oneLemma, chain.widest.theory) match {
      case Check.Holds(fewer, _) => replayed should be > fewer
      case other => fail(s"the checker did not accept the one-lemma proof: $other")
    }
  }

  "The index" should "read the goal's head under its quantifiers, not the quantifier" in {
    // The defect this file's class comment records, asserted so that it cannot come back silently.
    // With the universals left on, every goal here falls in a bucket nothing is filed under and
    // every assertion above fails with `NoRoute`, which is also what an empty library says.
    Chaining.headOf(read("!x:real. 0 < x * x + 1")) should not be Some(Real.Order)
    val body = Logic.stripForall(read("!x:real. 0 < x * x + 1")).toOption.map(_._2).get
    Chaining.headOf(body) shouldBe Some(Real.Order)
  }
}
