package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The bridge into arithmetic, found rather than named, and what the search is allowed to claim.
 *
 * `docs/adr/0024` made a domain claim that reaches the foundation's constants settle when the
 * caller hands over the theorem carrying it across, and named the search as the next piece of work
 * with four conditions on it: bounded, reports what it used, refuses rather than guessing, and does
 * not make the accounting worse. `docs/adr/0027` is what it landed as and this file is what says so.
 *
 * The four assertions that carry those conditions are the four this file would be worth nothing
 * without, and each names what would make it vacuous:
 *
 *  - **found rather than named**, which is the acceptance criterion: the same claim
 *    `DomainTheorySpec` settles by naming `NUM_LT_NOT_LE` settles here with nothing named, and the
 *    report says which lemma carried it. Vacuous if the claim did not need a bridge at all, which
 *    is the assertion below it.
 *  - **a bridge reported is a bridge spent.** A foundation constant can sit where the decision
 *    never reads it, and then any lemma at all "settles" the claim and naming one would be
 *    inventing a reason. The claim with an inert `NUM_LT` in it comes back settled with **no**
 *    bridge, which is what says the report is about need rather than about order.
 *  - **cheapest rather than first**, which the published library cannot be asked on its own: what
 *    it holds is one derivation per statement, so any two candidates that both carry the claim
 *    differ in what they say and not only in what they cost. A second derivation of the **same**
 *    statement at a higher price is put in front of the first in a session library, sorting earlier
 *    by name, and the search is asked to pass it over. Nothing but the accounting separates them,
 *    which is what makes the assertion about price rather than about order.
 *  - **refuses rather than approximates**, with a claim whose arithmetic no single lemma supplies.
 */
class BridgingSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val job = TyApp("job", Nil)

  /**
   * The retry rule of `docs/adr/0024`, which is the case the record was decided on.
   *
   * One axiom, in the domain's own vocabulary except for the order it counts with: a job that was
   * abandoned had at least three attempts. The claim below is the contrapositive of it across the
   * two orders, and the whole of what it is missing is that `<` and `<=` are related.
   */
  private val retryRule: Domain = Domain(
    name = "the retry rule",
    typeOperators = Vector("job" -> 0),
    constants = Vector(
      "Attempts" -> Type.fun(job, TyApp(Natural.TypeName, Nil)),
      "Abandoned" -> Type.fun(job, Type.Bool)
    ),
    axioms = Vector(
      "AbandonedOnlyAfterThree" -> "!j:job. Abandoned j ==> NUM_LE 3 (Attempts j)"
    )
  )

  private lazy val retries: Domain.Built =
    force(Domain.build(chain.widest.theory, chain.widest.notation, retryRule))

  private lazy val published: Library = Library.of(chain)

  private lazy val logic: Logic = force(chain.classical.logic.over(chain.widest.theory))

  private lazy val cheapest: Kernel.Thm = published
    .named(Peano.BelowExcludesAtMost)
    .headOption
    .getOrElse(fail(s"${Peano.BelowExcludesAtMost} is what this route is built on and the library " +
      "no longer publishes it"))
    .theorem

  private def show(term: Term): String = Show.show(chain.widest.notation, term)

  private val retryClaim = "!j:job. NUM_LT (Attempts j) 3 ==> ~(Abandoned j)"

  "A domain claim reaching arithmetic" should "be settled by a bridge the caller did not name" in {
    // The acceptance criterion of the card, and the difference from `DomainTheorySpec`'s own version
    // of this claim is the argument list: there, `NUM_LT_NOT_LE` is handed over; here nothing is,
    // and the same theorem comes back.
    Bridging.settle(retries, chain.classical, published, retryClaim) match {
      case found @ Bridging.Found(Domain.Verdict.Settled(theorem, spending), bridges, considered, _) =>
        // Printed through the chain's own notation, where `DomainTheorySpec` prints the same
        // theorem through the classical extension's and gets `NUM_LT (Attempts x) (NUM_BIT1
        // NUM_ONE)`. Same term, two signatures: this one has the order and the numerals in it, so
        // what a reader compares against the informal claim is the claim.
        show(theorem.conclusion) shouldBe "!x:job. Attempts x < 3 ==> ~(Abandoned x)"
        theorem.hypotheses shouldBe empty

        // The report, which is the second of the card's four conditions: a conclusion reached by a
        // route the reader cannot see defeats the one thing this tool is for.
        bridges.map(_.name) shouldBe Vector(Peano.BelowExcludesAtMost)
        found.summary should include(Peano.BelowExcludesAtMost)

        // And the accounting is the fourth: a bridge found charges exactly what the same bridge
        // named charges, which is `DomainTheorySpec`'s assertion at this site. An equality rather
        // than a non-emptiness, because non-empty passes just as well when the decision fell
        // through to `Propositional` and charged `SELECT` on top.
        spending.ofTheDomain shouldBe Set("AbandonedOnlyAfterThree")
        spending.foundational shouldBe Derivation.axiomsOf(cheapest)
        spending.foundational should not be empty

        // The search looked at more than one thing, which is what says the answer was found rather
        // than arrived at: `Library.about` over this claim's constants is tens of lemmas, and the
        // one that carried it is not distinguished in advance by anything but the decision.
        considered should be > 1

      case other => fail(s"the search is what this claim was missing: $other")
    }
  }

  it should "report no bridge where the arithmetic it names is inert" in {
    // The control that makes the report above worth reading, and the reason the search asks this
    // first. `NUM_LT (Attempts j) 3` is here and the claim does not depend on it: the conjunction
    // is discharged by its other half. Every candidate in the library would "settle" this, so a
    // search that reported the first would be naming a lemma that did nothing, and a reader of the
    // report would take it for the reason.
    Bridging.settle(
      retries,
      chain.classical,
      published,
      "!j:job. NUM_LT (Attempts j) 3 /\\ Abandoned j ==> Abandoned j"
    ) match {
      case Bridging.Found(Domain.Verdict.Settled(theorem, spending), bridges, considered, _) =>
        theorem.hypotheses shouldBe empty
        bridges shouldBe empty
        considered shouldBe 0

        // And it cost nothing at all: no bridge means no arithmetic, so the foundational column is
        // empty where the claim above has the naturals' two axioms in it.
        spending.foundational shouldBe empty

      case other => fail(s"a claim whose arithmetic is inert needs no bridge: $other")
    }
  }

  it should "pass over a costlier derivation of the same statement" in {
    // The third condition, and the published library cannot be asked it on its own: what it holds
    // is one derivation per statement, so any two of its lemmas that both carry this claim differ
    // in what they SAY, and a search preferring one would be preferring a statement rather than a
    // price. So a second derivation of the SAME statement is built at a higher price and put in
    // front of the first.
    //
    // **The obvious way to build the expensive twin does not work, and the reason is a limit of the
    // instrument worth knowing.** Detaching the lemma against `p ==> p` proved by `Propositional`
    // spends `DOUBLE_NEGATION` and therefore the choice axiom — and this lemma is about `num`, so
    // choice is already in its column. Measured on the first run of this test: 2 axioms against 2.
    // The price is a SET, so a costlier derivation is not always a costlier answer, and a route
    // reaching only for something already paid for is invisible here.
    //
    // So the twin spends an axiom this one cannot already have: `ADD_SYM` is an axiom of the reals,
    // and conjoining it in and projecting back out leaves the statement untouched and the
    // derivation carrying it. The two entries are indistinguishable by their conclusions, which is
    // the sharpest form this test has: nothing but the accounting separates them.
    val statement = cheapest.conclusion
    val realAxiom = force(chain.reals.axiom("ADD_SYM"))
    val costlier = force(logic.rules.conjIntro(cheapest, realAxiom).flatMap(logic.rules.conjElim1))

    costlier.conclusion shouldBe statement
    Derivation.axiomsOf(costlier) should contain allElementsOf Derivation.axiomsOf(cheapest)
    Derivation.axiomsOf(costlier).size should be > Derivation.axiomsOf(cheapest).size

    // Named so that it sorts BEFORE the published lemma, because the order candidates are tried in
    // is by name: an expensive twin sorting after the cheap one would be passed over by a search
    // that merely kept the first thing that worked.
    val session = Library.of(Vector("the session" -> Map("NUM_LT_EXCLUDES_LE_THE_LONG_WAY" -> costlier)))

    Bridging.settle(retries, chain.classical, session ++ published, retryClaim) match {
      case Bridging.Found(Domain.Verdict.Settled(_, spending), bridges, _, alternatives) =>
        bridges.map(_.name) shouldBe Vector(Peano.BelowExcludesAtMost)
        spending.foundational shouldBe Derivation.axiomsOf(cheapest)

        // The one it passed over is reported rather than dropped, which is what lets a reader check
        // that "the cheapest was chosen" instead of taking it. Both halves are asserted: that the
        // expensive twin was among the candidates that would have worked, and that it really is
        // more expensive, so neither can go quietly empty.
        alternatives.map(_.name) should contain("NUM_LT_EXCLUDES_LE_THE_LONG_WAY")
        Derivation.axiomsOf(costlier) should not be Derivation.axiomsOf(cheapest)

      case other => fail(s"the cheaper of two bridges is what the search reports: $other")
    }
  }

  it should "refuse rather than approximate where no one lemma carries it" in {
    // The negative control. The converse of the axiom does not follow from it, so no lemma about
    // the order can make it follow, and what the search must not do is hand back a theorem about a
    // skeleton it decided some other way.
    Bridging.settle(
      retries,
      chain.classical,
      published,
      "!j:job. NUM_LT (Attempts j) 3 ==> Abandoned j"
    ) match {
      case Bridging.Found(Domain.Verdict.Refused(why), bridges, considered, alternatives) =>
        bridges shouldBe empty
        alternatives shouldBe empty
        considered should be > 1

        // The refusal names what it could not do rather than what the claim is, which is the rule
        // every procedure here follows: the number it looked at, and that it never put two
        // together, so a reader knows the claim is not thereby out of reach.
        why should include("carries it into the foundation")
        why should include("never two together")

      case other => fail(s"a search that cannot close a claim must refuse: $other")
    }
  }

  "The search space of a claim" should "be smaller than the bound the search refuses at" in {
    // The bound is a number and this is what says it is above the shape the method was built for.
    // Neither count is written down here, because a count the code knows is the copy that drifts:
    // what is asserted is the relation the design rests on.
    val goal = force(Parser.proposition(retries.theory, retries.notation, retryClaim))
    val reached = retries.reaches(goal)

    // Three constants and not one: `NUM_LT`, and the two the numeral `3` is built from. A reader
    // expecting the search space to be "the lemmas about `<`" is reading the claim and not the
    // term, and the search drops those two on purpose: what the claim is about is the order.
    reached.size should be > 1

    val about = reached.toVector.sorted
      .flatMap(published.about)
      .distinctBy(entry => (entry.name, entry.theorem.conclusion))

    val tried = Bridging.candidates(retries, published, goal)

    // The filter is exact rather than a heuristic — a lemma binding a type this claim names no term
    // of produces no instance and can change no decision — and it is most of the difference between
    // a search that runs and one refused for its size. Both halves are asserted so that neither a
    // filter that stopped filtering nor one that emptied the set reads as a pass.
    tried.length should be < about.length
    tried should not be empty

    // **Room rather than a fit, and the margin is the assertion.** This read 128 against a bound of
    // 128 on 2026-09-18, and a peer's lemmas landing in `Peano` that afternoon took it to 129 and
    // turned an answer into a refusal for size. A bound a claim only just fits under is one the next
    // proof about the number one breaks, so what is asserted is that the shape this method was built
    // for sits well inside it. Going red here is a decision to take, not a number to raise.
    withClue(s"the search space of the retry claim is ${tried.length} of ${Bridging.Candidates}: ") {
      tried.length * 2 should be <= Bridging.Candidates
    }

    // And the lemma the claim is really missing survived the filter, which is the positive control
    // on it: a filter that dropped everything would satisfy the three assertions above.
    tried.map(_.name) should contain(Peano.BelowExcludesAtMost)
  }

  it should "be past what one call could carry, which is why the search is one candidate at a time" in {
    // The measurement under `docs/adr/0027`'s rejected alternative, rather than the argument for it.
    // Handing the whole candidate set to `settle` at once is the obvious way to reach a claim that
    // needs two lemmas, and the reason it is not the shape here is arithmetic: the instances are a
    // PRODUCT over the subjects the claim names, and this set is past `Domain.Instances` on its own.
    // So that route decides nothing at all, rather than deciding something expensive.
    val goal = force(Parser.proposition(retries.theory, retries.notation, retryClaim))
    val every = Bridging.candidates(retries, published, goal).map(_.theorem)

    retries.settle(chain.classical, goal, every) match {
      case Domain.Verdict.Refused(why) =>
        why should include(s"at most ${Domain.Instances} specialised axioms")
      case other =>
        fail(s"the whole candidate set at once is what `docs/adr/0027` rejects on this measurement: $other")
    }
  }

  "A claim in the domain's own vocabulary" should "reach the same answer the search is not asked for" in {
    // A search may add a theorem and must never take a refusal away, and here that is structural:
    // a claim naming no foundation constant is handed to `Domain.Built.settle` unchanged, with no
    // candidate considered, so the answer is the one that method gives.
    val claim = "!j:job. Abandoned j ==> Abandoned j"

    val searched = Bridging.settle(retries, chain.classical, published, claim)
    val direct = retries.settle(chain.classical, claim)

    searched.considered shouldBe 0
    searched.bridges shouldBe empty

    (searched.verdict, direct) match {
      case (Domain.Verdict.Settled(found, spent), Domain.Verdict.Settled(named, alsoSpent)) =>
        found.conclusion shouldBe named.conclusion
        spent.foundational shouldBe alsoSpent.foundational
      case (searchedVerdict, directVerdict) =>
        fail(s"the two routes are the same call here: $searchedVerdict against $directVerdict")
    }
  }
}
