package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A theory that is not about numbers, proved against, and accounted for.
 *
 * The declared purpose of this repository is not only mathematics: it is to state axioms and rules
 * from domains that are neither logical nor mathematical, and settle claims about them. Nothing had
 * ever done it. The card that carries the aim lists four things missing, and reads as though the
 * first of them blocks the rest: the eight entry points in `modules/tactics` take a `RealTheory`,
 * and a domain theory is not one and never will be.
 *
 * **That is true and it does not block this.** The card's own acceptance criterion is a page: a
 * claim of some real domain formalised end to end, with the constants declared, the axioms asserted
 * and counted, the conclusion derived, and a report saying which of the assumptions it rests on and
 * which of them are foundational. Every piece of that is reachable with the kernel, the derived
 * rules and `Derivation`, and this file is the page. What the eight signatures would buy is
 * `Cost`'s formatting and the search tactics, which is convenience and automation rather than the
 * criterion.
 *
 * == The domain, and why this one ==
 *
 * A release gate: a change ships when two people have reviewed it, or when one has and the pipeline
 * is green, or when it is a revert of something already shipped, and on no other ground. It is a
 * rule about when work is allowed out, so it is as far from arithmetic as the shelf gets, and its
 * shape is what makes the accounting below worth reading: three sufficient conditions, the third
 * failing differently in kind from the other two, and one sentence saying those three are the only
 * ones there are.
 *
 * **The criterion is invented, and that is deliberate rather than a weakness.** Until 2026-09-15
 * this test asserted the four sentences of a private document's admission criterion, which made a
 * fragment of that document the subject of a public test. Nothing in the accounting depended on the
 * sentences being anybody's real rule: what the derivation spends is fixed by the logical shape,
 * and every criterion of this shape spends the same. What a real one bought was the claim that the
 * domain is in daily use rather than written for a demonstration, and that claim is given up here
 * on purpose. A reader who wants to know whether this machinery works on a rule somebody actually
 * follows should point it at their own, which is the whole use of this file.
 *
 * == What the accounting says, which is the part worth the trouble ==
 *
 * Four axioms are asserted and the conclusion rests on **one**. The three that state when a
 * change *is* admitted are not used at all; what the conclusion needs is the converse, the
 * direction that makes the criterion a gate rather than a sufficiency. A reader would not have
 * guessed that from the four, and it is exactly the question the card says is the useful one about
 * a claim of the world: not "is it a theorem" but "which of my assumptions did it actually spend".
 *
 * And it rests on **no foundational axiom at all**: not choice, not infinity, none of the reals.
 * The reasoning is propositional over the domain's own assumptions, which is what a reader should
 * be told before being asked to believe anything about a domain.
 *
 * == The same claim by hand and by procedure, which is what this file measures ==
 *
 * Both routes are kept and the comparison is the finding rather than the theorem. The hand
 * derivation is forty lines of `for`-comprehension out of the derived rules; `Domain.Built.settle`
 * is one call, and what it does is what those lines do: specialise the axioms at the subject the
 * claim names, decide the propositional skeleton with the domain's five constants as atoms given no
 * meaning, detach, and quantify again. Same conclusion, same one domain axiom.
 *
 * **And, since 2026-09-16, the same foundational cost, which is nought.** This section recorded the
 * opposite for as long as `Propositional` was the only procedure that could take a statement with a
 * negation in it: that one decides classical validity and closes with `DOUBLE_NEGATION`, so it
 * charged the choice axiom where the hand derivation charged nothing, and the honest report was that
 * neither procedure covered an argument about a domain at its real cost. `Intuitionistic` is what
 * closed it, and the assertion below is that the two routes now agree on the accounting and not
 * merely on the theorem. The classical route is still exercised there, at its own price, so that
 * the agreement is a measurement rather than a sentence about an empty set.
 *
 * Nor is this a development of the chain, and it must not become one. A theory built beside the
 * chain is the case `docs/adr/0008` warns about, and `SoundnessAttackSpec` still carries the row
 * where two such theories produce `|- F`. What makes that nameable here is `Derivation.foreignTo`,
 * which the last assertion spends.
 */
class DomainTheorySpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def lift[T](result: Either[KernelError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val classical = Classical.standard
  private val foundation = classical.theory
  private val change = TyApp("change", Nil)

  /**
   * The release gate, as a description: one type, five names and four sentences.
   *
   * The first three sentences are the grounds it gives, and the third is deliberately unlike the
   * other two: a revert is not a weaker review, it is a different kind of reason, and the two fail
   * differently. The fourth is the direction the prose means by "ships **when**": without it the
   * three say only that a change meeting one of them may ship, and nothing at all follows about one
   * that meets none. The conclusion below is about a change that meets none, so the fourth is the
   * only one it can possibly spend, which is the accounting this file exists to show.
   *
   * A `Domain` rather than a fold over `declareConstant` and `assertAxiom` written out here, which
   * is what this file did until 2026-09-16: the description is the thing a reader checks against the
   * prose, and the twenty lines that turned it into a theory were the same twenty lines in every
   * file that has ever done this.
   */
  private val gate: Domain = Domain(
    name = "the release gate",
    typeOperators = Vector("change" -> 0),
    constants = Vector(
      "TwoReviews" -> Type.fun(change, Type.Bool),
      "OneReview" -> Type.fun(change, Type.Bool),
      "PipelineGreen" -> Type.fun(change, Type.Bool),
      "IsRevert" -> Type.fun(change, Type.Bool),
      "Ships" -> Type.fun(change, Type.Bool)
    ),
    axioms = Vector(
      "TwoReviewsShip" -> "!r:change. TwoReviews r ==> Ships r",
      "OneReviewAndGreenShips" -> "!r:change. OneReview r /\\ PipelineGreen r ==> Ships r",
      "ARevertShips" -> "!r:change. IsRevert r ==> Ships r",
      "OnThoseGroundsOnly" -> ("!r:change. Ships r ==> " +
        "TwoReviews r \\/ (OneReview r /\\ PipelineGreen r) \\/ IsRevert r")
    )
  )

  private lazy val built: Domain.Built = force(Domain.build(foundation, classical.notation, gate))
  private lazy val theory: Theory = built.theory
  private lazy val converseAxiom: Kernel.Thm = force(built.axiom("OnThoseGroundsOnly"))

  private lazy val logic: Logic = force(classical.logic.over(theory))
  private lazy val rules: Rules = logic.rules

  private def show(term: Term): String = Show.show(classical.notation, term)
  private def proposition(text: String): Term =
    force(Parser.proposition(theory, classical.notation, text))
  private def constant(name: String): Term =
    lift(theory.constant(name, Type.fun(change, Type.Bool)))

  /** The claim: a change meeting none of the three bases is not admitted. */
  private val statement: String =
    "!r:change. ~(TwoReviews r) /\\ ~(PipelineGreen r) /\\ ~(IsRevert r) " +
      "==> ~(Ships r)"

  /**
   * The derivation, by hand, because when it was written nothing here could be asked to find it.
   *
   * Assume the three negations and suppose the change admitted; the fourth axiom gives a
   * disjunction of three, each of which contradicts one of the three negations. The middle case
   * needs only the second half of its conjunction, which is the `PipelineGreen` the caller denied.
   *
   * It is kept now that something can be asked, because it is what the procedure is measured
   * against: what a claim of the world costs when a person writes every step of it.
   */
  private lazy val derived: Kernel.Thm = {
    val subject = Term.variable("r", change)
    val antecedent = proposition(
      "~(TwoReviews (r:change)) /\\ ~(PipelineGreen r) /\\ ~(IsRevert r)"
    )
    val admitted = lift(Term.app(constant("Ships"), subject))
    val two = lift(Term.app(constant("TwoReviews"), subject))
    val one = lift(Term.app(constant("OneReview"), subject))
    val incident = lift(Term.app(constant("PipelineGreen"), subject))
    val standing = lift(Term.app(constant("IsRevert"), subject))

    force(for {
      assumed <- LogicError.lift(Kernel.assume(antecedent))
      noTwo <- rules.conjElim1(assumed)
      rest <- rules.conjElim2(assumed)
      noIncident <- rules.conjElim1(rest)
      noStanding <- rules.conjElim2(rest)

      converse <- rules.specAll(converseAxiom, List(subject))
      supposed <- LogicError.lift(Kernel.assume(admitted))
      cases <- rules.mp(converse, supposed)

      firstCase <- LogicError.lift(Kernel.assume(two)).flatMap(rules.notElim(noTwo, _))
      pair <- logic.mkConj(one, incident)
      secondCase <- LogicError
        .lift(Kernel.assume(pair))
        .flatMap(rules.conjElim2)
        .flatMap(rules.notElim(noIncident, _))
      thirdCase <- LogicError.lift(Kernel.assume(standing)).flatMap(rules.notElim(noStanding, _))

      inner <- logic.mkDisj(pair, standing)
      innerAssumed <- LogicError.lift(Kernel.assume(inner))
      tail <- rules.disjElim(innerAssumed, secondCase, thirdCase)
      whole <- rules.disjElim(cases, firstCase, tail)

      negated <- rules.notIntro(admitted, whole)
      discharged <- rules.disch(antecedent, negated)
      closed <- rules.gen(subject, discharged)
    } yield closed)
  }

  /** The same statement, put to the domain's own machinery instead of written out. */
  private lazy val settled: Domain.Verdict = built.settle(classical, statement)

  private lazy val derivedByTactic: Kernel.Thm = settled match {
    case Domain.Verdict.Settled(theorem, _) => theorem
    case other => fail(s"the claim was not settled: $other")
  }

  private lazy val spending: Domain.Spending = settled match {
    case Domain.Verdict.Settled(_, spent) => spent
    case other => fail(s"the claim was not settled: $other")
  }

  "The same claim put to a procedure" should "come back as the same theorem" in {
    // Not a weaker theorem, not a conditional one, and not one about a different statement: the
    // conclusion is compared with the hand derivation's rather than with the text, because two
    // statements that print the same can be different terms.
    derivedByTactic.conclusion shouldBe derived.conclusion
    derivedByTactic.hypotheses shouldBe empty
  }

  it should "spend the same one of the four domain axioms" in {
    // The accounting the card calls the product, produced by the procedure instead of by reading a
    // hand derivation. Same answer: one of the four, and it is the converse.
    spending.ofTheDomain shouldBe Set("OnThoseGroundsOnly")
    spending.unspent should have size 3
  }

  it should "cost no foundational axiom either, which is what closed the gap" in {
    // **The half this file reported as a gap until 2026-09-16, asserted the other way round.**
    //
    // The hand derivation spends no foundational axiom at all: assume the subject ships, take the
    // disjunction, contradict each case, conclude the negation. Every step of that is
    // intuitionistic. `Propositional` reaches the same theorem and charges the choice axiom,
    // because it decides classical validity and closes with `DOUBLE_NEGATION`, and while it was the
    // only procedure that could take a statement with a negation in it, that was what a domain
    // claim cost through a tactic.
    //
    // `Domain.Built.settle` asks `Intuitionistic` first, which decides the fragment the hand
    // derivation works in and certifies the answer out of the derived rules alone.
    spending.foundational shouldBe empty
    Derivation.axiomsOf(derived).filterNot(built.ours.contains) shouldBe empty

    // The classical route, kept and still overpaying, which is what makes the two lines above a
    // measurement rather than a remark about an empty set: same bridge, same theorem, one axiom.
    val subject = Term.variable("r", change)
    val body = proposition(
      "~(TwoReviews (r:change)) /\\ ~(PipelineGreen r) /\\ ~(IsRevert r) ==> ~(Ships r)"
    )
    val classicalRoute = force(for {
      converse <- rules.specAll(converseAxiom, List(subject))
      bridge <- logic.mkImp(converse.conclusion, body)
      tautology <- Propositional.over(classical, logic).prove(bridge)
      applied <- rules.mp(tautology, converse)
      closed <- rules.gen(subject, applied)
    } yield closed)

    classicalRoute.conclusion shouldBe derived.conclusion
    Derivation.axiomsOf(classicalRoute).filterNot(built.ours.contains) shouldBe
      Set(force(classical.axiom(Classical.Choice)).conclusion)
  }

  "A claim that does not follow" should "come back as an assignment rather than as a refusal" in {
    // The other answer, and the one a reader has to be told how to read. A change with two reviews
    // is admitted, and nothing in the gate says a change that ships has two reviews: the converse
    // of the first axiom is not an axiom. What comes back names the atoms and the reading under
    // which the skeleton fails, and it refutes the claim AS A SCHEMA over those atoms rather than
    // saying that the claim is false, which is `SkeletonFailsAt`'s caveat carried one level up.
    built.settle(classical, "!r:change. Ships r ==> TwoReviews r") match {
      case Domain.Verdict.Countermodel(assignment) => assignment should not be empty
      case other => fail(s"a claim that does not follow must not be settled: $other")
    }
  }

  "A claim naming more subjects than the method will specialise at" should "be refused for its size" in {
    // The bound, fired rather than described. It is a **product**: every subject the claim names is
    // tried at every binder of every axiom, so an axiom of two binders over nine subjects is
    // eighty-one specialised axioms and one of eight binders over ten subjects is a hundred
    // million. The count is therefore taken before the tuples are built, which is what this asserts
    // by the number in the message: a bound checked on the finished list is a bound checked after
    // the machine has been asked for the list.
    val pairs = Domain(
      name = "the ordering rule",
      typeOperators = Vector("change" -> 0),
      constants = Vector(
        "Ships" -> Type.fun(change, Type.Bool),
        "Before" -> Type.fun(change, Type.fun(change, Type.Bool))
      ),
      axioms = Vector("BeforeShips" -> "!r:change. !s:change. Before r s /\\ Ships s ==> Ships r")
    )
    val ordering = force(Domain.build(foundation, classical.notation, pairs))

    // Every one of the nine has to OCCUR, which is the other half of what a subject is: a variable
    // the claim quantifies and never mentions is not something to specialise an axiom at, and the
    // first version of this test bound nine and mentioned one, so it was settled rather than
    // refused and the number it produced was 1 instead of 81.
    val names = Vector("a", "b", "c", "d", "e", "f", "g", "h", "i")
    val nine = s"!${names.map(_ + ":change").mkString(" ")}. " +
      names.map(name => s"Ships $name").mkString(" /\\ ") + " ==> Ships a"

    ordering.settle(classical, nine) match {
      case Domain.Verdict.Refused(why) =>
        why should include("81")
        why should include("at most 64")
      case other => fail(s"a claim of that size must be refused for it: $other")
    }
  }

  "A claim reaching outside the domain's vocabulary" should "be refused by name" in {
    // The line the card draws and the reason it is drawn there: "at most three attempts" is
    // arithmetic, the procedures give an arithmetic constant no meaning, and what they would decide
    // is a skeleton in which the requirement is one opaque atom. An approximation nobody asked for
    // is worse than a refusal, so the refusal names the constant instead.
    //
    // Built over the chain's widest signature rather than over the classical logic, because a
    // domain that cannot even SAY `NUM_LE` cannot demonstrate a claim being turned away for
    // reaching it.
    val chain = Chain.standard
    val job = TyApp("job", Nil)
    val attempts = Domain(
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

    val retries = force(Domain.build(chain.widest.theory, chain.widest.notation, attempts))

    retries.settle(chain.classical, "!j:job. NUM_LT (Attempts j) 3 ==> ~(Abandoned j)") match {
      case Domain.Verdict.Refused(why) =>
        why should include("NUM_LT")
        why should include("foundation")
      case other => fail(s"arithmetic with no bridge named is outside this fragment: $other")
    }
  }

  it should "be settled when the caller names the fact that carries it across" in {
    // `docs/adr/0024`. The claim above is the same claim; what changes is that the caller hands over
    // the theorem relating the two orders, and `Attempts j` stays a term of type `num` whose value
    // nobody knows. Nothing is interpreted and nothing is approximated: `NUM_LT_NOT_LE` holds for
    // every `num` there is, so it holds for whatever this job's attempts were.
    val chain = Chain.standard
    val job = TyApp("job", Nil)
    val attempts = Domain(
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
    val retries = force(Domain.build(chain.widest.theory, chain.widest.notation, attempts))

    val bridge = Library
      .of(chain)
      .named(Peano.BelowExcludesAtMost)
      .headOption
      .getOrElse(fail(s"${Peano.BelowExcludesAtMost} is what this route is built on and the library " +
        "no longer publishes it"))
      .theorem

    retries.settle(
      chain.classical,
      "!j:job. NUM_LT (Attempts j) 3 ==> ~(Abandoned j)",
      Vector(bridge)
    ) match {
      case Domain.Verdict.Settled(theorem, spending) =>
        // Printed with the numeral expanded, which is what this printer does with `3:num` and is
        // worth seeing here rather than hidden behind a nicer expectation: the bridge was
        // specialised at the term the claim names, and that term is the bit encoding.
        show(theorem.conclusion) shouldBe
          "!x:job. NUM_LT (Attempts x) (NUM_BIT1 NUM_ONE) ==> ~(Abandoned x)"
        theorem.hypotheses shouldBe empty

        // The domain's one axiom, which is the accounting still working across the new route: a
        // report that lost the domain column when arithmetic arrived would be the failure this
        // whole file exists to prevent.
        spending.ofTheDomain shouldBe Set("AbandonedOnlyAfterThree")

        // And the foundation's, which is the half `docs/adr/0024` insists on: a reader of this
        // conclusion is being asked for what the naturals cost, where the release gate's reader was
        // asked for nothing.
        //
        // Asserted as an EQUALITY against what the bridge itself spends, not as "non-empty", and
        // the difference is the whole of what could have gone wrong here. Non-empty passes just as
        // well if the decision fell through to `Propositional` and charged `SELECT` for the
        // classical step, which is the trade `docs/adr/0022` exists to refuse and which would be
        // invisible behind a choice axiom the naturals were going to cost anyway. Equality says the
        // conclusion spent what it was carried across by and not one axiom more, so the logical
        // half stayed free.
        spending.foundational shouldBe Derivation.axiomsOf(bridge)
        spending.foundational should not be empty

      case other => fail(s"the bridge is what this claim was missing: $other")
    }
  }

  it should "still refuse when the domain's own type is what would need a meaning" in {
    // The narrowed refusal, and the reason `docs/adr/0024` keeps one at all. `Cost` is a type this
    // domain declares and the foundation has never heard of, so no theorem anywhere relates
    // `Expensive c` to a number, and there is no bridge a caller could name. Without this the
    // record's line between the two cases would be prose with nothing watching it.
    val chain = Chain.standard
    val cost = TyApp("cost", Nil)
    val budget = Domain(
      name = "the budget rule",
      typeOperators = Vector("cost" -> 0),
      constants = Vector(
        "Expensive" -> Type.fun(cost, Type.Bool),
        "Approved" -> Type.fun(cost, Type.Bool)
      ),
      axioms = Vector("ExpensiveNeedsApproval" -> "!c:cost. Expensive c ==> Approved c")
    )
    val budgets = force(Domain.build(chain.widest.theory, chain.widest.notation, budget))

    budgets.settle(chain.classical, "!c:cost. NUM_LE 3 3 /\\ Expensive c ==> Approved c") match {
      case Domain.Verdict.Refused(why) =>
        why should include("NUM_LE")
        // And that it is THIS refusal rather than a parse error that happens to quote the same
        // constant back: a claim the notation cannot read is also a `Refused`, with a message
        // naming what it choked on, and the two are told apart by the sentence rather than by the
        // constant.
        why should include("belongs to the foundation underneath it")
      case other => fail(s"a claim reaching the foundation with no bridge is refused: $other")
    }
  }

  "A theory of a domain that is not mathematics" should "be a theory like any other" in {
    theory.typeOperators.keySet should contain("change")
    (theory.constants.keySet -- foundation.constants.keySet) shouldBe gate.introduced

    // Counted, which the card asks for by name. The domain's four sit on top of the foundation's,
    // and the difference is what a reader of this page is being asked to accept beyond what the
    // logic already assumes.
    built.axioms should have size 4
    theory.axioms.length shouldBe foundation.axioms.length + 4
  }

  it should "settle a claim about that domain, with nothing assumed" in {
    show(derived.conclusion) shouldBe
      "!x:change. ~(TwoReviews x) /\\ ~(PipelineGreen x) /\\ ~(IsRevert x) " +
        "==> ~(Ships x)"
    derived.hypotheses shouldBe empty
    derived.conclusion shouldBe proposition(statement)
  }

  "The accounting" should "name which assumptions the conclusion actually spent" in {
    // The half the card says is the product, and the half no other system packages. Four axioms
    // were asserted; the conclusion rests on one, and it is the converse rather than any of the
    // three that say when a change qualifies.
    val spent = built.spends(derived)

    spent.ofTheDomain shouldBe Set("OnThoseGroundsOnly")

    // And the three unspent ones are asserted and really unused, which is the statement a reader
    // would not have guessed from reading the four.
    spent.unspent shouldBe (built.axioms.keySet - "OnThoseGroundsOnly")
  }

  it should "say that no foundational axiom was spent either" in {
    // Not choice, not infinity, none of the reals. The reasoning is propositional over the domain's
    // own assumptions, and a reader being asked to believe something about a domain should be told
    // that before anything else.
    //
    // Paired with the assertion above, because "no foundational axiom" is also what a report that
    // found nothing at all would say: one domain axiom was found, so the walk is reading something.
    val spent = Derivation.axiomsOf(derived)

    built.spends(derived).foundational shouldBe empty

    // Two paired assertions rather than one, because "no foundational axiom" is what a walk that
    // reads nothing also says, and what a walk that cannot see foundational axioms also says.
    // The first shows it reads something; the second shows that when a foundational axiom IS
    // spent, this same call reports it. The excluded middle is derived from choice and is the
    // nearest theorem that spends one.
    spent should not be empty
    Derivation.axiomsOf(force(classical.fact(Classical.ExcludedMiddle))) should not be empty
  }

  it should "be foreign to the foundation it was built on, and at home in its own theory" in {
    // What `docs/adr/0008` leaves open and what was made detectable on 2026-09-13. A theory built
    // beside the chain is the case that produces `|- F` when two of them axiomatise one name, and
    // this is how a caller at a boundary is told which theorem belongs to which.
    Derivation.foreignTo(theory, derived).clean shouldBe true

    val outside = Derivation.foreignTo(foundation, derived)
    outside.axioms should have size 1
    outside.constants should not be empty
  }

  /* ------------------------------------------- two domains at once, which is the card's fourth point */

  /**
   * A second domain, built ON the first rather than beside it.
   *
   * The card carrying the aim lists "no composition" as one of four things missing: nothing takes
   * two independent domain theories and makes one, nor says what happens if they collide on a name.
   * Both halves are answered here and neither needs machinery.
   *
   * A theory is a value, and extending one is what every development in `Chain` does. So two
   * domains compose by building the second over the first, and then one signature states a claim
   * about both. The version that cannot be made to work is the UNION of two theories built
   * independently, and it cannot be made to work because it is not sound: `SoundnessAttackSpec`
   * derives `|- F` from two theories that declare one name and constrain it differently. What is
   * right there is a refusal, and `Derivation.foreignTo` is the refusal.
   */
  private lazy val (second, secondAxiom) = {
    val declared = lift(theory.declareConstant("Frozen", Type.fun(change, Type.Bool)))
    val text = "!r:change. Frozen r ==> ~(Ships r)"
    val proposition = force(Parser.proposition(declared, classical.notation, text))
    val (extended, asserted) = lift(Kernel.assertAxiom(declared, proposition))
    (extended, asserted)
  }

  "A second domain built over the first" should "state a claim naming both vocabularies" in {
    // The composition the card asks for, which is extension and not union. `Frozen` is a second
    // domain's word and `Ships` is the first's, and the claim below names both because there is
    // one signature holding both. Nothing was written to make that possible.
    val across = force(
      Parser.proposition(
        second,
        classical.notation,
        "!r:change. Frozen r ==> ~(TwoReviews r) \\/ ~(IsRevert r)"
      )
    )

    Show.show(classical.notation, across) should include("Frozen")
    Show.show(classical.notation, across) should include("TwoReviews")

    // And the first domain's theorem is a theorem of the second, because extension only adds. That
    // is what makes building one over the other a composition rather than a coincidence.
    Derivation.foreignTo(second, derived).clean shouldBe true
  }

  it should "make the union of two INDEPENDENT domains refusable rather than silent" in {
    // The other half of the card's fourth point, and the reason union is not offered. A sibling
    // that declares the same name and constrains it its own way is the case `docs/adr/0008` leaves
    // open: the constants compare equal, the theorems combine, and `SoundnessAttackSpec` gets
    // `|- F` out of it. Nothing here makes that impossible; what `foreignTo` does is let a caller
    // at the boundary find out, and the test is that the sibling's theorem is reported foreign.
    val sibling = {
      val declared = lift(theory.declareConstant("Frozen", Type.fun(change, Type.Bool)))
      val text = "!r:change. Frozen r ==> Ships r"
      val proposition = force(Parser.proposition(declared, classical.notation, text))
      lift(Kernel.assertAxiom(declared, proposition))
    }

    // The two siblings say opposite things about one declared name, and each is consistent alone.
    Show.show(classical.notation, secondAxiom.conclusion) should include("~(Ships")
    Show.show(classical.notation, sibling._2.conclusion) should not include "~(Ships"

    // Neither is at home in the other, and it is the AXIOM that says so rather than the constant:
    // `Frozen` is declared in both with no origin in either, so nothing on the term tells them
    // apart, which is exactly what `Term`'s comment says is right for an uninterpreted name.
    val fromSibling = Derivation.foreignTo(second, sibling._2)
    fromSibling.axioms should have size 1
    fromSibling.constants shouldBe empty

    Derivation.foreignTo(sibling._1, secondAxiom).axioms should have size 1
  }

  "What a domain gets and what it does not" should "be said rather than left to be discovered" in {
    // `Ring` and `Linarith` decide fragments of the reals and have nothing to say here. What does
    // reach a domain is the propositional skeleton, and the two numbers below are what that costs
    // against writing the same argument out by hand. They are reported rather than asserted against
    // a bound, because what they are evidence for is the shape of the cost and not a budget.
    info(s"by hand: ${Derivation.size(derived)} inferences")
    info(s"by procedure: ${Derivation.size(derivedByTactic)} inferences, ${spending.summary}")

    Derivation.size(derived) should be > 0
    Derivation.size(derivedByTactic) should be > 0
  }

  /* --------------------------------------- the net under the free route, and what reaching it costs */

  private val ticket = TyApp("ticket", Nil)

  /**
   * A domain of `links` axioms whose claim walks every one of them, and the claim.
   *
   * One axiom per link, one binder each, and the claim names one subject of that binder's type, so
   * the specialised instances are exactly `links`: the family grows along the axis
   * [[Domain.Instances]] bounds and along no other. `conjuncts` is how many atoms stand in an
   * axiom's antecedent, which is what makes a link cost the search more than one step without
   * making the claim any harder to believe: every member of the family is a chain of modus ponens
   * and is intuitionistically valid at every size.
   */
  private def escalation(links: Int, conjuncts: Int): (Domain.Built, String) = {
    val stages = (0 to links).map(index => s"Stage$index" -> Type.fun(ticket, Type.Bool)).toVector
    val guards = (1 until conjuncts).map(index => s"Guard$index" -> Type.fun(ticket, Type.Bool)).toVector
    val guarded = (1 until conjuncts).map(index => s" /\\ Guard$index t").mkString
    val rule = Domain(
      name = "the escalation rule",
      typeOperators = Vector("ticket" -> 0),
      constants = stages ++ guards,
      axioms = (0 until links)
        .map(index => s"Stage${index}Escalates" -> s"!t:ticket. Stage$index t$guarded ==> Stage${index + 1} t")
        .toVector
    )

    (
      force(Domain.build(foundation, classical.notation, rule)),
      s"!t:ticket. Stage0 t$guarded ==> Stage$links t"
    )
  }

  private def settleEscalation(links: Int, conjuncts: Int): Domain.Verdict =
    escalation(links, conjuncts) match { case (built, claim) => built.settle(classical, claim) }

  /**
   * Whether a claim of this size reached the net, by the one answer that says the search stopped.
   *
   * The criterion, written here rather than left to the reader: a claim REACHES the net when
   * `settle` answers [[Domain.Verdict.CutShort]], which is the verdict carrying the calculus's
   * `BoundReached` and the only refusal that means "I stopped" rather than "it is not so". Reading
   * it off `Spending.foundational` instead would count a claim that genuinely needs classical logic
   * as a claim that ran out of net, which is the collapse this whole card is about.
   */
  private def cutShortAt(links: Int, conjuncts: Int): Boolean =
    settleEscalation(links, conjuncts) match {
      case Domain.Verdict.CutShort(_, _, _) => true
      case _ => false
    }

  /** How many atoms stand in the antecedent of the family this file measures on. */
  private val Atoms: Int = 4

  /**
   * The least chain length at which the free route is lost, at an [[Atoms]]-atom antecedent.
   *
   * Binary search, and the pair of assertions at the edge is what says it landed on a real one.
   * The figure is found rather than written down, because it is a property of the calculus's rules
   * and would move for reasons that are not defects; what the assertions below are about is the
   * relation between it and [[Domain.Instances]], which is the claim.
   *
   * **Four atoms rather than two, and the reason is the first measurement's own weakness.** At two
   * the free route is lost at exactly sixty-four links, which is [[Domain.Instances]] to the link:
   * a reading at the boundary supports "reachable inside the bound" on one point, and a small
   * change in the calculus's rules would move it to the other side and take the finding with it.
   * Measured the same day at three, four and five atoms, the third and the fourth agree: still free
   * at twenty-four links and cut short at thirty-two, which is half the bound. So the family here
   * is the one with margin, and what the width buys is nothing about the claim's difficulty —
   * every member of every one of these families is a chain of modus ponens.
   */
  private lazy val lostAt: Int = {
    var low = 2
    var high = Domain.Instances
    while (low < high) {
      val middle = low + (high - low) / 2
      if (cutShortAt(middle, Atoms)) high = middle else low = middle + 1
    }
    low
  }

  "The net under the free route" should "be reachable by a claim this method accepts" in {
    // Mycelium card `0b9ce0ca`, step one: measure before building. `Domain.close` asks the
    // intuitionistic calculus first and falls to the classical decision when it refuses, and until
    // 2026-09-18 the two ways of refusing were one `None`. Whether that is worth a report at all
    // depends on whether anything reaches the net, and the figure this file used to rest on is
    // `PropositionalRouteSpec`'s: the deepest of 1114 enumerated formulas needs 7 of the 256. That
    // population is formulas of at most six nodes, and what this method builds is an implication
    // chain one link per specialised instance, so the figure does not travel to it.
    //
    // It is reachable, and inside this method's own bound rather than at it: the claim is a chain
    // of modus ponens and is intuitionistically valid at every length, so the whole difference
    // between the case that is free and the case that is not is size.
    cutShortAt(lostAt, Atoms) shouldBe true
    lostAt should be < Domain.Instances

    // The edge, and the positive control the count needs: one link short of it the same family
    // comes back settled and free, so the instrument is reading the size rather than reporting
    // every large claim as truncated.
    settleEscalation(lostAt - 1, Atoms) match {
      case Domain.Verdict.Settled(theorem, spending) =>
        spending.foundational shouldBe empty
        theorem.hypotheses shouldBe empty
      case other => fail(s"one link short of the net the free route must still answer: $other")
    }

    // And the same length with a one-atom antecedent, which is still free: what costs the search is
    // the weight of what it takes apart and not the number of axioms on its own, so a bound on the
    // instance count is not a bound on the net. This is the row that stops the finding from being
    // read as "a domain of this many axioms cannot be settled for free".
    cutShortAt(lostAt, 1) shouldBe false

    info(
      s"the free route is lost at $lostAt links of an antecedent of $Atoms atoms, against " +
        s"${Domain.Instances} instances allowed, and holds at $lostAt links of one atom"
    )
  }

  it should "come back saying it was cut short, rather than as a price the claim asked for" in {
    // The repair, read from the outside. The theorem is real and the `SELECT` was really spent; what
    // the verdict adds is that the free route was truncated rather than decided against, which is
    // the difference between "this claim needs choice" and "this search ran out of net". Nothing in
    // the answer said which before 2026-09-18.
    settleEscalation(lostAt, Atoms) match {
      case Domain.Verdict.CutShort(theorem, spending, why) =>
        theorem.hypotheses shouldBe empty
        spending.ofTheDomain should not be empty

        // The price is the classical route's, named rather than described: this is what a reader of
        // the accounting would otherwise have taken for the claim's own cost.
        spending.foundational shouldBe Set(force(classical.axiom(Classical.Choice)).conclusion)

        // The calculus's own refusal, verbatim, naming the search that stopped. Rewritten here it
        // would be this file inventing a sentence about somebody else's bound.
        why should include(Intuitionistic.SearchName)

      case other => fail(s"a claim whose free route ran out of net must say so: $other")
    }
  }

  it should "not be what a claim that genuinely needs classical logic comes back as" in {
    // The separation the card is about, from the other side, and the assertion that keeps the one
    // above from being "anything that costs SELECT is reported truncated". The excluded middle over
    // a domain atom is refused by the calculus because it is **not so** intuitionistically, not
    // because anything stopped: it is settled, it costs choice, and it is not cut short.
    built.settle(classical, "!r:change. Ships r \\/ ~(Ships r)") match {
      case Domain.Verdict.Settled(_, spending) =>
        spending.foundational shouldBe Set(force(classical.axiom(Classical.Choice)).conclusion)
        spending.ofTheDomain shouldBe empty
      case other => fail(s"a classically valid claim is settled at its own price: $other")
    }
  }
}
