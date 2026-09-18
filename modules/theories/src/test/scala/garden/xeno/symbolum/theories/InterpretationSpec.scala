package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What a domain whose own TYPE has to carry arithmetic needs, measured before it is built.
 *
 * `docs/adr/0024` keeps one refusal: a claim needing arithmetic about a type the domain declares
 * and the foundation has never heard of. There is no theorem anywhere relating `cost` to a number,
 * so there is no bridge to name and none to find, and `DomainTheorySpec` asserts that refusal.
 *
 * Before anything is designed for that, this file measures what a caller can already do, because
 * the answer decides what the missing capability IS rather than what it looks like from the
 * refusal.
 */
class InterpretationSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val num = TyApp(Natural.TypeName, Nil)

  "A domain that declares its constants over the foundation's own type" should
    "already get the arithmetic, which is what says the missing piece is not the type map" in {
    // The budget rule of `DomainTheorySpec`, written with `cost` NOT declared: the subject is a
    // `num` and `Expensive` is a predicate on numbers. Nothing new is needed to write this, which
    // is the whole point of the measurement.
    val budget = Domain(
      name = "the budget rule",
      typeOperators = Vector.empty,
      constants = Vector(
        "Expensive" -> Type.fun(num, Type.Bool),
        "Approved" -> Type.fun(num, Type.Bool)
      ),
      axioms = Vector(
        "ExpensiveAboveThree" -> "!c:num. Expensive c ==> NUM_LE 3 c",
        "CheapIsApproved" -> "!c:num. ~(Expensive c) ==> Approved c"
      )
    )

    val budgets = force(Domain.build(chain.widest.theory, chain.widest.notation, budget))

    Bridging.settle(
      budgets,
      chain.classical,
      Library.of(chain),
      "!c:num. NUM_LT c 3 ==> Approved c"
    ) match {
      case found @ Bridging.Found(Domain.Verdict.Settled(theorem, spending), bridges, _, _) =>
        theorem.hypotheses shouldBe empty
        bridges should not be empty
        spending.ofTheDomain should not be empty
        withClue(s"${found.summary}\n") { succeed }

      case other => fail(s"a domain written over `num` needs nothing new for arithmetic: $other")
    }
  }

  it should "be refused where the same domain keeps a type of its own" in {
    // The same rule with `cost` declared, which is the refusal `docs/adr/0024` keeps. The claim
    // cannot even be WRITTEN the same way: `NUM_LT c 3` at `c:cost` is a type error rather than a
    // refusal, and that difference is what this measurement is for.
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

    Parser.proposition(budgets.theory, budgets.notation, "!c:cost. NUM_LT c 3 ==> Approved c") match {
      case Left(error) => withClue(s"the claim does not typecheck: ${error.message}\n") { succeed }
      case Right(goal) =>
        fail(s"the claim typechecks at a declared type, which this measurement assumed it does not: $goal")
    }
  }

  /**
   * The budget rule as a description, written once and built two ways below.
   *
   * `cost` is the domain's own type and `Expensive` its own predicate, which is what a reader of
   * the rule would write. Neither build edits this: what differs is the interpretation handed to
   * `Domain.build`, which is the whole point of `docs/adr/0028`.
   */
  private val cost = TyApp("cost", Nil)

  private val budgetRule: Domain = Domain(
    name = "the budget rule",
    typeOperators = Vector("cost" -> 0),
    constants = Vector(
      "Expensive" -> Type.fun(cost, Type.Bool),
      "Approved" -> Type.fun(cost, Type.Bool)
    ),
    // "What is not expensive is approved", which is the direction a gate is written in and the one
    // the claim below can spend. The converse — expensive needs approval — is the first thing
    // anybody writes and the first run of this file wrote it: `Propositional` came back with a
    // countermodel, correctly, because from `~(Expensive c)` nothing follows about `Approved c`.
    axioms = Vector("CheapIsApproved" -> "!c. ~(Expensive c) ==> Approved c")
  )

  private val meaning = Domain.Interpretation(
    types = Map("cost" -> TyApp(Natural.TypeName, Nil)),
    meanings = Map("Expensive" -> "\\c:num. NUM_LE 3 c")
  )

  "A domain whose type is interpreted" should "settle a claim its abstract build cannot state" in {
    // The acceptance criterion of the card. `cost` is `num` here, so the claim can be WRITTEN, and
    // `Expensive` is a definition, so the skeleton has something to look inside instead of an atom.
    val budgets = force(Domain.build(chain.widest.theory, chain.widest.notation, budgetRule, meaning))
    val logic = force(chain.classical.logic.over(budgets.theory))

    // The meaning as a fact a decision can read. The defining equation itself cannot be used:
    // equality is not one of the five connectives, so `Expensive c = NUM_LE 3 c` is one atom.
    val expensive = force(budgets.meaningOf("Expensive", logic))
    Derivation.axiomsOf(expensive) shouldBe empty

    // Named at the call site rather than found, which is `docs/adr/0024`'s discipline: what a
    // conclusion was allowed to use is visible where somebody asked for it.
    val bridge = force(
      Library
        .of(chain)
        .named(Peano.BelowExcludesAtMost)
        .headOption
        .map(_.theorem)
        .toRight(MissingDefinition(Peano.BelowExcludesAtMost))
    )

    budgets.settle(
      chain.classical,
      "!c:num. NUM_LT c 3 ==> Approved c",
      Vector(expensive, bridge)
    ) match {
      case Domain.Verdict.Settled(theorem, spending) =>
        theorem.hypotheses shouldBe empty

        // The domain axiom is spent, which says the conclusion is still about the RULE and not only
        // about arithmetic: without it, `~(Expensive c)` says nothing about `Approved c`.
        spending.ofTheDomain shouldBe Set("CheapIsApproved")

        // And the half the card asked this report to grow. `Expensive` cost no axiom and appears in
        // neither column above, so a reader told only about axioms would be told that a claim
        // resting on a translation rests on nothing.
        spending.defined shouldBe Set("Expensive")
        spending.summary should include("interpreted rather than assumed")

      case other => fail(s"an interpreted domain is what makes this claim statable: $other")
    }
  }

  it should "still refuse the same claim where the same description is built abstractly" in {
    // The negative control the card insists stays, and it stays NON-VACUOUS: the description is the
    // same value, so what is being compared is the interpretation and not two different domains.
    // Without it, the assertion above would hold of a domain nobody could have written abstractly.
    val abstractly = force(Domain.build(chain.widest.theory, chain.widest.notation, budgetRule))

    Parser.proposition(abstractly.theory, abstractly.notation, "!c:num. NUM_LT c 3 ==> Approved c") match {
      case Left(_) => succeed
      case Right(goal) =>
        abstractly.settle(chain.classical, goal) match {
          case Domain.Verdict.Refused(why) => withClue(s"$why\n") { succeed }
          case other => fail(s"the abstract build cannot reach this claim: $other")
        }
    }
  }

  it should "refuse an interpretation of a name the domain does not declare" in {
    // A typo in the map is not a decision, and the failure it would otherwise produce is a domain
    // silently built without the meaning its caller thought they had given it.
    Domain.build(
      chain.widest.theory,
      chain.widest.notation,
      budgetRule,
      Domain.Interpretation(types = Map("expense" -> TyApp(Natural.TypeName, Nil)), meanings = Map.empty)
    ) match {
      case Left(error) =>
        error.message should include("expense")
        error.message should include("does not declare")
      case Right(_) => fail("an interpretation naming a type this domain has not got is a typo")
    }
  }

  it should "refuse to hand back a meaning that is not a proposition" in {
    // The named limit of `meaningOf`. A constant interpreted as a FUNCTION into `num` is interpreted
    // just as usefully, and what a claim about it needs is rewriting rather than a skeleton; this
    // refuses rather than handing back something that looks like a bridge and decides nothing.
    val measured = Domain(
      name = "the budget rule",
      typeOperators = Vector("cost" -> 0),
      constants = Vector("Size" -> Type.fun(cost, TyApp(Natural.TypeName, Nil))),
      axioms = Vector.empty
    )

    val built = force(
      Domain.build(
        chain.widest.theory,
        chain.widest.notation,
        measured,
        Domain.Interpretation(
          types = Map("cost" -> TyApp(Natural.TypeName, Nil)),
          meanings = Map("Size" -> "\\c:num. c")
        )
      )
    )

    val logic = force(chain.classical.logic.over(built.theory))

    built.meaningOf("Size", logic) match {
      case Left(error) => error.message should include("answering a proposition")
      case Right(theorem) => fail(s"a meaning that is not a proposition is not a bridge: $theorem")
    }
  }
}
