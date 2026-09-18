package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Chain, Field, Library, Linarith, LinearForm, Order, Real, RealTheory, Ring, Signature}

/**
 * One entry point for "prove this goal", and one rule for which refusal survives.
 *
 * Until this existed every caller wrote its own two lines — try LINARITH, then RING — and kept
 * whichever refusal came last. That is how a goal whose real obstacle is division came back saying
 * "restate it as an equation": LINARITH refused for the right reason, RING refused because a
 * strict inequality is not an equation, and the caller reported the second.
 *
 * Measured on the frozen corpus of 2026-09-07, five goals were refused and **none** of the five
 * messages named the actual obstacle. The taxonomy was right — every refusal arrived as a
 * `RestateTheProblem`, which looks well formed — and the content came from whoever spoke last.
 *
 * == The rule ==
 *
 * The procedure whose fragment recognises the goal's shape is the one whose refusal is reported.
 * LINARITH decides goals about the order, equalities between reals, and conjunctions of those;
 * RING decides equations. A goal of neither shape is nobody's, and that is said as itself rather
 * than borrowed from a procedure that was never the right address.
 *
 * The rule is shape-directed rather than confidence-directed on purpose. "Which procedure got
 * furthest" would need a measure of progress that neither procedure reports, and inventing one
 * would put a guess in the one place this repository is careful not to guess.
 *
 * == The one thing asked after everything else ==
 *
 * Since 2026-09-15 a goal none of the procedures settle and no single lemma states is put to
 * `Chaining`, which is backward chaining over the library with the obligations of a match becoming
 * subgoals and each subgoal offered back to everything above. It can only add a theorem: its failure
 * leaves the refusal the shape rule chose, because it recognises no shape and so has no claim on the
 * message.
 *
 * == What it does not do ==
 *
 * It does not try harder than the procedures do. A goal both could take is offered to both, and if
 * both refuse both refusals are carried, because a caller that can read only one of them is better
 * served by the one for its shape and a caller that can read both learns more than either.
 *
 * And it does not route to `Field`. `Field` is asked, on an equation the other two have refused,
 * but only for what it would charge: it settles such a goal by cancelling a denominator, which
 * costs `~(d = 0)` for each one and takes the quantifier off the variable that condition names.
 * Returning that theorem from here would hand a conditional result to callers who read this
 * method's `Right` as "proved", which is the misleading thing this repository exists not to do. So
 * the theorem is discarded and the price is reported as [[ProvableOnlyUnder]]: a caller that wants
 * it asks `Field` itself, where the sequent shows what the theorem rests on. Naming the condition
 * is also what a caller can act on, where "the two normal forms differ" is not.
 */
final class Prove private (
  val order: Order,
  val ring: Ring,
  val linarith: Linarith,
  val field: Field,
  val reals: Signature,
  /**
   * The lemmas this development already holds, and the connectives to apply one with.
   *
   * Asked before the decision procedures, and the reason is a measurement rather than an ordering
   * principle. `!x. 0 <= x * x` is `SQUARE_NONNEG`, a lemma sitting four lines from the prover, and
   * until 2026-09-11 asking for it got a refusal: LINARITH is the right address for an inequality
   * and cannot take a goal whose atom is a product of unknowns, so the answer was "nobody here can
   * do this" from a system that had it written down. Reading somebody else's benchmark is what
   * turned that from a suspicion into a row.
   *
   * A lookup rather than a search: `Apply` decides what the lemma's variables must be for its
   * conclusion to *be* the goal, and only a candidate that then owes **nothing** is used. A lemma
   * that would settle the goal at the cost of an obligation is not a proof of the goal, and taking
   * one would put a hypothesis on the left of a theorem this method's `Right` says is unconditional.
   *
   * `None` is a development with no library, and it is a real configuration rather than a degraded
   * one: `Prove.construct` over somebody's own order has no facts to look in until they pass some.
   */
  val library: Option[(Library, Logic)],
  /**
   * The classical extension, where the caller holds one, and what it buys is completeness.
   *
   * `Option` for the same reason [[library]] is one: an `Order` has never heard of the classical
   * axioms, so a prover built over somebody's own order has none and says so by doing less. Only
   * [[Prove.construct]] over a `Chain` can supply it, because only a chain carries one.
   *
   * **A second `Classical` must never be built here to fill the gap.** `Classical.construct`
   * asserts the choice axiom into a theory, so building one over a logic that already has it is
   * two theories declaring one name, which is the case `docs/adr/0008` leaves open and
   * `SoundnessAttackSpec` derives `|- F` from. The capability is absent or it is passed in.
   */
  val classical: Option[Classical]
) {

  /**
   * What it READS a goal in, which need not be what it DECIDES over.
   *
   * The two were one object until 2026-09-10 and the reason was that a `RealTheory` was the only
   * development there was. It stopped being true when the naturals landed: `Chain.standard`
   * assembles a signature holding `num` beside `real`, and until this parameter existed no entry
   * point a caller drives could so much as **parse** a goal mentioning a natural number, so
   * everything that work bought was reachable only from inside `modules/theories`.
   *
   * Reading wider than deciding is the honest arrangement and not a compromise. The procedures
   * below are decision procedures for fragments of the reals and they refuse everything else by
   * name, which is this repository's rule for a tactic. A goal about `num` now gets read and then
   * refused for what it is, where before it could not be stated; "I cannot parse that" and "that is
   * outside my fragment" are different answers and only the second is true.
   */

  /**
   * A goal in the theory's notation, proved or refused with the refusal that fits its shape.
   *
   * The text is read first, so a goal that does not parse is a [[RepairTheText]] and never a
   * complaint from a procedure that was handed nothing.
   */
  def apply(text: String): Either[TacticError, Kernel.Thm] =
    TacticError.lift(reals.proposition(text)).flatMap(apply)

  /** The same, for a goal already read. */
  def apply(goal: Term): Either[TacticError, Kernel.Thm] =
    held(goal) match {
      case Some(theorem) => Right(theorem)
      case None =>
        decided(goal) match {
          case Right(theorem) => Right(theorem)
          // Asked last, and its failure changes no refusal. The rule this class is about is that the
          // procedure whose fragment recognises the goal's shape is the one whose refusal is
          // reported, and chaining recognises no fragment: it either reaches the goal or does not,
          // so it can add a theorem and must not take a message away from the procedure that had
          // something to say. `Chaining.prove` names its own bound to a caller that asks it
          // directly, which `chained` deliberately does not turn into a refusal here.
          case Left(refusal) => chained(goal).toRight(refusal)
        }
    }

  /**
   * The goal as an instance of a lemma already held, owing nothing.
   *
   * Every entry is tried rather than the first that matches, because two developments can hold a
   * name each and because a lemma that matches and owes an obligation must not stop the search: the
   * next one may match and owe none. The order among those that owe nothing does not matter, since
   * each is a proof of the same goal.
   */
  /**
   * What this prover settles **without** chaining: the scan, then the decision procedures.
   *
   * The two steps [[apply]] takes before it reaches `Chaining`, published because two callers need
   * them and neither can get at them otherwise.
   *
   * A caller that wants the cheap answer is one: chaining is bounded but not free, and a consumer
   * asking many goals it expects to be refused pays for a search every time.
   *
   * The other is a test of `Chaining` itself, and it is the one that forced this method to exist.
   * `Chaining` takes its leaf as an argument, and the obvious leaf to hand it in a test is this
   * prover — which now **contains** a `Chaining`, so what is measured is two searches nested, at
   * twice the depth asked for. Two assertions about the depth bound passed for the wrong reason that
   * way and two others failed for it; what they were reading was the leaf's own search, not the
   * bound under test.
   */
  def directly(goal: Term): Either[TacticError, Kernel.Thm] =
    held(goal).map(Right(_)).getOrElse(decided(goal))

  /**
   * The library searched rather than scanned: a lemma that owes an obligation, and the obligation
   * proved by everything above.
   *
   * [[held]] is the scan and takes only what owes nothing, for the reason its own comment gives.
   * This is what makes the ones it turns away usable, and it is the first thing here that puts two
   * lemmas together. `Chaining` carries the loop, the index and the bounds; what is passed in is the
   * leaf, which is this class's own two steps, so a subgoal of a chained proof is offered to RING,
   * to LINARITH, to the propositional fragment and to the scan before anything recurses.
   *
   * `None` where there is no library, which is the same real configuration [[library]] describes.
   */
  private def chained(goal: Term): Option[Kernel.Thm] =
    searchFor(goal) match {
      case Some(Chaining.Outcome.Proved(theorem, _)) => Some(theorem)
      case _ => None
    }

  /**
   * The chaining search over this prover's own leaf, with what it found or the bound it reached.
   *
   * Public because two callers cannot get at it otherwise and both are ones this repository cares
   * about. A measurement wants to know **which** lemmas were chained, and the theorem does not say:
   * `Derivation.restingOn` answers a coarser question and a search that used one lemma and a search
   * that used two are the claim being made and its negation. And a session that wants to know
   * whether it was the bound that stopped it, rather than the absence of a route, has nowhere else
   * to ask: [[apply]] deliberately reports the procedure's refusal and not this one, for the reason
   * its own comment gives.
   *
   * `None` where there is no library, which is the configuration [[library]] describes rather than a
   * degraded one.
   */
  def searchFor(goal: Term): Option[Chaining.Outcome] =
    chaining.map(search => search.prove(goal, target => held(target).orElse(decided(target).toOption)))

  /** Built once, because the index over the library is what makes a question milliseconds. */
  private val chaining: Option[Chaining] =
    library.map { case (lemmas, logic) => Chaining(logic, lemmas) }

  /**
   * The searches this prover reaches, which is not the same as the searches that exist.
   *
   * Only `Intuitionistic` is certain. `Propositional` needs the classical extension and `Chaining`
   * needs a library, and a prover built over somebody's own order has neither, so this answers
   * `Intuitionistic` alone there and the whole set over a chain. That is the same real
   * configuration [[library]] and [[classical]] describe rather than a degraded prover.
   *
   * **No count of them appears in this comment**, deliberately, and it is the defect this method
   * exists to remove written one floor down: a docstring that said "two of the three" would be a
   * figure beside the thing it counts, going stale on the case after next, in a file arguing
   * against exactly that. `docs/naming.md` carries the instance this repository found first.
   *
   * **It exists because the front page carried the number by hand and the number drifted.** The
   * row about proof search answered *two* from the day it was written while naming three of them,
   * and nothing went red, because a count in prose is a fact written twice and the second copy is
   * the one nobody recounts. The row no longer carries a count: it names them, and
   * `DocumentationSpec` asserts that what it names is exactly what this returns, so the guard fails
   * both on a search this reaches that the row has never heard of and on one the row still
   * describes after it went.
   *
   * **What it does not cover, and it is the direction a reader should not assume.** Adding a case
   * to [[Prove.Search]] without wiring it here is a compile error, because the match below is
   * exhaustive over a closed set under `-Xfatal-warnings`. Building a fourth search in this class
   * and declaring no case for it is not caught anywhere: nothing here knows what a search is except
   * that enumeration, and a test that tried to learn it from the source would be asking the same
   * question it is answering.
   */
  def searches: Vector[Prove.Search] =
    Prove.Search.values.toVector.filter {
      case Prove.Search.Intuitionistic => true
      case Prove.Search.Propositional => propositional.isDefined
      case Prove.Search.Chaining => chaining.isDefined
    }

  private def held(goal: Term): Option[Kernel.Thm] =
    library.flatMap { case (lemmas, logic) =>
      lemmas.entries.view
        .flatMap(entry => Apply.to(logic, entry.theorem, goal).toOption)
        .filter(application => application.obligations.isEmpty && application.theorem.hypotheses.isEmpty)
        // The goal's own quantifiers went off before matching and go back on here, which is the one
        // step `Apply` deliberately leaves to its caller: it cannot know whether the obligations
        // are going to be discharged first.
        .flatMap(application =>
          logic.rules.genAll(application.theorem, application.generalising.toList).toOption
        )
        .find(theorem => theorem.conclusion == goal)
    }

  private def decided(goal: Term): Either[TacticError, Kernel.Thm] =
    Prove.addressOf(reals, goal) match {
      case Prove.Address.Order => TacticError.lift(linarith.prove(goal))

      case Prove.Address.Equation =>
        // Both are the right address for an equation between reals: RING decides it by
        // normalising, LINARITH by bounding it on both sides. RING is asked first because it is
        // the one that decides the shape outright, and its refusal is the one kept when both fail.
        ring.prove(goal) match {
          case Right(theorem) => Right(theorem)
          case Left(fromRing) =>
            linarith.prove(goal) match {
              case Right(theorem) => Right(theorem)

              // Both refused, and there are three things the refusal can be, in decreasing order
              // of what it tells a caller. `Field` proves it at a price, and the price is named.
              // Or a side carries something neither procedure reads, and that is named. Or RING's
              // "the two normal forms differ" is the whole of what is known, which is the honest
              // answer when the identity is simply false. The example this comment used to carry,
              // `2 * ((3 * n + 1) / 2) = 3 * n + 1`, is proved since 2026-09-09; the witness for
              // the first case is `(2 * y) / y = 2`, which holds wherever `y` is not zero.
              case Left(_) =>
                Left(priceOf(goal).getOrElse(FromLogic(named(goal).getOrElse(fromRing))))
            }
        }

      case Prove.Address.Propositional =>
        intuitionistic.prove(goal) match {
          case Right(theorem) => Right(theorem)
          // The refusal that survives is the second one where there is a second procedure, which is
          // the opposite of this class's usual rule and is right here for the reason that rule is:
          // the first procedure's refusal is about a fragment, and once a wider procedure has run
          // that message is about the wrong one. `Propositional` refuses by exhibiting an
          // assignment, which is what a caller can act on.
          case Left(fromIntuitionistic) =>
            propositional match {
              // No classical extension to ask, so the intuitionistic answer is the whole of what is
              // known, and what a caller has to be told is which of two things stopped it. The
              // calculus says "not a goal this calculus reaches", which names a fragment; what it
              // does not say is that the goal may be classically valid and that this prover was
              // built without the axioms for that, which is the configuration and not the
              // mathematics. A refusal that stopped short is kept verbatim: `Standing.Exhausted`
              // and `Standing.Unread` are the distinction `LogicError` exists to keep, and
              // rewriting a bound that was reached into a statement about the goal would collapse
              // them.
              case None =>
                Left(FromLogic(
                  if (fromIntuitionistic.standing.stoppedShort) fromIntuitionistic
                  else withoutTheClassicalAxioms(goal)
                ))
              case Some(classicalFragment) => TacticError.lift(classicalFragment.prove(goal))
            }
        }

      case Prove.Address.Nobody(why) =>
        Left(FromLogic(NotOfForm(why, goal)))
    }

  /**
   * A propositional goal the free calculus refused, where there is no classical procedure to ask.
   *
   * The message names the caller's configuration rather than the goal's shape, and that is the
   * whole of why it exists. The calculus refuses with "a goal this calculus reaches", which names a
   * fragment and reads as a fact about the statement; what it does not say is that the statement
   * may be perfectly valid and that this prover holds none of the axioms that would settle it. An
   * author told the first rewrites the statement for ever, and an author told the second builds the
   * prover over a chain and asks again.
   *
   * **One literal and not a concatenation**, which is not a style preference:
   * `NotationBoundarySpec` classifies every expression a refusal writes into its own prose, and a
   * description that is neither a literal nor an interpolation is one the scan cannot decide about
   * and has to be listed by hand. A sentence with nothing in it from a term has no business being
   * on that list.
   */
  private def withoutTheClassicalAxioms(goal: Term): LogicError =
    NotOfForm("a goal intuitionistic logic decides; this one may be classically valid, and this prover has no classical axioms", goal)

  /**
   * The whole intuitionistic propositional fragment, negation included, over whatever theory this
   * reads in.
   *
   * Built here rather than passed in because it needs nothing a caller could choose: the
   * connectives are the signature's and the rules come with them.
   *
   * **It is asked here and `Minimal` is not, and until 2026-09-18 it was the other way round.**
   * `docs/adr/0022` made `Minimal` a fragment gate whose search *is* this calculus: `Minimal.prove`
   * is this method behind a test for a negation. So asking `Minimal` here decided nothing extra and
   * turned away the goals with a negation in them, which went on to the classical procedure and
   * came back at the choice axiom where this reaches them at none. The front page had already been
   * rewritten to call `Minimal` "a fragment gate rather than a search of its own" while this class
   * still asked it as a search, which is a fact written twice and disagreeing.
   *
   * `Minimal` did not go anywhere: [[Prove.addressOf]] is where it is spent now, and its `reads`
   * and `declines` are what put a goal at this address in the first place. What it stopped being is
   * the thing that answers once the goal is here. `docs/adr/0023` is the decision, and what it
   * rejects is the three-step insertion this came from: gate, then calculus, then classical, which
   * runs one search twice.
   *
   * **What it buys, measured on two populations that answer different questions.** Over the
   * library of `Chain.standard`: of 503 statements 184 take this address and **two** carry a
   * negation, both of them `Classical`'s own, the excluded middle and double negation, which are
   * classical by construction and refused here. Over the Mathlib ring corpus and the statable slice
   * of miniF2F, **none** takes this address at all. So nothing this repository already proves or
   * measures changes price, and that is a fact about those populations rather than about the
   * change: they are arithmetic, and a goal reaches this address with a negation in it only where
   * every atom is a bare proposition.
   *
   * The population the change is actually about is the propositional formulas themselves, and over
   * every one of at most six nodes on two atoms — 1116 of them, 1114 at this address — 152 carry a
   * negation and are classically provable, and **58 of those are provable here**, at no axiom where
   * the classical procedure charges one. The other 98 stay classical-only, `p \/ ~p` among them, so
   * the procedure below keeps a real job. And the cell that decides the order: of the 32 goals
   * `Minimal` proves, this calculus proves **all 32**, because `Minimal.prove` *is* this method
   * behind a test for a negation — which is why asking `Minimal` first added nothing and cost the
   * 58.
   */
  private val intuitionistic: Intuitionistic = Intuitionistic(reals.logic)

  /**
   * The whole classical propositional fragment, decided by a solver and certified, where there is
   * one to build.
   *
   * Asked **after** [[intuitionistic]] and never instead of it, and the order is a measurement
   * rather than a preference: on the goal both take, `(p /\ q) ==> (q /\ p)`, the free calculus
   * costs 182 primitive inferences and **no axiom** while this costs 1236 and the choice axiom,
   * re-measured on 2026-09-18 when the routing moved. The pair read 216 and 1242 here until then,
   * which was `Minimal`'s own search against this one before `docs/adr/0022` replaced it; both
   * halves of a pair go stale together when what produced them is replaced. A theorem resting on
   * nothing is worth more than the same theorem resting on something, so the cheaper address keeps
   * the goals it can reach.
   *
   * **That is the whole answer to "what does a caller get when two procedures reach one theorem at
   * two prices", and it is written here rather than left implicit in the order.** The theorem is
   * the same term either way; what differs is `Derivation.axiomsOf`, and the rule is that the
   * cheapest procedure that settles the goal is the one whose theorem is returned. `Cost` reports
   * the price of what it was given and names no procedure, which stays true because the order here
   * is by price: naming the procedure would be a second way of saying the same thing and the one
   * that goes stale.
   *
   * What it adds is the rest of the fragment, which is the classical part and no more. Peirce's law
   * and the excluded middle are the witnesses: neither is intuitionistically provable, both are
   * proved here, and `IntuitionisticSpec` holds that boundary from the other side.
   */
  private val propositional: Option[Propositional] = classical.map(Propositional(_))

  /**
   * What `Field` would charge for this goal, as a refusal, when it can settle it at all.
   *
   * The theorem is dropped on purpose and the class comment argues why. What is kept is its
   * hypothesis list, which is the whole of what a caller has to decide about.
   *
   * **An empty list is not this case and falls through.** A cancellation rule that never fires
   * contributes no hypothesis, so `Field` proving something with nothing assumed means it did no
   * more than the ring normalisation did, and RING has already refused this goal. Reporting a price
   * of zero would announce a charge where there was none and would bury the refusal that says what
   * the obstacle actually is.
   */
  private def priceOf(goal: Term): Option[TacticError] =
    field
      .prove(goal)
      .toOption
      .map(theorem => field.conditions(theorem).toVector)
      .filter(_.nonEmpty)
      .map(ProvableOnlyUnder(goal, _))

  /**
   * The obstacle a procedure can name in this goal, as a refusal, when there is one.
   *
   * Shared between the two addresses because the constructions neither procedure reads are the
   * same constructions: a quotient, an inverse, a product of two unknowns.
   */
  private def named(goal: Term): Option[LogicError] = {
    val body = Logic.stripForall(goal).map(_._2).getOrElse(goal)
    val conclusion = reals.logic.destImp(body).map(_._2).getOrElse(body)

    LinearForm.obstacleIn(reals, conclusion)
      .map(obstacle => NotOfForm(s"a goal these procedures can read: $obstacle", conclusion))
  }

  /**
   * Which procedure the goal belongs to, without attempting it.
   *
   * Public because a caller deciding whether to spend anything at all wants the answer before the
   * cost, and because a session shown a refusal wants to know whether rephrasing could ever reach
   * a procedure or whether nothing here is the right address.
   */
  def addressOf(goal: Term): Prove.Address = Prove.addressOf(reals, goal)
}

object Prove {

  /** Which procedure a goal's shape belongs to. */
  enum Address:

    /** An inequality, or a conjunction of goals that are themselves LINARITH's. */
    case Order

    /** An equation between reals: RING normalises it, LINARITH bounds it. */
    case Equation

    /**
     * A statement built from propositions with `/\`, `\/`, `==>` and `~`.
     *
     * Reached only where the arithmetic addresses are not, which is deliberate and is what keeps
     * this from changing any answer that already existed: a goal about the order is the order's
     * whatever else it also is. What arrives here is what used to arrive at [[Nobody]].
     *
     * **The negation is in the shape and was never out of the address**: `Minimal.declines` is half
     * of what puts a goal here, and it fires precisely on a statement of bare propositions that has
     * a negation in it. What was out of the address was nothing; what was out of the free procedure
     * serving it was the negation, and since 2026-09-18 the procedure serving it is the one that
     * takes them.
     */
    case Propositional

    /** Neither shape, and `why` names what a goal would have to be. */
    case Nobody(why: String)

  /**
   * A search this prover reaches, named as the front page names it.
   *
   * The closed set behind [[Prove.searches]], and it is a type rather than a set of strings because
   * a spelling that resolves to nothing is exactly what this is here to stop: the count it replaces
   * on the front page went stale in prose, where nothing resolves.
   *
   * **A search is not a decision procedure, and the distinction is the row's subject rather than
   * this file's taxonomy.** RING, LINARITH and `Field` decide a fragment: handed a goal of their
   * shape they answer, and handed anything else they refuse by name, with no alternative explored
   * on the way. Each case below explores alternatives it may abandon, which is what makes "no
   * given-clause loop, no saturation" a sentence worth writing about these and not about those.
   * [[held]] is not one either: it is a scan of the library that takes a lemma owing nothing, and a
   * scan that never backtracks is a lookup.
   *
   * **[[Search.Propositional]] and [[Address.Propositional]] are different things with one name.**
   * The address is a property of the goal, which shape decides where it is sent; this is the
   * procedure that is sent it. They are separate enumerations because a goal can have the address
   * and reach no procedure, which is what happens over an order carrying no classical extension.
   */
  enum Search(val spelling: String):

    /**
     * The intuitionistic propositional fragment, negation included, asked first because it costs
     * no axiom.
     *
     * Always reached: it is built from the signature's own connectives, so there is no
     * configuration in which a prover has no copy of it.
     *
     * **This case was `Minimal` until 2026-09-18**, and the rename is the enumeration catching up
     * with `docs/adr/0022`: `Minimal` became a gate over this calculus, so a list of the searches a
     * prover reaches that named `Minimal` was naming the gate and not the search. `Minimal` is
     * still reached, by [[Prove.addressOf]], and what it decides there is the **address** rather
     * than the goal.
     */
    case Intuitionistic extends Search("Intuitionistic")

    /** The whole classical propositional fragment, where the caller supplied a `Classical`. */
    case Propositional extends Search("Propositional")

    /** Backward chaining over the library, where there is a library to chain over. */
    case Chaining extends Search("Chaining")

  /** Over the standard theory. */
  lazy val standard: Prove =
    new Prove(
      Order.standard,
      Ring.standard,
      Linarith.standard,
      Field.standard,
      Order.standard.reals,
      libraryOf(Order.standard),
      None
    )

  /**
   * The facts of the developments a prover was built over, as something it can look in.
   *
   * The connectives have to be widened first, and that is not a detail: `Rules.spec` asks the
   * theory for the quantifier constant **at the type the universal ranges over**, and
   * `Real.standard` deliberately stays over a logic that has never heard of `real`. Without the
   * widening every application of every lemma would refuse with "no type operator named real", and
   * the library would look empty rather than unreachable. `Divisibility` documents the same
   * widening for the same reason.
   *
   * A failure to widen gives `None`, which is a prover with no library rather than a prover that
   * does not build: a lookup that cannot be performed is a capability that is absent, and absent is
   * something this system says rather than something it crashes over.
   */
  private def libraryOf(order: Order): Option[(Library, Logic)] =
    order.reals.logic
      .over(order.reals.theory)
      .toOption
      .map(logic =>
        (
          Library.of(
            Vector(
              "Real, assumed" -> order.reals.axioms,
              "Real, defined" -> order.reals.definitions,
              "Positivity" -> order.ring.positivity.facts,
              "Order" -> order.facts
            )
          ),
          logic
        )
      )

  /**
   * Over a theory of one's own, which is what `RealTheory.extended` produces.
   *
   * A failure here is a failure to build LINARITH or `Field` over that order, which is a defect in
   * the theories rather than something a caller chose, so it is returned rather than raised.
   */
  def construct(order: Order): Either[LogicError, Prove] = construct(order, order.reals)

  /**
   * The same, reading in a signature wider than the one it decides over.
   *
   * `Prove.construct(chain.order, chain.series)` is the call that lets a goal mentioning `num` be
   * stated. What comes back still decides only the fragments of the reals its procedures decide,
   * and says so by name on everything else.
   */
  def construct(order: Order, reals: Signature): Either[LogicError, Prove] =
    for {
      linarith <- Linarith.construct(order)
      field <- Field.construct(order.ring.arithmetic)
    } yield new Prove(order, order.ring, linarith, field, reals, libraryOf(order), None)

  /**
   * The prover a chain deserves: its widest signature, and everything it holds.
   *
   * [[standard]] is over `Order.standard`, which is the reals and nothing else, and that is right
   * for a caller who has only those. A chain has more — `num` with its arithmetic, finite sums and
   * products, the embedding — and until this existed a caller holding one had to assemble the
   * three pieces themselves and would get the library wrong, because the obvious call takes the
   * library an `Order` can reach and an `Order` has never heard of `num`.
   *
   * What comes back reads in `Chain.widest`, decides the same fragments of the reals it always did,
   * looks in the whole chain's library before any of them, and reaches the propositional fragment
   * for a goal none of them address.
   */
  def construct(chain: Chain): Either[LogicError, Prove] =
    Linarith
      .construct(chain.order)
      .flatMap(construct(chain.order, chain.widest, Library.of(chain), _, Some(chain.classical)))

  /**
   * The same, with a library the caller assembled rather than the one the order can reach.
   *
   * [[libraryOf]] collects the facts of the developments an `Order` is built over, which is the
   * reals and nothing else, because that is all an `Order` knows about. A chain that has the
   * naturals and finite sums on top holds a great deal more, and until this existed the prover
   * could not use any of it: `!n:num. ZERO <= n` is `NUM_ZERO_LE`, a lemma standing in the same
   * development, and asking for it got a refusal. Found by the trap corpus for the naturals, which
   * reported the pair as separated by nothing but the way the two print.
   *
   * The connectives are widened against the signature the caller is reading in rather than against
   * the reals, because a lemma about `num` is specialised at `num`.
   */
  def construct(order: Order, reals: Signature, held: Library): Either[LogicError, Prove] =
    Linarith.construct(order).flatMap(construct(order, reals, held, _, None))

  /**
   * The same, with the linear procedure supplied rather than built from the order.
   *
   * The one thing a caller can choose about it is where its two bounds sit, and those became
   * parameters on 2026-09-11 so that what they cut could be measured. A measurement that cannot
   * reach through this entry point measures half the surface: `Cost` asks `Prove`, `Prove` builds
   * its own, and the bound a caller moved would have been ignored.
   */
  def construct(
    order: Order,
    reals: Signature,
    held: Library,
    linarith: Linarith,
    classical: Option[Classical]
  ): Either[LogicError, Prove] =
    for {
      field <- Field.construct(order.ring.arithmetic)
      logic <- reals.logic.over(reals.theory)
    } yield new Prove(order, order.ring, linarith, field, reals, Some((held, logic)), classical)

  /**
   * The shape test, applied under any leading quantifiers and through any antecedent.
   *
   * A goal is addressed by its conclusion, because that is what a procedure has to produce; the
   * hypotheses only ever help. Quantifiers come off first for the same reason they come off inside
   * the procedures.
   */
  def addressOf(reals: Signature, goal: Term): Address = {
    val body = Logic.stripForall(goal).map(_._2).getOrElse(goal)

    // Every antecedent, not one. `!x y. 0 < x ==> 0 < y ==> 0 < x + y` is the shape this repository
    // writes its own lemmas in, and until 2026-09-10 it was addressed by its second antecedent
    // rather than by its conclusion, so it went to `Nobody` while the same claim written with `/\`
    // was decided at once.
    def conclusionOf(current: Term): Term =
      reals.logic.destImp(current).map(pair => conclusionOf(pair._2)).getOrElse(current)

    conclusionAddress(reals, conclusionOf(body)) match {
      // Asked last and only where nothing else answered. A propositional reading of an arithmetic
      // goal is a real reading and would sometimes even succeed, and taking it would move goals
      // away from the procedures written for them for no gain. What this picks up is the set that
      // was refused before it existed.
      case Address.Nobody(why) =>
        val fragment = Minimal(reals.logic)

        // Either half of the propositional address: what the free fragment reads, and what it
        // recognises and turns away. The second used to be a refusal naming the negation, and it was
        // the right answer while the free fragment was the only propositional procedure there was.
        // It is not any more, and a goal like `p \/ ~p` was being told to remove a negation by a
        // system that can now settle it.
        //
        // **Narrow on purpose, and the narrowness is `Minimal.declines`'s.** It fires only where
        // every atom is a bare proposition, so nothing arithmetic is taken away from the procedure
        // whose message is worth more: `~(x = 0)` has an arithmetic atom, is not this address, and
        // keeps the refusal LINARITH would give it.
        if (fragment.reads(goal) || fragment.declines(goal).isDefined) Address.Propositional
        else Address.Nobody(why)
      case other => other
    }
  }

  private def conclusionAddress(reals: Signature, conclusion: Term): Address =
    reals.logic.destConj(conclusion) match {
      // A conjunction is LINARITH's exactly when both sides are, which is what its own route does:
      // it proves each conjunct and introduces. A conjunction with one side outside the fragment
      // is outside it, and saying so names the side that is.
      case Some((left, right)) =>
        (conclusionAddress(reals, left), conclusionAddress(reals, right)) match {
          case (Address.Nobody(why), _) => Address.Nobody(why)
          case (_, Address.Nobody(why)) => Address.Nobody(why)
          case _ => Address.Order
        }

      case None =>
        if (Order.destOrder(reals, conclusion).isDefined) Address.Order
        else
          Term.destEq(conclusion) match {
            case Some((left, _)) if Term.typeOf(left) == Real.realType => Address.Equation
            case Some(_) =>
              Address.Nobody("an equation between reals; this one is between something else")

            // A denial is LINARITH's exactly when what it denies is, which is what its own route
            // does: assume the denied thing, find the facts impossible with it, discharge. Without
            // this line `!x. 0 < x ==> ~(x = 0)` was refused here before the procedure that decides
            // it was ever asked.
            case None =>
              reals.logic.destNot(conclusion) match {
                // Always LINARITH's, whatever is denied, because LINARITH is the only one of the
                // two with the route: it assumes the denied thing and finds the facts impossible
                // with it. Sending a denied equation to RING would spend a normalisation on a goal
                // RING has no reading of.
                case Some(denied) =>
                  conclusionAddress(reals, denied) match {
                    case Address.Nobody(why) => Address.Nobody(why)
                    case _ => Address.Order
                  }
                case None =>
                  Address.Nobody(
                    "an inequality, an equation between reals, a denial of one, or a conjunction"
                  )
              }
          }
    }
}
