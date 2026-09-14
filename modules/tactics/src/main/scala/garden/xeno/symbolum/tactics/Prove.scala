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
  val library: Option[(Library, Logic)]
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
      case None => decided(goal)
    }

  /**
   * The goal as an instance of a lemma already held, owing nothing.
   *
   * Every entry is tried rather than the first that matches, because two developments can hold a
   * name each and because a lemma that matches and owes an obligation must not stop the search: the
   * next one may match and owe none. The order among those that owe nothing does not matter, since
   * each is a proof of the same goal.
   */
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

      case Prove.Address.Propositional => TacticError.lift(minimal.prove(goal))

      case Prove.Address.Nobody(why) =>
        Left(FromLogic(NotOfForm(why, goal)))
    }

  /**
   * The negation-free propositional fragment, over whatever theory this reads in.
   *
   * Built here rather than passed in because it needs nothing a caller could choose: the
   * connectives are the signature's and the rules come with them.
   */
  private val minimal: Minimal = Minimal(reals.logic)

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
     * A statement built from propositions with `/\`, `\/` and `==>`, and no negation in it.
     *
     * Reached only where the arithmetic addresses are not, which is deliberate and is what keeps
     * this from changing any answer that already existed: a goal about the order is the order's
     * whatever else it also is. What arrives here is what used to arrive at [[Nobody]].
     */
    case Propositional

    /** Neither shape, and `why` names what a goal would have to be. */
    case Nobody(why: String)

  /** Over the standard theory. */
  lazy val standard: Prove =
    new Prove(
      Order.standard,
      Ring.standard,
      Linarith.standard,
      Field.standard,
      Order.standard.reals,
      libraryOf(Order.standard)
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
    } yield new Prove(order, order.ring, linarith, field, reals, libraryOf(order))

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
    construct(chain.order, chain.widest, Library.of(chain))

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
    Linarith.construct(order).flatMap(construct(order, reals, held, _))

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
    linarith: Linarith
  ): Either[LogicError, Prove] =
    for {
      field <- Field.construct(order.ring.arithmetic)
      logic <- reals.logic.over(reals.theory)
    } yield new Prove(order, order.ring, linarith, field, reals, Some((held, logic)))

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

        if (fragment.reads(goal)) Address.Propositional
        // Recognised and turned away, which is a better answer than the arithmetic shapes: a goal
        // with a negation in it is OUT of the fragment that costs no axiom, and a caller told only
        // the shapes reformulates a statement that has nothing wrong with it.
        else Address.Nobody(fragment.declines(goal).getOrElse(why))
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
