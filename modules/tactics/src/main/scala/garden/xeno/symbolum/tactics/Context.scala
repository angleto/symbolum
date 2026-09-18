package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A goal's own hypotheses, as facts something can look in, and the deduction that pays for them.
 *
 * Until this existed a goal `H ==> C` was put to the library and to the search **whole**: a lemma
 * had to conclude the implication itself, and `H` was a piece of syntax on the way to `C` rather
 * than something known. Every statement of the miniF2F corpus is written that way, hypotheses
 * conjoined into one antecedent, so the corpus was being asked a question with its own premises
 * turned off.
 *
 * == What a local fact is, which is the decision this file carries ==
 *
 * `Kernel.assume A` gives `A |- A`, and that theorem is a lemma in every sense `Apply` cares
 * about: it has a conclusion to match against, it may carry universals of its own, and where it is
 * an implication `Apply` peels it and owes the antecedent. So nothing in the matching step had to
 * learn what a hypothesis is, and this file adds no rule of inference: what it adds is a **set of
 * theorems the goal itself supplies** and the discharge that removes them again.
 *
 * The price is exactly one relaxation, and it is the one to read before trusting anything here.
 * `Prove.held` and `Chaining` both refuse a candidate whose theorem carries a hypothesis, because
 * their `Right` says the result is unconditional. Under a context that test becomes *carries no
 * hypothesis other than the ones this goal assumed*, and what restores the promise is
 * [[Context.discharge]]: every assumption goes back on as an antecedent, in the order it was
 * written, and the result is compared against the goal as asked. A fold that lost one produces a
 * theorem that is true and is not the one that was asked for, which is the check `Chaining` already
 * argues for at its own end.
 *
 * == The conjunction is split, and the implication is not ==
 *
 * `A /\ B ==> C` yields three facts: the conjunction and both halves. Assuming `A /\ B` and
 * assuming `A` and `B` are the same assumption, which is what `ReachSpec` already says where it
 * reads miniF2F's `(h₀ : 0 < b ∧ 0 < h)` as two hypotheses, and what `Linarith.split` already does
 * one floor down for the linear fragment. The whole conjunction is kept beside its halves because
 * a lemma may be stated with a conjunctive antecedent.
 *
 * An assumption that is **itself an implication** is left whole on purpose, and it is the case a
 * design for this has to answer. `A ==> B` as a fact is a lemma owing `A`: `Apply` reads its body
 * first and peels only where the fuller reading does not match, so a goal `B` gets the obligation
 * `A` and the obligation goes back to the whole surface. Breaking it up here would be doing the
 * search's job in the wrong place, and doing it worse: nothing here knows whether `A` is reachable.
 *
 * == What it does not do ==
 *
 * It does not saturate. No consequence is derived from a fact before something asks for one, and
 * two facts are never put together except by a search that was already going to put two lemmas
 * together. That is the next absence on the front page's list and it is a different piece of work.
 */
final class Context private (
  /**
   * The assumed theorems, each concluding one fact and resting on the antecedent it came from.
   *
   * The conjunction's halves rest on the conjunction, not on themselves, which is why [[assumed]]
   * is the list to discharge and this one is not.
   */
  val facts: Vector[Kernel.Thm],

  /** The goal's antecedents, in the order written, which is the order they go back on in. */
  val assumed: Vector[Term],

  /** What is left to prove once they are assumed. */
  val conclusion: Term,

  /**
   * The goal's own leading universals, taken off before the antecedents were peeled.
   *
   * Off for the same reason `Apply` takes them off: the antecedents mention the variables they
   * bound, so a fact about them cannot be stated under the quantifier. They go back on in
   * [[discharge]], after the antecedents, which is the order that rebuilds the goal as written.
   */
  val generalising: Vector[FVar]
) {

  /** The terms a theorem proved under this context is allowed to still rest on. */
  val allowed: Set[Term] = assumed.toSet

  /**
   * The conclusion proved under this context, turned back into the goal that was asked.
   *
   * The antecedents are discharged innermost first, so `A1` ends up outermost and the implication
   * reads as it was written; then the universals go back on. `Rules.disch` discharges whether or
   * not the hypothesis was used, which is what makes an unused assumption cost nothing rather than
   * break the fold.
   */
  def discharge(logic: Logic, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    assumed
      .foldRight(Right(theorem): Either[LogicError, Kernel.Thm]) { (antecedent, carried) =>
        carried.flatMap(inner => logic.rules.disch(antecedent, inner))
      }
      .flatMap(closed => logic.rules.genAll(closed, generalising.toList))
}

object Context {

  /**
   * The context a goal supplies, where it supplies one.
   *
   * `None` where the goal has no antecedent under its universals, which is not a failure: it is a
   * goal whose premises are already nothing, and a caller has nothing to gain by assuming an empty
   * set and discharging it again.
   */
  def of(logic: Logic, goal: Term): Option[Context] =
    for {
      stripped <- Logic.stripForall(goal).toOption
      (generalising, body) = stripped
      peeled = peel(logic, body, Vector.empty)
      (antecedents, conclusion) = peeled
      if antecedents.nonEmpty
      assumptions <- traverse(antecedents)(term => Kernel.assume(term).toOption)
      facts = assumptions.flatMap(assumption => split(logic, assumption))
    } yield new Context(facts, antecedents, conclusion, generalising)

  /** The antecedents of a chain of implications, and what it finally concludes. */
  private def peel(logic: Logic, current: Term, taken: Vector[Term]): (Vector[Term], Term) =
    logic.destImp(current) match {
      case Some((antecedent, consequent)) => peel(logic, consequent, taken :+ antecedent)
      case None => (taken, current)
    }

  /**
   * A fact and, where it is a conjunction, everything it is a conjunction of.
   *
   * The theorem itself first, so a lemma stated with a conjunctive antecedent still finds it. A
   * projection that refuses is dropped rather than raised: what comes back is the facts that could
   * be taken, and a term that is not a conjunction is simply itself.
   */
  private def split(logic: Logic, fact: Kernel.Thm): Vector[Kernel.Thm] =
    logic.destConj(fact.conclusion) match {
      case None => Vector(fact)
      case Some(_) =>
        Vector(fact) ++
          logic.rules.conjElim1(fact).toOption.toVector.flatMap(split(logic, _)) ++
          logic.rules.conjElim2(fact).toOption.toVector.flatMap(split(logic, _))
    }

  /** Every element read, or nothing, which is `Option`'s traverse and is not in the standard library. */
  private def traverse[A, B](values: Vector[A])(read: A => Option[B]): Option[Vector[B]] =
    values.foldLeft(Option(Vector.empty[B])) { (carried, value) =>
      for { done <- carried; next <- read(value) } yield done :+ next
    }
}
