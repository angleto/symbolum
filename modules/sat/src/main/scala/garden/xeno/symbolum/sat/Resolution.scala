package garden.xeno.symbolum.sat

import Cnf.*

/**
 * A refutation by resolution, which is the thing this module exists to produce.
 *
 * == The verdict is not the product ==
 *
 * A solver that answered "unsatisfiable" and nothing else would be useless here. Nothing in this
 * repository believes a search, so the answer has to arrive with its reasons attached and be
 * re-derived through the kernel's rules; `garden.xeno.symbolum.logic.Propositional` is what does
 * that, and this type is the interface between the two halves.
 *
 * That is also the argument for writing the solver rather than driving one. A CDCL solver's
 * conflict analysis **is** a resolution derivation: it starts at the conflicting clause and resolves
 * it against the reasons of the literals it contains until one literal of the current decision level
 * is left. Writing the solver makes those antecedents free, because they are what the analysis is
 * already computing. The standard output format of an external solver, DRAT, throws them away and
 * records only the clauses; recovering them means a reverse unit propagation check per lemma, which
 * is another search and another thing to get right. The library makes the part that is needed harder
 * rather than easier, which is the opposite of the usual reason to take one.
 *
 * == Binary steps only ==
 *
 * A learned clause is usually several resolutions deep, and it is recorded as several [[Step]]s
 * rather than as one chain. It costs a few more entries and it buys the property that matters: every
 * step has exactly two antecedents and one pivot, so [[Derivation.check]] is a comparison of three
 * sets and the replay above is two rule applications. A chain would push the work of splitting it
 * into both consumers instead of doing it once here.
 */
enum Step {

  /** The clause at that index of the problem, assumed rather than derived. */
  case Input(at: Int)

  /**
   * The resolvent of two earlier steps: `left` holds `pivot` and `right` holds its negation.
   *
   * `left` and `right` index the step list and are both smaller than this step's own index, which is
   * what makes a derivation a list rather than a graph to be traversed and what makes the replay one
   * pass.
   *
   * **`pivot` is a literal and it is always positive**, which is not a normalisation for tidiness.
   * Resolution is symmetric, so either orientation states the same step; the consumer is not. A
   * caller replaying this through a kernel discharges the pivot from one side to get a **negation**
   * and cuts it into the other, and a negated pivot would ask for the positive fact instead, which
   * on the propositional side costs a double-negation elimination per step. `Solver.resolveStep` is
   * where the orientation is chosen, once, rather than at every reading.
   */
  case Resolve(left: Int, right: Int, pivot: Literal)
}

/**
 * The steps of a refutation, ending on the empty clause.
 *
 * Holding the steps and **not** the clauses they conclude is deliberate: a derivation that carried
 * both would let the two disagree, and then a checker comparing them would be checking the producer
 * against itself. [[check]] computes the clauses from the steps and is therefore the only place a
 * clause of this derivation exists.
 */
final case class Derivation(steps: Vector[Step], empty: Int) {

  /**
   * The clause each step concludes, or why this is not a refutation of that problem.
   *
   * **This is the first of the two checks and it is the cheap one.** It works over sets of `Int` and
   * costs microseconds; the second is the replay through the kernel's rules, which costs 92
   * primitive inferences per step. A derivation that fails here would fail there too, forty thousand
   * times more slowly and with a message about terms rather than about numbers, so this runs first
   * and the other never sees a derivation that did not pass it.
   *
   * It is not a formality. The solver is untrusted and a defect in its conflict analysis produces
   * exactly this: a step whose antecedents do not resolve to what the analysis thought they did.
   */
  def check(problem: Problem): Either[String, Vector[Clause]] = {
    def fault(at: Int, why: String): Left[String, Nothing] = Left(s"step $at: $why")

    /**
     * What each step concludes, in order, built forwards.
     *
     * A fold and not a scan over an array, and the append is the reason it can be one: a step reads
     * only steps earlier than itself, which the two bounds below enforce, so the answer at index
     * `at` is always the next one to be written. `Vector`'s append is amortised constant, so this
     * costs what the array cost; what it removes is the state in which some entries are filled and
     * the rest are whatever `ofDim` left there, which is the state the failure path used to leave.
     */
    val concluded = steps.zipWithIndex.foldLeft[Either[String, Vector[Clause]]](Right(Vector.empty)) {
      case (Left(why), _) => Left(why)
      case (Right(clauses), (Step.Input(index), at)) =>
        if (index < 0 || index >= problem.clauses.length)
          fault(at, s"an input clause of the problem; there is no clause $index")
        else Right(clauses :+ problem.clauses(index))

      case (Right(clauses), (Step.Resolve(left, right, pivot), at)) =>
        if (left < 0 || left >= at) fault(at, s"an antecedent earlier than itself; left is $left")
        else if (right < 0 || right >= at)
          fault(at, s"an antecedent earlier than itself; right is $right")
        else if (!clauses(left).contains(pivot))
          fault(at, s"the pivot $pivot in the left antecedent, which is ${clauses(left).mkString("[", " ", "]")}")
        else if (!clauses(right).contains(-pivot))
          fault(at, s"the negated pivot ${-pivot} in the right antecedent, which is ${clauses(right).mkString("[", " ", "]")}")
        else
          normalise(clauses(left).filterNot(_ == pivot) ++ clauses(right).filterNot(_ == -pivot)) match {
            // A resolvent that is a tautology is not a defect in the producer and is not usable
            // either: every later step that reads it would be sound and would prove nothing, so it
            // is refused here where the message can say which step made it.
            case None => fault(at, "a resolvent that is not a tautology")
            case Some(resolvent) => Right(clauses :+ resolvent)
          }
    }

    concluded.flatMap { clauses =>
      if (empty < 0 || empty >= steps.length)
        Left(s"a step index for the empty clause; $empty is not one of ${count(steps.length, "step", "steps")}")
      else if (clauses(empty).nonEmpty)
        Left(s"step $empty to be the empty clause; it is ${clauses(empty).mkString("[", " ", "]")}")
      else Right(clauses)
    }
  }

  /**
   * The input clauses this refutation actually reads, which is an unsatisfiable core.
   *
   * Walked backwards from the empty clause rather than collected forwards, so a step the solver
   * learned and then never used contributes nothing. That is the whole of what makes it a core:
   * the clauses reached from the empty clause are enough on their own, because every step above them
   * is a resolution and resolution is sound.
   *
   * **This is what a caller wanting the accounting asks for, and it is exact rather than minimal.**
   * A smaller core may exist; finding it is another search (repeated solving with clauses dropped)
   * and is deliberately not done here. Saying "an unsatisfiable core" rather than "the minimal
   * unsatisfiable core" is the difference between the two, and the weaker word is the true one.
   */
  /**
   * A number and its noun, with the singular at one.
   *
   * **A copy, and the copy is the price of the dependency graph rather than an oversight.** The
   * counter the rest of the repository uses is `Prose.count` in `modules/theories`, which this
   * module cannot see: `sat` depends on nothing, and a module that cannot see `kernel` cannot
   * construct a theorem whatever it does, which is what makes an untrusted search safe to have.
   * What is repeated here is a rule of English rather than a fact about this system, so it cannot
   * drift against any source of truth in it, and the test in this module's own spec is what holds
   * it.
   *
   * It takes BOTH forms where `Prose.count` appends an `s`, because this class of site contains
   * `entry`/`entries` in `core` and a counter that can only append is wrong for it.
   */
  private def count(howMany: Int, one: String, many: String): String =
    s"$howMany ${if (howMany == 1) one else many}"

  def core: Set[Int] = {
    // One backwards pass and not a search, for the reason the paragraph above gives: an antecedent
    // is always an earlier step, so a step's own reachability is settled by the time this arrives at
    // it and nothing has to be revisited. That is what lets the walk carry two sets forward instead
    // of iterating to a fixed point.
    //
    // What this asks of its caller, which the `BitSet` it replaces asked by throwing: that `empty`
    // names a step. It did not name one only in a derivation `check` refuses, and there the old
    // code raised `IllegalArgumentException` from `BitSet` while this returns the empty set, which
    // reads as "no input clause is needed" and is not an answer at all. Nothing in this repository
    // can reach that: every call site runs on a refutation the solver has just built. It is said
    // here because a silence is the one failure of this method a reader cannot see.
    val (_, used) = (steps.length - 1 to 0 by -1)
      .foldLeft((Set(empty), Set.empty[Int])) { case ((reached, used), at) =>
        if (!reached.contains(at)) (reached, used)
        else
          steps(at) match {
            case Step.Input(index) => (reached, used + index)
            case Step.Resolve(left, right, _) => (reached + left + right, used)
          }
      }
    used
  }
}
