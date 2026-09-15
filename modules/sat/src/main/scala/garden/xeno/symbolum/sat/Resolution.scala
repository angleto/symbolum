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
    val clauses = Array.ofDim[Clause](steps.length)

    def fault(at: Int, why: String): Either[String, Vector[Clause]] =
      Left(s"step $at: $why")

    var at = 0
    var failure: Option[Either[String, Vector[Clause]]] = None

    while (at < steps.length && failure.isEmpty) {
      steps(at) match {
        case Step.Input(index) =>
          if (index < 0 || index >= problem.clauses.length)
            failure = Some(fault(at, s"an input clause of the problem; there is no clause $index"))
          else clauses(at) = problem.clauses(index)

        case Step.Resolve(left, right, pivot) =>
          if (left < 0 || left >= at) failure = Some(fault(at, s"an antecedent earlier than itself; left is $left"))
          else if (right < 0 || right >= at)
            failure = Some(fault(at, s"an antecedent earlier than itself; right is $right"))
          else if (!clauses(left).contains(pivot))
            failure = Some(fault(at, s"the pivot $pivot in the left antecedent, which is ${clauses(left).mkString("[", " ", "]")}"))
          else if (!clauses(right).contains(-pivot))
            failure = Some(fault(at, s"the negated pivot ${-pivot} in the right antecedent, which is ${clauses(right).mkString("[", " ", "]")}"))
          else
            normalise(clauses(left).filterNot(_ == pivot) ++ clauses(right).filterNot(_ == -pivot)) match {
              // A resolvent that is a tautology is not a defect in the producer and is not usable
              // either: every later step that reads it would be sound and would prove nothing, so it
              // is refused here where the message can say which step made it.
              case None => failure = Some(fault(at, "a resolvent that is not a tautology"))
              case Some(resolvent) => clauses(at) = resolvent
            }
      }
      at += 1
    }

    failure.getOrElse {
      if (empty < 0 || empty >= steps.length)
        Left(s"a step index for the empty clause; $empty is not one of ${steps.length} steps")
      else if (clauses(empty).nonEmpty)
        Left(s"step $empty to be the empty clause; it is ${clauses(empty).mkString("[", " ", "]")}")
      else Right(clauses.toVector)
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
  def core: Set[Int] = {
    val reached = scala.collection.mutable.BitSet(empty)
    val used = scala.collection.mutable.Set.empty[Int]
    var at = steps.length - 1
    while (at >= 0) {
      if (reached.contains(at)) steps(at) match {
        case Step.Input(index) => used += index
        case Step.Resolve(left, right, _) => reached += left; reached += right
      }
      at -= 1
    }
    used.toSet
  }
}
