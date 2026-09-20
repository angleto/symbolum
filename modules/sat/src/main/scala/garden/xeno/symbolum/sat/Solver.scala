package garden.xeno.symbolum.sat

import scala.collection.mutable.ArrayBuffer
import Cnf.*

/**
 * Conflict-driven clause learning, and the refutation is what it is for.
 *
 * == What this replaces, and what it does not ==
 *
 * `garden.xeno.symbolum.tactics.Consistency` decides the same question by enumerating every
 * assignment, which it can do up to sixteen atoms and refuses above; its own comment says a register
 * of rules reaching that bound wants a solver rather than an enumeration. This is that solver. It
 * does **not** replace that file: the question there is satisfiability, which wants no theorem, and
 * a procedure that answers it without one is the honest shape for it.
 *
 * What this adds is the second half, which an enumeration cannot give at any size: when the answer
 * is unsatisfiable, **why**. [[Derivation]] is the why, and it is what
 * `garden.xeno.symbolum.logic.Propositional` turns into a theorem.
 *
 * == The part that is not standard, and it is the reason for writing one ==
 *
 * Conflict analysis is already a resolution derivation. The first UIP scheme starts at the
 * conflicting clause and resolves it against the reason of the most recently assigned literal in it,
 * again and again, until one literal of the current decision level is left. Every one of those is a
 * binary resolution on a variable, and this file records it. Nothing is reconstructed and nothing is
 * searched for a second time: [[analyse]] returns the learned clause and the index of the step that
 * concludes it, and the two agree by construction.
 *
 * That is the argument for not driving an external solver. DRAT, which is what one emits, records
 * the learned clauses and **not** their antecedents, so replaying it means a reverse unit
 * propagation check per lemma to recover them, which is a second search to write and to get right.
 *
 * == What is deliberately absent ==
 *
 * **No clause deletion.** Every learned clause is kept. A solver aimed at competition instances
 * deletes most of them and lives or dies by the policy; at the size a proof assistant's propositional
 * goals reach, the memory is not the constraint and the policy would be one more untested thing
 * between a conflict and a theorem. If a measured goal ever needs it, the derivation survives
 * deletion untouched, because a step is never removed from the list even when its clause leaves the
 * database.
 *
 * **No preprocessing.** No subsumption, no variable elimination, no equivalence reduction. Each of
 * them changes the problem, so each would owe the derivation a justification of the change, and that
 * is a larger piece of work than the solver.
 *
 * **The decision heuristic scans rather than heaps.** Picking the unassigned variable of greatest
 * activity is a linear pass over the variables instead of a priority queue. It is O(n) per decision
 * against O(log n), and it is here because a heap with lazy deletion is the part of a CDCL that is
 * most often subtly wrong and the least visible when it is. The bound this trades against is stated
 * rather than hidden: it is the wrong structure past some tens of thousands of variables, and
 * nothing in this repository has asked for one.
 */
final class Solver private (problem: Problem, conflictLimit: Int) {

  import Solver.*

  private val variables = problem.variables

  /** 1 where the variable is true, -1 where false, 0 where unassigned. Indexed from 1. */
  private val value = new Array[Int](variables + 1)

  /** The decision level a variable was assigned at. Meaningless where unassigned. */
  private val level = new Array[Int](variables + 1)

  /** The clause that propagated a variable, or -1 where it was a decision. */
  private val reasonOf = Array.fill(variables + 1)(-1)

  /** Where on the trail a variable sits, which is what orders two literals by recency. */
  private val position = new Array[Int](variables + 1)

  /** The polarity a variable last held, so that a restart does not throw the work away. */
  private val phase = new Array[Boolean](variables + 1)

  private val activity = new Array[Double](variables + 1)
  private var activityIncrement = 1.0

  private val trail = ArrayBuffer.empty[Literal]
  private val trailLimits = ArrayBuffer.empty[Int]

  /** The clause database: input clauses first, then everything learned. */
  private val database = ArrayBuffer.empty[Array[Literal]]

  /** For each clause of the database, the derivation step concluding it. */
  private val databaseStep = ArrayBuffer.empty[Int]

  /** Clauses watching a literal, visited when that literal becomes false. */
  private val watches = Array.fill(2 * (variables + 1))(ArrayBuffer.empty[Int])

  private val steps = ArrayBuffer.empty[Step]

  private var conflicts = 0

  private def decisionLevel: Int = trailLimits.length

  private def watchIndex(literal: Literal): Int = 2 * variableOf(literal) + (if (literal > 0) 0 else 1)

  private def valueOf(literal: Literal): Int = {
    val assigned = value(variableOf(literal))
    if (assigned == 0) 0 else if ((assigned > 0) == (literal > 0)) 1 else -1
  }

  private def addStep(step: Step): Int = { steps += step; steps.length - 1 }

  /**
   * A resolution step, oriented so that the pivot is positive.
   *
   * Every producer below has a pivot whose sign falls out of where it came from on the trail, and
   * the consumer wants one sign. Swapping the two antecedents is the same step, because resolution
   * is symmetric, and doing it here means the replay never meets the other orientation. [[Step]]
   * carries the reason this matters to a kernel.
   */
  private def resolveStep(left: Int, right: Int, pivot: Literal): Int =
    if (pivot > 0) addStep(Step.Resolve(left, right, pivot))
    else addStep(Step.Resolve(right, left, -pivot))

  private def enqueue(literal: Literal, reason: Int): Unit = {
    val variable = variableOf(literal)
    value(variable) = if (literal > 0) 1 else -1
    level(variable) = decisionLevel
    reasonOf(variable) = reason
    position(variable) = trail.length
    phase(variable) = literal > 0
    trail += literal
  }

  /* ------------------------------------------------------------------ setting the problem up */

  /**
   * The database, the watches and the level-0 assignments, or the step refuting the problem outright.
   *
   * Three cases arrive before any search happens and each has to be answered here rather than by the
   * loop below. An empty input clause is already the refutation. A unit is an assignment at level 0
   * and not a clause to watch, because watching needs two literals. Two units that contradict are a
   * conflict at level 0, which is [[refute]]'s case.
   *
   * Nothing here handles a tautology or a repeated literal, because [[Cnf.Problem.check]] refuses a
   * problem carrying either and `Cnf.problem` is what removes them. Putting the filter here instead
   * would have to special-case it in the watch setup, in the unit pass and in the derivation's
   * indices, which is three places for one condition.
   */
  private def install(): Option[Int] = {
    var refutation: Option[Int] = None
    val units = ArrayBuffer.empty[Int]

    var at = 0
    while (at < problem.clauses.length && refutation.isEmpty) {
      val clause = problem.clauses(at)
      val step = addStep(Step.Input(at))

      if (clause.isEmpty) refutation = Some(step)
      else {
        val index = database.length
        database += clause.toArray
        databaseStep += step
        if (clause.length == 1) units += index
        else {
          watches(watchIndex(clause(0))) += index
          watches(watchIndex(clause(1))) += index
        }
      }
      at += 1
    }

    // The units go in only once every clause is watched. The other order is a defect that hides:
    // a unit assigned first makes a literal false, and a clause watched at that literal afterwards
    // is never visited, because propagation visits a watch list when the literal becomes false and
    // it already had. The clause then sits in the database unwatched and a conflict is missed.
    var u = 0
    while (u < units.length && refutation.isEmpty) {
      val index = units(u)
      val literal = database(index)(0)
      if (valueOf(literal) == -1) refutation = Some(refute(index))
      else if (valueOf(literal) == 0) enqueue(literal, index)
      u += 1
    }

    refutation
  }

  /* ---------------------------------------------------------------------------- propagation */

  /**
   * Unit propagation to a fixed point, returning the clause that conflicts if one does.
   *
   * Two watched literals per clause, kept at positions 0 and 1. A clause is visited only when one of
   * the two becomes false, which is what makes the cost proportional to the assignments made rather
   * than to the size of the database.
   */
  private def propagate(): Option[Int] = {
    var head = propagated
    var conflict: Option[Int] = None

    while (head < trail.length && conflict.isEmpty) {
      val assigned = trail(head)
      head += 1

      val falsified = -assigned
      val watching = watches(watchIndex(falsified))
      val pending = watching.toVector
      watching.clear()

      var at = 0
      while (at < pending.length) {
        val index = pending(at)
        if (conflict.isDefined) watching += index
        else {
          val clause = database(index)
          if (clause(0) == falsified) { clause(0) = clause(1); clause(1) = falsified }

          if (valueOf(clause(0)) == 1) watching += index
          else {
            var k = 2
            var moved = false
            while (k < clause.length && !moved) {
              if (valueOf(clause(k)) != -1) {
                clause(1) = clause(k)
                clause(k) = falsified
                watches(watchIndex(clause(1))) += index
                moved = true
              }
              k += 1
            }

            if (!moved) {
              watching += index
              if (valueOf(clause(0)) == -1) conflict = Some(index)
              else enqueue(clause(0), index)
            }
          }
        }
        at += 1
      }
    }

    conflict
  }

  /** How much of the trail propagation has already read, kept as a count so a backjump resets it. */
  private var propagated = 0

  /* ----------------------------------------------------------------------- conflict analysis */

  /**
   * The learned clause, the level to jump back to, and the step concluding it.
   *
   * First UIP. The loop resolves the current clause against the reason of the most recently assigned
   * literal it contains, and stops when exactly one literal of the current decision level is left.
   *
   * **A literal assigned at level 0 is kept rather than dropped.** A solver that only wanted the
   * clause would remove it, since it is permanently false and shortens the clause for nothing; here
   * removing it would be a step with no justification, and the derivation would stop being a
   * derivation. The learned clause is therefore sometimes longer than a solver of the same design
   * would produce, and that is the price of the refutation being exact.
   */
  private def analyse(conflict: Int): (Vector[Literal], Int, Int) = {
    val seen = new Array[Boolean](variables + 1)
    var elsewhere = Vector.empty[Literal]
    var counter = 0
    var resolved = 0
    var clause = conflict
    var step = databaseStep(conflict)
    var at = trail.length - 1
    var uip = 0

    var done = false
    while (!done) {
      val literals = database(clause)
      // Index 0 of a reason clause is the literal it propagated, which is the one just resolved
      // away. On the first pass there is no such literal and the whole clause is read.
      var j = if (resolved == 0) 0 else 1
      while (j < literals.length) {
        val literal = literals(j)
        val variable = variableOf(literal)
        if (!seen(variable)) {
          seen(variable) = true
          bump(variable)
          if (level(variable) == decisionLevel) counter += 1 else elsewhere = elsewhere :+ literal
        }
        j += 1
      }

      while (!seen(variableOf(trail(at)))) at -= 1
      val literal = trail(at)
      at -= 1
      val variable = variableOf(literal)
      seen(variable) = false
      counter -= 1
      resolved += 1

      if (counter > 0) {
        val reason = reasonOf(variable)
        step = resolveStep(step, databaseStep(reason), -literal)
        clause = reason
      } else { uip = literal; done = true }
    }

    val learned = -uip +: elsewhere
    val backjump = if (elsewhere.isEmpty) 0 else elsewhere.map(literal => level(variableOf(literal))).max
    (learned, backjump, step)
  }

  /**
   * The step concluding the empty clause, from a conflict at decision level zero.
   *
   * Nothing at level 0 was decided, so every literal of the conflicting clause has a reason, and
   * resolving away the most recently assigned one strictly moves the clause earlier on the trail.
   * That is the termination argument and it is why the literal is chosen by trail position rather
   * than arbitrarily.
   *
   * This is not [[analyse]] with a special case bolted on. That loop stops at the unique implication
   * point of the current decision level, and at level 0 there is no such point: the two answers are
   * different shapes and merging them would put a branch inside the loop that runs on every conflict.
   */
  private def refute(conflict: Int): Int = {
    var step = databaseStep(conflict)
    var clause = database(conflict).toVector
    var stuck = false

    while (clause.nonEmpty && !stuck) {
      val literal = clause.maxBy(l => position(variableOf(l)))
      val variable = variableOf(literal)
      val reason = reasonOf(variable)

      if (reason < 0) stuck = true
      else {
        val resolvent = normalise(
          clause.filterNot(variableOf(_) == variable) ++ database(reason).toVector.filterNot(variableOf(_) == variable)
        )
        step = resolveStep(step, databaseStep(reason), literal)
        resolvent match {
          case Some(next) => clause = next
          // Unreachable at level 0, where every literal of the clause is false and so no resolvent
          // can hold a variable and its negation. Left as a stop rather than an exception because
          // `Derivation.check` is what decides whether this produced a refutation, and it will say
          // that the last step is not the empty clause.
          case None => stuck = true
        }
      }
    }

    step
  }

  /* --------------------------------------------------------------------------- the search */

  private def bump(variable: Variable): Unit = {
    activity(variable) += activityIncrement
    if (activity(variable) > 1e100) {
      var v = 1
      while (v <= variables) { activity(v) *= 1e-100; v += 1 }
      activityIncrement *= 1e-100
    }
  }

  private def decide(): Option[Literal] = {
    var best = 0
    var bestActivity = -1.0
    var v = 1
    while (v <= variables) {
      if (value(v) == 0 && activity(v) > bestActivity) { best = v; bestActivity = activity(v) }
      v += 1
    }
    if (best == 0) None else Some(if (phase(best)) best else -best)
  }

  private def backjump(to: Int): Unit = {
    val limit = trailLimits(to)
    var at = trail.length - 1
    while (at >= limit) {
      val variable = variableOf(trail(at))
      value(variable) = 0
      reasonOf(variable) = -1
      at -= 1
    }
    trail.remove(limit, trail.length - limit)
    trailLimits.remove(to, trailLimits.length - to)
    propagated = trail.length
  }

  private def learn(learned: Vector[Literal], step: Int): Int = {
    val index = database.length
    database += learned.toArray
    databaseStep += step
    if (learned.length >= 2) {
      watches(watchIndex(learned(0))) += index
      watches(watchIndex(learned(1))) += index
    }
    index
  }

  /**
   * The two answers that arrive before any search, then the search.
   *
   * Written as a chain of alternatives rather than as two early exits, and the order is the whole
   * of it: `Option.orElse` and `Option.getOrElse` take their argument by name, so [[install]] runs
   * only where the problem checked out and [[search]] only where installing did not already refute
   * it. Both of those are side-effecting, so an eager version of either would set the database up
   * for a problem that was never going to be searched.
   */
  def run(): Answer =
    problem.check
      .map(why => Answer.Malformed(why))
      .orElse(install().map(step => Answer.Unsatisfiable(Derivation(steps.toVector, step))))
      .getOrElse(search())

  private def search(): Answer = {
    propagated = 0
    var restartAt = FirstRestart
    var sinceRestart = 0
    var answer: Option[Answer] = None

    while (answer.isEmpty) {
      propagate() match {
        case Some(conflict) =>
          conflicts += 1
          sinceRestart += 1
          if (decisionLevel == 0) {
            // `refute` appends to `steps`, so the list is snapshotted after it runs and not in the
            // same argument list. Written the other way round the snapshot is taken first and the
            // derivation names a step it does not contain, which is what `Derivation.check` reported
            // on 298 of 300 refutations the first time this was run.
            val empty = refute(conflict)
            answer = Some(Answer.Unsatisfiable(Derivation(steps.toVector, empty)))
          }
          else if (conflicts > conflictLimit)
            answer = Some(Answer.Undecided(
              s"a problem settled within ${Plural.count(conflictLimit, "conflict", "conflicts")}; " +
                "this one was not"))
          else {
            val (learned, to, step) = analyse(conflict)
            backjump(to)
            val index = learn(learned, step)
            // The learned clause is asserting by construction: every literal but the first is false
            // below the level jumped to, so it propagates immediately and the search never repeats
            // the assignment that produced this conflict.
            enqueue(learned.head, index)
          }

        case None =>
          propagated = trail.length
          if (sinceRestart >= restartAt && decisionLevel > 0) {
            backjump(0)
            sinceRestart = 0
            restartAt = restartAt * 2
          } else
            decide() match {
              case None =>
                answer = Some(Answer.Satisfiable((1 to variables).map(v => value(v) > 0).toVector))
              case Some(literal) =>
                trailLimits += trail.length
                enqueue(literal, -1)
            }
      }
    }

    answer.get
  }
}

object Solver {

  /**
   * What a problem came out as, and the four are kept apart for the reason `Refutation` keeps seven.
   *
   * Collapsing [[Solver.Answer.Undecided]] into [[Solver.Answer.Satisfiable]] would turn "I could
   * not settle it" into "I settled it and it holds", which is the one way a solver can mislead a
   * proof assistant. Collapsing [[Solver.Answer.Malformed]] into [[Solver.Answer.Undecided]] would
   * hide a caller's own numbering error inside a bound.
   */
  enum Answer {

    /** An assignment, indexed from variable 1, which [[Cnf.Problem.satisfiedBy]] can check. */
    case Satisfiable(assignment: Vector[Boolean])

    /** No assignment satisfies it, and the derivation says why, step by step. */
    case Unsatisfiable(derivation: Derivation)

    /** The bound was reached. Not a claim about the problem. */
    case Undecided(why: String)

    /** The problem itself is not well formed, and `why` names the clause. */
    case Malformed(why: String)
  }

  /**
   * How many conflicts before the search gives up, which is a bound on work and not on wall clock.
   *
   * Counted in conflicts rather than in milliseconds so that the answer does not depend on the
   * machine: a suite that settles a goal on one machine and refuses it on a busier one is a suite
   * whose failures cannot be read. The figure is the one every bound in this repository is: large
   * enough that nothing measured has reached it, and named in the refusal when it is.
   */
  val Conflicts: Int = 100000

  /**
   * Conflicts before the first restart, doubled at each one.
   *
   * Geometric and not Luby, and the distinction is worth the line because the literature's answer is
   * Luby: it is optimal for a search whose run-time distribution is unknown, which is the situation a
   * competition solver is in. Nothing here has measured such a distribution, so taking the more
   * elaborate schedule would be copying a conclusion without its premise. Geometric restarts with
   * clause learning are enough to escape a bad decision order, which is the whole of what a restart
   * buys, and swapping the schedule later changes one expression.
   */
  private val FirstRestart: Int = 100

  /** Decide a problem, and get the refutation where there is one. */
  def solve(problem: Problem, conflictLimit: Int = Conflicts): Answer =
    new Solver(problem, conflictLimit).run()
}
