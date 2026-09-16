package garden.xeno.symbolum.sat

/**
 * Propositional formulas in conjunctive normal form, as numbers and nothing else.
 *
 * == Why this module depends on nothing ==
 *
 * A solver is a search, and a search is untrusted here by construction. `docs/adr/0003` makes the
 * module graph the trust boundary, and this module is that argument applied to a solver: it cannot
 * construct a theorem because it cannot see `kernel`, so no scan, no naming convention and no
 * reviewer's attention is load-bearing.
 *
 * `garden.xeno.symbolum.tactics.Consistency` keeps a solver out of the kernel the other way, with a
 * test that scans its source and fails if the file names an inference rule. That file's own comment
 * says why it is a scan rather than a runtime check: `Kernel.Thm` erases to a pair, so a type
 * assertion about it would pass whatever the file did. A module with no dependency needs neither,
 * and that is the whole reason this is a module rather than a file under `tactics`.
 *
 * == The encoding ==
 *
 * A variable is an `Int` from 1 upwards. A literal is that number, positive for the variable and
 * negative for its negation; **zero is not a literal** and a clause never contains one. Nothing here
 * carries a name: what a variable means is the caller's business, and the caller that has one is
 * `garden.xeno.symbolum.logic.Propositional`, which holds the map from variable to term.
 *
 * The choice is not aesthetic. Watched literals index an array by literal, conflict analysis marks
 * variables in a bitset, and both are the reason a solver is fast; a representation carrying terms
 * would make every one of those a hash lookup. The cost is that an error here reads as a number
 * rather than as a proposition, which is why [[Problem.check]] exists and why every entry point
 * refuses a malformed problem by name rather than misreading it.
 */
object Cnf {

  /** A variable, from 1 upwards. Zero is not one, so that a literal can carry its sign. */
  type Variable = Int

  /** A variable, or its negation as the same number negated. Never zero. */
  type Literal = Int

  /**
   * A disjunction of literals, in the canonical order [[normalise]] puts them in.
   *
   * A `Vector` rather than an `Array` because a clause is compared, hashed and put in a set by the
   * derivation checker, and an `Array` has reference equality. The solver keeps its own `Array`
   * copies in the clause database where the cost matters and equality does not.
   */
  type Clause = Vector[Literal]

  /** The empty clause, which is falsity and is what a refutation ends on. */
  val Empty: Clause = Vector.empty

  /** The variable a literal is about. */
  def variableOf(literal: Literal): Variable = math.abs(literal)

  /** The same literal with the opposite sign. */
  def negate(literal: Literal): Literal = -literal

  /**
   * A clause in canonical form, or `None` where it is a tautology.
   *
   * Canonical means sorted by variable and then by sign, with repetitions removed, which makes two
   * clauses with the same literals the same value. Sorting by variable rather than by the literal's
   * own number keeps `-3` next to `3`, which is what makes the tautology check one pass.
   *
   * **A tautology is `None` rather than an empty clause or an error.** It is a clause that says
   * nothing, so a solver may drop it and a refutation may not use it; returning it as a clause would
   * let a derivation resolve on it and produce a step that looks sound and proves nothing. The one
   * caller that must not drop it is a CNF conversion reporting what it built, and it gets `None` and
   * decides.
   */
  def normalise(literals: Iterable[Literal]): Option[Clause] = {
    // `distinct` and not a set, because the answer is a sorted vector and the insertion order of a
    // set is a thing to remember rather than a thing the type says. The membership test below reads
    // the same vector, which is linear where a set is constant and is the right trade at the length
    // of a clause: `Propositional` builds clauses of three literals and a learned one reaches tens.
    val seen = literals.toVector.distinct
    if (seen.exists(literal => seen.contains(-literal))) None
    else Some(seen.sortBy(literal => (variableOf(literal), -math.signum(literal))))
  }

  /**
   * A problem from clauses that may be neither canonical nor free of tautologies.
   *
   * The one entry point a caller building CNF should use. It normalises each clause and **drops**
   * the tautologies, which is why [[Problem.check]] can then insist on canonical form: a tautology
   * reaching the solver would have to be special-cased in three places, and dropping it is sound
   * because it constrains nothing. What the caller loses is the index: the clause at position `at`
   * of the result need not be the one it handed over at that position, so a caller that has to map
   * a clause back to where it came from builds the map from the result.
   */
  def problem(variables: Int, clauses: Iterable[Iterable[Literal]]): Problem =
    Problem(variables, clauses.flatMap(normalise).toVector)

  /** Whether the clause holds under an assignment indexed from variable 1. */
  def holds(clause: Clause, assignment: Vector[Boolean]): Boolean =
    clause.exists(literal => assignment(variableOf(literal) - 1) == (literal > 0))

  /**
   * A set of clauses over a declared number of variables.
   *
   * `variables` is declared rather than derived from the clauses, because a variable nothing
   * mentions is still a variable of the problem: an assignment has to have a value for it, and a
   * caller that built the problem from a formula knows about it where the clause list does not.
   */
  final case class Problem(variables: Int, clauses: Vector[Clause]) {

    /**
     * Why this problem is malformed, or nothing.
     *
     * Checked once at the entry point rather than defended against everywhere. A literal outside the
     * declared range is the error this catches, and it is the one an off-by-one in a caller's
     * variable numbering produces: without it the solver indexes past its own arrays and the failure
     * arrives as an exception from somewhere with no useful name on it.
     */
    def check: Option[String] =
      if (variables < 0) Some(s"a non-negative number of variables; this problem declares $variables")
      else
        clauses.iterator.zipWithIndex
          .flatMap { case (clause, at) =>
            clause.iterator.map { literal =>
              if (literal == 0) Some(s"no zero literal; clause $at has one")
              else if (variableOf(literal) > variables)
                Some(s"a literal within the $variables declared variables; clause $at has $literal")
              // Canonical form is required rather than repaired, so that a step of a derivation and
              // the clause it names are the same value. `Cnf.problem` is what puts clauses into it.
              else if (normalise(clause) != Some(clause))
                Some(s"clause $at in canonical form; build it with Cnf.problem")
              else None
            }
          }
          .flatten
          .nextOption()

    /** Whether an assignment satisfies every clause. The independent reading of a `Satisfiable`. */
    def satisfiedBy(assignment: Vector[Boolean]): Boolean =
      assignment.length == variables && clauses.forall(holds(_, assignment))
  }
}
