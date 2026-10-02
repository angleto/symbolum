package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * Using a lemma on a goal, which is the step every proof assistant calls `apply` and this had not.
 *
 * A development holds theorems of the shape `|- !x y. A ==> B ==> C`. Using one on a goal means
 * deciding what `x` and `y` have to be for `C` to *be* the goal, specialising the lemma at those,
 * and handing back what is left to prove. `Rules.spec` does the specialising and has always been
 * here; what was missing is the deciding, and without it every use of a lemma was a caller writing
 * the instance out by hand.
 *
 * == Why this file exists now and not earlier ==
 *
 * Because [[Matching]] could not answer the question for the lemma it matters most for.
 * **Completeness is the only one of the sixteen axioms that quantifies over a predicate, and the
 * only one that separates the reals from the rationals.** Its `P` occurs applied to a bound
 * variable, which is a Miller pattern and was outside a first-order matcher, so the axiom could be
 * used only by a person writing `\x. …` themselves. It never was. The corpus report said
 * "completeness never reached" over 46 goals and read as a fact about the corpus.
 *
 * The same shape is what the stated purpose needs outside mathematics: *every policy satisfying P
 * satisfies Q*, applied to a particular policy, is an axiom with a predicate parameter and a goal
 * that says which predicate. It is one mechanism, and this is it.
 *
 * == What it is not ==
 *
 * **Not a prover.** It returns the obligations rather than discharging them, and a caller that
 * cannot discharge them has learned what the lemma would have cost rather than nothing. Chaining it
 * into a search is a different piece of work and is deliberately not started here: this is the
 * step, and `Prove` is where a strategy over steps belongs.
 *
 * **Not a unifier.** The goal is fixed and only the lemma has variables to fill, which is the same
 * asymmetry `Matching` is built on. A lemma variable the conclusion does not mention cannot be
 * decided by looking at the goal, and that is a refusal naming the variable rather than a guess.
 */
object Apply {

  /**
   * A lemma used on a goal: the instance, and what is left to prove.
   *
   * `theorem` concludes the obligations implying the goal, so a caller that proves them all reaches
   * the goal by `Rules.mp` and one that proves none still holds a theorem. `instantiation` is kept
   * because it is the answer to "what did it decide `P` was", which is the interesting half when
   * the lemma is completeness, and since 2026-09-12 the answer to "at which type", which is the
   * interesting half when the lemma is `FST_PAIR`.
   */
  final case class Application(
    theorem: Kernel.Thm,
    obligations: Vector[Term],
    instantiation: Matching.Instantiation,
    /**
     * The goal's own leading universals, taken off before matching and **not** put back.
     *
     * A goal `!x. 0 <= x * x` and a lemma `!x. 0 <= x * x` match as bodies and not as statements,
     * which is what `Library.instantiatesTo` already did and what this file did not until
     * 2026-09-11: it stripped the lemma and matched against the whole quantified goal, so a lemma
     * that IS the goal was refused. Found by asking the library for a lemma it holds and watching
     * the prover report LINARITH's complaint instead.
     *
     * They are not put back because the obligations mention the variables they bound. A caller that
     * discharges everything closes the result with `Rules.genAll` over this list and has the goal as
     * written; a caller that cannot has the obligations in the form it has to prove them, which is
     * one variable at a time rather than under a quantifier.
     */
    generalising: Vector[FVar]
  )

  /**
   * The lemma specialised so that its conclusion is the goal, with its remaining antecedents.
   *
   * The antecedents are peeled one at a time, and the **whole body is tried first**: a lemma
   * `!x. A x ==> B x` used on the goal `A a ==> B a` is that lemma at `a` and nothing is owed, and
   * a version that always peeled would have answered the same goal with an obligation the caller
   * did not have to meet. Only when the fuller reading does not match is one more antecedent moved
   * from the statement to the bill.
   */
  def to(logic: Logic, lemma: Kernel.Thm, goal: Term): Either[LogicError, Application] =
    for {
      stripped <- Logic.stripForall(lemma.conclusion)
      (held, body) = stripped
      opened <- Logic.stripForall(goal)
      (generalising, target) = opened
      antecedents = peel(logic, body, Vector.empty)
      matched <- decide(logic, held, antecedents, target)
      (decided, owed) = matched
      arguments <- held.foldLeft(Right(Vector.empty[Term]): Either[LogicError, Vector[Term]]) {
        (acc, variable) =>
          for {
            done <- acc
            value <- decided.terms.get(variable).toRight(Undetermined(variable))
          } yield done :+ value
      }
      // The lemma at the types the match decided, before it is specialised at the terms: `FST_PAIR`
      // is stated over `'a` and the goal is about `num`, so `specAll` would otherwise be handed an
      // argument of the wrong type and the quantifier would be looked up at the wrong one. The
      // range of that substitution is read off the goal; `Matching.Instantiation.instance` carries
      // the argument for why that is sound, and this is the same argument at one remove.
      atTypes = if (decided.types.isEmpty) lemma else Kernel.instType(decided.types, lemma)
      specialised <- logic.rules.specAll(atTypes, arguments.toList)
      instance <- reduced(specialised)
    } yield Application(
      instance,
      // What was moved to the bill to make the rest match, and nothing past it. Until 2026-10-02
      // this was every antecedent of the instance, so a lemma whose whole body matched owed its own
      // premises and a lemma that IS the goal was refused by every caller that takes only what owes
      // nothing: `COS_INJECTIVE` and `PI_HALF_LEAST_ZERO` asked of the prover verbatim came back
      // unsettled, and were reached at all only when the search under the goal's hypotheses
      // happened to rank them inside its budget. Counting from the lemma rather than from the
      // instance also keeps a predicate variable instantiated at an implication, which reduces to
      // one more arrow in the instance, from being read as one more obligation.
      peel(logic, instance.conclusion, Vector.empty)._1.take(owed),
      decided,
      generalising
    )

  /**
   * Every lemma of a set that applies to the goal, with what each would cost.
   *
   * The listing a reader wants when they have a goal and not a lemma in mind, and the reason it is
   * here rather than in a search: the order is the caller's to choose, and the honest default is
   * the one that owes least.
   */
  def candidates(
    logic: Logic,
    lemmas: Vector[(String, Kernel.Thm)],
    goal: Term
  ): Vector[(String, Application)] =
    lemmas
      .flatMap { case (name, lemma) => to(logic, lemma, goal).toOption.map(name -> _) }
      .sortBy(_._2.obligations.size)

  /* --------------------------------------------------------------------- the plumbing */

  /**
   * The instance with its redexes contracted, so that its conclusion IS the goal.
   *
   * `Rules.spec` leaves a redex the argument creates where it is, following HOL Light's `SPEC`, and
   * the argument here is a lambda: specialising completeness at `\x. x < 1` gives a theorem whose
   * conclusion says `(\x. x < 1) x` in three places. That is the same statement and it is not the
   * same term, and a caller comparing what came back against what they asked for would find them
   * different. Contracting is a derived step and costs a rewriting of the conclusion, not trust.
   */
  private def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      equation <- Conv.betaNormalise(theorem.conclusion)
      result <- LogicError.lift(Kernel.eqMp(equation, theorem))
    } yield result

  /** The antecedents of a chain of implications, and what it finally concludes. */
  private def peel(logic: Logic, current: Term, taken: Vector[Term]): (Vector[Term], Term) =
    logic.destImp(current) match {
      case Some((antecedent, consequent)) => peel(logic, consequent, taken :+ antecedent)
      case None => (taken, current)
    }

  /**
   * What the lemma's variables have to be, reading as much of the body as still matches.
   *
   * Fewest obligations first, which is why the fold runs from the whole body down: `k` antecedents
   * kept means `k` fewer things to prove. The count dropped comes back beside the instantiation,
   * because it is the number of obligations and nothing else records it.
   */
  private def decide(
    logic: Logic,
    held: Vector[FVar],
    peeled: (Vector[Term], Term),
    goal: Term
  ): Either[LogicError, (Matching.Instantiation, Int)] = {
    val (antecedents, conclusion) = peeled

    val attempts = (0 to antecedents.size).view.flatMap { dropped =>
      rebuild(logic, antecedents.drop(dropped), conclusion)
        .flatMap(pattern => Matching.matchTerm(held.toSet, pattern, goal))
        .map(_ -> dropped)
    }

    attempts.headOption.toRight(NotOfForm("a lemma whose conclusion is this goal", goal))
  }

  private def rebuild(logic: Logic, antecedents: Vector[Term], conclusion: Term): Option[Term] =
    antecedents
      .foldRight(Right(conclusion): Either[LogicError, Term]) { (antecedent, acc) =>
        acc.flatMap(inner => logic.mkImp(antecedent, inner))
      }
      .toOption
}
