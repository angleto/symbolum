package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.Library

/**
 * Proving a goal from **two** lemmas rather than one, which is the step the library lookup stops at.
 *
 * `Prove.held` scans every lemma the development holds, keeps one whose conclusion *is* the goal at
 * some instance and which owes nothing, and reports it. A lemma that would settle the goal at the
 * cost of an obligation is refused there, deliberately: discharging that obligation is a search, and
 * `Prove`'s `Right` says the theorem is unconditional. This is that search, and it is the thing the
 * README said this system had none of.
 *
 * `Apply` already produced everything it needs and threw none of it away. Its own class comment says
 * so: *"It returns the obligations rather than discharging them"*, and *"Chaining it into a search is
 * a different piece of work and is deliberately not started here"*. So what is new here is the loop
 * and the bounds on it, not the step.
 *
 * == What it is, named precisely, because the words in this area are taken ==
 *
 * Backward chaining with a bounded depth, over an index of the library by the head of what each
 * lemma can conclude. A goal is matched against every lemma that could conclude it, the obligations
 * of the match become subgoals, and each subgoal is put back to the whole tactic surface and then,
 * failing that, to this loop one level shallower. Candidates are tried fewest-obligations first and
 * the next is tried when one fails, which is a queue and a choice point.
 *
 * It is **not** a given-clause loop and this file does not claim to be one. That architecture
 * saturates a clause set forwards, keeps a passive and an active set, and is what a resolution
 * prover for first-order logic is built on. Nothing here does that, and calling this by that name
 * would make the remaining work look done, which is the mistake `docs/adr/0013` records about D2.
 *
 * == The bounds, and why they are counted in these units ==
 *
 * [[Chaining.Bounds.depth]] is how many lemmas may be chained; depth 1 is what `Prove.held` already
 * does, so 2 is the first value that buys anything. [[Chaining.Bounds.expansions]] is how many
 * candidates may have their obligations attempted **in one question**, which is the unit that
 * bounds the recursion rather than the matching: a goal whose head matches forty lemmas costs forty
 * matches and only expands the ones that match, and it is the expansions that recurse.
 *
 * Neither is a wall clock, for the reason every bound in this repository is not one: a suite that
 * settles a goal on a quiet machine and refuses it on a busy one is a suite whose failures cannot
 * be read.
 *
 * == The obligation this file could get wrong, and where it is checked ==
 *
 * A chained proof is only a proof if the thing that comes back **concludes the goal and rests on
 * nothing**. `Prove.held` gets that by construction, since it only takes candidates that owe
 * nothing; here the obligations are discharged one at a time and a mistake in the fold would leave
 * an antecedent standing or a hypothesis attached. So [[Chaining.prove]] checks its own answer
 * before returning it, against the goal it was asked, and a candidate that fails the check is
 * dropped rather than returned. The check is cheap and the alternative is a `Right` that lies.
 */
final class Chaining private (
  val logic: Logic,
  val library: Library,
  val bounds: Chaining.Bounds,
  val refutation: Option[Refutation]
) {

  import Chaining.*

  /**
   * The lemmas that could conclude a term with each head, and the ones whose head is unknown.
   *
   * A lemma is filed under the head of everything it can conclude: its whole body, and each
   * consequent left after peeling one more antecedent, because `Apply.to` reads the body first and
   * peels only where the fuller reading does not match. So `!x. A x ==> B x` is filed under both
   * `==>` and the head of `B`.
   *
   * **The wildcard bucket is not an empty case to be tidied away.** A lemma concluding `P x`, where
   * `P` is one of its own universals, has no head constant and can conclude anything; completeness
   * is that shape and it is the one axiom of the sixteen that separates the reals from the
   * rationals. Filing it nowhere would make it unreachable by chaining, which is the defect
   * `Apply`'s class comment records about the state before it existed.
   */
  private lazy val filed: (Map[String, Vector[Library.Entry]], Vector[Library.Entry]) = {
    val readable = library.entries.flatMap(entry =>
      Logic.stripForall(entry.theorem.conclusion).toOption
        .map { case (_, body) => entry -> consequents(body).map(headOf).distinct }
    )

    (
      readable.flatMap { case (entry, heads) => heads.flatten.map(_ -> entry) }.groupMap(_._1)(_._2),
      readable.collect { case (entry, heads) if heads.contains(None) => entry }
    )
  }

  /**
   * What a candidate would leave to prove, as the pair the order is taken on.
   *
   * **Total size first and the number of obligations second, and the other way round is what this
   * file did until it was measured.** Fewest-obligations-first is the obvious order and `Apply`
   * already offers it; on every goal tried it put the same three lemmas at the front, and all three
   * make the goal **bigger**:
   *
   *   - `DOUBLE_NEGATION`, `!p. ~~p ==> p`, matches every goal at all and owes `~~goal`;
   *   - `LT_FROM_ZERO`, `0 < y - x ==> x < y`, owes `0 < goal - 0`;
   *   - `LT_OF_NOT_LE` and `LE_OF_NOT_LT`, which owe the denial of the goal's own converse.
   *
   * Each owes exactly one obligation, so each sorts ahead of the lemma that settles the goal. The
   * measured ranks of the lemma that actually works, over three goals: 4, 5 and 3 by count, and 1, 2
   * and 0 by size. A budget spent from the front therefore bought nothing, which is not a reason to
   * raise the budget, and raising it is what was tried first: at forty expansions the corpus cost
   * 2.45 times its own baseline and proved nothing new, and at ten it cost nothing and lost every
   * goal this file exists to reach. Under this order ten reaches all of them and the corpus is back
   * at its baseline.
   *
   * Size is not a heuristic dressed up: a candidate whose obligations are smaller than the target is
   * making progress and one whose obligations are larger is not, and the three above are exactly the
   * lemmas that turn a goal into a longer statement of itself. The count stays as the tie-break
   * because between two candidates owing the same total, the one owing it in fewer pieces has fewer
   * places to fail.
   */
  private def cost(obligations: Vector[Term]): (Int, Int) =
    // Nodes in a term, which is what "smaller" means above. `Rewrite.nodesOf` rather than a fold
    // written here: the guard that refuses a closed rule whose right side contains its left needs
    // the same count, and this file held the only copy of it until 2026-09-18.
    (obligations.map(Rewrite.nodesOf).sum, obligations.size)

  /**
   * Every term the lemma's body could be read as concluding: itself, then one antecedent less.
   *
   * Unfolded rather than looped, because this module is written without a mutable local and
   * `StyleSpec` asserts it over the sources. The first version here used a `var` and a `while` and
   * that check is what said so.
   */
  private def consequents(body: Term): Vector[Term] =
    LazyList
      .iterate(Option(body))(current => current.flatMap(term => logic.destImp(term).map(_._2)))
      .takeWhile(_.isDefined)
      .flatten
      .toVector

  /**
   * The lemmas worth matching against this goal.
   *
   * **The goal's own universals come off before its head is read**, and leaving them on is how this
   * file did nothing at all for its first hour. The index is built over lemma **bodies**, so the
   * head of `!x. 0 < x * x + 1` is the universal quantifier and not `<`: every quantified goal
   * landed in a bucket nothing is filed under, no candidate was ever matched, and what came back was
   * [[Outcome.NoRoute]].
   *
   * That failure is worth the paragraph rather than the one-line fix, because [[Outcome.NoRoute]] is
   * also the honest answer when the library really holds nothing, so the symptom of a broken index
   * and the symptom of an empty library are the same answer. What separated them was constructing a goal whose two-lemma
   * route was known in advance and watching it come back exhausted; a measurement over goals whose
   * answer nobody knew would have read as a fact about the library.
   */
  private def candidatesFor(goal: Term): Vector[Library.Entry] = {
    val (byHead, wild) = filed
    val body = Logic.stripForall(goal).toOption.map(_._2).getOrElse(goal)
    headOf(body).flatMap(byHead.get).getOrElse(Vector.empty) ++ wild
  }

  /**
   * The goal, proved by chaining, or the bound that stopped it.
   *
   * `leaf` is what settles a subgoal without chaining, and it is passed in rather than built here so
   * that this file does not depend on `Prove` while `Prove` uses it. The recursion is therefore over
   * the **whole** tactic surface at every level and not only over the library: a chained step whose
   * obligation is an inequality is discharged by LINARITH, which is the arrangement that makes two
   * lemmas worth chaining at all.
   *
   * `under` is the goal's own hypotheses, where a caller assumed them: their theorems join the
   * candidates at every level, and what comes back may rest on them and on nothing else. That is
   * why the caller who supplied the context is the one who discharges it, and the pair is spent in
   * one place: `Prove.underHypotheses` assumes, asks this, and gives `Context.discharge` the
   * result. With no context this is what it always was, which is the configuration every existing
   * caller is in.
   */
  def prove(
    goal: Term,
    leaf: Term => Option[Kernel.Thm],
    under: Option[Context] = None
  ): Outcome = {
    val start = Budget(bounds.expansions, stoppedBy = None)

    go(goal, bounds.depth, Set.empty, leaf, under, start) match {
      case (Some((theorem, used)), _) => Outcome.Proved(theorem, used)
      case (None, spent) =>
        spent.stoppedBy match {
          case Some(Bound.Expansions) => Outcome.Depleted(Bound.Expansions, bounds.expansions)
          case Some(Bound.Lemmas) => Outcome.Depleted(Bound.Lemmas, bounds.depth)
          case None => Outcome.NoRoute
        }
    }
  }

  /** A theorem concluding the target and the lemmas it took, or nothing, with the budget left. */
  private type Found = Option[(Kernel.Thm, Vector[String])]

  private def go(
    target: Term,
    depth: Int,
    above: Set[Term],
    leaf: Term => Option[Kernel.Thm],
    under: Option[Context],
    budget: Budget
  ): (Found, Budget) =
    leaf(target) match {
      case Some(theorem) => (Some((theorem, Vector.empty)), budget)

      // A target already on the path above is a loop and not a subgoal: the depth bound would stop
      // it anyway, and stopping here keeps the budget for candidates that can move. The path holds
      // bodies, for the reason [[bodyOf]] gives.
      case None if above.contains(bodyOf(target)) => (None, budget)

      case None if depth <= 0 => (None, budget.stoppedAt(Bound.Lemmas))

      case None =>
        val held = assumed(under)
        val path = above + bodyOf(target)

        val applied = (assumptions(under) ++ fromLibrary(target))
          .flatMap { case (name, theorem) => Apply.to(logic, theorem, target).toOption.map(name -> _) }
          // What owes nothing is what `leaf` has already tried, through `Prove.held`, over the same
          // library. Trying it again here would double the cost of every question and could not
          // find anything the line above did not.
          .filter { case (_, application) => application.obligations.nonEmpty }
          // A candidate may rest on what the goal assumed and on nothing else. With no context
          // `held` is empty and this is the emptiness test it was until 2026-09-18.
          .filter { case (_, application) => application.theorem.hypotheses.forall(held) }
          // A candidate owing a goal on the path is the loop the second case above refuses, met one
          // step earlier: its obligation would reach that case after `leaf` had failed on it once
          // already, so it cannot succeed, and trying it costs an expansion. Measured on 2026-09-25,
          // when `INTERVAL_GLUING` joined the library. Its conclusion `P a b` has no head, so it is
          // a candidate at every goal, and at `0 <= t` it owes `0 <= t` itself; at every subgoal
          // under that goal it owes the goal again. One expansion per subgoal was the whole of what
          // took `ChainingSpec`'s one-lemma witness past its budget of ten, and removing this lemma
          // alone from the library put it back. Nothing that can succeed is dropped, on one premise:
          // that `leaf` answers a goal and its generalisation alike. `Prove.held` does by
          // construction, since `Apply.to` takes the goal's universals off before matching; the
          // procedures take theirs off first as well, and `ReachSpec`'s corpus not moving when this
          // landed is the measurement that premise rests on rather than a proof of it.
          .filterNot { case (_, application) => application.obligations.exists(owed => path.contains(bodyOf(owed))) }
          .sortBy { case (_, application) => cost(application.obligations) }

        closedByLeaf(applied, target, depth, path, leaf, under, budget) match {
          case Some(found) => (Some(found), budget)
          case None => first(applied, target, depth, path, leaf, under, budget)
        }
    }

  /**
   * A candidate whose every obligation the leaf settles, looked for across all of them before any
   * is expanded: one level of iterative deepening, at the levels where expanding means recursing.
   *
   * **Why the order in [[cost]] is not enough on its own.** It ranks by what a candidate owes and
   * not by whether what it owes is already known, and the two part exactly where a goal's premise is
   * an obligation. Measured on 2026-10-02 (card `39429606`): under the hypotheses of
   * `!x. 0 < x ==> cos x = 0 ==> pi / 2 <= x`, the lemma that settles it is `PI_HALF_LEAST_ZERO`,
   * owing the conjunction of the two premises, and it ranked sixth of seven, behind `LE_OF_LT`,
   * `LE_OF_EQ`, `LE_OF_NOT_LT`, `DOUBLE_NEGATION` and `LE_FROM_ZERO`. Each of those owes the goal
   * restated, so each is the same size as the target, sorts ahead of a candidate owing more, and
   * spends its expansion on a subtree that cannot close: `LE_OF_EQ` owes `pi / 2 = x`, and every
   * lemma concluding an equation is a candidate for that. Ten expansions ran out before the sixth.
   * A bigger budget finds it, and so would a different order on this goal; neither says why.
   *
   * **What it costs, and why it is free where it would duplicate.** One leaf question per obligation
   * of each candidate, stopping at the first the leaf refuses, and nothing is spent from the
   * expansion budget because nothing recurses: that bound is on recursion, which is what its own
   * comment says it counts. It runs only where `depth > 1`, because at depth one the expansions
   * below are leaf questions already and this would ask each of them twice. Whatever this finds,
   * the expansions below would also have found inside a large enough budget, so it can only add a
   * theorem the bound was hiding, and the theorem goes through the same check in [[discharge]].
   *
   * The budget a probe returns is dropped: a leaf-only discharge reaching depth zero marks the
   * depth bound as hit, and a pass that only looked must not decide what the search reports.
   */
  private def closedByLeaf(
    candidates: Vector[(String, Apply.Application)],
    target: Term,
    depth: Int,
    above: Set[Term],
    leaf: Term => Option[Kernel.Thm],
    under: Option[Context],
    budget: Budget
  ): Found =
    if (depth <= 1) None
    else
      candidates.view
        .filterNot { case (_, application) => application.obligations.exists(refuted(under)) }
        .flatMap { case (name, application) =>
          discharge(name, application, target, 1, above, leaf, under, budget)._1
        }
        .headOption

  /**
   * A goal without its leading universals, which is what "the same goal" means on the path.
   *
   * `Apply.to` takes a goal's own universals off before matching and does not put them back, so
   * every obligation below the first level is an open term, while the goal a caller hands over is
   * usually closed. Compared as written, `!x. 0 <= x * x` and the obligation `0 <= x * x` are two
   * goals and a loop between them goes unseen; they are one goal, since proving the open body with
   * nothing assumed about `x` is proving its generalisation. Until 2026-09-25 the path held terms
   * as written, and no loop through the top goal could be caught before the depth bound stopped it.
   */
  private def bodyOf(goal: Term): Term =
    Logic.stripForall(goal).toOption.map(_._2).getOrElse(goal)

  /** The library's candidates for this target, paired with the name each is filed under. */
  private def fromLibrary(target: Term): Vector[(String, Kernel.Thm)] =
    candidatesFor(target).map(entry => entry.name -> entry.theorem)

  /**
   * The goal's own hypotheses as candidates, which are tried at every level and not only the first.
   *
   * Named rather than numbered, because [[Outcome.Proved]] carries the names to answer "which
   * lemmas were chained" and a proof that spent a premise the goal handed it is answering that
   * question with something that is not a lemma. A reader of the list has to be able to tell.
   */
  private def assumptions(under: Option[Context]): Vector[(String, Kernel.Thm)] =
    under.toVector.flatMap(_.facts).map("a hypothesis of the goal" -> _)

  /** What a theorem produced under this context may still rest on, which is nothing without one. */
  private def assumed(under: Option[Context]): Set[Term] =
    under.map(_.allowed).getOrElse(Set.empty)

  /**
   * Whether the model finds a point where an obligation is false, under the goal's own hypotheses
   * where a caller assumed them.
   *
   * **Why a search may skip on a model's word.** The order in [[cost]] ranks candidates and prunes
   * none, so every candidate that matches is expanded until the budget runs out, and a candidate
   * owing a false statement spends expansions on a subtree that cannot close. Measured on
   * 2026-09-28 (card `4bcfc8b9`): with `Circle` in the library, `ChainingSpec`'s one-lemma witness
   * `0 <= (x * x) * (y * y)` came back `Depleted(Expansions, 10)`, because `LE_OF_EQ` owes
   * `0 = (x * x) * (y * y)`, false at `x = y = 1`, and under that equation every injectivity lemma
   * (`EXP_INJECTIVE`, and `COS_INJECTIVE` new with `Circle`) is a candidate, since `x = y` matches
   * every equation. Raising the budget, removing the lemma or moving the witness would each hide
   * that; skipping an obligation the model refutes removes the subtree for the reason it is dead.
   *
   * **What it may not do is take a refusal away or add a theorem**, and it does neither: a skipped
   * candidate is one fewer thing tried, so the worst a wrong answer here costs is a proof the search
   * would otherwise have found. Nothing the model says reaches a theorem.
   *
   * **A point found in floating point counts here, and that is a decision rather than a lapse.** The
   * first version asked `Refutation.exactly` as well, the test a reported refutation has to pass, and
   * a probe on the same day showed it answering no for every obligation over the reals, the one above
   * included: the model computes a real through `Double`, so nothing over `real` is exact and the
   * screen skipped nothing. What a sampled point is instead is false beyond `Evaluate`'s tolerance,
   * which is loose on purpose and errs towards "equal" and "not less", so a true obligation is read
   * as false only where rounding exceeds that tolerance, and the price of that is one route, never a
   * wrong theorem. A report would be misled by the same point; a search is only made narrower. An
   * obligation the model says nothing about, a constant it does not interpret, is never skipped, and
   * with no refutation the search is what it was.
   */
  private def refuted(under: Option[Context])(owed: Term): Boolean =
    refutation.exists { screen =>
      screen.counterexample(under.toVector.flatMap(_.assumed), owed) match {
        case Refutation.Found(_, _) | Refutation.Solved(_, _) => true
        case _ => false
      }
    }

  /** The candidates in order, until one reaches the target or the budget runs out. */
  private def first(
    candidates: Vector[(String, Apply.Application)],
    target: Term,
    depth: Int,
    above: Set[Term],
    leaf: Term => Option[Kernel.Thm],
    under: Option[Context],
    budget: Budget
  ): (Found, Budget) =
    candidates.headOption match {
      case None => (None, budget)

      case Some(_) if budget.left <= 0 => (None, budget.stoppedAt(Bound.Expansions))

      // A candidate owing something false cannot succeed, so it is passed over without spending an
      // expansion. See [[refuted]] for what "false" has to mean before this may skip anything.
      case Some((_, application)) if application.obligations.exists(refuted(under)) =>
        first(candidates.tail, target, depth, above, leaf, under, budget)

      case Some((name, application)) =>
        discharge(name, application, target, depth, above, leaf, under, budget.spend) match {
          case (Some(found), spent) => (Some(found), spent)
          case (None, spent) => first(candidates.tail, target, depth, above, leaf, under, spent)
        }
    }

  /** One candidate: its obligations proved in turn, then the antecedents discharged. */
  private def discharge(
    name: String,
    application: Apply.Application,
    target: Term,
    depth: Int,
    above: Set[Term],
    leaf: Term => Option[Kernel.Thm],
    under: Option[Context],
    budget: Budget
  ): (Found, Budget) = {
    val (carried, spent) = application.obligations.foldLeft(
      (Option((application.theorem, Vector(name))), budget)
    ) {
      case ((None, running), _) => (None, running)

      case ((Some((implication, used)), running), obligation) =>
        go(obligation, depth - 1, above, leaf, under, running) match {
          case (Some((proof, from)), next) =>
            (logic.rules.mp(implication, proof).toOption.map(step => (step, used ++ from)), next)
          case (None, next) => (None, next)
        }
    }

    val closed = carried
      .flatMap { case (theorem, used) =>
        logic.rules.genAll(theorem, application.generalising.toList).toOption.map(_ -> used)
      }
      // The check the class comment argues for. A fold that left an antecedent standing, or a `mp`
      // that attached a hypothesis, produces a theorem that is true and is not the one that was
      // asked for, and returning it would be the misleading answer this repository exists not to
      // give. Under a context the hypotheses it may carry are the ones the goal assumed, and
      // `Context.discharge` is what turns them back into the antecedents they came from; a
      // hypothesis from anywhere else still fails here.
      .filter { case (theorem, _) =>
        theorem.conclusion == target && theorem.hypotheses.forall(assumed(under))
      }

    (closed, spent)
  }

  /**
   * What is left to spend, and which bound stopped the search if one did.
   *
   * Threaded through the recursion rather than held in a mutable field, for the reason
   * [[consequents]] gives. What it buys beyond style is that the answer says **which** bound was
   * reached, which a counter alone could not: `Outcome.Depleted` carries it as a value, and
   * `Remedy` reads the value rather than the wording of a sentence written in this file.
   */
  private final case class Budget(left: Int, stoppedBy: Option[Bound]) {
    def spend: Budget = copy(left = left - 1)

    /**
     * The bound that stopped a branch, kept once.
     *
     * Where both are reached the **expansion** budget is the one reported, and the choice is not
     * arbitrary: running out of it means the search did not finish looking, so what it says about
     * the goal is weaker than what the depth says. A caller raising the wrong one learns nothing.
     */
    def stoppedAt(bound: Bound): Budget = stoppedBy match {
      case Some(Bound.Expansions) => this
      case _ => copy(stoppedBy = Some(bound))
    }
  }
}

object Chaining {

  /**
   * What came back, and the three are kept apart because they ask for three different next steps.
   *
   * **The bound is a value and not a sentence**, which is a decision `Remedy`'s own comment about
   * `Quantified.Verdict` asks for in as many words: that verdict carries its reason as prose, so
   * telling a budget apart from a question of shape there would mean matching on the wording of a
   * sentence written one file over. This enum first had a single exhausted case carrying a string,
   * and the check in `RemedySpec` that every verdict be mapped is what said so.
   *
   * [[Chaining.Outcome.NoRoute]] is the one that is not a limit. Every candidate was tried inside
   * the bounds and none reached the goal, so raising a bound changes nothing and what is missing is
   * a lemma.
   */
  enum Outcome {

    /**
     * The theorem, and the lemmas it was built from in the order they were used.
     *
     * The names are carried because they are the answer to the question this file exists to make
     * answerable, which is **which** lemmas were chained. A caller that only wanted the theorem
     * ignores them; a test asserting that two were chained cannot be written without them, and the
     * assertion that one was used is not the same claim.
     */
    case Proved(theorem: Kernel.Thm, lemmas: Vector[String])

    /** A bound stopped the search before it finished looking. Never a claim about the goal. */
    case Depleted(bound: Bound, at: Int)

    /** Everything inside the bounds was tried and nothing reached the goal. */
    case NoRoute
  }

  /** Which of the two bounds a search ran into. */
  enum Bound {

    /** How many lemmas may be chained: [[Bounds.depth]]. */
    case Lemmas

    /** How many candidates may have their obligations attempted: [[Bounds.expansions]]. */
    case Expansions
  }

  /** How far the search may go, in lemmas chained and in candidates expanded. */
  final case class Bounds(depth: Int, expansions: Int)

  /**
   * The default, and both figures were measured rather than chosen.
   *
   * Depth 2 because depth 1 is what `Prove.held` already does, so it is the first value that buys
   * anything, and because the measurement in `ChainingSpec` says what the third level costs against
   * what it finds.
   *
   * The expansion bound is the one that keeps `ReachSpec` from becoming unrunnable, which is the
   * constraint that actually binds here: that suite is already the most expensive in the repository
   * and a search inside it multiplies its cost by whatever this allows.
   */
  val Default: Bounds = Bounds(depth = 2, expansions = 10)

  /** The head constant of a term's application spine, where it has one. */
  def headOf(term: Term): Option[String] = term match {
    case App(fn, _) => headOf(fn)
    case Const(name, _) => Some(name)
    case _ => None
  }

  /** Over a library and the logic its lemmas are stated in. */
  def apply(
    logic: Logic,
    library: Library,
    bounds: Bounds = Default,
    refutation: Option[Refutation] = None
  ): Chaining =
    new Chaining(logic, library, bounds, refutation)
}
