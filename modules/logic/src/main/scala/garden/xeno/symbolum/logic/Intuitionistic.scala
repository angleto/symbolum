package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * A decision for intuitionistic propositional logic, negation included, at no axiom at all.
 *
 * Dyckhoff's contraction-free sequent calculus, the one usually called G4ip or LJT. It takes a
 * propositional goal, searches a space it is guaranteed to exhaust, and either builds a
 * `Kernel.Thm` out of [[Rules]] or reports that the goal is not intuitionistically provable. Every
 * rule it uses is derived from the kernel's ten, so what comes back rests on **nothing**:
 * `IntuitionisticSpec` asserts an empty `Derivation.axiomsOf` on every theorem it proves rather
 * than describing it.
 *
 * == Why it exists beside the two procedures that were already here ==
 *
 * [[Minimal]] searched the fragment with no negation in it and this file is what it delegates its
 * search to, so the two are one implementation and not two. [[Propositional]] decides **classical**
 * validity, which is strictly more, and pays for it: its last step is `DOUBLE_NEGATION`, so every
 * theorem it produces rests on the choice axiom. That is a real price and not a bookkeeping detail,
 * and `DomainTheorySpec` is where it was measured: the same claim about a release gate, settled by
 * hand, spends one domain axiom and no foundational one; settled by `Propositional`, it spends the
 * same domain axiom **and** choice.
 *
 * So until this landed, neither procedure covered an ordinary argument about a domain at its real
 * cost: the one that costs nothing refused anything with a negation in it, and a criterion about
 * the world is made of negations. That gap is what this closes, and the gap was named in
 * `DomainTheorySpec` before it was closed rather than after: the comment that asked for
 * "a decision procedure for intuitionistic propositional logic, negation included -- Dyckhoff's
 * contraction-free calculus is the standard one" is the sentence this file answers.
 *
 * == Why contraction-free, which is the whole of the construction ==
 *
 * The naive left rule for implication,
 *
 * {{{
 *   G, A ==> B |- A      G, B |- C
 *   ------------------------------
 *          G, A ==> B |- C
 * }}}
 *
 * keeps `A ==> B` in the left premise, because in general it is needed to prove `A`. A search built
 * on it does not terminate on its own and needs a depth bound, and a depth bound turns "not
 * provable" into "not found within a number somebody chose", which is a different answer and the
 * one this repository refuses to conflate with the first.
 *
 * Dyckhoff's calculus replaces that rule with four, one per shape of the antecedent, and **none of
 * them keeps the principal formula**:
 *
 *   - an atom: `P ==> B` with `P` already on the left becomes `B`;
 *   - a conjunction: `(C /\ D) ==> B` becomes `C ==> (D ==> B)`;
 *   - a disjunction: `(C \/ D) ==> B` becomes the two hypotheses `C ==> B` and `D ==> B`;
 *   - an implication: `(C ==> D) ==> B` becomes `D ==> B` proving `C ==> D`, and `B` proving the
 *     original goal.
 *
 * Termination is then a measure rather than a bound. Give every formula a weight, with an atom, `T`
 * and `F` weighing one, `w(A /\ B) = w(A \/ B) = w(A) + w(B) + 1` and **`w(A ==> B) = w(A) + w(B)`**
 * — the implication is the one connective that costs nothing for itself, which is exactly what makes
 * `(C /\ D) ==> B` heavier than `C ==> (D ==> B)` by the one the conjunction carries. Read the
 * sequent as the multiset of the weights of its hypotheses and its goal, and every rule above
 * strictly decreases it in the multiset order. [[Intuitionistic.Fuel]] is a net under that argument
 * and not the argument, which is the arrangement `Minimal.Depth` had before this file replaced its
 * search and took the bound with it.
 *
 * **The weight was got wrong once, in the obvious way, and the error is worth keeping.** With
 * `w(A ==> B) = w(A) + w(B) + 1`, which is what one writes by reflex beside the other two, the
 * conjunction rule leaves the weight **exactly equal**: both sides come to `w(C) + w(D) + w(B) + 2`.
 * A measure that does not decrease is not a termination argument, and nothing about the rule looks
 * wrong when you read it.
 *
 * == Negation is `A ==> F` here, and that is a decision with a visible consequence ==
 *
 * `~A` and `A ==> F` are provably equivalent and are **different terms**, and this file works with
 * the second. A hypothesis is read through [[asImplication]], which sees `~A` as `(A, F)`, and the
 * hypotheses the rules build are always real implications: `~(C /\ D)` becomes `C ==> (D ==> F)` and
 * not `C ==> ~D`.
 *
 * What that buys is one set of rules instead of two. What it costs is that a term the caller wrote
 * as a negation can come back inside the search as an implication to falsity, which nothing outside
 * ever sees, because the goal and the hypotheses the **caller** gave are the terms the theorem is
 * about: the built ones are cut away by [[Rules.proveHyp]] before the answer leaves.
 *
 * == What it does not do ==
 *
 * **It is not complete for classical validity, and that is the point rather than a shortfall.**
 * Peirce's law and the excluded middle are refused here and proved by [[Propositional]], at one
 * axiom. A caller that wants an answer whatever it costs asks this one first and that one second,
 * which is what `Domain.Built.settle` does and, since `docs/adr/0023`, what `Prove` does at its
 * propositional address, and then the accounting says which of the two answered.
 *
 * **An atom is given no meaning**, so a goal whose validity lives inside an atom is refused here
 * exactly as it would be by a procedure that had never looked. `~(x = y) ==> ~(y = x)` is not
 * reachable: the two equations are two atoms. The refusal therefore says nothing about the goal,
 * which is why it carries `Standing.Unread` and not `Standing.Decided`, and that is the same
 * argument `SkeletonFailsAt` makes about the classical side in its own documentation.
 *
 * **No quantifier reaches the search.** Leading universals come off the goal and go back on the
 * theorem, which is what [[Minimal.prove]] and [[Propositional.decide]] both do; a quantifier
 * anywhere else makes its subformula an atom.
 */
final class Intuitionistic private (val logic: Logic) {

  import Intuitionistic.*

  private val rules: Rules = logic.rules

  /**
   * The goal, proved, or why not.
   *
   * Leading universal quantifiers come off before the search and go back on after it, for the
   * reason the two procedures beside this one give: the body is what the fragment is about, and a
   * quantifier left on would make the whole goal a single atom and the answer an immediate refusal.
   */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] = prove(goal, Fuel)

  /**
   * The same, at a stated depth, which is what makes the net measurable rather than only present.
   *
   * [[Intuitionistic.Fuel]] is a net under a termination argument and not the argument, so the
   * question a reader should be able to ask of it is how much of it anything uses. With the depth
   * fixed inside there is no way to ask: a goal either comes back proved or comes back
   * `BoundReached`, and the distance between the two is invisible. Running a population at a
   * descending depth and finding where its answers first change is that distance, and
   * `PropositionalRouteSpec` does exactly that.
   *
   * It is **not** a knob for a caller wanting more search. Nothing in this repository passes
   * anything but the default, the bound is not part of what the procedure promises, and a caller
   * who reached for a larger one would be buying a deeper search for a fragment whose termination
   * does not need it.
   */
  def prove(goal: Term, fuel: Int): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Logic.stripForall(goal)
      (variables, body) = stripped
      _ <-
        if (Term.typeOf(body) == Type.Bool) Right(())
        else Left(NotOfForm("a proposition", body))
      proved <- search(Vector.empty, body, fuel).left.map(atDepth(fuel))
      closed <- rules.genAll(proved, variables.toList)
    } yield closed

  /**
   * The exhaustion refusal, carrying the depth this run was actually given.
   *
   * [[search]] reports [[Intuitionistic.Fuel]] because it counts down and never knew what it
   * started from, which is right for every caller but the measuring one. Rewriting it here rather
   * than threading the starting depth through the recursion keeps the change to the one place that
   * can be wrong: a refusal from a run at depth 40 saying 256 is a figure nobody could reconcile,
   * and this repository loses more to that than to a missing figure.
   */
  private def atDepth(fuel: Int)(error: LogicError): LogicError = error match {
    case BoundReached(SearchName, _, _, goal) => BoundReached(SearchName, fuel, fuel, goal)
    case other => other
  }

  /**
   * Whether this would take the goal at all, answered before anything is spent on it.
   *
   * The address question, the way `Prove.addressOf` asks it of the arithmetic fragments. Narrower
   * than "is a proposition" on purpose: a goal with no connective in it is a single atom, and the
   * only such goals this proves are the ones that are literally `T`, so answering yes to them would
   * send a caller here whose statement belongs to a procedure that can read its atoms.
   */
  def reads(goal: Term): Boolean =
    Logic.stripForall(goal).toOption.exists { case (_, body) =>
      Term.typeOf(body) == Type.Bool && connective(body)
    }

  /** Whether the term uses any of the connectives this decides. */
  private def connective(term: Term): Boolean =
    logic.destConj(term).isDefined || logic.destDisj(term).isDefined ||
      logic.destImp(term).isDefined || logic.destNot(term).isDefined

  /* ------------------------------------------------------------------ reading a hypothesis */

  /**
   * A hypothesis read as an implication, which is what `~A` is.
   *
   * The one place negation enters the rules, and everything below is written against implications
   * because of it. [[detach]] is its other half: the two have to agree, and a `~A` read here as
   * `(A, F)` is detached there by [[Rules.notElim]] rather than by [[Rules.mp]].
   */
  private def asImplication(term: Term): Option[(Term, Term)] =
    logic.destImp(term).orElse(logic.destNot(term).map(inner => (inner, logic.falsity)))

  /** `h` and its antecedent give its consequent, whichever of the two shapes `h` has. */
  private def detach(implication: Kernel.Thm, antecedent: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    if (logic.destImp(implication.conclusion).isDefined) rules.mp(implication, antecedent)
    else rules.notElim(implication, antecedent)

  /**
   * The consequent, held, gives the implication itself, whichever of the two shapes it has.
   *
   * [[detach]] read backwards, and the two have to agree for the same reason: discharging an
   * antecedent that was never assumed gives `A ==> B` through [[Rules.disch]] and `~A` through
   * [[Rules.notIntro]], and only the second produces the term the caller wrote.
   */
  private def introduce(
    implication: Term,
    antecedent: Term,
    consequent: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    if (logic.destImp(implication).isDefined) rules.disch(antecedent, consequent)
    else rules.notIntro(antecedent, consequent)

  private def assume(term: Term): Either[LogicError, Kernel.Thm] = LogicError.lift(Kernel.assume(term))

  /* -------------------------------------------------------------------------- the search */

  /**
   * A theorem concluding the goal, resting on hypotheses among those given.
   *
   * The order is the calculus read as a program: what can be done without ever having to be undone
   * comes first, and only the two rules that can be the wrong choice branch.
   *
   * **An invertible rule that fires is the answer, whether it succeeds or fails**, which is what the
   * `Option` in the three phases below carries and what `orElse` on an `Either` would quietly throw
   * away. A rule is invertible exactly when its premises are provable if its conclusion is, so a
   * sequent whose conjunction was taken apart and then not proved is a sequent nothing else will
   * prove either: trying the right rules on it afterwards is work that cannot change the answer, and
   * it is the kind of work that doubles. Only [[guessing]] may be wrong, and it backtracks inside
   * itself.
   */
  private def search(hypotheses: Vector[Term], goal: Term, fuel: Int): Either[LogicError, Kernel.Thm] =
    if (fuel <= 0) Left(BoundReached(SearchName, Fuel, Fuel, goal))
    else if (hypotheses.contains(goal)) assume(goal)
    else if (goal == logic.truth) rules.truth
    else if (hypotheses.contains(logic.falsity))
      assume(logic.falsity).flatMap(rules.falsityElim(goal, _))
    else
      onTheLeft(hypotheses, goal, fuel)
        .orElse(onTheRight(hypotheses, goal, fuel))
        .orElse(splitting(hypotheses, goal, fuel))
        .getOrElse(guessing(hypotheses, goal, fuel))

  /**
   * The left rules that never have to be undone, which is all of them but one.
   *
   * A conjunction is taken apart; an implication is replaced by something strictly lighter,
   * according to the shape of its antecedent. The principal formula is **removed** in each case, and
   * that is the difference between this calculus and the obvious one: the rule that keeps its
   * implication and asks for its antecedent is what does not terminate, and it is not here at all.
   *
   * `Minimal`'s note about removal causing a loop was true of `Minimal`'s rules and is not true of
   * these. What looped there was an implication manufacturing a consequent that had just been taken
   * apart; here the only rule that concludes anything is the one for an antecedent already on the
   * left, and what it produces is a subformula of a formula that has gone.
   */
  private def onTheLeft(
    hypotheses: Vector[Term],
    goal: Term,
    fuel: Int
  ): Option[Either[LogicError, Kernel.Thm]] = {
    val conjunction = hypotheses.find(hypothesis => logic.destConj(hypothesis).isDefined)

    conjunction match {
      case Some(hypothesis) =>
        val (first, second) = logic.destConj(hypothesis).get
        val remaining = without(hypotheses, hypothesis)

        Some(for {
          assumed <- assume(hypothesis)
          leftHalf <- rules.conjElim1(assumed)
          rightHalf <- rules.conjElim2(assumed)
          proved <- search(remaining ++ gained(remaining, Vector(first, second)), goal, fuel - 1)
          // The two halves were assumed to prove it, and are discharged against the conjunction, so
          // what comes back rests on the conjunction as the caller gave it.
          withFirst <- rules.proveHyp(leftHalf, proved)
          result <- rules.proveHyp(rightHalf, withFirst)
        } yield result)

      case None => implicationOnTheLeft(hypotheses, goal, fuel)
    }
  }

  /**
   * The four contraction-free rules for an implication on the left, plus the two trivial ones.
   *
   * Each replaces the hypothesis with something lighter and derives the replacement from it, so the
   * recursive call works on a sequent that is strictly smaller and the cut at the end puts the
   * caller's own hypothesis back. The implication whose antecedent is itself an implication is the
   * one that is **not** invertible, and it is not decided here: [[guessing]] has it.
   */
  private def implicationOnTheLeft(
    hypotheses: Vector[Term],
    goal: Term,
    fuel: Int
  ): Option[Either[LogicError, Kernel.Thm]] = {
    val applicable = hypotheses.view
      .flatMap(hypothesis => asImplication(hypothesis).map((hypothesis, _)))
      .collectFirst {
        case (hypothesis, (antecedent, consequent))
            if replacementFor(hypotheses, antecedent, consequent).isDefined =>
          (hypothesis, antecedent, consequent)
      }

    applicable match {
      case None => None

      case Some((hypothesis, antecedent, consequent)) =>
        val replacement = replacementFor(hypotheses, antecedent, consequent).get

        Some(for {
          assumed <- assume(hypothesis)
          derived <- replacement.derive(assumed, antecedent, consequent)
          remaining = without(hypotheses, hypothesis)
          proved <- search(remaining ++ gained(remaining, derived.map(_.conclusion)), goal, fuel - 1)
          result <- derived.foldLeft[Either[LogicError, Kernel.Thm]](Right(proved)) { (acc, step) =>
            acc.flatMap(rules.proveHyp(step, _))
          }
        } yield result)
    }
  }

  /**
   * Which of the left rules an implication's antecedent selects, and what it produces.
   *
   * `None` where none applies, which is the atomic antecedent that is not on the left: such a
   * hypothesis can never be used and is not an obstacle either. It stays in the sequent rather than
   * being dropped, because a later rule can put its antecedent there.
   */
  private def replacementFor(
    hypotheses: Vector[Term],
    antecedent: Term,
    consequent: Term
  ): Option[Replacement] =
    if (antecedent == logic.falsity)
      // `F ==> B` is a theorem, so the hypothesis says nothing: it is dropped rather than used.
      Some(Replacement((_, _, _) => Right(Vector.empty)))
    else if (antecedent == logic.truth)
      Some(Replacement { (assumed, _, _) =>
        rules.truth.flatMap(detach(assumed, _)).map(Vector(_))
      })
    else
      logic.destConj(antecedent) match {
        case Some((first, second)) =>
          // `(C /\ D) ==> B` becomes `C ==> (D ==> B)`: assume both halves, put them together, and
          // detach. One conjunction lighter, which is the whole termination argument in one rule.
          Some(Replacement { (assumed, _, _) =>
            for {
              firstHeld <- assume(first)
              secondHeld <- assume(second)
              pair <- rules.conjIntro(firstHeld, secondHeld)
              detached <- detach(assumed, pair)
              inner <- rules.disch(second, detached)
              curried <- rules.disch(first, inner)
            } yield Vector(curried)
          })

        case None =>
          logic.destDisj(antecedent) match {
            case Some((first, second)) =>
              // `(C \/ D) ==> B` becomes the pair `C ==> B`, `D ==> B`. Two hypotheses out of one,
              // and each is lighter than what it replaces by the disjunction's own weight.
              Some(Replacement { (assumed, _, _) =>
                for {
                  fromFirst <- assume(first)
                    .flatMap(rules.disjIntro1(second, _))
                    .flatMap(detach(assumed, _))
                    .flatMap(rules.disch(first, _))
                  fromSecond <- assume(second)
                    .flatMap(rules.disjIntro2(first, _))
                    .flatMap(detach(assumed, _))
                    .flatMap(rules.disch(second, _))
                } yield Vector(fromFirst, fromSecond)
              })

            case None if asImplication(antecedent).isDefined =>
              // `(C ==> D) ==> B` is the one that guesses, and it is not decided here.
              None

            case None if hypotheses.contains(antecedent) =>
              // An atom already on the left: detach and keep the consequent, dropping the
              // implication. This is the only rule that concludes rather than rearranges.
              Some(Replacement { (assumed, antecedent, _) =>
                assume(antecedent).flatMap(detach(assumed, _)).map(Vector(_))
              })

            case None => None
          }
      }

  /** The right rules that never have to be undone: a conjunction, an implication, a negation. */
  private def onTheRight(
    hypotheses: Vector[Term],
    goal: Term,
    fuel: Int
  ): Option[Either[LogicError, Kernel.Thm]] =
    logic.destConj(goal) match {
      case Some((first, second)) =>
        Some(for {
          left <- search(hypotheses, first, fuel - 1)
          right <- search(hypotheses, second, fuel - 1)
          result <- rules.conjIntro(left, right)
        } yield result)

      case None =>
        logic.destImp(goal) match {
          case Some((antecedent, consequent)) =>
            Some(
              search(hypotheses ++ gained(hypotheses, Vector(antecedent)), consequent, fuel - 1)
                .flatMap(rules.disch(antecedent, _))
            )

          case None =>
            logic.destNot(goal).map { proposition =>
              search(hypotheses ++ gained(hypotheses, Vector(proposition)), logic.falsity, fuel - 1)
                .flatMap(rules.notIntro(proposition, _))
            }
        }
    }

  /**
   * A disjunction on the left, which branches and is still invertible.
   *
   * Both branches have to be proved whatever else is tried, so nothing is lost by committing to it,
   * which is why it is here rather than among the guesses. It is kept apart from the other left
   * rules only so that the cheap ones are tried first: a sequent with a conjunction and a
   * disjunction on it is better off taking the conjunction apart before it doubles.
   */
  private def splitting(
    hypotheses: Vector[Term],
    goal: Term,
    fuel: Int
  ): Option[Either[LogicError, Kernel.Thm]] =
    hypotheses.find(hypothesis => logic.destDisj(hypothesis).isDefined) match {
      case None => None

      case Some(hypothesis) =>
        val (first, second) = logic.destDisj(hypothesis).get
        val remaining = without(hypotheses, hypothesis)

        Some(for {
          assumed <- assume(hypothesis)
          leftCase <- search(remaining ++ gained(remaining, Vector(first)), goal, fuel - 1)
          rightCase <- search(remaining ++ gained(remaining, Vector(second)), goal, fuel - 1)
          result <- rules.disjElim(assumed, leftCase, rightCase)
        } yield result)
    }

  /**
   * The two rules that can be the wrong choice, and every one of them is tried.
   *
   * A disjunctive goal is proved on one side or the other, and an implication whose antecedent is
   * an implication asks for two premises at once. Neither is invertible: a goal reachable through
   * the second implication on the left may be unreachable through the first, so the search tries
   * each in turn and the refusal comes back only when all of them have been.
   */
  private def guessing(
    hypotheses: Vector[Term],
    goal: Term,
    fuel: Int
  ): Either[LogicError, Kernel.Thm] = {
    val nested = hypotheses.view.flatMap { hypothesis =>
      asImplication(hypothesis).flatMap { case (antecedent, consequent) =>
        asImplication(antecedent).map { case (inner, target) =>
          (hypothesis, antecedent, inner, target, consequent)
        }
      }
    }

    val advanced = nested
      .map { case (hypothesis, antecedent, inner, target, consequent) =>
        nestedImplication(hypotheses, hypothesis, antecedent, inner, target, consequent, goal, fuel)
      }
      .collectFirst { case Right(theorem) => theorem }

    advanced match {
      case Some(theorem) => Right(theorem)

      case None =>
        logic.destDisj(goal) match {
          case None => Left(NotOfForm("a goal this calculus reaches", goal))

          case Some((first, second)) =>
            search(hypotheses, first, fuel - 1)
              .flatMap(rules.disjIntro1(second, _))
              .orElse(search(hypotheses, second, fuel - 1).flatMap(rules.disjIntro2(first, _)))
        }
    }
  }

  /**
   * `(C ==> D) ==> B` on the left: `D ==> B` proving `C ==> D`, and `B` proving the goal.
   *
   * The half of this worth reading is how the left premise gets to assume `D ==> B` for free.
   * Assume `D`; then `C ==> D` holds by weakening, so the hypothesis applies and gives `B`;
   * discharge `D` and what is left is `D ==> B` resting on the hypothesis alone. That is the
   * derivation the cut below spends, and it is why this rule needs no contraction: the implication
   * is used exactly once, here, and what the premises see is strictly lighter.
   */
  private def nestedImplication(
    hypotheses: Vector[Term],
    hypothesis: Term,
    antecedent: Term,
    inner: Term,
    target: Term,
    consequent: Term,
    goal: Term,
    fuel: Int
  ): Either[LogicError, Kernel.Thm] = {
    val remaining = without(hypotheses, hypothesis)

    for {
      assumed <- assume(hypothesis)
      targetHeld <- assume(target)
      weakened <- introduce(antecedent, inner, targetHeld)
      reached <- detach(assumed, weakened)
      targetGivesConsequent <- rules.disch(target, reached)

      lighter <- logic.mkImp(target, consequent)
      // The left premise proves the ANTECEDENT as the caller wrote it, `~C` and not `C ==> F`,
      // because it is the term the hypothesis is waiting for and two terms that are provably equal
      // are still two terms to `mp`.
      fromLighter <- search(remaining ++ gained(remaining, Vector(lighter)), antecedent, fuel - 1)
      established <- rules.proveHyp(targetGivesConsequent, fromLighter)
      gainedConsequent <- detach(assumed, established)

      fromConsequent <- search(remaining ++ gained(remaining, Vector(consequent)), goal, fuel - 1)
      result <- rules.proveHyp(gainedConsequent, fromConsequent)
    } yield result
  }

  /* ------------------------------------------------------------------------- the sequent */

  /** The hypotheses without the one a rule is about, which is what "contraction-free" means here. */
  private def without(hypotheses: Vector[Term], principal: Term): Vector[Term] =
    hypotheses.filterNot(_ == principal)

  /**
   * What a rule adds that is not there already.
   *
   * The sequent is carried as a set rather than as a multiset, so a rule that produces a formula
   * already on the left adds nothing and the measure still falls: the principal formula has gone
   * and nothing replaced it.
   */
  private def gained(hypotheses: Vector[Term], produced: Vector[Term]): Vector[Term] =
    produced.distinct.filterNot(hypotheses.contains)
}

object Intuitionistic {

  /**
   * What a left rule replaces a hypothesis with, and how the replacement is derived from it.
   *
   * A function rather than a data type because every rule's replacement is a derivation and the
   * derivations have nothing in common: what the four cases share is only that each produces
   * theorems whose hypotheses are the principal formula, which is what makes the cut at the call
   * site one loop instead of four cases.
   */
  private final case class Replacement(
    derive: (Kernel.Thm, Term, Term) => Either[LogicError, Vector[Kernel.Thm]]
  )

  /**
   * How deep the search goes before it says so.
   *
   * The net and not the termination argument: the measure in the class comment falls on every rule,
   * so a goal of this fragment terminates without it. It is the last thing left of `Minimal.Depth`,
   * which is the bound the search in that file carried and which went with the search in 2026-09-16;
   * two sentences here went on naming it, which is what a reference to something that has moved
   * costs when it is a docstring and nothing resolves it. It is here
   * because that argument is a paragraph and this is a number, and because a mistake in one of the
   * rules would otherwise be an out-of-memory rather than a refusal. A goal that reaches it comes
   * back as `BoundReached`, which carries `Standing.Exhausted`: evidence in neither direction,
   * which is the honest report for a net being hit.
   *
   * Higher than `Minimal.Depth` because the rules here take smaller steps: currying `(C /\ D) ==> B`
   * spends a level to produce a hypothesis that spends another two being used.
   *
   * **How much of it anything uses is measured rather than assumed, and the figure is not written
   * here.** A count copied next to the number it is about is the copy that drifts, so what stands
   * here is where to read it: `PropositionalRouteSpec` runs its whole enumerated population at a
   * descending depth, finds the depth at which the answers first change, asserts that the margin is
   * wide, and prints what it found. That spec is also the only caller anywhere that passes a depth.
   *
   * == What 256 promises, which is the criterion it is chosen by ==
   *
   * **The fuel a goal needs never exceeds the goal's own size**, counting one for each connective
   * and one for each atom occurrence. So this number read forwards is a promise about what a caller
   * may write: **a goal of at most 256 nodes is answered rather than stopped.** That is the
   * sentence this constant was missing, and without it 256 is a rounding.
   *
   * It is measured and asserted rather than argued. `PropositionalRouteSpec` puts it to every
   * formula of the enumerated population and also asserts that the bound is approached, since a
   * search that spent one unit on everything would satisfy the first half alone. Exhaustively over
   * every formula on two atoms of at most **seven** nodes, 5618 of them, measured 2026-09-22: none
   * needs more than its size. Eight nodes is 26032 formulas and did not finish in the time it was
   * given, which is why the figure quoted is seven.
   *
   * **The bound is attained rather than approached, and it is attained at two nodes.** `~p` and
   * `~q` need 2 of 2, which is what that spec prints and what the first perturbation of
   * `tools/verify/perturb-the-nets-criterion.sh` names when it fires. So the relation is tight,
   * and tight trivially: a negation opens and the search is done, which any calculus at all
   * attains. What is asserted is therefore the non-trivial half, that some goal of at least four
   * nodes needs all but one of them, and the two are kept apart because collapsing them is the
   * defect this paragraph repairs. It said the closest needs **6 of 7** until 2026-09-22, here and
   * in `docs/adr/0031` and in that spec's own comment; 6 is the worst NEED among the probe's
   * seven-node formulas, a figure per size band, and is not a ratio at all.
   *
   * **That relation is also what the net is for.** This is a net against a mistake in the rules and
   * not against the mathematics, which is what the paragraph above says; a rule that stopped
   * decreasing the measure would show up as a goal needing more than its size, and now goes red
   * there instead of arriving as an out-of-memory.
   *
   * == Where it bites, and what that costs ==
   *
   * The edge is one link wide and it is exhibited rather than possible. On the chain of
   * implications `PropositionalRouteSpec.chainOf` builds, consumption grows as `2n + 2`: at 127
   * links the search needs **256 of 256** and settles at no axiom, and at 128 it is cut short and
   * the classical route settles it at one. **Past that point the price is decided by this constant
   * rather than by the claim**, which is the whole reason `Prove.Outcome.CutShort` exists to say so;
   * `docs/adr/0031` is that decision and carries the table.
   *
   * A 127-link chain is 511 nodes, so the family that saturates the net is twice the size the
   * criterion above admits: the criterion is the conservative reading and the edge is the generous
   * one. Nothing this repository holds is near either. When `docs/adr/0023` counted the library on
   * 2026-09-18, 184 of its 505 statements took this address and the deepest used 9; the corpora
   * cannot take the address at all, and over the enumerated population of at most six nodes nothing
   * is cut short.
   *
   * **So it stays at 256, and that is a decision rather than an inheritance.** Raising it moves the
   * edge without changing its nature and would want a criterion for which population must fit;
   * removing it trades a refusal for an out-of-memory in exactly the case the net is there to take,
   * which the paragraph above declines. What was missing was never the number, it was the sentence
   * saying what the number buys, and that sentence is the first paragraph of this section.
   */
  val Fuel: Int = 256

  /**
   * What the exhaustion refusal calls itself, published so that reading it back is not a literal.
   *
   * A caller that has to tell "I stopped" from "it is not so" has only the refusal to tell them
   * apart by, and `BoundReached` from this search is the one that means the first. Leaving the
   * string at its two use sites would make that test a quotation, which is the shape that goes
   * stale when one of the two is reworded and nothing compares them.
   */
  val SearchName: String = "the intuitionistic search"


  /** Over the plain logic, which is where a statement with no arithmetic in it lives. */
  lazy val standard: Intuitionistic = new Intuitionistic(Logic.standard)

  /** Over a development of one's own, so that its own declared predicates are the atoms. */
  def apply(logic: Logic): Intuitionistic = new Intuitionistic(logic)
}
