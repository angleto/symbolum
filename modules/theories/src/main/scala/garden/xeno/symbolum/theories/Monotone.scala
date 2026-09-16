package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * `|- MONOTONE f`, read off the shape of `f` rather than proved again for each rule set.
 *
 * [[Inductive.Introduction]] — the introduction rules of a set defined by clauses — asks
 * `MONOTONE f`, and [[Inductive.Induction]] asks nothing, which is the asymmetry that file is built
 * on: the half that decides a non-membership is free and the half that decides a membership is not.
 * So every caller that wants to put something **into** an inductively defined set pays for
 * monotonicity first, and until this landed every caller paid by hand.
 *
 * == What it costs a caller, measured rather than estimated ==
 *
 * The two hand proofs this replaces are the measurement, and they are the same proof written twice.
 * Counted as code lines, blanks and comments stripped, over the body of each function from its
 * signature to its closing brace:
 *
 *  - `InductiveSpec.evenIsMonotone`, the even numbers, an operator of two clauses: **52** lines,
 *    66 with its comments.
 *  - `Reaching.monotone`, a derivation carrying its step count, an operator of two clauses with a
 *    three-way split nested to the right of the set argument: **56** lines, 68 with its comments.
 *
 * The pair is the argument for this file rather than either figure on its own, and the card that
 * asked for the work predicted forty and seventy, which is a spread of 75% where the measurement
 * gives 8%. The second operator is substantially larger than the first and its proof is **not**
 * larger, because everything to the right of the one positive occurrence is carried across without
 * being looked at. A cost that does not grow with the operator is not a cost about the operator.
 *
 * **What it does not do is make the repository shorter today, and saying otherwise would be the
 * easy claim to make.** This file is 175 code lines against the 108 it retires, so the first two
 * callers together do not pay for it. What it changes is the shape of the cost: a caller's
 * monotonicity goes from about 54 lines to one, so the third rule set is where the total crosses,
 * and there is one of those open already.
 *
 * == It reads a shape; it does not search ==
 *
 * There is nothing here to decide. `MONOTONE f` unfolds to an implication between `f S x` and
 * `f T x` for an arbitrary inclusion of `S` in `T`, and those two terms are the same term with one
 * variable exchanged for the other. So the proof is a walk over that term: at each connective,
 * take the hypothesis apart, carry the pieces, and put it back together. The **one** step that uses
 * the inclusion is the leaf `S t` against `T t`, and every other step is bookkeeping.
 *
 * The positive shapes it walks, which are the shapes a rule set is written in: conjunction,
 * disjunction, the existential, the universal, and an implication whose antecedent does not mention
 * the set. A subterm the set does not occur in at all is not walked: it is carried across whole,
 * which is what makes the cost independent of everything the clauses say about the elements.
 *
 * **So a negation in the operator is not by itself a refusal**, and `Reaching` is the case that
 * says so rather than a hypothetical: its clause contains `~(A (FST p) (FST q))`, and it is
 * accepted, because the set does not occur inside that negation and the whole conjunct crosses
 * without being read. What is refused is the set argument occurring **under** a negation. The two
 * are easy to run together and they are not the same question: the first is about the operator, the
 * second is about a position in it.
 *
 * == The refusal, which is the half that says it was tested ==
 *
 * It refuses where the set argument occurs under a negation or to the left of an implication, and
 * the refusal names the **subterm**, not the operator, because that is what a caller has to go and
 * change. `\S x. ~(S x)` is the witness: `InductiveSpec` puts it here and gets the refusal, and then
 * derives falsity from `MONOTONE` of it, so the refusal is not this procedure being careful about
 * something that happens to be true anyway.
 *
 * A refusal is not a claim that `f` is not monotone, and cannot be: `\S x. ~(~(S x))` is monotone
 * and is refused, because two negations is not a shape this reads. What it says is that this
 * operator is not written in the shape a rule set is written in, which is [[LogicError.Standing]]'s
 * `Unread` and is why the refusal is a [[NotOfForm]] rather than a decision.
 *
 * == What a defect here could and could not cost ==
 *
 * Nothing this returns is believed because this file built it. Every step goes through the derived
 * rules and therefore through the kernel, and the last step checks the assembled theorem against
 * `MONOTONE f` by `eqMp` across the definition, so a walk that went wrong produces a refusal and
 * never a theorem about something else. What a defect here costs is a caller that cannot proceed,
 * which is the failure mode this repository asks for.
 */
object Monotone {

  /**
   * `|- MONOTONE operator`, or a refusal naming the subterm that stopped it.
   *
   * `logic` is the caller's rather than [[Inductive]]'s: an operator written over a development
   * above `Inductive` mentions constants `Inductive.logic` cannot read, and `Reaching` is the
   * caller that made that concrete. `inductive` is here for one thing, the definition of `MONOTONE`,
   * which is what the result has to be folded back into.
   */
  def prove(logic: Logic, inductive: Inductive, operator: Term): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      element <- elementType(operator)
      definition <- inductive.definition(Inductive.Monotone)
      atElement = Kernel.instType(Map(Classical.TypeVariable -> element), definition)

      unfolded <- Conv.unfold(atElement, List(operator))
      body <- rightOf(unfolded)
      normalising <- Conv.betaNormalise(body)
      normal <- rightOf(normalising)

      // `!S T. (!x. S x ==> T x) ==> (!x. f S x ==> f T x)`, opened. The two sets and the
      // implication between them belong to `MONOTONE`'s definition and not to the caller, so this
      // much of the shape is guaranteed; everything below the second `!x.` is the caller's.
      outer <- Logic.stripForall(normal)
      (sets, betweenThem) = outer
      smaller <- sets.lift(0).toRight(NotOfForm("a claim about two sets", normal))
      larger <- sets.lift(1).toRight(NotOfForm("a claim about two sets", normal))

      parts <- impliesOf(logic, betweenThem)
      (inclusion, everywhere) = parts
      assumedInclusion <- LogicError.lift(Kernel.assume(inclusion))

      // Exactly one binder comes off here, by the destructor rather than by `stripForall`, because
      // the next one belongs to the operator: a clause written `\S x. !y. ...` would otherwise be
      // opened one quantifier too far and rebuilt one too few.
      opened <- openOne(logic, everywhere, sets.toSet)
      (point, clause) = opened
      clauseParts <- impliesOf(logic, clause)
      (premise, target) = clauseParts
      assumedPremise <- LogicError.lift(Kernel.assume(premise))

      carried <- carry(logic, assumedInclusion, smaller, larger, premise, target, assumedPremise)

      proved <- rules
        .disch(premise, carried)
        .flatMap(rules.gen(point, _))
        .flatMap(rules.disch(inclusion, _))
        .flatMap(rules.gen(larger, _))
        .flatMap(rules.gen(smaller, _))

      folded <- Conv.sym(normalising).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, proved)))
      result <- Conv.sym(unfolded).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, folded)))
    } yield result
  }

  /* ------------------------------------------------------------------ the walk */

  /**
   * A proof of `source` becomes a proof of `target`, which is the same term with `larger` where
   * `source` has `smaller`.
   *
   * The two terms are never built here: they arrive as a pair out of `MONOTONE`'s own statement, so
   * there is no opportunity to construct the wrong target and then prove it. What the walk decides
   * is only how to get from one to the other, and where it cannot, it says which subterm.
   */
  private def carry(
    logic: Logic,
    inclusion: Kernel.Thm,
    smaller: FVar,
    larger: FVar,
    source: Term,
    target: Term,
    proof: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    def recur(nextSource: Term, nextTarget: Term, nextProof: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      carry(logic, inclusion, smaller, larger, nextSource, nextTarget, nextProof)

    // The set variable is NOT named in the message, and that is the second time this decision is
    // taken in this change rather than a style point. `smaller` is freshened off `MONOTONE`'s own
    // binders, so its name is an artefact of stripping a definition and not anything the caller
    // wrote: a refusal saying `S` would name a variable that appears nowhere in the operator the
    // caller handed over. `InductiveSpec` declines to assert the name for the same reason, and a
    // message printing what a test refuses to pin is the two halves disagreeing. What identifies
    // the problem is the subterm, which is carried as a value.
    def refuse(where: Term): Either[LogicError, Kernel.Thm] =
      Left(NotOfForm("an operator whose set argument occurs only positively", where))

    // Everything a witness must not be confused with: what either side mentions, what the proof
    // stands on, and the two set variables themselves.
    val avoid: Set[FVar] =
      Term.freeVariables(source) ++ Term.freeVariables(target) ++
        Term.freeVariables(proof.conclusion) ++
        proof.hypotheses.flatMap(Term.freeVariables) ++
        Term.freeVariables(inclusion.conclusion) + smaller + larger

    def conjunction(parts: ((Term, Term), (Term, Term))): Either[LogicError, Kernel.Thm] = {
      val ((left, right), (targetLeft, targetRight)) = parts
      for {
        leftProof <- rules.conjElim1(proof)
        leftCarried <- recur(left, targetLeft, leftProof)
        rightProof <- rules.conjElim2(proof)
        rightCarried <- recur(right, targetRight, rightProof)
        result <- rules.conjIntro(leftCarried, rightCarried)
      } yield result
    }

    def disjunction(parts: ((Term, Term), (Term, Term))): Either[LogicError, Kernel.Thm] = {
      val ((left, right), (targetLeft, targetRight)) = parts
      for {
        assumedLeft <- LogicError.lift(Kernel.assume(left))
        leftCarried <- recur(left, targetLeft, assumedLeft)
        leftCase <- rules.disjIntro1(targetRight, leftCarried)
        assumedRight <- LogicError.lift(Kernel.assume(right))
        rightCarried <- recur(right, targetRight, assumedRight)
        rightCase <- rules.disjIntro2(targetLeft, rightCarried)
        result <- rules.disjElim(proof, leftCase, rightCase)
      } yield result
    }

    /**
     * An implication is positive on the right and negative on the left, so this is where half the
     * refusals come from and the other half are negations.
     */
    def implication(parts: ((Term, Term), (Term, Term))): Either[LogicError, Kernel.Thm] = {
      val ((antecedent, consequent), (targetAntecedent, targetConsequent)) = parts
      if (Term.occursFree(smaller, antecedent)) refuse(antecedent)
      else if (antecedent != targetAntecedent) refuse(source)
      else
        for {
          assumed <- LogicError.lift(Kernel.assume(antecedent))
          detached <- rules.mp(proof, assumed)
          carriedOn <- recur(consequent, targetConsequent, detached)
          result <- rules.disch(antecedent, carriedOn)
        } yield result
    }

    def existential(predicates: (Term, Term)): Either[LogicError, Kernel.Thm] =
      Type.destFun(Term.typeOf(predicates._1)) match {
        case None => Left(NotOfForm("a predicate", predicates._1))
        case Some((domain, _)) =>
          val (predicate, targetPredicate) = predicates
          val witness = Conv.freshVariable("w", domain, avoid)
          for {
            appliedSource <- LogicError.lift(Term.app(predicate, witness))
            instance <- Term.betaReduce(appliedSource).toRight(NotOfForm("a redex", appliedSource))
            appliedTarget <- LogicError.lift(Term.app(targetPredicate, witness))
            targetInstance <- Term.betaReduce(appliedTarget).toRight(NotOfForm("a redex", appliedTarget))
            // Assumed reduced, which is the form `Rules.existsElim` discharges against: assuming
            // the application leaves a hypothesis that is the same proposition and not the same
            // term, and both hand proofs this replaces carry a comment saying so.
            opened <- LogicError.lift(Kernel.assume(instance))
            carriedOn <- recur(instance, targetInstance, opened)
            introduced <- rules.existsIntro(targetPredicate, witness, carriedOn)
            result <- rules.existsElim(proof, witness, introduced)
          } yield result
      }

    def universal(predicates: (Term, Term)): Either[LogicError, Kernel.Thm] =
      Type.destFun(Term.typeOf(predicates._1)) match {
        case None => Left(NotOfForm("a predicate", predicates._1))
        case Some((domain, _)) =>
          val targetPredicate = predicates._2
          val variable = Conv.freshVariable("v", domain, avoid)
          for {
            specialised <- rules.spec(variable, proof)
            appliedTarget <- LogicError.lift(Term.app(targetPredicate, variable))
            targetInstance <- Term.betaReduce(appliedTarget).toRight(NotOfForm("a redex", appliedTarget))
            // The source is read off the theorem rather than computed a second time from the
            // predicate: what the recursion has to carry is what `spec` actually produced.
            carriedOn <- recur(specialised.conclusion, targetInstance, specialised)
            result <- rules.gen(variable, carriedOn)
          } yield result
      }

    if (!Term.occursFree(smaller, source))
      // Nothing to carry: the subterm says nothing about the set, so the inclusion is irrelevant to
      // it and it crosses whole. This is the case that makes the walk cost what the operator's
      // POSITIONS cost rather than what the operator costs.
      if (source == target) Right(proof) else refuse(source)
    else
      source match {
        // The leaf, and the one step in the whole walk that spends the inclusion.
        case App(fn, argument) if fn == smaller =>
          target match {
            case App(other, otherArgument) if other == larger && otherArgument == argument =>
              rules.spec(argument, inclusion).flatMap(rules.mp(_, proof))
            case _ => refuse(source)
          }

        case _ =>
          List(
            both(logic.destConj(source), logic.destConj(target)).map(conjunction),
            both(logic.destDisj(source), logic.destDisj(target)).map(disjunction),
            both(logic.destImp(source), logic.destImp(target)).map(implication),
            both(logic.destExistsPredicate(source), logic.destExistsPredicate(target)).map(existential),
            both(logic.destForallPredicate(source), logic.destForallPredicate(target)).map(universal)
          ).flatten.headOption.getOrElse(refuse(source))
      }
  }

  /* ----------------------------------------------------------------- internals */

  /** The two sides destructured the same way, or nothing: a shape one side has is not a shape. */
  private def both[A](source: Option[A], target: Option[A]): Option[(A, A)] = source.zip(target)

  /** `'a`, from an operator's type `('a -> bool) -> 'a -> bool`. */
  private def elementType(operator: Term): Either[LogicError, Type] = {
    val refusal = Left(NotOfForm("an operator over sets, of type ('a -> bool) -> 'a -> bool", operator))

    Type.destFun(Term.typeOf(operator)).flatMap { case (sets, _) => Type.destFun(sets) } match {
      case Some((element, Type.Bool)) => Right(element)
      case _ => refusal
    }
  }

  /** One leading universal off, and the variable it was over. */
  private def openOne(
    logic: Logic,
    term: Term,
    avoid: Set[FVar]
  ): Either[LogicError, (FVar, Term)] =
    logic.destForallPredicate(term) match {
      case None => Left(NotOfForm("a universally quantified claim", term))
      case Some(predicate) =>
        Type.destFun(Term.typeOf(predicate)) match {
          case None => Left(NotOfForm("a predicate", predicate))
          case Some((domain, _)) =>
            val variable = Conv.freshVariable("x", domain, avoid ++ Term.freeVariables(term))
            for {
              applied <- LogicError.lift(Term.app(predicate, variable))
              opened <- Term.betaReduce(applied).toRight(NotOfForm("a redex", applied))
            } yield (variable, opened)
        }
    }

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term
      .destEq(theorem.conclusion)
      .map(_._2)
      .toRight(NotOfForm("an equation", theorem.conclusion))

  private def impliesOf(logic: Logic, term: Term): Either[LogicError, (Term, Term)] =
    logic.destImp(term).toRight(NotOfForm("an implication", term))
}
