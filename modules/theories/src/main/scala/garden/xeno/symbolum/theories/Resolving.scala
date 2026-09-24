package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Resolution as an object this system reasons **about**, and the first theorem of that kind.
 *
 * `modules/sat` produces resolution refutations and `logic.Propositional` replays one into a
 * theorem, a step at a time. Neither of them says anything about resolution itself: the replay is
 * trusted because every step goes through the kernel's rules, not because resolution is known to be
 * sound. This development is the third reading of the same object, one level up, where resolution
 * is a mathematical object and soundness is a theorem with a proof.
 *
 * == Why this is the first brick of Cook and Reckhow, and why that is the honest frame ==
 *
 * Cook and Reckhow (1979) proved that NP = coNP if and only if some propositional proof system has
 * polynomial-size proofs of every tautology, which turns lower bounds on proof size into an attack
 * on NP != coNP and so on P != NP. **A proof system in their sense has to be sound**: it is what
 * makes the size of a proof mean anything. So a development that wants to talk about the size of
 * resolution refutations owes this theorem before it owes any other, and it is what is here.
 *
 * What is **not** here is the content of that programme, and the gap should be read as large.
 * Haken's lower bound for the pigeonhole principle, and the width bound of Ben-Sasson and
 * Wigderson that gives a shorter route to it, are combinatorial arguments about restrictions and
 * about a sub-additive measure on clauses; nothing below is a step towards either. Width and size
 * are not even defined here. `docs/adr/0013`'s warning about calling a meta-level closure by the
 * name of an object-level theorem applies to this file too: this is soundness, it is the floor, and
 * it is not a lower bound.
 *
 * == Nothing is coded, and the card that asked for this expected the opposite ==
 *
 * The obvious route, and the one written down before anything was measured, was to arithmetise:
 * a clause as a number, a derivation as a beta-function sequence, the way `Provability` codes a
 * derivation of PA. That was wrong, and the measurement that says so is that the four statements
 * this file needs **parse in the chain's widest signature as it already stands**. Arithmetisation
 * buys self-reference, which is what Goedel's argument needs and what proof complexity does not:
 * a statement about resolution quantifies over derivations, and a derivation is a finite object the
 * ambient logic can hold directly.
 *
 * So there is no coding, no beta function, no division, and no new primitive. `Provability` and
 * `Language` each run to thousands of lines; this is a fraction of either, and the difference is
 * the decision rather than the effort.
 *
 * == How a clause and a derivation are written ==
 *
 * A derivation is three functions and two numbers, and no type of its own:
 *
 *   - `k : num -> num` gives the number of literals in clause `j`;
 *   - `v : num -> num -> num` gives the **variable** of literal `i` of clause `j`;
 *   - `s : num -> num -> bool` gives its **polarity**.
 *
 * An assignment is `a : num -> bool` on variables. Literal `i` of clause `j` is satisfied exactly
 * when `a (v j i) = s j i`, which is the whole of the semantics and needs no arithmetic: a positive
 * literal wants the variable true, a negative one wants it false, and one equation says both.
 *
 * The clause is satisfied when some literal below its length is, which is `?i. NUM_LT i (k j) /\ (a
 * (v j i) = s j i)`. The empty clause has `k j = ZERO` and nothing below zero, so nothing satisfies
 * it; [[Resolving.EmptyUnsatisfiable]] is that, and it is what makes a refutation a refutation.
 *
 * **Nothing is given a name of its own, and that is deliberate for now.** A constant for "clause
 * `j` is satisfied" would read better and would make this a link in the chain, which moves the
 * signature, the reading register, `docs/lemmas.md` and three pinned counts. The statements below
 * are written out instead, which is more to read and is checkable against the informal claim
 * without trusting a definition. Naming them is the first thing the next piece of work should do.
 */
final class Resolving private (
  val peano: Peano,
  val classical: Classical,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** A derived fact of this development, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Resolving {

  /**
   * Soundness of one resolution step, in the form the proof actually needs.
   *
   * ```
   * |- !a v1 s1 v2 s2 v3 s3 n1 n2 n3 x.
   *      (!i. NUM_LT i n1 ==> ~(v1 i = x /\ s1 i = T) ==>
   *           (?m. NUM_LT m n3 /\ v3 m = v1 i /\ s3 m = s1 i)) ==>
   *      (!i. NUM_LT i n2 ==> ~(v2 i = x /\ s2 i = F) ==>
   *           (?m. NUM_LT m n3 /\ v3 m = v2 i /\ s3 m = s2 i)) ==>
   *      (?i. NUM_LT i n1 /\ (a (v1 i) = s1 i)) ==>
   *      (?i. NUM_LT i n2 /\ (a (v2 i) = s2 i)) ==>
   *      (?i. NUM_LT i n3 /\ (a (v3 i) = s3 i))
   * ```
   *
   * Read informally: if every literal of the first parent except the pivot taken positively appears
   * in the third clause, and every literal of the second parent except the pivot taken negatively
   * appears in it too, then any assignment satisfying both parents satisfies the third.
   *
   * == The two conditions resolution has that this does not ask for ==
   *
   * Resolution's own definition says four things, and the two missing are that the pivot **occurs**:
   * positively in the first parent and negatively in the second. They are what make the third clause
   * the resolvent rather than merely a weakening of either parent, and [[StepSoundOfResolvent]] is
   * the statement carrying all four.
   *
   * **They are not spent.** That is not a saving, it is what the proof turns out to need, and it is
   * the same question `DomainTheorySpec` asks of its four axioms: which of the assumptions did the
   * conclusion actually cost. Here the answer is two of four, and a reader of the definition would
   * not have guessed which two.
   *
   * == The proof, and the one axiom ==
   *
   * By cases on `a x`. If it holds, the second parent's satisfying literal cannot be the pivot,
   * because the pivot is negative there and would make `a x = F`; so that literal is one the second
   * condition carries into the third clause, and it is satisfied there by the same equation. If
   * `a x` fails, the first parent gives the witness by the mirror argument.
   *
   * The case split is the whole of what it costs: `Classical.cases` rests on the excluded middle,
   * which rests on `SELECT`. **One axiom, and it is the same one `logic.Propositional` spends**,
   * for the same reason: deciding that a boolean is one of two things is classical here.
   *
   * One and not two, which is the half worth checking against [[EmptyUnsatisfiable]]: the naturals
   * cost choice **and** infinity, and this theorem never reaches a fact about `num`. `NUM_LT` is
   * carried through its statement and never unfolded.
   */
  val StepSound: String = "RES_STEP_SOUND"

  /**
   * The same, with resolution's two occurrence conditions in front of it.
   *
   * What a reader checks against the textbook definition, and it is a corollary of
   * [[StepSound]] by discharging two antecedents nothing used. Kept as a separate fact rather than
   * as the only one, because the pair is the measurement: the statement a reader recognises, and
   * the statement the proof needed.
   */
  val StepSoundOfResolvent: String = "RES_STEP_SOUND_OF_RESOLVENT"

  /**
   * `|- !a v s n. n = ZERO ==> ~(?i. NUM_LT i n /\ (a (v i) = s i))`
   *
   * Nothing satisfies the empty clause, which is what makes a derivation ending on it a refutation
   * rather than a derivation.
   *
   * **It costs two axioms where [[StepSound]] costs one, and that is the opposite of where a reader
   * would look for the price.** The step has the classical case split in it and spends choice alone;
   * this has no case split at all and spends choice **and infinity**, because it is the only one of
   * the two that reaches a fact about `num`. `Peano.NUM_NOT_LT_ZERO` is that fact, and `num` is a
   * defined type carved out of an infinite one, so every lemma about it carries the naturals' two.
   *
   * Which says something about [[StepSound]] worth knowing: `NUM_LT` occurs all through its
   * statement and is never unfolded, so a theorem that looks like arithmetic spends none of it.
   * The soundness of a resolution step is about the **shape** of a clause and not about the numbers
   * indexing it.
   */
  val EmptyUnsatisfiable: String = "RES_EMPTY_UNSATISFIABLE"

  /**
   * Soundness of a whole derivation: every clause of it is satisfied wherever the inputs are.
   *
   * ```
   * |- !a k v s inputs m.
   *      (!j. NUM_LT j inputs ==> (?i. NUM_LT i (k j) /\ (a (v j i) = s j i))) ==>
   *      (!j. NUM_LT j m ==> <j is an input, or a resolvent of two earlier steps>) ==>
   *      (!j. NUM_LT j m ==> (?i. NUM_LT i (k j) /\ (a (v j i) = s j i)))
   * ```
   *
   * A derivation is `k`, `v` and `s` read at `m` indices: clause `j` is `k j` literals long and its
   * `i`th is the variable `v j i` at polarity `s j i`. Step `j` is justified when it is one of the
   * first `inputs` clauses or when two **earlier** steps resolve to it, and that the two are earlier
   * is the whole of what makes a derivation well founded, exactly as `Provability.NUM_STEP` needs
   * its justifications to name earlier steps.
   *
   * By strong induction on the step index, which is `Peano.NUM_STRONG_INDUCTION` and is the right
   * shape for the same reason `Language` needs it: what a step follows from is *some* earlier steps
   * rather than its predecessor. The step case is a disjunction with two arms, and the second is
   * [[StepSound]] specialised at `v p`, `s p`, `v q`, `s q` and `v j`, `s j`, which is where the
   * derivation's three functions become the step lemma's six.
   *
   * **It costs two axioms where [[StepSound]] costs one**, and the extra is infinity for the reason
   * [[EmptyUnsatisfiable]] gives: strong induction and the transitivity of the order are facts about
   * `num`, and `num` is carved out of an infinite type. The step lemma reaches neither, which is why
   * the pair is worth reading together.
   */
  val DerivationSound: String = "RES_SOUND"

  /**
   * What a refutation is for: a derivation reaching the empty clause means nothing satisfies the
   * inputs.
   *
   * ```
   * |- !k v s inputs m.
   *      (!j. NUM_LT j m ==> <j is an input, or a resolvent of two earlier steps>) ==>
   *      (?j. NUM_LT j m /\ k j = ZERO) ==>
   *      ~(?a. !j. NUM_LT j inputs ==> (?i. NUM_LT i (k j) /\ (a (v j i) = s j i)))
   * ```
   *
   * **The assignment is quantified inside the negation and that is the statement rather than a
   * detail.** [[DerivationSound]] says what one assignment does; this says there is no such
   * assignment at all, which is the claim `modules/sat` makes every time it answers unsatisfiable
   * and which nothing here could state until now.
   *
   * Three lines over the two theorems above: soundness gives every clause satisfied, the step that
   * is empty is one of them, and [[EmptyUnsatisfiable]] says nothing satisfies that one.
   *
   * This is the property Cook and Reckhow require of a proof system before the size of a proof means
   * anything, and having it is what makes the next question — how large a refutation of a given
   * family has to be — a question rather than a category error. It is still not a lower bound, and
   * nothing here defines width or size.
   */
  val Refutes: String = "RES_REFUTES"

  /** Over the standard chain. */
  lazy val standard: Resolving =
    construct(Chain.standard).fold(
      error => throw new IllegalStateException(s"the standard resolution facts do not build: $error"),
      identity
    )

  /**
   * Over a chain of one's own.
   *
   * Beside the chain rather than in it, like `Bounded`, `Primes` and `Deduction`: it declares no
   * type, no constant and no definition, so it cannot be the widest signature and adding it moves
   * nothing. `ResolvingSpec` asserts that the theory it hands on is the one it was given.
   */
  def construct(chain: Chain): Either[LogicError, Resolving] = {
    val signature = chain.widest
    val logic = signature.logic
    val rules = logic.rules
    val classical = chain.classical

    for {
      step <- stepSoundness(signature, logic, rules, classical)
      resolvent <- ofResolvent(signature, logic, rules, step)
      empty <- emptyUnsatisfiable(signature, logic, rules, chain.peano)
      sound <- derivationSoundness(signature, logic, rules, chain.peano, step)
      refutes <- refutation(signature, logic, rules, sound, empty)
    } yield new Resolving(
      chain.peano,
      classical,
      signature.theory,
      signature.notation,
      logic,
      Map(
        StepSound -> step,
        StepSoundOfResolvent -> resolvent,
        EmptyUnsatisfiable -> empty,
        DerivationSound -> sound,
        Refutes -> refutes
      )
    )
  }

  /** The statement of [[StepSound]], written out so a reader compares text with the claim. */
  private val StepStatement: String =
    "!a:num->bool. !v1:num->num. !s1:num->bool. !v2:num->num. !s2:num->bool. " +
      "!v3:num->num. !s3:num->bool. !n1:num. !n2:num. !n3:num. !x:num. " +
      "(!i:num. NUM_LT i n1 ==> ~(v1 i = x /\\ s1 i = T) ==> " +
      "   (?m:num. NUM_LT m n3 /\\ v3 m = v1 i /\\ s3 m = s1 i)) ==> " +
      "(!i:num. NUM_LT i n2 ==> ~(v2 i = x /\\ s2 i = F) ==> " +
      "   (?m:num. NUM_LT m n3 /\\ v3 m = v2 i /\\ s3 m = s2 i)) ==> " +
      "(?i:num. NUM_LT i n1 /\\ (a (v1 i) = s1 i)) ==> " +
      "(?i:num. NUM_LT i n2 /\\ (a (v2 i) = s2 i)) ==> " +
      "(?i:num. NUM_LT i n3 /\\ (a (v3 i) = s3 i))"

  /** The two occurrence conditions [[StepSound]] does not need, as text. */
  private val OccursPositively: String = "?i:num. NUM_LT i n1 /\\ v1 i = x /\\ s1 i = T"
  private val OccursNegatively: String = "?i:num. NUM_LT i n2 /\\ v2 i = x /\\ s2 i = F"

  private def freeIn(theorem: Kernel.Thm): Set[FVar] =
    theorem.hypotheses.flatMap(Term.freeVariables).toSet ++ Term.freeVariables(theorem.conclusion)

  private def peel(logic: Logic, term: Term, taken: Vector[Term]): (Vector[Term], Term) =
    logic.destImp(term) match {
      case Some((antecedent, rest)) => peel(logic, rest, taken :+ antecedent)
      case None => (taken, term)
    }

  private def stepSoundness(
    signature: Signature,
    logic: Logic,
    rules: Rules,
    classical: Classical
  ): Either[LogicError, Kernel.Thm] =
    for {
      whole <- signature.proposition(StepStatement)
      stripped <- Logic.stripForall(whole)
      (binders, body) = stripped
      (antecedents, conclusion) = peel(logic, body, Vector.empty)

      // By position and not by name: `Logic.stripForall` hands back variables it chose, so the
      // order the statement above was written in is the only thing either side can agree on.
      subject = binders(0)
      pivot = binders(10)
      atPivot <- LogicError.lift(Term.app(subject, pivot))
      predicate <- logic.destExistsPredicate(conclusion).toRight(NotOfForm("an existential", conclusion))

      carriesFirst <- LogicError.lift(Kernel.assume(antecedents(0)))
      carriesSecond <- LogicError.lift(Kernel.assume(antecedents(1)))
      satisfiesFirst <- LogicError.lift(Kernel.assume(antecedents(2)))
      satisfiesSecond <- LogicError.lift(Kernel.assume(antecedents(3)))

      // `a x` holds: the second parent's witness cannot be the pivot, which is negative there.
      holds <- LogicError.lift(Kernel.assume(atPivot))
      positive <- branch(
        logic,
        rules,
        subject,
        binders.toSet,
        predicate,
        satisfiesSecond,
        carriesSecond,
        equation => LogicError.lift(Kernel.eqMp(equation, holds))
      )

      // `a x` fails: the first parent's, by the mirror argument.
      denied <- logic.mkNot(atPivot)
      fails <- LogicError.lift(Kernel.assume(denied))
      negative <- branch(
        logic,
        rules,
        subject,
        binders.toSet,
        predicate,
        satisfiesFirst,
        carriesFirst,
        equation => rules.eqTruthElim(equation).flatMap(rules.notElim(fails, _))
      )

      split <- classical.cases(atPivot, positive, negative)
      discharged <- antecedents.reverse.foldLeft(Right(split): Either[LogicError, Kernel.Thm])(
        (carried, antecedent) => carried.flatMap(rules.disch(antecedent, _))
      )
      closed <- rules.genAll(discharged, binders.toList)
    } yield closed

  /**
   * One half of the case split, over the parent whose satisfying literal is not the pivot.
   *
   * `contradict` receives `|- a x = <the polarity this parent holds the pivot at>` and makes falsity
   * of it against what the branch assumed. Passing the step rather than an equation is why neither
   * branch needs `~(T = F)`: one contradicts by `Kernel.eqMp` and the other by `Rules.notElim`, and
   * each is two rules rather than an orientation argument.
   */
  private def branch(
    logic: Logic,
    rules: Rules,
    subject: Term,
    binders: Set[FVar],
    goalPredicate: Term,
    satisfied: Kernel.Thm,
    carries: Kernel.Thm,
    contradict: Kernel.Thm => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val avoid = freeIn(satisfied) ++ freeIn(carries) ++ binders

    for {
      parentPredicate <- logic
        .destExistsPredicate(satisfied.conclusion)
        .toRight(NotOfForm("an existential", satisfied.conclusion))
      domain <- Type
        .destFun(Term.typeOf(parentPredicate))
        .map(_._1)
        .toRight(NotOfForm("a predicate", parentPredicate))
      index = Conv.freshVariable("i", domain, avoid)

      atIndex <- LogicError.lift(Term.app(parentPredicate, index)).flatMap(Conv.betaRoot)
      parentBody <- Term.destEq(atIndex.conclusion).map(_._2).toRight(NotOfForm("an equation", atIndex.conclusion))
      assumed <- LogicError.lift(Kernel.assume(parentBody))
      below <- rules.conjElim1(assumed)
      holds <- rules.conjElim2(assumed)

      carriesAtIndex <- rules.spec(index, carries)
      afterBound <- logic.destImp(carriesAtIndex.conclusion).map(_._2).toRight(NotOfForm("an implication", carriesAtIndex.conclusion))
      denialNeeded <- logic.destImp(afterBound).map(_._1).toRight(NotOfForm("an implication", afterBound))
      pivotClaim <- logic.destNot(denialNeeded).toRight(NotOfForm("a negation", denialNeeded))

      supposed <- LogicError.lift(Kernel.assume(pivotClaim))
      sameVariable <- rules.conjElim1(supposed)
      samePolarity <- rules.conjElim2(supposed)

      // `a (v i) = a x`, so `a x = s i` and then `a x = <polarity>`, which the branch contradicts.
      congruence <- Conv.apTerm(subject, sameVariable)
      pivotIsLiteral <- Conv.sym(congruence).flatMap(Conv.trans(_, holds))
      pivotIsPolarity <- Conv.trans(pivotIsLiteral, samePolarity)
      absurd <- contradict(pivotIsPolarity)
      notPivot <- rules.notIntro(pivotClaim, absurd)

      carried <- rules.mp(carriesAtIndex, below).flatMap(rules.mp(_, notPivot))

      target = Conv.freshVariable("m", domain, avoid ++ freeIn(carried) + index)
      innerPredicate <- logic
        .destExistsPredicate(carried.conclusion)
        .toRight(NotOfForm("an existential", carried.conclusion))
      atTarget <- LogicError.lift(Term.app(innerPredicate, target)).flatMap(Conv.betaRoot)
      innerBody <- Term.destEq(atTarget.conclusion).map(_._2).toRight(NotOfForm("an equation", atTarget.conclusion))

      innerAssumed <- LogicError.lift(Kernel.assume(innerBody))
      targetBelow <- rules.conjElim1(innerAssumed)
      rest <- rules.conjElim2(innerAssumed)
      sameTargetVariable <- rules.conjElim1(rest)
      sameTargetPolarity <- rules.conjElim2(rest)

      targetCongruence <- Conv.apTerm(subject, sameTargetVariable)
      targetIsLiteral <- Conv.trans(targetCongruence, holds)
      targetHolds <- Conv.sym(sameTargetPolarity).flatMap(Conv.trans(targetIsLiteral, _))

      witness <- rules.conjIntro(targetBelow, targetHolds)
      introduced <- rules.existsIntro(goalPredicate, target, witness)
      overInner <- rules.existsElim(carried, target, introduced)
      result <- rules.existsElim(satisfied, index, overInner)
    } yield result
  }

  /**
   * The statement of [[StepSoundOfResolvent]]: resolution's four conditions, in the textbook order.
   *
   * Written out in full rather than assembled from [[StepStatement]], so that a reader checking this
   * against the definition of resolution reads one text and not a composition of two.
   */
  private val ResolventStatement: String =
    "!a:num->bool. !v1:num->num. !s1:num->bool. !v2:num->num. !s2:num->bool. " +
      "!v3:num->num. !s3:num->bool. !n1:num. !n2:num. !n3:num. !x:num. " +
      "(?i:num. NUM_LT i n1 /\\ v1 i = x /\\ s1 i = T) ==> " +
      "(?i:num. NUM_LT i n2 /\\ v2 i = x /\\ s2 i = F) ==> " +
      "(!i:num. NUM_LT i n1 ==> ~(v1 i = x /\\ s1 i = T) ==> " +
      "   (?m:num. NUM_LT m n3 /\\ v3 m = v1 i /\\ s3 m = s1 i)) ==> " +
      "(!i:num. NUM_LT i n2 ==> ~(v2 i = x /\\ s2 i = F) ==> " +
      "   (?m:num. NUM_LT m n3 /\\ v3 m = v2 i /\\ s3 m = s2 i)) ==> " +
      "(?i:num. NUM_LT i n1 /\\ (a (v1 i) = s1 i)) ==> " +
      "(?i:num. NUM_LT i n2 /\\ (a (v2 i) = s2 i)) ==> " +
      "(?i:num. NUM_LT i n3 /\\ (a (v3 i) = s3 i))"

  /**
   * [[StepSoundOfResolvent]], by specialising [[StepSound]] at this statement's own binders.
   *
   * Specialised at the corollary's binders rather than the two statements being matched up, which
   * is the positional specialisation `CLAUDE.md` records being bitten by: here there are eleven
   * binders, seven of them sharing a type, and nothing in a name would have caught a swap.
   *
   * The two occurrence conditions are assumed and never used, which is the whole content of the
   * corollary and is asserted in `ResolvingSpec` rather than left to a reading of this comment.
   */
  private def ofResolvent(
    signature: Signature,
    logic: Logic,
    rules: Rules,
    step: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      whole <- signature.proposition(ResolventStatement)
      stripped <- Logic.stripForall(whole)
      (binders, body) = stripped
      (antecedents, _) = peel(logic, body, Vector.empty)

      assumed <- antecedents.foldLeft(Right(Vector.empty[Kernel.Thm]): Either[LogicError, Vector[Kernel.Thm]])(
        (carried, antecedent) => carried.flatMap(done => LogicError.lift(Kernel.assume(antecedent)).map(done :+ _))
      )
      here <- rules.specAll(step, binders.toList.map(variable => variable: Term))

      // The four the step actually needs, in its order: the two carrying conditions and then the
      // two parents being satisfied. The two occurrence conditions, `assumed(0)` and `assumed(1)`,
      // are never passed to anything.
      afterCarrying <- rules.mp(here, assumed(2)).flatMap(rules.mp(_, assumed(3)))
      satisfied <- rules.mp(afterCarrying, assumed(4)).flatMap(rules.mp(_, assumed(5)))

      discharged <- antecedents.reverse.foldLeft(Right(satisfied): Either[LogicError, Kernel.Thm])(
        (carried, antecedent) => carried.flatMap(rules.disch(antecedent, _))
      )
      closed <- rules.genAll(discharged, binders.toList)
    } yield closed

  /** The justification a step carries: it is an input, or two earlier steps resolve to it. */
  private val Justified: String =
    "NUM_LT j inputs \\/ (?p:num. ?q:num. ?x:num. NUM_LT p j /\\ NUM_LT q j /\\ " +
      "(!i:num. NUM_LT i (k p) ==> ~(v p i = x /\\ s p i = T) ==> " +
      "   (?n:num. NUM_LT n (k j) /\\ v j n = v p i /\\ s j n = s p i)) /\\ " +
      "(!i:num. NUM_LT i (k q) ==> ~(v q i = x /\\ s q i = F) ==> " +
      "   (?n:num. NUM_LT n (k j) /\\ v j n = v q i /\\ s j n = s q i)))"

  /** Clause `j` of the derivation, satisfied by the assignment. */
  private val SatisfiedAt: String = "?i:num. NUM_LT i (k j) /\\ (a (v j i) = s j i)"

  private val SoundStatement: String =
    "!a:num->bool. !k:num->num. !v:num->num->num. !s:num->num->bool. !inputs:num. !m:num. " +
      s"(!j:num. NUM_LT j inputs ==> ($SatisfiedAt)) ==> " +
      s"(!j:num. NUM_LT j m ==> ($Justified)) ==> " +
      s"(!j:num. NUM_LT j m ==> ($SatisfiedAt))"

  private val RefutesStatement: String =
    "!k:num->num. !v:num->num->num. !s:num->num->bool. !inputs:num. !m:num. " +
      s"(!j:num. NUM_LT j m ==> ($Justified)) ==> " +
      "(?j:num. NUM_LT j m /\\ k j = ZERO) ==> " +
      "~(?a:num->bool. !j:num. NUM_LT j inputs ==> " +
      "   (?i:num. NUM_LT i (k j) /\\ (a (v j i) = s j i)))"

  /** The body of a quantification at a chosen variable, with the redex contracted. */
  private def openAt(logic: Logic, quantified: Term, at: Term): Either[LogicError, Term] =
    logic
      .destForallPredicate(quantified)
      .orElse(logic.destExistsPredicate(quantified))
      .toRight(NotOfForm("a quantification", quantified))
      .flatMap(predicate => LogicError.lift(Term.app(predicate, at)).flatMap(Conv.betaRoot))
      .flatMap(contraction =>
        Term.destEq(contraction.conclusion).map(_._2).toRight(NotOfForm("an equation", contraction.conclusion))
      )

  private def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv.betaNormalise(theorem.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

  /**
   * [[DerivationSound]], by strong induction on the step index.
   *
   * The predicate inducted on is the conclusion's own, `\j. NUM_LT j m ==> <clause j is satisfied>`,
   * read off the statement rather than rebuilt beside it. Its step splits on the justification: an
   * input is the first antecedent at that index, and a resolvent needs both parents, which are below
   * `j` and so below `m` by `Peano.NUM_LT_TRANS`, and so satisfied by the induction hypothesis.
   *
   * The step lemma is specialised **positionally**, which this repository warns against, and the
   * warning is answered rather than ignored: the four `num` binders are alike, so a swap would be
   * invisible in the types. What catches one is the four `Rules.mp` calls below, each of which has
   * to match an antecedent against a theorem already in hand, and a swapped `n1` and `n2` fails the
   * first of them. The statement being specialised is also written in this file, twenty lines up.
   */
  private def derivationSoundness(
    signature: Signature,
    logic: Logic,
    rules: Rules,
    peano: Peano,
    step: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      whole <- signature.proposition(SoundStatement)
      stripped <- Logic.stripForall(whole)
      (binders, body) = stripped
      (antecedents, conclusion) = peel(logic, body, Vector.empty)

      subject = binders(0)
      lengths = binders(1)
      variables = binders(2)
      polarities = binders(3)
      bound = binders(5)

      inputsSatisfied <- LogicError.lift(Kernel.assume(antecedents(0)))
      everyStepJustified <- LogicError.lift(Kernel.assume(antecedents(1)))

      predicate <- logic.destForallPredicate(conclusion).toRight(NotOfForm("a universal", conclusion))
      strong <- peano.fact(Peano.StrongInduction)
      instance <- rules.spec(predicate, strong).flatMap(reduced)
      opened <- logic.destImp(instance.conclusion).toRight(NotOfForm("an implication", instance.conclusion))
      (stepGoal, _) = opened

      avoid = binders.toSet ++ freeIn(inputsSatisfied) ++ freeIn(everyStepJustified)
      index = Conv.freshVariable("n", Term.typeOf(bound), avoid)

      stepBody <- openAt(logic, stepGoal, index)
      split <- logic.destImp(stepBody).toRight(NotOfForm("an implication", stepBody))
      (hypothesisTerm, claimAtIndex) = split
      hypothesis <- LogicError.lift(Kernel.assume(hypothesisTerm))
      inner <- logic.destImp(claimAtIndex).toRight(NotOfForm("an implication", claimAtIndex))
      (belowTerm, satisfiedHere) = inner
      below <- LogicError.lift(Kernel.assume(belowTerm))

      justifiedHere <- rules.spec(index, everyStepJustified).flatMap(rules.mp(_, below))
      arms <- logic
        .destDisj(justifiedHere.conclusion)
        .toRight(NotOfForm("a disjunction", justifiedHere.conclusion))
      (isInputTerm, isResolventTerm) = arms

      isInput <- LogicError.lift(Kernel.assume(isInputTerm))
      fromInputs <- rules.spec(index, inputsSatisfied).flatMap(rules.mp(_, isInput))

      transitive <- peano.fact(Peano.StrictTransitive)

      left = Conv.freshVariable("p", Term.typeOf(bound), avoid + index)
      afterLeft <- openAt(logic, isResolventTerm, left)
      right = Conv.freshVariable("q", Term.typeOf(bound), avoid + index + left)
      afterRight <- openAt(logic, afterLeft, right)
      pivot = Conv.freshVariable("x", Term.typeOf(bound), avoid + index + left + right)
      afterPivot <- openAt(logic, afterRight, pivot)

      witnessed <- LogicError.lift(Kernel.assume(afterPivot))
      leftBelow <- rules.conjElim1(witnessed)
      afterFirst <- rules.conjElim2(witnessed)
      rightBelow <- rules.conjElim1(afterFirst)
      afterSecond <- rules.conjElim2(afterFirst)
      carriesLeft <- rules.conjElim1(afterSecond)
      carriesRight <- rules.conjElim2(afterSecond)

      satisfiedLeft <- parentSatisfied(rules, transitive, hypothesis, below, left, leftBelow, index, bound)
      satisfiedRight <- parentSatisfied(rules, transitive, hypothesis, below, right, rightBelow, index, bound)

      here <- rules.specAll(
        step,
        List(
          subject,
          applied(variables, left), applied(polarities, left),
          applied(variables, right), applied(polarities, right),
          applied(variables, index), applied(polarities, index),
          applied(lengths, left), applied(lengths, right), applied(lengths, index),
          pivot
        )
      )
      fromResolution <- rules
        .mp(here, carriesLeft)
        .flatMap(rules.mp(_, carriesRight))
        .flatMap(rules.mp(_, satisfiedLeft))
        .flatMap(rules.mp(_, satisfiedRight))

      overPivot <- LogicError
        .lift(Kernel.assume(afterRight))
        .flatMap(rules.existsElim(_, pivot, fromResolution))
      overRight <- LogicError
        .lift(Kernel.assume(afterLeft))
        .flatMap(rules.existsElim(_, right, overPivot))
      overLeft <- LogicError
        .lift(Kernel.assume(isResolventTerm))
        .flatMap(rules.existsElim(_, left, overRight))

      bothArms <- rules.disjElim(justifiedHere, fromInputs, overLeft)
      _ <-
        if (bothArms.conclusion == satisfiedHere) Right(())
        else Left(NotOfForm("the induction step's own claim", bothArms.conclusion))

      stepProved <- rules
        .disch(belowTerm, bothArms)
        .flatMap(rules.disch(hypothesisTerm, _))
        .flatMap(rules.gen(index, _))
      inducted <- rules.mp(instance, stepProved)

      discharged <- rules.disch(antecedents(1), inducted).flatMap(rules.disch(antecedents(0), _))
      closed <- rules.genAll(discharged, binders.toList)
    } yield closed

  /** A parent below the current step is below the bound, so the induction hypothesis reaches it. */
  private def parentSatisfied(
    rules: Rules,
    transitive: Kernel.Thm,
    hypothesis: Kernel.Thm,
    below: Kernel.Thm,
    parent: FVar,
    parentBelow: Kernel.Thm,
    index: FVar,
    bound: FVar
  ): Either[LogicError, Kernel.Thm] =
    for {
      chained <- rules.conjIntro(parentBelow, below)
      atThree <- rules.specAll(transitive, List(parent: Term, index: Term, bound: Term))
      parentBelowBound <- rules.mp(atThree, chained)
      atParent <- rules.spec(parent, hypothesis)
      satisfied <- rules.mp(atParent, parentBelow).flatMap(rules.mp(_, parentBelowBound))
    } yield satisfied

  private def applied(fn: FVar, argument: FVar): Term =
    Term.app(fn, argument).fold(error => throw new IllegalStateException(error.toString), identity)

  /**
   * [[Refutes]], which is three lines over the two theorems it rests on.
   *
   * Soundness gives every clause of the derivation satisfied by an assignment that satisfies the
   * inputs; the step that is empty is one of those clauses; and [[EmptyUnsatisfiable]] says nothing
   * satisfies that one. The assignment is introduced by opening the existential inside the negation,
   * which is what lets the conclusion speak about **every** assignment rather than one.
   */
  private def refutation(
    signature: Signature,
    logic: Logic,
    rules: Rules,
    sound: Kernel.Thm,
    empty: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      whole <- signature.proposition(RefutesStatement)
      stripped <- Logic.stripForall(whole)
      (binders, body) = stripped
      (antecedents, conclusion) = peel(logic, body, Vector.empty)

      lengths = binders(0)
      variables = binders(1)
      polarities = binders(2)
      inputs = binders(3)
      bound = binders(4)

      everyStepJustified <- LogicError.lift(Kernel.assume(antecedents(0)))
      reachesEmpty <- LogicError.lift(Kernel.assume(antecedents(1)))
      satisfiable <- logic.destNot(conclusion).toRight(NotOfForm("a negation", conclusion))
      supposed <- LogicError.lift(Kernel.assume(satisfiable))

      subject = Conv.freshVariable("a", Type.fun(Term.typeOf(bound), Type.Bool), binders.toSet)
      inputsBody <- openAt(logic, satisfiable, subject)
      inputsSatisfied <- LogicError.lift(Kernel.assume(inputsBody))

      at = Conv.freshVariable("j", Term.typeOf(bound), binders.toSet + subject)
      emptyBody <- openAt(logic, antecedents(1), at)
      emptyHere <- LogicError.lift(Kernel.assume(emptyBody))
      atBelow <- rules.conjElim1(emptyHere)
      atIsEmpty <- rules.conjElim2(emptyHere)

      here <- rules.specAll(sound, List(subject, lengths, variables, polarities, inputs, bound))
      everySatisfied <- rules.mp(here, inputsSatisfied).flatMap(rules.mp(_, everyStepJustified))
      satisfiedThere <- rules.spec(at, everySatisfied).flatMap(rules.mp(_, atBelow))

      nothingSatisfies <- rules
        .specAll(empty, List(subject, applied(variables, at), applied(polarities, at), applied(lengths, at)))
        .flatMap(rules.mp(_, atIsEmpty))
      absurd <- rules.notElim(nothingSatisfies, satisfiedThere)

      overIndex <- rules.existsElim(reachesEmpty, at, absurd)
      overSubject <- rules.existsElim(supposed, subject, overIndex)
      negated <- rules.notIntro(satisfiable, overSubject)
      discharged <- rules.disch(antecedents(1), negated).flatMap(rules.disch(antecedents(0), _))
      closed <- rules.genAll(discharged, binders.toList)
    } yield closed

  /**
   * [[EmptyUnsatisfiable]], which is what makes a derivation ending on the empty clause a refutation.
   *
   * Assume a witness below a length that is zero, rewrite the length, and meet
   * `Peano.NUM_NOT_LT_ZERO`. No case split anywhere, so no axiom.
   */
  private def emptyUnsatisfiable(
    signature: Signature,
    logic: Logic,
    rules: Rules,
    peano: Peano
  ): Either[LogicError, Kernel.Thm] =
    for {
      whole <- signature.proposition(
        "!a:num->bool. !v:num->num. !s:num->bool. !n:num. " +
          "n = ZERO ==> ~(?i:num. NUM_LT i n /\\ (a (v i) = s i))"
      )
      stripped <- Logic.stripForall(whole)
      (binders, body) = stripped
      (antecedents, conclusion) = peel(logic, body, Vector.empty)

      isZero <- LogicError.lift(Kernel.assume(antecedents(0)))
      existential <- logic.destNot(conclusion).toRight(NotOfForm("a negation", conclusion))
      supposed <- LogicError.lift(Kernel.assume(existential))

      predicate <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
      domain <- Type.destFun(Term.typeOf(predicate)).map(_._1).toRight(NotOfForm("a predicate", predicate))
      index = Conv.freshVariable("i", domain, binders.toSet ++ freeIn(supposed))

      atIndex <- LogicError.lift(Term.app(predicate, index)).flatMap(Conv.betaRoot)
      witnessBody <- Term.destEq(atIndex.conclusion).map(_._2).toRight(NotOfForm("an equation", atIndex.conclusion))
      assumed <- LogicError.lift(Kernel.assume(witnessBody))
      below <- rules.conjElim1(assumed)

      // `NUM_LT i n` becomes `NUM_LT i ZERO` across the hypothesis, rather than by rewriting the
      // whole statement: one congruence and one `eqMp`.
      partial <- below.conclusion match {
        case App(fn, _) => Right(fn)
        case other => Left(NotOfForm("an application", other))
      }
      moved <- Conv.apTerm(partial, isZero)
      belowZero <- LogicError.lift(Kernel.eqMp(moved, below))

      // `|- !i. ~(NUM_LT i ZERO)` at this witness. Specialised at the index rather than matched
      // against the goal: there is one binder, so there is nothing a match could get wrong and
      // nothing a positional call can either.
      never <- peano.fact(Peano.NotBelowZero)
      atThisIndex <- rules.spec(index, never)
      absurd <- rules.notElim(atThisIndex, belowZero)

      overWitness <- rules.existsElim(supposed, index, absurd)
      negated <- rules.notIntro(existential, overWitness)
      discharged <- rules.disch(antecedents(0), negated)
      closed <- rules.genAll(discharged, binders.toList)
    } yield closed
}
