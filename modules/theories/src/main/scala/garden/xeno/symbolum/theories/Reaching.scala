package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Derivations of a relation, with their length, and the lemma that bounds it from below.
 *
 * `Inductive` gives the least set closed under an operator. This is the first thing built on it,
 * and the one the rewriting work asked for: what a relation reaches, counting the steps that
 * belong to a distinguished sub-relation on the way.
 *
 * == The count is inside the set, which is why there is a pair ==
 *
 * `INDUCTIVE` is unary, and a derivation is not: it goes from somewhere to somewhere in some number
 * of steps. Fixing the start turns it into a set, and the number is carried in the element:
 *
 * {{{
 *   REACH R A x q     q : prod('a, num)
 * }}}
 *
 * says there is an `R`-derivation from `x` to `FST q` in which exactly `SND q` steps were `A`-steps.
 * The two clauses are the whole content: the counter starts at `ZERO`, goes up by one across an
 * `A`-step, and stays put across any other `R`-step.
 *
 * Taking `A` to be `R` itself makes the counter the **length** of the derivation, so the
 * reflexive-transitive closure and the length are not two constructions: `?k. REACH R R x (PAIR y k)`
 * is the closure and the `k` is the length. Nothing separate is defined for them.
 *
 * **No recursion on `num` anywhere here**, which is the return on defining the closure rather than
 * iterating it. `Recursion` and `Descent` are untouched: the induction over a derivation IS
 * [[Inductive.Induction]] at this operator, and [[Induction]] below is that specialised once so no
 * consumer has to unfold the operator by hand.
 *
 * == The potential-function lemma, and the hypothesis that is easy to write backwards ==
 *
 * [[Potential]] is the reusable half of the argument this development was asked for. Given a
 * measure `Phi` into `num`:
 *
 *  - every `A`-step drops it by exactly one, written `Phi u = SUC (Phi v)` so that no subtraction
 *    appears;
 *  - **no other step lowers it**, written `Phi u <= Phi v`;
 *
 * then any derivation from `x` to `FST q` has `Phi x <= SND q + Phi (FST q)`: at least `Phi x`
 * minus whatever is left over `A`-steps were spent.
 *
 * **The second hypothesis is "does not lower" and not "does not raise", and the difference is the
 * lemma.** The card that asked for this file wrote the second one, and the consumer it was written
 * for cannot meet it: in the rewriting system that motivated the work, two of the eleven rules
 * **raise** the measure. Under "does not raise" the lemma is true, unusable, and points the wrong
 * way — with `k` the `A`-steps and `d` the total change across the others,
 * `k = Phi x - Phi y + d`, so `d >= 0` gives the bound below and `d <= 0` gives the bound above.
 * `ReachingSpec` derives the counterexample that says the hypothesis cannot be dropped, which is
 * the only form a negative control can take for a lemma: a theorem does not refuse.
 *
 * The conclusion is written additively, `Phi x <= SND q + Phi (FST q)`, for the reason
 * `Provability` gives about a proof carrying the index of its last step: subtraction on `num` is
 * truncated, so the subtractive form would buy a guard and an asymmetry for nothing. A consumer
 * whose derivation ends where the measure is zero instantiates and reads `Phi x <= SND q`.
 *
 * == What is not here ==
 *
 * **The rewriting relation on words is not here and no longer missing**: it landed as
 * `Forward.WORD_STEP` on 2026-09-16, the same day this file did, once `Concatenation` gave `word`
 * the factor relation a step is stated with. This section said it did not exist for the day after
 * that, which is the shape of stale sentence this repository loses most: an absence a reader
 * believes rather than checks.
 *
 * **What has not happened is the instantiation**, which is the sentence worth keeping. `Forward`
 * builds its closure out of [[Inductive]] directly and never mentions `REACH`, so nothing yet puts
 * this file at `R := WORD_STEP R`, `A` the rules being counted and `Phi` the measure, and until
 * something does, the potential-function lemma has no consumer. `Collatz`'s own docstring names
 * that instantiation as what its argument is for.
 *
 * == Where the monotonicity comes from, which is no longer here ==
 *
 * The three introduction rules below each spend [[Inductive.Introduction]], so each needs this
 * operator to be monotone. That was proved here by hand, in 56 lines, and it is now one call to
 * [[Monotone.prove]], which reads the shape every rule set has — a disjunction of clauses with the
 * set argument only positive — instead of being written out again per operator. This file was the
 * second of the two hand proofs and the measurement that argued for the procedure: its operator is
 * substantially larger than `InductiveSpec`'s and its proof was four lines longer, because
 * everything to the right of the one positive occurrence is carried across without being looked at.
 */
final class Reaching private (
  val inductive: Inductive,
  val peano: Peano,
  val product: Product,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = inductive.classical.logic
    .over(theory)
    .fold(
      error => throw new IllegalStateException(s"the logic does not extend: ${error.message}"),
      identity
    )

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Reaching {

  /** `REACH R A x q` — `FST q` is reachable from `x`, spending `SND q` steps of `A`. */
  val Name: String = "REACH"

  /** `|- !R A x. REACH R A x (PAIR x ZERO)` — the empty derivation, at no cost. */
  val Start: String = "REACH_START"

  /** `|- !R A x p y. REACH R A x p /\ R (FST p) y /\ A (FST p) y ==> REACH R A x (PAIR y (SUC (SND p)))` */
  val CountedStep: String = "REACH_COUNTED"

  /** `|- !R A x p y. REACH R A x p /\ R (FST p) y /\ ~(A (FST p) y) ==> REACH R A x (PAIR y (SND p))` */
  val PlainStep: String = "REACH_PLAIN"

  /**
   * The induction principle over a derivation, with the operator already unfolded.
   *
   * `[[Inductive.Induction]]` specialised at this operator and then put into the two-clause shape a
   * consumer writes: a base case at `PAIR x ZERO` and one step covering both kinds of move. Doing
   * it once here is the difference between a consumer reasoning about derivations and a consumer
   * unfolding a definition.
   */
  val Induction: String = "REACH_INDUCT"

  /** The potential-function lemma. See the class docstring for which way its second hypothesis goes. */
  val Potential: String = "REACH_POTENTIAL"

  /** `'a`, the type the relation relates. Nothing here is about any particular one. */
  val State: Type = TyVar(Classical.TypeVariable)

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)

  /** `prod('a, num)`: where a derivation got to, and what it spent getting there. */
  val Steps: Type = TyApp(Product.TypeName, List(State, Numbers))

  /** `'a -> 'a -> bool`. */
  val Relations: Type = Type.fun(State, Type.fun(State, Type.Bool))

  /**
   * The clause the whole file is about, as text, so that a reader checks it once.
   *
   * `q = PAIR x ZERO` is the empty derivation. The other disjunct extends a derivation that reached
   * `p`: the move has to be an `R`-move, and then either it is an `A`-move and the counter goes up
   * by one, or it is not and the counter stays. Nothing else is said, and in particular nothing
   * says `A` is inside `R` — a caller whose `A` is not simply never gets to use the first branch.
   */
  private val ClauseText: String =
    "q = PAIR x ZERO \\/ (?p:prod('a,num). S p /\\ R (FST p) (FST q) /\\ " +
      "((A (FST p) (FST q) /\\ SND q = SUC (SND p)) \\/ " +
      "(~(A (FST p) (FST q)) /\\ SND q = SND p)))"

  private val Body: String =
    "\\R:'a->'a->bool. \\A:'a->'a->bool. \\x:'a. " +
      "INDUCTIVE (\\S:prod('a,num)->bool. \\q:prod('a,num). " + ClauseText + ")"

  /** Everything this development proves, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    Start -> "!R:'a->'a->bool. !A:'a->'a->bool. !x:'a. REACH R A x (PAIR x ZERO)",
    CountedStep ->
      ("!R:'a->'a->bool. !A:'a->'a->bool. !x:'a. !p:prod('a,num). !y:'a. " +
        "REACH R A x p /\\ R (FST p) y /\\ A (FST p) y ==> " +
        "REACH R A x (PAIR y (SUC (SND p)))"),
    PlainStep ->
      ("!R:'a->'a->bool. !A:'a->'a->bool. !x:'a. !p:prod('a,num). !y:'a. " +
        "REACH R A x p /\\ R (FST p) y /\\ ~(A (FST p) y) ==> " +
        "REACH R A x (PAIR y (SND p))"),
    Induction ->
      ("!R:'a->'a->bool. !A:'a->'a->bool. !x:'a. !S:prod('a,num)->bool. " +
        "S (PAIR x ZERO) /\\ " +
        "(!p:prod('a,num). !q:prod('a,num). S p /\\ R (FST p) (FST q) /\\ " +
        "((A (FST p) (FST q) /\\ SND q = SUC (SND p)) \\/ " +
        "(~(A (FST p) (FST q)) /\\ SND q = SND p)) ==> S q) " +
        "==> (!q:prod('a,num). REACH R A x q ==> S q)"),
    Potential ->
      ("!R:'a->'a->bool. !A:'a->'a->bool. !Phi:'a->num. !x:'a. " +
        "(!u:'a. !v:'a. A u v ==> Phi u = SUC (Phi v)) /\\ " +
        "(!u:'a. !v:'a. R u v /\\ ~(A u v) ==> Phi u <= Phi v) " +
        "==> (!q:prod('a,num). REACH R A x q ==> Phi x <= SND q + Phi (FST q))")
  )

  /**
   * The standard development, a lookup rather than a second construction.
   *
   * `Rotation.standard`'s reason, unchanged: nothing is built on top of this, so a second one would
   * have no caller and would put a second `REACH` of a different origin into the world.
   */
  lazy val standard: Reaching = Chain.standard.reaching

  /**
   * The development, over the chain's last link.
   *
   * It needs three things and takes them: `Inductive` for the closure, `Product` for the pair the
   * count rides in, and `Peano` for the arithmetic [[Potential]] is stated in. What it **extends**
   * is `base`, which is the last extension and not any of those, for the reason
   * `Rotation.construct`'s comment gives.
   */
  def construct(
    inductive: Inductive,
    peano: Peano,
    product: Product,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Reaching] =
    for {
      body <- Parser.term(base, notation, Body)
      defined <- LogicError.lift(Kernel.defineConstant(base, Name, body))
      (theory, definition) = defined

      logic <- inductive.classical.logic.over(theory)

      // `|- REACH R A x = INDUCTIVE op`, built once. Everything below is derived in the
      // `INDUCTIVE op` vocabulary and carried across this equation at the end, because the set
      // occurs INSIDE the clause as well as outside it and a pointwise conversion would miss the
      // inner one.
      unfolding <- Conv.unfold(definition, List(Relation, Counted, Origin))
      operator <- operatorOf(unfolding)

      inductiveInduct <- inductive.fact(Inductive.Induction)
      inductiveIntro <- inductive.fact(Inductive.Introduction)

      monotonicity <- Monotone.prove(logic, inductive, operator)
      induction <- inductionPrinciple(logic, inductiveInduct, operator, unfolding)
      steps <- introductionRules(
        logic, theory, notation, product, inductiveIntro, monotonicity, operator, unfolding)
      (start, counted, plain) = steps
      potential <- potentialLemma(logic, theory, notation, induction, peano, product)
    } yield new Reaching(
      inductive,
      peano,
      product,
      theory,
      notation,
      Map(Name -> definition),
      Map(
        Start -> start,
        CountedStep -> counted,
        PlainStep -> plain,
        Induction -> induction,
        Potential -> potential
      )
    )

  /* ------------------------------------------------------------------ shared pieces */

  private def statement(theory: Theory, notation: Notation, name: String): Either[LogicError, Term] =
    Statements
      .collectFirst { case (label, text) if label == name => text }
      .toRight(MissingDefinition(name))
      .flatMap(text => Parser.proposition(theory, notation, text))

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  /** `|- t` becomes `|- t'`, `t'` the beta normal form. */
  private def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv.betaNormalise(theorem.conclusion).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, theorem)))

  /** A proof of the beta normal form of `target` becomes a proof of `target`. */
  private def shaped(target: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv
      .betaNormalise(target)
      .flatMap(Conv.sym)
      .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

  /**
   * The operator this development's closure is taken of, at the caller's `R`, `A` and `x`.
   *
   * Obtained by unfolding the definition rather than by parsing it a second time: a second parse is
   * a second term that has to be kept in step with the first, which is the defect `DOC-02` names
   * about counts and which applies to a term just as well.
   */
  /* ------------------------------------------------------- the free variables of every proof */

  private val Relation: FVar = Term.variable("R", Relations)
  private val Counted: FVar = Term.variable("A", Relations)
  private val Origin: FVar = Term.variable("x", State)
  private val Measure: FVar = Term.variable("Phi", Type.fun(State, Numbers))
  private val Carrier: FVar = Term.variable("S", Type.fun(Steps, Type.Bool))
  private val Before: FVar = Term.variable("p", Steps)
  private val After: FVar = Term.variable("q", Steps)
  private val Landing: FVar = Term.variable("y", State)

  private def ruleOf(logic: Logic, theorem: Kernel.Thm): Either[LogicError, Rewrite.Rule] =
    Rewrite.Rule.of(logic, theorem)

  /**
   * A proof of what `rules` normalise `target` to becomes a proof of `target` itself.
   *
   * The counterpart of `Rewrite.inTheorem`, which goes the other way. Used everywhere a clause has
   * to be handed back to the machinery in the shape the machinery produced it, after having been
   * proved in the shape a person can read: `FST (PAIR y k)` is what the introduction rule asks for
   * and `y` is what the caller has.
   */
  private def viaRules(
    rewrites: Vector[Rewrite.Rule],
    target: Term,
    proof: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    Rewrite
      .rewrite(rewrites, target)
      .flatMap(Conv.sym)
      .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, proof)))

  /** What `rules` normalise `target` to, as a term, so a proof can be aimed at it. */
  private def normalOf(rewrites: Vector[Rewrite.Rule], target: Term): Either[LogicError, Term] =
    Rewrite.rewrite(rewrites, target).flatMap(rightOf)

  private def conjunctsOf(term: Term, logic: Logic): Either[LogicError, (Term, Term)] =
    logic.destConj(term).toRight(NotOfForm("a conjunction", term))

  private def disjunctsOf(term: Term, logic: Logic): Either[LogicError, (Term, Term)] =
    logic.destDisj(term).toRight(NotOfForm("a disjunction", term))

  private def impliesOf(term: Term, logic: Logic): Either[LogicError, (Term, Term)] =
    logic.destImp(term).toRight(NotOfForm("an implication", term))

  private def existsBody(term: Term, logic: Logic): Either[LogicError, Term] =
    logic.destExistsPredicate(term).toRight(NotOfForm("an existential", term))

  /**
   * [[Induction]]: [[Inductive.Induction]] at this operator, put into the shape a consumer writes.
   *
   * The general principle asks for one hypothesis, that the carrier is closed under the operator,
   * and the operator here is a disjunction of two clauses. So what a consumer would otherwise have
   * to do is unfold the definition and split the disjunction by hand every time it reasons about a
   * derivation. Doing it once is the whole of this function: the base case and the step case go in
   * as a conjunction and the disjunction is discharged here.
   *
   * The step is stated over `p` and `q` both universally quantified rather than over `q` alone,
   * because the clause relates two steps and a consumer instantiating it knows both.
   */
  private def inductionPrinciple(
    logic: Logic,
    inductiveInduct: Kernel.Thm,
    operator: Term,
    unfolding: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      atSteps <- Right(Kernel.instType(Map(Classical.TypeVariable -> Steps), inductiveInduct))
      instance <- rules.specAll(atSteps, List(operator, Carrier))
      parts <- impliesOf(instance.conclusion, logic)
      (rawPremise, _) = parts

      normalising <- Conv.betaNormalise(rawPremise)
      normal <- rightOf(normalising)
      stripped <- Logic.stripForall(normal)
      point <- stripped._1.lift(0).toRight(NotOfForm("a claim about every step", normal))
      clause <- impliesOf(stripped._2, logic)
      (antecedent, consequent) = clause
      sides <- disjunctsOf(antecedent, logic)
      (isStart, hasPrevious) = sides

      // The two hypotheses a consumer supplies, built from the clause rather than parsed a second
      // time: a second parse is a second term to keep in step with the first.
      startPoint <- Term.destEq(isStart).map(_._2).toRight(NotOfForm("an equation", isStart))
      baseHypothesis <- LogicError.lift(Term.app(Carrier, startPoint))

      predicate <- existsBody(hasPrevious, logic)
      witness = Conv.freshVariable("p", Steps, Term.freeVariables(stripped._2))
      applied <- LogicError.lift(Term.app(predicate, witness))
      contraction <- Conv.betaRoot(applied)
      instanceAtWitness <- rightOf(contraction)
      stepBody <- logic.mkImp(instanceAtWitness, consequent)
      stepInner <- logic.mkForall(point, stepBody)
      stepHypothesis <- logic.mkForall(witness, stepInner)

      hypothesis <- logic.mkConj(baseHypothesis, stepHypothesis)
      assumed <- LogicError.lift(Kernel.assume(hypothesis))
      assumedBase <- rules.conjElim1(assumed)
      assumedStep <- rules.conjElim2(assumed)

      // The base disjunct says the step IS the start, so the carrier at it is the carrier at the
      // start, which is the hypothesis.
      assumedStart <- LogicError.lift(Kernel.assume(isStart))
      carried <- Conv.apTerm(Carrier, assumedStart)
      leftCase <- Conv.sym(carried).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumedBase)))

      openedWitness <- LogicError.lift(Kernel.assume(instanceAtWitness))
      applied2 <- rules.specAll(assumedStep, List(witness, point)).flatMap(rules.mp(_, openedWitness))
      assumedPrevious <- LogicError.lift(Kernel.assume(hasPrevious))
      rightCase <- rules.existsElim(assumedPrevious, witness, applied2)

      assumedAntecedent <- LogicError.lift(Kernel.assume(antecedent))
      split <- rules.disjElim(assumedAntecedent, leftCase, rightCase)
      premiseProof <- rules.disch(antecedent, split).flatMap(rules.gen(point, _))
      shapedPremise <- shaped(rawPremise, premiseProof)
      everywhere <- rules.mp(instance, shapedPremise)

      // And back into this development's own vocabulary, pointwise: the conclusion mentions the
      // closure only at the top, so one application of the defining equation does it.
      specialised <- rules.spec(point, everywhere)
      reachAt <- Conv.apThm(unfolding, point)
      reachTerm <- leftOf(reachAt)
      assumedReach <- LogicError.lift(Kernel.assume(reachTerm))
      converted <- LogicError.lift(Kernel.eqMp(reachAt, assumedReach))
      inside <- rules.mp(specialised, converted)

      result <- rules
        .disch(reachTerm, inside)
        .flatMap(rules.gen(point, _))
        .flatMap(rules.disch(hypothesis, _))
        .flatMap(rules.gen(Carrier, _))
        .flatMap(rules.gen(Origin, _))
        .flatMap(rules.gen(Counted, _))
        .flatMap(rules.gen(Relation, _))
    } yield result
  }

  /**
   * [[Start]], [[CountedStep]] and [[PlainStep]], which are the introduction rules of the clause.
   *
   * All three are [[Inductive.Introduction]] at this operator, specialised at the step being
   * reached, with the clause's disjunct supplied. The work in each is the same and is arithmetic
   * rather than logic: the clause is stated about `FST q` and `SND q`, and the caller's step is
   * written `PAIR y k`, so `FST (PAIR y k)` has to become `y` before the caller's hypothesis fits.
   * That is what the three rewrite rules are for, and the same three carry `INDUCTIVE op` back to
   * `REACH R A x` on the way out.
   */
  private def introductionRules(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    product: Product,
    inductiveIntro: Kernel.Thm,
    monotonicity: Kernel.Thm,
    operator: Term,
    unfolding: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules

    for {
      atSteps <- Right(Kernel.instType(Map(Classical.TypeVariable -> Steps), inductiveIntro))
      clauses <- rules.spec(operator, atSteps).flatMap(rules.mp(_, monotonicity))

      firstOfPair <- product.fact(Product.FirstOfPair)
      secondOfPair <- product.fact(Product.SecondOfPair)
      reachRule <- Conv.sym(unfolding).flatMap(ruleOf(logic, _))
      firstRule <- ruleOf(logic, firstOfPair)
      secondRule <- ruleOf(logic, secondOfPair)
      readable = Vector(reachRule, firstRule, secondRule)

      start <- startRule(logic, theory, notation, rules, clauses, reachRule)
      counted <- stepRule(
        logic, theory, notation, clauses, readable, reachRule, counting = true)
      plain <- stepRule(
        logic, theory, notation, clauses, readable, reachRule, counting = false)
    } yield (start, counted, plain)
  }

  /** [[Start]]: the empty derivation, which is the base disjunct at `PAIR x ZERO`. */
  private def startRule(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    rules: Rules,
    clauses: Kernel.Thm,
    reachRule: Rewrite.Rule
  ): Either[LogicError, Kernel.Thm] =
    for {
      startPoint <- Parser.term(theory, notation, "PAIR (x:'a) ZERO", Steps)
      clause <- rules.spec(startPoint, clauses)
      parts <- impliesOf(clause.conclusion, logic)
      (premise, _) = parts
      normalising <- Conv.betaNormalise(premise)
      normal <- rightOf(normalising)
      sides <- disjunctsOf(normal, logic)
      (_, hasPrevious) = sides
      // The disjunct is `PAIR x ZERO = PAIR x ZERO`, so reflexivity is the whole proof.
      proof <- rules.disjIntro1(hasPrevious, Conv.refl(startPoint))
      shapedPremise <- shaped(premise, proof)
      reached <- rules.mp(clause, shapedPremise)
      converted <- Rewrite.inTheorem(Vector(reachRule), reached)
      result <- rules
        .gen(Origin, converted)
        .flatMap(rules.gen(Counted, _))
        .flatMap(rules.gen(Relation, _))
    } yield result

  /**
   * [[CountedStep]] and [[PlainStep]], which differ in one disjunct and in nothing else.
   *
   * Written once with a flag rather than twice, because the difference really is that small: the
   * step reached is `PAIR y (SUC (SND p))` against `PAIR y (SND p)`, and the branch supplied is the
   * left against the right. Everything between — reducing the projections, reassembling the
   * conjunction, introducing the existential — is identical, and two copies of it would be two
   * places for the same defect.
   */
  private def stepRule(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    clauses: Kernel.Thm,
    readable: Vector[Rewrite.Rule],
    reachRule: Rewrite.Rule,
    counting: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val reachedText =
      if (counting) "PAIR (y:'a) (SUC (SND (p:prod('a,num))))"
      else "PAIR (y:'a) (SND (p:prod('a,num)))"

    for {
      reached <- Parser.term(theory, notation, reachedText, Steps)
      clause <- rules.spec(reached, clauses)
      parts <- impliesOf(clause.conclusion, logic)
      (premise, _) = parts
      normalising <- Conv.betaNormalise(premise)
      normal <- rightOf(normalising)
      sides <- disjunctsOf(normal, logic)
      (isStart, hasPrevious) = sides

      predicate <- existsBody(hasPrevious, logic)
      applied <- LogicError.lift(Term.app(predicate, Before))
      contraction <- Conv.betaRoot(applied)
      instanceAtBefore <- rightOf(contraction)

      // The same clause with the projections done and the closure named, which is the form the
      // caller's hypothesis is in. Read off the rewriter rather than written out, so that a change
      // to the clause cannot leave this function proving the wrong thing.
      legible <- normalOf(readable, instanceAtBefore)
      firstSplit <- conjunctsOf(legible, logic)
      (atBefore, tail) = firstSplit
      secondSplit <- conjunctsOf(tail, logic)
      (moved, choice) = secondSplit
      branches <- disjunctsOf(choice, logic)
      (countedBranch, plainBranch) = branches
      chosen = if (counting) countedBranch else plainBranch
      other = if (counting) plainBranch else countedBranch
      branchParts <- conjunctsOf(chosen, logic)
      (about, equation) = branchParts

      // Right-associated, which is what `/\` parses as and therefore what `Statements` says. Built
      // left-associated first, and the term comparison in `ReachingSpec` is what caught it: the
      // two are the same proposition and not the same term, so every other assertion passed.
      hypothesis <- logic.mkConj(moved, about).flatMap(logic.mkConj(atBefore, _))
      assumed <- LogicError.lift(Kernel.assume(hypothesis))
      hasReached <- rules.conjElim1(assumed)
      trailingPair <- rules.conjElim2(assumed)
      hasMoved <- rules.conjElim1(trailingPair)
      trailing <- rules.conjElim2(trailingPair)

      // The counter's equation is `SUC (SND p) = SUC (SND p)` in one case and `SND p = SND p` in
      // the other, because the projection has already been done: reflexivity settles both.
      counter <- Right(Conv.refl(Term.destEq(equation).map(_._1).getOrElse(equation)))
      branchProof <- rules.conjIntro(trailing, counter)
      lifted <-
        if (counting) rules.disjIntro1(other, branchProof)
        else rules.disjIntro2(other, branchProof)
      rebuiltTail <- rules.conjIntro(hasMoved, lifted)
      rebuilt <- rules.conjIntro(hasReached, rebuiltTail)

      restored <- viaRules(readable, instanceAtBefore, rebuilt)
      introduced <- rules.existsIntro(predicate, Before, restored)
      disjoined <- rules.disjIntro2(isStart, introduced)
      shapedPremise <- shaped(premise, disjoined)
      arrived <- rules.mp(clause, shapedPremise)
      converted <- Rewrite.inTheorem(Vector(reachRule), arrived)

      result <- rules
        .disch(hypothesis, converted)
        .flatMap(rules.gen(Landing, _))
        .flatMap(rules.gen(Before, _))
        .flatMap(rules.gen(Origin, _))
        .flatMap(rules.gen(Counted, _))
        .flatMap(rules.gen(Relation, _))
    } yield result
  }

  /**
   * [[Potential]], which is [[Induction]] at the carrier `\q. Phi x <= SND q + Phi (FST q)`.
   *
   * The base is `Phi x <= ZERO + Phi x`, which is reflexivity once the projections and the zero
   * are done. The step splits on the clause's own disjunction and the two halves are different in
   * kind, which is the thing to know before reading it:
   *
   *  - across a **counted** step the two sides are EQUAL, not merely ordered. The counter goes up
   *    by one and the measure goes down by one, so `SND p + Phi (FST p)` and `SND q + Phi (FST q)`
   *    are both `SUC (SND p + Phi (FST q))`. Nothing about the order is used; what closes it is
   *    `NUM_ADD_SUC` on one side and `NUM_SUC_ADD` on the other.
   *  - across any **other** step the counter stands still and the measure may rise, so this is
   *    where the order is used and where the second hypothesis is spent: `NUM_ADD_MONOTONE` lifts
   *    `Phi (FST p) <= Phi (FST q)` under the counter, and `NUM_LE_TRANS` joins it to what the
   *    induction hypothesis already gave.
   *
   * That asymmetry is why the second hypothesis has to read "does not lower" rather than "does not
   * raise". A step that raised the measure would still be covered here, because a larger right-hand
   * side only makes the bound easier; a step that lowered it would break the chain at exactly this
   * point, since there would be nothing to put between the two.
   */
  private def potentialLemma(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    induction: Kernel.Thm,
    peano: Peano,
    product: Product
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      carrier <- Parser.term(
        theory,
        notation,
        "\\q:prod('a,num). (Phi:'a->num) (x:'a) <= SND q + Phi (FST q)"
      )
      instance <- rules.specAll(induction, List(Relation, Counted, Origin, carrier))
      parts <- impliesOf(instance.conclusion, logic)
      (hypothesis, _) = parts
      goals <- conjunctsOf(hypothesis, logic)
      (baseGoal, stepGoal) = goals

      dropsOne <- Parser.proposition(
        theory,
        notation,
        "!u:'a. !v:'a. (A:'a->'a->bool) u v ==> (Phi:'a->num) u = SUC (Phi v)"
      )
      neverLowers <- Parser.proposition(
        theory,
        notation,
        "!u:'a. !v:'a. (R:'a->'a->bool) u v /\\ ~((A:'a->'a->bool) u v) ==> " +
          "(Phi:'a->num) u <= Phi v"
      )
      assumption <- logic.mkConj(dropsOne, neverLowers)
      assumed <- LogicError.lift(Kernel.assume(assumption))
      assumedDrops <- rules.conjElim1(assumed)
      assumedNever <- rules.conjElim2(assumed)

      firstOfPair <- product.fact(Product.FirstOfPair)
      secondOfPair <- product.fact(Product.SecondOfPair)
      zeroPlus <- peano.fact(Peano.ZeroPlus)
      addAtSuccessor <- peano.fact(Peano.AddAtSuccessor)
      successorPlus <- peano.fact(Peano.SuccessorPlus)
      reflexive <- peano.fact(Peano.Reflexive)
      transitive <- peano.fact(Peano.Transitive)
      addMonotone <- peano.fact(Peano.AddMonotone)

      firstRule <- ruleOf(logic, firstOfPair)
      secondRule <- ruleOf(logic, secondOfPair)
      zeroRule <- ruleOf(logic, zeroPlus)
      addSucRule <- ruleOf(logic, addAtSuccessor)
      sucAddRule <- ruleOf(logic, successorPlus)

      /* --------------------------------------------------------------------- the base */
      baseNormalising <- Conv.betaNormalise(baseGoal)
      baseNormal <- rightOf(baseNormalising)
      atOrigin <- LogicError.lift(Term.app(Measure, Origin))
      reflexivity <- rules.spec(atOrigin, reflexive)
      baseProof <- viaRules(Vector(firstRule, secondRule, zeroRule), baseNormal, reflexivity)
      baseFact <- shaped(baseGoal, baseProof)

      /* --------------------------------------------------------------------- the step */
      stripped <- Logic.stripForall(stepGoal)
      before <- stripped._1.lift(0).toRight(NotOfForm("a claim about two steps", stepGoal))
      after <- stripped._1.lift(1).toRight(NotOfForm("a claim about two steps", stepGoal))
      clause <- impliesOf(stripped._2, logic)
      (antecedent, consequent) = clause
      assumedAntecedent <- LogicError.lift(Kernel.assume(antecedent))
      atBefore <- rules.conjElim1(assumedAntecedent)
      tail <- rules.conjElim2(assumedAntecedent)
      hasMoved <- rules.conjElim1(tail)
      choice <- rules.conjElim2(tail)
      inherited <- reduced(atBefore)
      consequentNormalising <- Conv.betaNormalise(consequent)
      consequentNormal <- rightOf(consequentNormalising)

      firstConstant <- LogicError.lift(theory.constant(Product.First, Type.fun(Steps, State)))
      secondConstant <- LogicError.lift(theory.constant(Product.Second, Type.fun(Steps, Numbers)))
      firstBefore <- LogicError.lift(Term.app(firstConstant, before))
      firstAfter <- LogicError.lift(Term.app(firstConstant, after))
      secondBefore <- LogicError.lift(Term.app(secondConstant, before))
      measureBefore <- LogicError.lift(Term.app(Measure, firstBefore))
      measureAfter <- LogicError.lift(Term.app(Measure, firstAfter))

      branches <- disjunctsOf(choice.conclusion, logic)
      (countedBranch, plainBranch) = branches

      /* the counted step, where the two sides are equal rather than ordered */
      assumedCounted <- LogicError.lift(Kernel.assume(countedBranch))
      isCounted <- rules.conjElim1(assumedCounted)
      counterRose <- rules.conjElim2(assumedCounted)
      dropped <- rules.specAll(assumedDrops, List(firstBefore, firstAfter)).flatMap(rules.mp(_, isCounted))
      dropRule <- ruleOf(logic, dropped)
      roseRule <- ruleOf(logic, counterRose)
      movedInherited <- Rewrite.inTheorem(Vector(dropRule, addSucRule), inherited)
      countedCase0 <- viaRules(Vector(roseRule, sucAddRule), consequentNormal, movedInherited)
      countedCase <- shaped(consequent, countedCase0)

      /* every other step, where the order is what carries it */
      assumedPlain <- LogicError.lift(Kernel.assume(plainBranch))
      notCounted <- rules.conjElim1(assumedPlain)
      counterStood <- rules.conjElim2(assumedPlain)
      together <- rules.conjIntro(hasMoved, notCounted)
      bounded <- rules.specAll(assumedNever, List(firstBefore, firstAfter)).flatMap(rules.mp(_, together))
      lifted <- rules.specAll(addMonotone, List(secondBefore, measureBefore, measureAfter))
        .flatMap(rules.mp(_, bounded))
      stoodRule <- ruleOf(logic, counterStood)
      plainTarget <- normalOf(Vector(stoodRule), consequentNormal)
      joined <- rules.conjIntro(inherited, lifted)
      // By the instance rather than by position: `NUM_LE_TRANS` binds three variables of one type,
      // which is the case a positional call gets silently wrong and the type checker cannot see.
      wanted <- logic
        .mkConj(inherited.conclusion, lifted.conclusion)
        .flatMap(logic.mkImp(_, plainTarget))
      chained <- rules.specTo(transitive, wanted).flatMap(rules.mp(_, joined))
      plainCase0 <- viaRules(Vector(stoodRule), consequentNormal, chained)
      plainCase <- shaped(consequent, plainCase0)

      split <- rules.disjElim(choice, countedCase, plainCase)
      stepFact <- rules
        .disch(antecedent, split)
        .flatMap(rules.gen(after, _))
        .flatMap(rules.gen(before, _))

      supplied <- rules.conjIntro(baseFact, stepFact)
      reached <- rules.mp(instance, supplied)
      // The carrier was substituted into the induction principle and never contracted, so the
      // conclusion here reads `(\q. Phi x <= ...) q` rather than the claim itself. Beta-normalising
      // is the whole repair and there is nothing else in the statement to reduce: the two
      // hypotheses mention only variables.
      everywhere <- reduced(reached)
      result <- rules
        .disch(assumption, everywhere)
        .flatMap(rules.gen(Origin, _))
        .flatMap(rules.gen(Measure, _))
        .flatMap(rules.gen(Counted, _))
        .flatMap(rules.gen(Relation, _))
    } yield result
  }

  private def operatorOf(unfolding: Kernel.Thm): Either[LogicError, Term] =
    rightOf(unfolding).flatMap {
      case App(_, operator) => Right(operator)
      case other => Left(NotOfForm("INDUCTIVE applied to an operator", other))
    }

  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))
}
