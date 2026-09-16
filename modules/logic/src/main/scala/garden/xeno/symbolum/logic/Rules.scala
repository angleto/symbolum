package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * The rules of ordinary reasoning, derived from the ten primitive ones.
 *
 * None of these is an axiom and none of them is trusted. Each is a function that puts primitive
 * rules together, and its result is a theorem for the same reason any other theorem is one.
 *
 * == Schemas, instantiated ==
 *
 * Each connective's definition is unfolded once, over the variables `P` and `Q`, into a schema:
 * `P, Q |- P /\ Q`, `P /\ Q |- P`, `|- (P ==> Q) = ((P /\ Q) = P)` and so on. A use of a rule
 * instantiates the schema with the kernel's `inst` and moves the caller's theorems into it with
 * [[proveHyp]]. So a rule reduces nothing per use, and a statement goes through in exactly the
 * terms it arrived in: a redex in an argument is neither contracted nor an obstacle.
 *
 * The first version unfolded the definition on the caller's own arguments at every use and beta
 * normalised what came out. That normalised the arguments too, so every introduction rule refused
 * a statement containing a redex: the term it had built from the arguments as written no longer
 * matched. An audit found it. The arrangement here is the one HOL Light uses, for the same reason.
 *
 * The reductions a rule performs per use are only of applications it has itself just built.
 * [[spec]] contracts the two it makes by applying the predicate and `\x. T` to the argument;
 * [[existsIntro]] and [[existsElim]] each contract the one they make by applying the caller's
 * predicate to a witness. In all three, a term the caller wrote arrives as it was written.
 */
final class Rules(val logic: Logic) {

  import LogicError.lift

  /** The variables the schemas are stated over. */
  private val P: FVar = Term.variable("P", Type.Bool)
  private val Q: FVar = Term.variable("Q", Type.Bool)

  /**
   * The target a disjunction is eliminated into.
   *
   * A third variable rather than a reuse of `Q`, because disjunction elimination has to name the
   * two disjuncts and the conclusion at once, and a schema that identified any two of them would
   * instantiate to fewer cases than the rule has.
   */
  private val R: FVar = Term.variable("R", Type.Bool)

  /* --------------------------------------------------------------------- truth */

  /** `|- T` */
  lazy val truth: Either[LogicError, Kernel.Thm] =
    for {
      definition <- logic.definitionOf(Logic.Truth)
      body <- rightOfConclusion(definition)
      identity <- leftOfEquation(body)
      reversed <- Conv.sym(definition)
      result <- lift(Kernel.eqMp(reversed, Conv.refl(identity)))
    } yield result

  /** `G |- p` gives `G |- p = T`. */
  def eqTruthIntro(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    truth.map(Kernel.deductAntisym(theorem, _))

  /** `G |- p = T` gives `G |- p`. */
  def eqTruthElim(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      reversed <- Conv.sym(theorem)
      truthTheorem <- truth
      result <- lift(Kernel.eqMp(reversed, truthTheorem))
    } yield result

  /* ----------------------------------------------------------------------- cut */

  /**
   * `G |- p` and `D |- q` give `G, D - {p} |- q`.
   *
   * The cut, derived as HOL Light derives it: the deduction theorem on the two gives `p = q` under
   * `G - {q}, D - {p}`, and modus ponens on that equation puts `p` back. Every rule below uses it
   * to move a caller's theorem into an instantiated schema, which is why the hypotheses of a
   * result are those of the theorems that went in.
   */
  def proveHyp(theorem: Kernel.Thm, target: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    lift(Kernel.eqMp(Kernel.deductAntisym(theorem, target), theorem))

  /* --------------------------------------------------------------- conjunction */

  /** `|- (P /\ Q) = ((\f. f P Q) = (\f. f T T))`, the definition applied to the two variables. */
  private lazy val conjunctionSchema: Either[LogicError, Kernel.Thm] =
    logic.definitionOf(Logic.Conjunction).flatMap(Conv.unfold(_, List(P, Q)))

  /**
   * `P, Q |- P /\ Q`.
   *
   * `P = T` and `Q = T` are applied to a selector `f` and abstracted over it, which is the right
   * side of the unfolded definition.
   */
  private lazy val conjIntroSchema: Either[LogicError, Kernel.Thm] = {
    val selector = Term.variable("f", Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool)))

    for {
      unfolded <- conjunctionSchema
      leftIsTruth <- lift(Kernel.assume(P)).flatMap(eqTruthIntro)
      rightIsTruth <- lift(Kernel.assume(Q)).flatMap(eqTruthIntro)
      applied <- lift(Kernel.mkComb(Conv.refl(selector), leftIsTruth))
      both <- lift(Kernel.mkComb(applied, rightIsTruth))
      abstracted <- lift(Kernel.abs(selector, both))
      reversed <- Conv.sym(unfolded)
      result <- lift(Kernel.eqMp(reversed, abstracted))
    } yield result
  }

  /**
   * `P /\ Q |- P` or `P /\ Q |- Q`.
   *
   * Both sides of the unfolded form are applied to `\a b. a` or `\a b. b` and reduced: one side
   * becomes the projection and the other becomes `T`. The reduction is over variables, which is
   * what makes it safe to normalise everything in sight.
   */
  private def projectionSchema(first: Boolean): Either[LogicError, Kernel.Thm] = {
    val a = Term.variable("a", Type.Bool)
    val b = Term.variable("b", Type.Bool)
    for {
      selector <- lift(Term.absAll(List(a, b), if (first) a else b))
      conjunction <- logic.mkConj(P, Q)
      assumed <- lift(Kernel.assume(conjunction))
      unfolded <- conjunctionSchema
      unpacked <- lift(Kernel.eqMp(unfolded, assumed))
      applied <- Conv.apThm(unpacked, selector)
      reduced <- Conv.normaliseSides(applied)
      result <- eqTruthElim(reduced)
    } yield result
  }

  private lazy val conjElim1Schema: Either[LogicError, Kernel.Thm] = projectionSchema(first = true)
  private lazy val conjElim2Schema: Either[LogicError, Kernel.Thm] = projectionSchema(first = false)

  /** `G |- p` and `D |- q` give `G, D |- p /\ q`. */
  def conjIntro(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      schema <- conjIntroSchema
      instance <- lift(Kernel.inst(Map(P -> left.conclusion, Q -> right.conclusion), schema))
      withLeft <- proveHyp(left, instance)
      result <- proveHyp(right, withLeft)
    } yield result

  /** `G |- p /\ q` gives `G |- p`. */
  def conjElim1(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    project(conjElim1Schema, theorem)

  /** `G |- p /\ q` gives `G |- q`. */
  def conjElim2(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    project(conjElim2Schema, theorem)

  private def project(
    schema: Either[LogicError, Kernel.Thm],
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    logic.destConj(theorem.conclusion) match {
      case None => Left(NotOfForm("a conjunction", theorem.conclusion))
      case Some((p, q)) =>
        for {
          proved <- schema
          instance <- lift(Kernel.inst(Map(P -> p, Q -> q), proved))
          result <- proveHyp(theorem, instance)
        } yield result
    }

  /* --------------------------------------------------------------- implication */

  /** `|- (P ==> Q) = ((P /\ Q) = P)` */
  private lazy val implicationSchema: Either[LogicError, Kernel.Thm] =
    logic.definitionOf(Logic.Implication).flatMap(Conv.unfold(_, List(P, Q)))

  /** `P ==> Q, P |- Q`: across the definition, `P` is `P /\ Q`, and the second half of that is `Q`. */
  private lazy val mpSchema: Either[LogicError, Kernel.Thm] =
    for {
      implication <- logic.mkImp(P, Q)
      assumed <- lift(Kernel.assume(implication))
      unfolded <- implicationSchema
      unpacked <- lift(Kernel.eqMp(unfolded, assumed))
      reversed <- Conv.sym(unpacked)
      positive <- lift(Kernel.assume(P))
      conjoined <- lift(Kernel.eqMp(reversed, positive))
      result <- conjElim2(conjoined)
    } yield result

  /**
   * `G |- q` gives `G - {p} |- p ==> q`.
   *
   * The antecedent is discharged whether or not it was among the hypotheses, which is what makes
   * this the deduction theorem rather than a rule about the shape of the hypothesis set. The proof
   * is HOL Light's: `p /\ q` and `p` are each derivable from the other, so the kernel's deduction
   * theorem makes them equal, and that equation is what `p ==> q` abbreviates.
   */
  def disch(antecedent: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      assumed <- lift(Kernel.assume(antecedent))
      conjoined <- conjIntro(assumed, theorem)
      conjunction <- logic.mkConj(antecedent, theorem.conclusion)
      projected <- lift(Kernel.assume(conjunction)).flatMap(conjElim1)
      equivalence = Kernel.deductAntisym(conjoined, projected)
      schema <- implicationSchema
      instance <- lift(Kernel.inst(Map(P -> antecedent, Q -> theorem.conclusion), schema))
      reversed <- Conv.sym(instance)
      result <- lift(Kernel.eqMp(reversed, equivalence))
    } yield result

  /**
   * `G |- p ==> q` and `D |- p` give `G, D |- q`, and an antecedent of something else is
   * **refused**.
   *
   * == What it did until 2026-09-16, and why that was not a refusal ==
   *
   * It did not check, and a caller could not read it as if it did. A theorem of something else went
   * through [[proveHyp]], which leaves what it cannot discharge where it is, so what came back was
   * `Right`, its conclusion was `q`, and `p` was still on the left of the turnstile beside whatever
   * the wrong premise rested on. That is sound: the result honestly said it assumed `p`. It was
   * simply not a refusal, and nothing looked, because the only thing that looks is
   * `thm.hypotheses`.
   *
   * Two sessions read it as a refusal on one afternoon in September. One inverted the order of a
   * lemma's binders and got a `Right` whose conclusion was the one it wanted; the other closed a
   * card by arguing that a swapped specialisation is caught **because `mp` refuses it**, which was
   * the wrong reason for a right conclusion. [[notElim]] was made strict first, after the same
   * reading cost a derivation of Euclid's theorem a hypothesis nobody had assumed.
   *
   * == Strict up to beta, which is not the same as strict ==
   *
   * The obvious repair, comparing `antecedent.conclusion` with `p` and refusing when they differ,
   * refuses two correct callers. Both hand the choice axiom specialised at a predicate and a
   * variable, whose antecedent is the **unreduced** application `P w`, together with an assumption
   * of its **reduct**. They differ by one beta redex and by nothing else, and beta-equivalent
   * propositions are the same proposition here.
   *
   * So the two forms are reconciled rather than compared: both sides are normalised, a difference
   * that survives normalisation is refused naming what was wanted, and a difference that does not
   * is **converted**, so the cut discharges `p` exactly and nothing is left standing. Checking
   * without converting would have been the worse repair of the two, because it passes at those two
   * sites while leaving the hypothesis they leak exactly where it was: the check would agree the
   * terms match and [[proveHyp]] would still fail to discharge one against the other.
   *
   * Converting rather than checking is [[existsElim]]'s answer to the same question, three hundred
   * lines below, where a case stated over a reduct is moved onto the unreduced application before
   * the cut. This is that, in the other direction.
   */
  def mp(implication: Kernel.Thm, antecedent: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    logic.destImp(implication.conclusion) match {
      case None => Left(NotOfForm("an implication", implication.conclusion))
      case Some((p, q)) =>
        for {
          proofOfP <- provingExactly(p, antecedent)
          schema <- mpSchema
          instance <- lift(Kernel.inst(Map(P -> p, Q -> q), schema))
          withImplication <- proveHyp(implication, instance)
          result <- proveHyp(proofOfP, withImplication)
        } yield result
    }

  /**
   * The same theorem, concluding `wanted` exactly, or a refusal naming what was wanted.
   *
   * Beta is the only difference reconciled, and that is a decision rather than a starting point:
   * it is the one the two callers in this repository actually have, it is decidable by
   * normalising, and every other way two propositions can be "the same" -- an unfolded definition,
   * a commuted conjunction, a renamed bound variable the kernel has not already identified -- is a
   * step somebody should be made to write down. A rule that quietly reconciled those would be the
   * permissiveness this method exists to remove, wearing a better name.
   *
   * **The refusal names the role and not the term, which loses something on purpose.** `notElim`
   * writes the proposition it wanted into its own sentence, and `NotationBoundarySpec` classifies
   * that as `Crossing`: a term rendered where the reader's notation is not known, carried on the
   * record as debt that every instance repays the same way. Adding a second instance to a list
   * somebody is paying down is worse than the reader reaching for the implication they already
   * hold, which is where the wanted term is. What is carried structurally is what they handed
   * over, which is the half they do not have.
   */
  private def provingExactly(
    wanted: Term,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    if (theorem.conclusion == wanted) Right(theorem)
    else if (Term.betaReduce(wanted).contains(theorem.conclusion))
      // The root redex, which is the whole of what the two callers have and is three kernel steps.
      // Reached before the general case on purpose: normalising both sides settles the same
      // question and costs the excluded middle 48 inferences, which is a foundational figure three
      // documents quote. A repair that moves a number that size should buy something with it, and
      // against a root redex it buys nothing.
      for {
        contraction <- Conv.betaRoot(wanted)
        backwards <- Conv.sym(contraction)
        exact <- lift(Kernel.eqMp(backwards, theorem))
      } yield exact
    else
      for {
        wantedNormal <- Conv.betaNormalise(wanted)
        heldNormal <- Conv.betaNormalise(theorem.conclusion)
        wantedForm <- rightOfConclusion(wantedNormal)
        heldForm <- rightOfConclusion(heldNormal)
        result <-
          if (wantedForm != heldForm)
            Left(NotOfForm("a proof of the implication's antecedent", theorem.conclusion))
          else
            for {
              normalised <- lift(Kernel.eqMp(heldNormal, theorem))
              backwards <- Conv.sym(wantedNormal)
              exact <- lift(Kernel.eqMp(backwards, normalised))
            } yield exact
      } yield result

  /* ------------------------------------------------------------------ negation */

  /** `|- (~P) = (P ==> F)` */
  private lazy val negationSchema: Either[LogicError, Kernel.Thm] =
    logic.definitionOf(Logic.Negation).flatMap(Conv.unfold(_, List(P)))

  /** `~P, P |- F` */
  private lazy val notElimSchema: Either[LogicError, Kernel.Thm] =
    for {
      negation <- logic.mkNot(P)
      assumed <- lift(Kernel.assume(negation))
      unfolded <- negationSchema
      unpacked <- lift(Kernel.eqMp(unfolded, assumed))
      positive <- lift(Kernel.assume(P))
      result <- mp(unpacked, positive)
    } yield result

  /** `G |- F` gives `G - {p} |- ~p`. */
  def notIntro(proposition: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      discharged <- disch(proposition, theorem)
      schema <- negationSchema
      instance <- lift(Kernel.inst(Map(P -> proposition), schema))
      reversed <- Conv.sym(instance)
      result <- lift(Kernel.eqMp(reversed, discharged))
    } yield result

  /** `G |- ~p` and `D |- p` give `G, D |- F`. */
  /**
   * `G |- ~p` and `D |- p` give `G, D |- F`, and a mismatched pair is **refused**.
   *
   * The check is the whole point of this comment, because the rule worked without it and worked
   * **wrongly**. Every other rule here moves a caller's theorem into an instantiated schema with
   * [[proveHyp]], which is a cut: handed a theorem whose conclusion is not the hypothesis it is
   * aimed at, it does not fail, it leaves that hypothesis standing and adds the theorem's own. So
   * `notElim` at `~(0 < 0)` and a proof of `d < 0` used to return falsity **carrying `0 < 0` as a
   * hypothesis**, which is sound, is not the rule, and is invisible until something counts
   * hypotheses. On 2026-09-14 that cost a derivation its provenance and was found only because the
   * probe printed the count.
   *
   * **Measured before it was changed.** Of the 105 call sites in this repository, the strict
   * version breaks none and the suite is green. `mp` is lenient in exactly the same way and was
   * measured the same way: it breaks 51 tests across 677 call sites, so the leniency is
   * load-bearing there and tightening it is its own piece of work rather than the same one-line
   * change. `falsityElim` already checks, which is what makes the inconsistency visible.
   */
  def notElim(negation: Kernel.Thm, positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    logic.destNot(negation.conclusion) match {
      case None => Left(NotOfForm("a negation", negation.conclusion))
      case Some(proposition) if positive.conclusion != proposition =>
        Left(NotOfForm(s"a proof of ${proposition}", positive.conclusion))
      case Some(proposition) =>
        for {
          schema <- notElimSchema
          instance <- lift(Kernel.inst(Map(P -> proposition), schema))
          withNegation <- proveHyp(negation, instance)
          result <- proveHyp(positive, withNegation)
        } yield result
    }

  /* ------------------------------------------------------------------- falsity */

  /**
   * `G |- F` gives `G |- p`, for any proposition `p`.
   *
   * No derivation of its own: `F` is defined as `!x:bool. x`, so everything this rule does is move
   * across that definition and specialise. It is a rule rather than four lines at each call site
   * because a case analysis that discharges one branch by contradiction wants it, and the first
   * such derivation in this development wrote it out by hand.
   *
   * Note what it does not need. Ex falso is intuitionistically valid, and the absence of excluded
   * middle costs nothing here: it is the converse direction, concluding `p` from `~~p`, that this
   * logic cannot reach.
   */
  def falsityElim(proposition: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    if (theorem.conclusion != logic.falsity)
      Left(NotOfForm("a proof of falsity", theorem.conclusion))
    else if (!Term.isProposition(proposition))
      Left(NotOfForm("a proposition", proposition))
    else
      for {
        definition <- logic.definitionOf(Logic.Falsity)
        universal <- lift(Kernel.eqMp(definition, theorem))
        result <- spec(proposition, universal)
      } yield result

  /* -------------------------------------------------------- universal quantifier */

  /**
   * `|- (!P) = (P = (\x. T))`, over `P : A -> bool` with `A` the definition's type variable.
   *
   * Instantiated at a type and then with a predicate by [[unfoldQuantifier]].
   */
  private lazy val universalSchema: Either[LogicError, Kernel.Thm] = {
    val predicate = Term.variable("P", Type.fun(TyVar(Rules.QuantifierTypeVariable), Type.Bool))
    logic.definitionOf(Logic.Universal).flatMap(Conv.unfold(_, List(predicate)))
  }

  /**
   * `G |- p` gives `G |- !x. p`, provided `x` is not free in `G`.
   *
   * The side condition is the kernel's, on abstraction, and it arrives from there rather than
   * being checked again here.
   */
  def gen(variable: FVar, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      predicate <- lift(Term.abs(variable, theorem.conclusion))
      isTruth <- eqTruthIntro(theorem)
      abstracted <- lift(Kernel.abs(variable, isTruth))
      unfolded <- unfoldQuantifier(variable.ty, predicate)
      reversed <- Conv.sym(unfolded)
      result <- lift(Kernel.eqMp(reversed, abstracted))
    } yield result

  /**
   * `G |- !x. p` gives `G |- p[a/x]`.
   *
   * The predicate and `\x. T` are each applied to the argument and the two applications that
   * makes are contracted, and only those: a redex inside the argument, or one that substituting
   * the argument creates inside the body, is left where it is, as HOL Light's `SPEC` leaves it.
   */
  def spec(argument: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    logic.destForallPredicate(theorem.conclusion) match {
      case None => Left(NotOfForm("a universal quantification", theorem.conclusion))
      case Some(predicate) =>
        Type.destFun(Term.typeOf(predicate)) match {
          case None => Left(NotOfForm("a predicate", predicate))
          case Some((domain, _)) =>
            for {
              unfolded <- unfoldQuantifier(domain, predicate)
              unpacked <- lift(Kernel.eqMp(unfolded, theorem))
              applied <- Conv.apThm(unpacked, argument)
              reduced <- Conv.betaSides(applied)
              result <- eqTruthElim(reduced)
            } yield result
        }
    }

  /**
   * `G |- !x y z. p` gives `G |- p[a/x, b/y, c/z]`, one [[spec]] per argument, outermost first.
   *
   * The fold rather than the single step is what most derivations want: a lemma about three
   * quantities is specialised at three of them or not at all, and writing the chain out names the
   * intermediate theorems, which have no meaning of their own.
   *
   * **A list shorter than the quantifier prefix is refused**, by [[PartialInstance]], naming both
   * numbers. Until 2026-09-12 it was accepted and gave a partial instance: one quantifier still in
   * front and every substitution shifted by one, which is a theorem, is not the theorem the caller
   * meant, and fails somewhere else entirely. That is how a session reaching `NUM_DIVISION_UNIQUE`
   * with `NUM_DIV_MOD_UNIQUE`'s four arguments read its first symptom at an unrelated `mp` several
   * steps later, as a complaint about an implication.
   *
   * A longer list was always refused and still is, by [[spec]] meeting something that is not a
   * quantification, so both mistakes now stop here. The prefix is counted rather than consumed, so
   * that the refusal can say how many there were.
   *
   * [[genAll]] has no counterpart to this and needs none: `spec` consumes a prefix the theorem
   * already has, and `gen` adds quantifiers the caller chose. Generalising over fewer variables
   * than are free is the ordinary case and not a mistake.
   */
  def specAll(theorem: Kernel.Thm, arguments: List[Term]): Either[LogicError, Kernel.Thm] = {
    val prefix = Rules.quantifierPrefix(theorem.conclusion)

    if (arguments.length < prefix) Left(PartialInstance(prefix, arguments.length, theorem.conclusion))
    else specPrefix(theorem, arguments)
  }

  /**
   * The same, at the **first** of the quantifiers, leaving the rest where they are.
   *
   * `G |- !x y z. p` at `a, b` gives `G |- !z. p[a/x, b/y]`. Asked for by name, because the only way
   * to get it before was to hand [[specAll]] a short list, which is also exactly what handing it
   * another lemma's arguments looks like, and nothing inside could tell the two apart.
   *
   * **Measured before it was written.** Every call the whole suite makes with a list shorter than
   * the prefix was counted on 2026-09-12, by a probe inside this method: one, in `SeriesSpec`,
   * where `SUM_REINDEX` is specialised at a function and at `SUC ZERO` and the bound is left
   * quantified on purpose, so that what comes out can be compared with `SUM_SHIFT`. One is not
   * zero, so the operation stays; one is also not many, so it does not get to be the default. The
   * count is dynamic and covers what the suite exercises rather than the 261 places `specAll` is
   * written, and a call on no tested path would not have been seen.
   */
  def specPrefix(theorem: Kernel.Thm, arguments: List[Term]): Either[LogicError, Kernel.Thm] =
    arguments.foldLeft(Right(theorem): Either[LogicError, Kernel.Thm]) { (acc, argument) =>
      acc.flatMap(current => spec(argument, current))
    }

  /**
   * `G |- !x y. p` at whatever makes the body exactly `target`, found by matching rather than by
   * position.
   *
   * [[specAll]] takes the arguments in the order the quantifiers happen to be written, and that
   * order is not part of any contract: it is a consequence of how the lemma was derived. A
   * derivation rewritten for an unrelated reason can reverse it, and on 2026-09-13 one did.
   * `SUM_SUC`, `POWER_SUC` and `PROD_SUC` came out of one shared driver instead of two copies that
   * disagreed, and the surviving copy generalised the parameter before the index; a consumer
   * specialising those three positionally stopped building. That consumer was lucky, and the
   * luck is what this exists for.
   *
   * == The measurement, which is the argument ==
   *
   * It stopped building because the two arguments had **different types**, so the application was
   * ill-typed and the kernel refused. Where the two leading quantifiers range over the **same**
   * type, reversing them is invisible: the arguments go into the other variables, every rule
   * downstream accepts what it is handed, and what comes out is a theorem that is true and is not
   * the one the caller meant. Nothing refuses, and the wrong theorem is in the artifact.
   *
   * Counted over the whole library on 2026-09-13, by `scratch/BinderTypes.scala`: of 260 lemmas,
   * 159 have two or more leading quantifiers, and **142 of those have two that share a type**. So
   * the case where the type checker catches a reordering is the minority, and the majority is the
   * silent one. That is the number that decided this method; four lemmas would not have.
   *
   * == Why the argument is a term and not a name ==
   *
   * The consumer that found it asked for specialisation by the **name** of the binder,
   * `spec(Map("f" -> t, "n" -> u))`, which is what a system with named bound variables would offer.
   * There are no names to offer. Binders here carry a type and nothing else, which is what
   * `docs/adr/0002` decided, and the names a reader sees printed are coined from the binder's
   * **position** as the term is opened. A map keyed on those would be positional dressed as
   * nominal: it would stop breaking without starting to be right, which is worse than what it
   * replaces. So the caller says what it wants to obtain, and the obtaining is matched against it.
   *
   * == The two refusals, and the guard after them ==
   *
   *  - [[NotOfForm]] when no instantiation of the leading quantifiers gives `target` at all.
   *  - [[Undetermined]] when the match succeeded but left a quantifier open, which happens when
   *    that variable does not occur in the body. Any value would give `target`, so picking one is
   *    exactly the silent choice this method exists to refuse; it names the variable instead.
   *
   * Then the result is compared with `target` and refused unless it **is** it. That is the guard
   * `Bounded.prove` and `Induct.proveBy` end with, and here it is what makes the matcher's
   * behaviour irrelevant to the reader: whatever the match found, what comes back is the term that
   * was asked for or nothing. Nothing reaches that line today, and the reason it is written anyway
   * is the one `Rewrite.idle`'s second guard gives: a match that determined every quantifier and a
   * `specAll` over what it determined agree, and the line is what keeps that argument local to this
   * method if either ever stops being true.
   *
   * What it does not do: it protects the call sites written this way and no others. Every
   * positional `specAll` in this repository and in a consumer's stays as exposed as it was. And it
   * compares the instance as `spec` leaves it, redexes included, which is not the term a reader
   * checks against an informal claim where the caller's argument was a lambda;
   * [[specToReduced]] is that case and is a separate operation for the reason written there.
   */
  def specTo(theorem: Kernel.Thm, target: Term): Either[LogicError, Kernel.Thm] =
    instantiatedTo(theorem, target).flatMap(isTarget(_, target))

  /**
   * The same, with what `spec` left as a redex contracted before the comparison.
   *
   * Two operations rather than one with a flag, and the difference is not presentation: `G |- !f.
   * Sum (\i. f i) n = ...` at a summand written as a lambda gives an instance carrying `(\j. h j)
   * i` under the binder, and the beta-normal form of that instance is **a different theorem**. A
   * caller that wanted the first would have no way left to ask for it if one name returned
   * sometimes the one and sometimes the other, which is the distinction `NotNormalised` and
   * `NotEqualTo` are kept apart for one file over.
   *
   * It exists because the consumer that asked for [[specTo]] migrated what it could and reported
   * the sites where it could not, and every one of them was a `SUM_LINEAR`, `SUM_ADD`,
   * `SUM_CONGRUENCE`, `SUM_MONOTONE` or `SUM_HALVES` followed by `Conv.betaNormalise`. At those,
   * the term a caller would have to write to say what it wants is the **un-reduced** one, which is
   * not the term anybody compares against an informal claim, and that comparison is half of what
   * this pair is for. How many sites that is, is that consumer's count and is not repeated here:
   * what is checkable from this side is the shape, and the shape is `Sum` over a summand written
   * as a lambda.
   *
   * **The matcher was measured before this was written**, because the whole thing rests on it: the
   * pattern holds `f i` under a binder and the target holds the reduced body, so finding the
   * instantiation is higher-order matching in Miller's fragment. `Matching.matchTerm` solves it,
   * and the reading is that `SUM_LINEAR` against its own normalised instance comes back with the
   * summand bound to the lambda that produced it. Nothing needed to change there: what refused was
   * only the comparison at the end, which is this.
   */
  def specToReduced(theorem: Kernel.Thm, target: Term): Either[LogicError, Kernel.Thm] =
    for {
      instance <- instantiatedTo(theorem, target)
      equation <- Conv.betaNormalise(instance.conclusion)
      reduced <- lift(Kernel.eqMp(equation, instance))
      result <- isTarget(reduced, target)
    } yield result

  /**
   * The instantiation both of them share, without the comparison either of them ends with.
   *
   * Private, because what it returns is an instance nobody has checked is the one that was asked
   * for, and that is exactly the value this pair exists to stop a caller from holding.
   */
  private def instantiatedTo(
    theorem: Kernel.Thm,
    target: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Logic.stripForall(theorem.conclusion)
      (variables, body) = stripped
      _ <-
        if (variables.nonEmpty) Right(())
        else Left(NotOfForm("a universal quantification", theorem.conclusion))

      found <- Matching
        .matchTerm(variables.toSet, body, target)
        .toRight(NotOfForm(s"an instance of $body", target))

      // The types first, where there were any to decide: the quantifiers below range over the
      // pattern's types, and `spec` would meet the target's.
      opened <-
        if (found.types.isEmpty) Right(theorem)
        else Right(Kernel.instType(found.types, theorem))

      arguments <- variables.toList.foldLeft(Right(Nil): Either[LogicError, List[Term]]) {
        (acc, variable) =>
          acc.flatMap(collected =>
            found.terms.get(variable).map(collected :+ _).toRight(Undetermined(variable))
          )
      }

      result <- specAll(opened, arguments)
    } yield result

  /** The guard both of them end with: what comes back is the term that was asked for, or nothing. */
  private def isTarget(theorem: Kernel.Thm, target: Term): Either[LogicError, Kernel.Thm] =
    if (theorem.conclusion == target) Right(theorem)
    else Left(NotOfForm("the target as it is written", theorem.conclusion))

  /**
   * `G |- p` gives `G |- !x y z. p`, one [[gen]] per variable.
   *
   * The variables are quantified in the order they are written, which is why the fold runs over
   * the reverse: the last one to be generalised is the one that ends up outermost.
   */
  def genAll(theorem: Kernel.Thm, variables: List[FVar]): Either[LogicError, Kernel.Thm] =
    variables.reverse.foldLeft(Right(theorem): Either[LogicError, Kernel.Thm]) { (acc, variable) =>
      acc.flatMap(current => gen(variable, current))
    }

  /** `|- (!predicate) = (predicate = (\x. T))`, at the type the predicate ranges over. */
  private def unfoldQuantifier(domain: Type, predicate: Term): Either[LogicError, Kernel.Thm] = {
    val variable = Term.variable("P", Type.fun(domain, Type.Bool))

    for {
      schema <- universalSchema
      atDomain = Kernel.instType(Map(Rules.QuantifierTypeVariable -> domain), schema)
      result <- lift(Kernel.inst(Map(variable -> predicate), atDomain))
    } yield result
  }

  /* --------------------------------------------------------------- disjunction */

  /**
   * `|- (P \/ Q) = (!r. (P ==> r) ==> ((Q ==> r) ==> r))`
   *
   * The definition says what a disjunction is good for rather than what it is: whatever both
   * disjuncts imply. That is why elimination here is a specialisation and two detachments, and why
   * neither rule needs a case-splitting principle the logic does not have.
   */
  private lazy val disjunctionSchema: Either[LogicError, Kernel.Thm] =
    logic.definitionOf(Logic.Disjunction).flatMap(Conv.unfold(_, List(P, Q)))

  /**
   * `P |- P \/ Q`, or `Q |- P \/ Q`.
   *
   * The same derivation both times, differing only in which implication is detached: assume the
   * disjunct and the one implication whose antecedent it is, detach the target from the two, then
   * discharge *both* implications, the one that was never assumed included, so that the antecedents
   * come out in the order the definition puts them whichever branch this is. Discharging an
   * antecedent that was not assumed is [[disch]]'s behaviour, and it is what lets one derivation
   * serve both injections. `R` is not free in the surviving hypothesis, which is the single
   * disjunct, so the generalisation goes through.
   */
  private def injectionSchema(first: Boolean): Either[LogicError, Kernel.Thm] = {
    val disjunct = if (first) P else Q

    for {
      leftCase <- logic.mkImp(P, R)
      rightCase <- logic.mkImp(Q, R)
      applicable = if (first) leftCase else rightCase
      assumed <- lift(Kernel.assume(disjunct))
      assumedCase <- lift(Kernel.assume(applicable))
      target <- mp(assumedCase, assumed)
      // Discharged innermost first, so the two implications come out in the order the definition
      // puts them, whichever of the two was the one detached.
      withRight <- disch(rightCase, target)
      withBoth <- disch(leftCase, withRight)
      generalised <- gen(R, withBoth)
      unfolded <- disjunctionSchema
      reversed <- Conv.sym(unfolded)
      result <- lift(Kernel.eqMp(reversed, generalised))
    } yield result
  }

  private lazy val disjIntro1Schema: Either[LogicError, Kernel.Thm] = injectionSchema(first = true)
  private lazy val disjIntro2Schema: Either[LogicError, Kernel.Thm] = injectionSchema(first = false)

  /** `P \/ Q, P ==> R, Q ==> R |- R` */
  private lazy val disjElimSchema: Either[LogicError, Kernel.Thm] =
    for {
      disjunction <- logic.mkDisj(P, Q)
      assumed <- lift(Kernel.assume(disjunction))
      unfolded <- disjunctionSchema
      unpacked <- lift(Kernel.eqMp(unfolded, assumed))
      specialised <- spec(R, unpacked)
      leftCase <- logic.mkImp(P, R).flatMap(term => lift(Kernel.assume(term)))
      afterLeft <- mp(specialised, leftCase)
      rightCase <- logic.mkImp(Q, R).flatMap(term => lift(Kernel.assume(term)))
      result <- mp(afterLeft, rightCase)
    } yield result

  /** `G |- p` gives `G |- p \/ q`. */
  def disjIntro1(right: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    inject(disjIntro1Schema, theorem.conclusion, right, theorem)

  /** `G |- q` gives `G |- p \/ q`. */
  def disjIntro2(left: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    inject(disjIntro2Schema, left, theorem.conclusion, theorem)

  private def inject(
    schema: Either[LogicError, Kernel.Thm],
    left: Term,
    right: Term,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    if (!Term.isProposition(right)) Left(NotOfForm("a proposition", right))
    else if (!Term.isProposition(left)) Left(NotOfForm("a proposition", left))
    else
      for {
        proved <- schema
        instance <- lift(Kernel.inst(Map(P -> left, Q -> right), proved))
        result <- proveHyp(theorem, instance)
      } yield result

  /**
   * `G |- p \/ q`, `D |- r` and `E |- r` give `G, D - {p}, E - {q} |- r`.
   *
   * The two case theorems are discharged before the schema is instantiated, so an assumption that
   * was never made is discharged anyway and a case that did not need its disjunct is accepted.
   * That is [[disch]]'s behaviour and it is the right one here: a case analysis where one branch
   * happens not to use its hypothesis is still a case analysis.
   */
  def disjElim(
    disjunction: Kernel.Thm,
    leftCase: Kernel.Thm,
    rightCase: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    logic.destDisj(disjunction.conclusion) match {
      case None => Left(NotOfForm("a disjunction", disjunction.conclusion))
      case Some((p, q)) =>
        if (leftCase.conclusion != rightCase.conclusion)
          Left(NotOfForm(s"a case proving ${leftCase.conclusion}", rightCase.conclusion))
        else
          for {
            leftImplies <- disch(p, leftCase)
            rightImplies <- disch(q, rightCase)
            proved <- disjElimSchema
            instance <- lift(
              Kernel.inst(Map(P -> p, Q -> q, R -> leftCase.conclusion), proved)
            )
            withDisjunction <- proveHyp(disjunction, instance)
            withLeft <- proveHyp(leftImplies, withDisjunction)
            result <- proveHyp(rightImplies, withLeft)
          } yield result
    }

  /* ------------------------------------------------------ existential quantifier */

  /**
   * `|- (?P) = (!q. (!x. P x ==> q) ==> q)`, over `P : A -> bool`.
   *
   * The mirror of [[universalSchema]], and instantiated the same way, because the existential
   * carries the same type variable and a schema fixed at one type would serve one domain only.
   */
  private lazy val existentialSchema: Either[LogicError, Kernel.Thm] = {
    val predicate = Term.variable("P", Type.fun(TyVar(Rules.QuantifierTypeVariable), Type.Bool))
    logic.definitionOf(Logic.Existential).flatMap(Conv.unfold(_, List(predicate)))
  }

  /** `|- (?predicate) = (!q. (!x. predicate x ==> q) ==> q)`, at the predicate's domain. */
  private def unfoldExistential(domain: Type, predicate: Term): Either[LogicError, Kernel.Thm] = {
    val variable = Term.variable("P", Type.fun(domain, Type.Bool))

    for {
      schema <- existentialSchema
      atDomain = Kernel.instType(Map(Rules.QuantifierTypeVariable -> domain), schema)
      result <- lift(Kernel.inst(Map(variable -> predicate), atDomain))
    } yield result
  }

  /**
   * `G |- p[a/x]` gives `G |- ?x. p`, with `predicate` the `\x. p` intended and `witness` the `a`.
   *
   * The predicate is a parameter rather than something recovered from the theorem because it
   * cannot be recovered: `f a = a` is `(\x. f x = x) a` and `(\x. f a = a) a` and several other
   * things, and which existential was meant is the caller's statement, not an inference. What is
   * checked instead is that the theorem proves this predicate at this witness, so a predicate that
   * does not fit is a refusal rather than a theorem about something else.
   *
   * The application is left unreduced where the derivation needs it that way: the assumption
   * discharged below has to be syntactically the definition's body, and the definition applies the
   * predicate rather than substituting into it.
   */
  def existsIntro(
    predicate: Term,
    witness: Term,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    Type.destFun(Term.typeOf(predicate)) match {
      case None => Left(NotOfForm("a predicate", predicate))
      case Some((domain, _)) if domain != Term.typeOf(witness) =>
        Left(NotOfForm(s"a witness of type $domain", witness))

      case Some((domain, _)) =>
        val avoid = Rules.freeIn(theorem) ++ Term.freeVariables(predicate)
        val target = Conv.freshVariable("q", Type.Bool, avoid)
        val bound = Conv.freshVariable("x", domain, avoid)

        for {
          applied <- lift(Term.app(predicate, witness))
          contraction <- Conv.betaRoot(applied)
          reduced <- rightOfConclusion(contraction)
          _ <- if (reduced == theorem.conclusion) Right(())
               else Left(NotOfForm(s"a proof of $reduced", theorem.conclusion))

          // The caller's theorem, restated over the unreduced application the definition uses.
          // Across the contraction rather than through a fresh assumption, so the hypotheses that
          // come out are the caller's and nothing has been added to them.
          reversedContraction <- Conv.sym(contraction)
          moved <- lift(Kernel.eqMp(reversedContraction, theorem))

          instantiated <- lift(Term.app(predicate, bound))
          body <- logic.mkImp(instantiated, target)
          hypothesis <- logic.mkForall(bound, body)
          assumed <- lift(Kernel.assume(hypothesis))
          specialised <- spec(witness, assumed)
          detached <- mp(specialised, moved)
          discharged <- disch(hypothesis, detached)
          generalised <- gen(target, discharged)

          unfolded <- unfoldExistential(domain, predicate)
          reversed <- Conv.sym(unfolded)
          result <- lift(Kernel.eqMp(reversed, generalised))
        } yield result
    }

  /**
   * `G |- ?x. p` and `D |- c`, where `D` contains `p[v/x]`, give `G, D - {p[v/x]} |- c`.
   *
   * `v` has to be arbitrary, and there are three ways it could fail to be. **One** the kernel
   * catches: `v` free in the rest of `D`, which is the side condition on abstraction that [[gen]]
   * inherits, and the instance is discharged before the generalisation so only the rest of `D`
   * reaches it. The other two are about the statement being built rather than the theorem handed
   * in, and both are refused here with [[EscapingVariable]]: `v` free in `c` would prove `c` for
   * that particular witness, and `v` free in the predicate would have the existential name the
   * witness it exists to hide.
   *
   * Neither of those two would fail loudly if it were left in, which is the reason to check them
   * rather than to let the derivation report it. [[gen]] closes over every occurrence of `v`,
   * including the ones inside the predicate, so the generalisation stops matching the antecedent
   * [[spec]] produced. The second half of that sentence used to read "and [[mp]] never compares an
   * antecedent against anything, so what comes back is a true sequent carrying that unmatched
   * antecedent as an extra hypothesis, rather than an error", and **that stopped being true on
   * 2026-09-16**: `mp` refuses an antecedent it cannot reconcile. The reason to check here is
   * unchanged and is now the stronger one, that a rule returning a weaker theorem than the one
   * asked for would be worse than one that refuses.
   *
   * == The instance is the REDUCT, and this is where a caller loses a cycle ==
   *
   * `D` has to contain `p[v/x]` as the **beta-reduced** instance, not as the application
   * `predicate v`. [[existsIntro]] documents the mirror of this in its own docstring and this one
   * did not, so a caller who assumed the application got [[MissingHypothesis]] naming a term that
   * looks identical to the one they assumed until the redex is noticed.
   *
   * It stayed undocumented because nothing met it head-on. The two callers that build an instance
   * this way go through the choice axiom, whose antecedent is the unreduced application, and `mp`'s
   * old permissiveness absorbed the difference: it left the unreduced form standing as a hypothesis
   * and the conversion below discharged both. Making `mp` strict removed that, so the requirement
   * is now met directly, by a caller rather than by an accident. Reported by the session that paid
   * for it in three failing tests.
   *
   * `G` is not constrained. `v` may occur free in the hypotheses of the existential itself, and it
   * necessarily occurs in the instance being discharged.
   */
  def existsElim(
    existential: Kernel.Thm,
    variable: FVar,
    caseTheorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    logic.destExistsPredicate(existential.conclusion) match {
      case None => Left(NotOfForm("an existential quantification", existential.conclusion))
      case Some(predicate) =>
        Type.destFun(Term.typeOf(predicate)) match {
          case None => Left(NotOfForm("a predicate", predicate))
          case Some((domain, _)) if domain != variable.ty =>
            Left(NotOfForm(s"a witness of type $domain", variable))

          case Some((domain, _)) =>
            val conclusion = caseTheorem.conclusion

            if (Term.occursFree(variable, conclusion))
              Left(EscapingVariable(variable, "the conclusion of the case it proves"))
            else if (Term.freeVariables(predicate).contains(variable))
              Left(EscapingVariable(variable, "the predicate it is the witness for"))
            else
              for {
                applied <- lift(Term.app(predicate, variable))
                contraction <- Conv.betaRoot(applied)
                reduced <- rightOfConclusion(contraction)

                // The case is stated over the reduced instance, which is what a caller assumes,
                // and the derivation needs it over the unreduced application.
                unreduced <- lift(Kernel.assume(applied))
                asReduced <- lift(Kernel.eqMp(contraction, unreduced))

                // Not a soundness condition, and this is where the two eliminations differ on
                // purpose. [[disjElim]] accepts a branch that never used its disjunct, because such
                // a branch still proves the conclusion and the rule's contract is met. Here the
                // contract would also be met, `D - {p[v/x]}` being `D` when the instance is absent,
                // and what comes back is the conclusion with the existential added as a premise
                // that did nothing. That is what passing the wrong witness looks like, and it looks
                // like success, so it is refused instead.
                _ <- if (caseTheorem.hypotheses.contains(reduced)) Right(())
                     else Left(MissingHypothesis(reduced, "eliminating an existential"))
                moved <- proveHyp(asReduced, caseTheorem)
                implied <- disch(applied, moved)
                generalised <- gen(variable, implied)

                unfolded <- unfoldExistential(domain, predicate)
                unpacked <- lift(Kernel.eqMp(unfolded, existential))
                specialised <- spec(conclusion, unpacked)
                result <- mp(specialised, generalised)
              } yield result
        }
    }

  /* ----------------------------------------------------------------- internals */

  private def leftOfEquation(equation: Term): Either[LogicError, Term] =
    Term.destEq(equation).map(_._1).toRight(NotOfForm("an equation", equation))

  private def rightOfConclusion(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}

object Rules {

  /**
   * How many universal quantifiers a proposition begins with.
   *
   * Counted from the structure rather than by opening each one, because the count is all that is
   * wanted and opening allocates a fresh variable per quantifier: `Logic.stripForall` is the
   * function for a caller that needs the variables, and this is not one.
   *
   * A quantifier whose predicate is not an abstraction ends the count, which is the right answer
   * rather than a limitation: `!P` over a variable `P` is specialisable and its prefix is not
   * something this can read, so it is counted as none and [[Rules.specAll]] lets any list through.
   * Under-counting only ever declines to refuse; over-counting would refuse a correct call.
   */
  private[logic] def quantifierPrefix(proposition: Term): Int = proposition match {
    case App(Const(Logic.Universal, _), Abs(_, body)) => 1 + quantifierPrefix(body)
    case _ => 0
  }

  /** Every variable free anywhere in a theorem, conclusion and hypotheses alike. */
  private[logic] def freeIn(theorem: Kernel.Thm): Set[FVar] =
    theorem.hypotheses.foldLeft(Term.freeVariables(theorem.conclusion)) { (acc, hypothesis) =>
      acc ++ Term.freeVariables(hypothesis)
    }

  /**
   * The type variable the quantifier definitions are stated with.
   *
   * Named here rather than written at each use because instantiating the wrong variable produces
   * a theorem about the wrong type, and the mistake would be a one-character one.
   */
  private[logic] val QuantifierTypeVariable: String = "A"
}
