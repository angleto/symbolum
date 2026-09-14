package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * `|- !e f. ?fn. fn ZERO = e /\ (!n. fn (SUC n) = f (fn n) n)`.
 *
 * Definition by recursion, derived. Point 2 of the card that asked for it, and the thing without
 * which not even addition can be defined on the naturals: `docs/proving.md` has said since the
 * naturals landed that what waits on it is everything indexed by an integer.
 *
 * == The relation, and why the proof is about a relation and not a function ==
 *
 * A function cannot be built by saying what it does; it has to be produced. So the graph is built
 * first, as the smallest relation containing `(ZERO, e)` and closed under the step:
 *
 * {{{
 *   Rec n y  =  !S. S ZERO e /\ (!m z. S m z ==> S (SUC m) (f z m)) ==> S n y
 * }}}
 *
 * That it relates each `n` to something is one induction. That it relates each `n` to **only** one
 * thing is the half the work is in, and it is proved together with existence rather than after it:
 * the step needs the uniqueness at `n` to get uniqueness at `SUC n`, so the two have to travel in
 * one induction. Then choice turns "for each `n` exactly one `y`" into a term, which is what the
 * choice operator was asserted for and why `docs/adr/0007` put it before the axiom of infinity.
 *
 * == Where the two Peano facts are used, which is the whole of what infinity buys ==
 *
 * Uniqueness needs `SUC n` never to be `ZERO` and `SUC` to be injective, and nothing else does.
 * Everything above this file rests on the recursion theorem, so this is where the axiom of infinity
 * finally reaches the mathematics: the type, induction and the case split reach no axiom at all,
 * and the proof record says so per theorem.
 *
 * == The theorem, and getting a constant out of it ==
 *
 * [[theorem]] says a function with a given value at zero and a given step **exists**. Turning that
 * into a named constant with its two equations is a dozen steps of choice, definition and
 * rewriting, and it is the same dozen every time; [[define]] is them, and nine definitions across
 * `Peano` and `Series` are built by it. Until the night of 2026-09-12 it was two copies of them,
 * one private to each of those two files, and the copies had drifted where nothing could see it:
 * `Series`'s generalised the index before the parameter, so `SUM_SUC`, `POWER_SUC` and `PROD_SUC`
 * read `!x:num. !y:num -> real. Sum y (SUC x) = ...` while their twins on `num` read
 * `NUM_SUM_SUC !x:num -> num. !y:num. NUM_SUM x (SUC y) = ...`.
 *
 * **That those three were the anomaly is measured, and the first version of this paragraph
 * overclaimed it.** Of the 159 published lemmas carrying two or more leading binders that the body
 * all mentions, 19 quantify in an order the printed body does not follow; 15 of the 19 carry a
 * hypothesis, which mentions whatever it is about before the conclusion applies anything, and is a
 * different question. Four are a bare claim. One of the four is `NUM_DIV_MOD`, whose binders do
 * follow `NUM_DIV x y` and `NUM_MOD x y` and whose body merely writes the product the other way
 * round. The other three are these three. So the convention is real and it had exactly one
 * exception, and the exception was one driver rather than three decisions.
 *
 * What it cost a caller: `SUM_ZERO` takes the summand and `SUM_SUC` took the index, so
 * specialising both recurrences of one function meant swapping the arguments between them. And
 * **two implementations that disagree do not disagree anywhere a test looks, because each is
 * tested against itself**; joining them is what made the difference visible at all.
 */
object Recursion {

  /**
   * The theorem, over the naturals given.
   *
   * Built rather than looked up, because it is the only fact here that is expensive and not
   * everything wants it; `Natural.recursion` caches one per development.
   */
  def theorem(naturals: Natural): Either[LogicError, Kernel.Thm] = {
    val logic = naturals.logic
    val rules = logic.rules
    val classical = naturals.classical
    val alpha = TyVar("a")
    val numbers = TyApp(Natural.TypeName, Nil)

    val e = Term.variable("e", alpha)
    val f = Term.variable("f", Type.fun(alpha, Type.fun(numbers, alpha)))
    val n = Term.variable("n", numbers)
    val y = Term.variable("y", alpha)
    val m = Term.variable("m", numbers)
    val w = Term.variable("w", alpha)

    /** A term applied and beta normalised, which is the form every proposition below is in. */
    def at(relation: Term, arguments: List[Term]): Either[LogicError, Term] =
      for {
        applied <- LogicError.lift(Term.appAll(relation, arguments))
        normalised <- Conv.betaNormalise(applied)
        sides <- Term.destEq(normalised.conclusion).toRight(NotOfForm("an equation", applied))
      } yield sides._2

    for {
      relation <- Parser.term(
        naturals.theory,
        naturals.notation,
        "\\n:num. \\y:'a. !S:num->'a->bool. S ZERO (e:'a) /\\ " +
          "(!m:num. !z:'a. S m z ==> S (SUC m) ((f:'a->num->'a) z m)) ==> S n y"
      )
      zero <- LogicError.lift(naturals.theory.constant(Natural.NumberZero, numbers))
      successor <- LogicError.lift(
        naturals.theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      notZero <- naturals.fact(Natural.SuccessorNotZero)
      injective <- naturals.fact(Natural.SuccessorInjective)
      induction <- naturals.fact(Natural.Induction)

      recOf = (index: Term, value: Term) => at(relation, List(index, value))

      // `|- Rec ZERO e`: every inductive relation holds of the pair it starts from.
      zeroGoal <- recOf(zero, e)
      base <- proveRelated(logic, zeroGoal, (antecedent, _) => rules.conjElim1(antecedent))

      // `|- !n y. Rec n y ==> Rec (SUC n) (f y n)`: it holds of the pair the step reaches.
      premise <- recOf(n, y)
      successorOfN <- LogicError.lift(Term.app(successor, n))
      stepped <- LogicError.lift(Term.appAll(f, List(y, n)))
      stepGoal <- recOf(successorOfN, stepped)
      carried <- LogicError.lift(Kernel.assume(premise)).flatMap { assumed =>
        proveRelated(
          logic,
          stepGoal,
          (inductive, predicate) =>
            for {
              here <- rules.spec(predicate, assumed).flatMap(rules.mp(_, inductive))
              step <- rules.conjElim2(inductive)
              there <- rules.specAll(step, List(n, y)).flatMap(rules.mp(_, here))
            } yield there
        )
      }
      step <- rules.disch(premise, carried).flatMap(rules.genAll(_, List(n, y)))

      unique <- uniqueAtZero(logic, relation, zero, e, f, m, w, successor, notZero, at)

      // `|- !n. ?y. Rec n y /\ (!z. Rec n z ==> z = y)`.
      //
      // Existence and uniqueness in one induction, because they cannot be separated: the step needs
      // the uniqueness at `n` to reach the uniqueness at `SUC n`, and an induction that carried only
      // existence would have nothing to hand it.
      togetherAt = (index: Term, value: Term) =>
        for {
          related <- recOf(index, value)
          z = Term.variable("z", alpha)
          other <- recOf(index, z)
          equal <- LogicError.lift(Term.eq(z, value))
          implied <- logic.mkImp(other, equal)
          only <- logic.mkForall(z, implied)
          both <- logic.mkConj(related, only)
        } yield both

      strengthenedBody <- togetherAt(n, y).flatMap(logic.mkExists(y, _))
      strengthened <- LogicError.lift(Term.abs(n, strengthenedBody))
      instance <- rules.spec(strengthened, induction)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic.destImp(opened.conclusion).toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      strongBase <- for {
        predicate <- logic.destExistsPredicate(baseTerm).toRight(NotOfForm("an existential", baseTerm))
        both <- rules.conjIntro(base, unique)
        built <- rules.existsIntro(predicate, e, both)
      } yield built

      strongStep <- strengthenedStep(
        logic,
        relation,
        stepTerm,
        (zero, e, f, successor),
        (m, w),
        (base, step),
        (notZero, injective),
        at
      )

      everywhere <- rules.conjIntro(strongBase, strongStep).flatMap(rules.mp(opened, _))

      result <- extract(logic, classical, naturals, relation, everywhere, unique, step, (e, f, n), zero, successor, at)
    } yield result
  }

  /**
   * Prove `Rec n y` in its unfolded form, given how to reach `S n y` from the inductive assumption.
   *
   * Every proof that something is related runs this way: strip the quantifier over the relation,
   * assume that it is inductive, reach the conclusion, and close both back up. Written once because
   * it happens four times below and the interesting part is only ever the middle.
   */
  private def proveRelated(
    logic: Logic,
    goal: Term,
    reach: (Kernel.Thm, FVar) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      stripped <- Logic.stripForall(goal)
      predicate <- stripped._1.headOption.toRight(NotOfForm("a claim about every relation", goal))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (inductive, consequent) = parts
      assumed <- LogicError.lift(Kernel.assume(inductive))
      reached <- reach(assumed, predicate)
      _ <-
        if (reached.conclusion == consequent) Right(())
        else Left(NotOfForm("what the relation says of that pair", reached.conclusion))
      result <- rules.disch(inductive, reached).flatMap(rules.gen(predicate, _))
    } yield result
  }

  /**
   * The step of the strengthened induction, which is where the two Peano facts are spent.
   *
   * Given a `y` the relation reaches at `k` and reaches only there, the value at `SUC k` is
   * `f y k`. Existence is the step lemma; uniqueness runs a second relation,
   * `\m w. Rec m w /\ (m = SUC k ==> w = f y k)`, whose own step is the only place in the file
   * where injectivity is needed: from `SUC m = SUC k` it gives `m = k`, and only then does the
   * induction hypothesis apply.
   */
  private def strengthenedStep(
    logic: Logic,
    relation: Term,
    stepTerm: Term,
    theory: (Term, Term, Term, Term),
    variables: (FVar, FVar),
    reached: (Kernel.Thm, Kernel.Thm),
    peano: (Kernel.Thm, Kernel.Thm),
    at: (Term, List[Term]) => Either[LogicError, Term]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (zero, e, f, successor) = theory
    val (m, w) = variables
    val (base, step) = reached
    val (notZero, injective) = peano
    val alpha = Term.typeOf(e)
    val recOf = (index: Term, value: Term) => at(relation, List(index, value))

    for {
      stripped <- Logic.stripForall(stepTerm)
      k <- stripped._1.headOption.toRight(NotOfForm("a claim about every number", stepTerm))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (before, after) = parts
      assumedBefore <- LogicError.lift(Kernel.assume(before))

      innerPredicate <- logic.destExistsPredicate(before).toRight(NotOfForm("an existential", before))
      value = Conv.freshVariable("y", alpha, Term.freeVariables(stepTerm) + k)
      applied <- LogicError.lift(Term.app(innerPredicate, value))
      instance <- Term.betaReduce(applied).toRight(NotOfForm("a redex", applied))
      assumedInstance <- LogicError.lift(Kernel.assume(instance))
      relatedHere <- rules.conjElim1(assumedInstance)
      onlyHere <- rules.conjElim2(assumedInstance)

      successorOfK <- LogicError.lift(Term.app(successor, k))
      target <- LogicError.lift(Term.appAll(f, List(value, k)))
      relatedThere <- rules.specAll(step, List(k, value)).flatMap(rules.mp(_, relatedHere))

      // `\m w. Rec m w /\ (m = SUC k ==> w = f y k)`, and that it is inductive.
      witnessBody <- for {
        related <- recOf(m, w)
        isSuccessor <- LogicError.lift(Term.eq(m, successorOfK))
        isTarget <- LogicError.lift(Term.eq(w, target))
        implied <- logic.mkImp(isSuccessor, isTarget)
        both <- logic.mkConj(related, implied)
      } yield both
      witness <- LogicError.lift(
        Term.absAll(List(m, w), witnessBody)
      )

      witnessAtZero <- for {
        goal <- at(witness, List(zero, e))
        conjuncts <- logic.destConj(goal).toRight(NotOfForm("a conjunction", goal))
        implication <- logic.destImp(conjuncts._2).toRight(NotOfForm("an implication", conjuncts._2))
        assumedAbsurd <- LogicError.lift(Kernel.assume(implication._1))
        flipped <- Conv.sym(assumedAbsurd)
        never <- rules.spec(k, notZero)
        contradiction <- rules.notElim(never, flipped)
        anything <- rules.falsityElim(implication._2, contradiction)
        vacuous <- rules.disch(implication._1, anything)
        both <- rules.conjIntro(base, vacuous)
      } yield both

      witnessStep <- for {
        source <- at(witness, List(m, w))
        successorOfM <- LogicError.lift(Term.app(successor, m))
        stepped <- LogicError.lift(Term.appAll(f, List(w, m)))
        destination <- at(witness, List(successorOfM, stepped))
        assumed <- LogicError.lift(Kernel.assume(source))
        relatedAtM <- rules.conjElim1(assumed)
        relatedAtSuccessor <- rules.specAll(step, List(m, w)).flatMap(rules.mp(_, relatedAtM))
        conjuncts <- logic.destConj(destination).toRight(NotOfForm("a conjunction", destination))
        implication <- logic.destImp(conjuncts._2).toRight(NotOfForm("an implication", conjuncts._2))
        assumedEqual <- LogicError.lift(Kernel.assume(implication._1))
        sameIndex <- rules.specAll(injective, List(m, k)).flatMap(rules.mp(_, assumedEqual))
        carried <- Conv
          .apTerm(relation, sameIndex)
          .flatMap(Conv.apThm(_, w))
          .flatMap(Conv.normaliseSides)
        relatedAtK <- LogicError.lift(Kernel.eqMp(carried, relatedAtM))
        sameValue <- rules.spec(w, onlyHere).flatMap(rules.mp(_, relatedAtK))
        onTheLeft <- Conv.apTerm(f, sameValue).flatMap(Conv.apThm(_, m))
        onTheRight <- LogicError.lift(Term.app(f, value)).flatMap(Conv.apTerm(_, sameIndex))
        joined <- Conv.trans(onTheLeft, onTheRight)
        proved <- rules.disch(implication._1, joined)
        both <- rules.conjIntro(relatedAtSuccessor, proved)
        discharged <- rules.disch(source, both)
        general <- rules.genAll(discharged, List(m, w))
      } yield general

      onlyThere <- for {
        z <- Right(Term.variable("z", alpha))
        premise <- recOf(successorOfK, z)
        assumed <- LogicError.lift(Kernel.assume(premise))
        inductive <- rules.conjIntro(witnessAtZero, witnessStep)
        instanceAt <- rules.spec(witness, assumed)
        openedAt <- Conv
          .betaNormalise(instanceAt.conclusion)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instanceAt)))
        applied <- rules.mp(openedAt, inductive)
        second <- rules.conjElim2(applied)
        equal <- rules.mp(second, Conv.refl(successorOfK))
        closed <- rules.disch(premise, equal).flatMap(rules.gen(z, _))
      } yield closed

      outerPredicate <- logic.destExistsPredicate(after).toRight(NotOfForm("an existential", after))
      both <- rules.conjIntro(relatedThere, onlyThere)
      built <- rules.existsIntro(outerPredicate, target, both)
      eliminated <- rules.existsElim(assumedBefore, value, built)
      result <- rules.disch(before, eliminated).flatMap(rules.gen(k, _))
    } yield result
  }

  /**
   * The function, named by choice, and the two equations it satisfies.
   *
   * `fn` is `\n. select (\y. Rec n y /\ only)`. Choice gives, for each `n`, that the chosen value
   * is related and is the only one, and the two equations follow by pointing uniqueness at a value
   * already known to be related: `e` at zero, and `f (fn n) n` at a successor.
   */
  private def extract(
    logic: Logic,
    classical: Classical,
    naturals: Natural,
    relation: Term,
    everywhere: Kernel.Thm,
    unique: Kernel.Thm,
    step: Kernel.Thm,
    variables: (FVar, FVar, FVar),
    zero: Term,
    successor: Term,
    at: (Term, List[Term]) => Either[LogicError, Term]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (e, f, n) = variables

    for {
      here <- rules.spec(n, everywhere)
      chosen <- classical.witness(here)
      reduced <- Conv
        .betaNormalise(chosen.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chosen)))
      selected <- chosen.conclusion match {
        case App(_, term) => Right(term)
        case other => Left(NotOfForm("a predicate applied to what was chosen", other))
      }
      function <- LogicError.lift(Term.abs(n, selected))

      atIndex = (index: Term) =>
        LogicError.lift(Kernel.inst(Map(n -> index), reduced))

      // `fn ZERO = e`
      atZero <- atIndex(zero)
      relatedAtZero <- rules.conjElim1(atZero)
      applied <- LogicError.lift(Term.app(function, zero))
      reduction <- Conv.betaRoot(applied)
      chosenAtZero <- Term.destEq(reduction.conclusion).map(_._2).toRight(NotOfForm("an equation", applied))
      valueAtZero <- rules.spec(chosenAtZero, unique).flatMap(rules.mp(_, relatedAtZero))
      zeroEquation <- Conv.trans(reduction, valueAtZero)

      // `fn (SUC n) = f (fn n) n`
      successorOfN <- LogicError.lift(Term.app(successor, n))
      atSuccessor <- atIndex(successorOfN)
      onlyAtSuccessor <- rules.conjElim2(atSuccessor)
      atHere <- atIndex(n)
      relatedHere <- rules.conjElim1(atHere)
      candidate <- LogicError.lift(Term.appAll(f, List(selected, n)))
      relatedCandidate <- rules.specAll(step, List(n, selected)).flatMap(rules.mp(_, relatedHere))
      equal <- rules.spec(candidate, onlyAtSuccessor).flatMap(rules.mp(_, relatedCandidate))
      flipped <- Conv.sym(equal)
      leftReduction <- LogicError.lift(Term.app(function, successorOfN)).flatMap(Conv.betaRoot)
      rightReduction <- LogicError.lift(Term.app(function, n)).flatMap(Conv.betaRoot)
      rightBack <- Conv.sym(rightReduction)
      inside <- Conv.apTerm(f, rightBack).flatMap(Conv.apThm(_, n))
      throughLeft <- Conv.trans(leftReduction, flipped)
      stepEquation <- Conv.trans(throughLeft, inside)

      statement <- naturals.proposition(Statement)
      stripped <- Logic.stripForall(statement)
      body = stripped._2
      generalised <- rules.gen(n, stepEquation)
      both <- rules.conjIntro(zeroEquation, generalised)
      predicate <- logic.destExistsPredicate(body).toRight(NotOfForm("an existential", body))
      substituted <- LogicError.lift(
        Term.substitute(Map(stripped._1(0) -> e, stripped._1(1) -> f), predicate)
      )
      built <- rules.existsIntro(substituted, function, both)
      result <- rules.genAll(built, List(e, f))
      _ <-
        if (result.conclusion == statement) Right(())
        else Left(NotOfForm("the recursion theorem as it is written", result.conclusion))
    } yield result
  }

  /** The theorem, as the text a person checks it by. */
  val Statement: String =
    "!e:'a. !f:'a->num->'a. ?fn:num->'a. fn ZERO = e /\\ (!n:num. fn (SUC n) = f (fn n) n)"

  /**
   * `|- !z. Rec ZERO z ==> z = e`.
   *
   * The relation `\m w. m = ZERO ==> w = e` is inductive, so anything related to `ZERO` satisfies
   * it. The step of that relation is where `SUC m` never being `ZERO` is used, and it is used ex
   * falso: there is nothing to prove about a case that cannot arise.
   */
  private def uniqueAtZero(
    logic: Logic,
    relation: Term,
    zero: Term,
    e: Term,
    f: Term,
    m: FVar,
    w: FVar,
    successor: Term,
    notZero: Kernel.Thm,
    at: (Term, List[Term]) => Either[LogicError, Term]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val z = Term.variable("z", Term.typeOf(e))

    for {
      isZero <- LogicError.lift(Term.eq(m, zero))
      isValue <- LogicError.lift(Term.eq(w, e))
      body <- logic.mkImp(isZero, isValue)
      only <- LogicError.lift(
        Term.absAll(List(m, w), body)
      )

      atZero <- at(only, List(zero, e))
      zeroParts <- logic.destImp(atZero).toRight(NotOfForm("an implication", atZero))
      onlyAtZero <- rules.disch(zeroParts._1, Conv.refl(e))

      before <- at(only, List(m, w))
      successorOfM <- LogicError.lift(Term.app(successor, m))
      stepped <- LogicError.lift(Term.appAll(f, List(w, m)))
      after <- at(only, List(successorOfM, stepped))
      afterParts <- logic.destImp(after).toRight(NotOfForm("an implication", after))
      assumedAbsurd <- LogicError.lift(Kernel.assume(afterParts._1))
      never <- rules.spec(m, notZero)
      contradiction <- rules.notElim(never, assumedAbsurd)
      anything <- rules.falsityElim(afterParts._2, contradiction)
      vacuous <- rules.disch(afterParts._1, anything)
      onlyStep <- LogicError
        .lift(Kernel.assume(before))
        .flatMap(_ => rules.disch(before, vacuous))
        .flatMap(rules.genAll(_, List(m, w)))

      premise <- at(relation, List(zero, z))
      assumed <- LogicError.lift(Kernel.assume(premise))
      inductive <- rules.conjIntro(onlyAtZero, onlyStep)
      instance <- rules.spec(only, assumed)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      applied <- rules.mp(opened, inductive)
      value <- rules.mp(applied, Conv.refl(zero))
      result <- rules.disch(premise, value).flatMap(rules.gen(z, _))
    } yield result
  }

  /* ---------------------------------------------------------------- the driver */

  /**
   * Define `name` on the naturals by recursion, and take its two equations out.
   *
   * What varies between the nine call sites, and so what this takes:
   *
   *  - **the type of the values**, `num` for the arithmetic on the naturals and `real` for the
   *    embedding and for the sums;
   *  - **the value at zero and the step**, as text, because that is what a reader checks against
   *    the informal recurrence;
   *  - **the parameter**, if there is one. `NUM_ADD` and `NUM_MUL` are functions of a number
   *    **and** a number, so the recursion produces a function of the second and the first is
   *    abstracted afterwards, exactly as `Power` abstracts its base; `real_of_num` and `PRE` have
   *    no parameter at all, and `None` is what says so.
   *
   * The two equations come back generalised over the parameter first and the index second, which
   * is the order every other lemma about the same functions is written in.
   */
  private[theories] def define(
    logic: Logic,
    naturals: Natural,
    theory: Theory,
    notation: Notation,
    recursion: Kernel.Thm,
    name: String,
    values: Type,
    startText: String,
    stepText: String,
    parameter: Option[FVar]
  ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)

    for {
      start <- Parser.term(theory, notation, startText)
      step <- Parser.term(theory, notation, stepText)
      atValues = Kernel.instType(Map("a" -> values), recursion)
      instance <- rules.specAll(atValues, List(start, step))
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))

      chosen <- naturals.classical.witness(opened)
      selected <- chosen.conclusion match {
        case App(_, term) => Right(term)
        case other => Left(NotOfForm("a predicate applied to what was chosen", other))
      }
      body <- LogicError.lift(Term.absAll(parameter.toList, selected))
      defined <- LogicError.lift(Kernel.defineConstant(theory, name, body))
      (extended, definition) = defined

      reduced <- Conv
        .betaNormalise(chosen.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chosen)))
      unfolded <- Conv.unfold(definition, parameter.toList)

      zeroTerm <- LogicError.lift(extended.constant(Natural.NumberZero, numbers))
      atZeroChosen <- rules.conjElim1(reduced)
      zeroSide <- Conv.apThm(unfolded, zeroTerm)
      atZeroBody <- Conv.trans(zeroSide, atZeroChosen)
      atZero <- parameter.fold(Right(atZeroBody): Either[LogicError, Kernel.Thm])(
        variable => rules.gen(variable, atZeroBody)
      )

      successor <- LogicError.lift(
        extended.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
      atStepChosen <- rules.conjElim2(reduced).flatMap(rules.spec(n, _))
      successorOfN <- LogicError.lift(Term.app(successor, n))
      onTheLeft <- Conv.apThm(unfolded, successorOfN)
      here <- Conv.apThm(unfolded, n)
      back <- Conv.sym(here)
      stepped <- Term
        .destEq(atStepChosen.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", atStepChosen.conclusion))
      onTheRight <- carry(logic, back, stepped)
      throughStep <- Conv.trans(onTheLeft, atStepChosen)
      atSuccessor <- Conv
        .trans(throughStep, onTheRight)
        .flatMap(rules.genAll(_, parameter.toList :+ n))
    } yield (extended, definition, atZero, atSuccessor)
  }

  /**
   * Carry `select ... = name` into the term that mentions the chosen thing.
   *
   * A rewrite rather than a hand-built congruence, because the chosen term sits in a different
   * place in each of the nine steps this drives.
   */
  private def carry(
    logic: Logic,
    equation: Kernel.Thm,
    term: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      rule <- Rewrite.Rule.of(logic, equation)
      rewritten <- Rewrite.rewrite(Vector(rule), term)
    } yield rewritten
}
