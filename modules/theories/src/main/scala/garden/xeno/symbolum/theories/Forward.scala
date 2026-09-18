package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The right forward closure of a string rewriting system, and the one-step relation under it.
 *
 * Source: Geser, Hofbauer and Waldmann, NASA/CR-2003-212685. `RFC(R)` is the least set containing
 * the right-hand sides of `R` and closed under two operations: **inside reduction**, a step of `R`
 * anywhere in the word, and **right extension**, which takes a member ending in `l1`, a rule
 * `l1 l2 -> r` and produces the member with `l1` replaced by `r`. It is the technique the survey
 * of match-bounds leaves standing as the one with no complexity ceiling, and it is what a
 * quadratic lower bound on derivation length is read off.
 *
 * == Why this could not be written here until today ==
 *
 * Two things were missing and both landed on 2026-09-16. `Concatenation` gave the word the
 * operation it did not have, so `?x y. w = x u y` became a sentence this repository can write and
 * the inside-reduction clause has something to say "the left-hand side occurs here" with.
 * `Inductive` gave the shape "the least set containing X and closed under these clauses", which is
 * what a closure **is**; before it, membership could be generated forwards and looked at, and a
 * non-membership was a budget rather than a theorem.
 *
 * The second is the one that changes what is provable rather than what is convenient.
 * [[Inductive.Induction]] asks nothing of the operator and is what settles a non-membership, so
 * every fact below of the form "this word is not in the closure" is reachable now and was not.
 *
 * == Three clauses, not two, and the difference is worth a line ==
 *
 * The card that asked for this work says two, meaning the two **closure** operations, which is how
 * the source states it: least set *containing* the right-hand sides, *closed under* inside
 * reduction and right extension. An `INDUCTIVE` operator has no separate notion of a base, so the
 * containment is a disjunct like the other two and the operator below has three. Nothing is
 * different about it; the count is, and a reader comparing the two sentences should not have to
 * work out which is wrong.
 *
 * == The emptiness conditions on the extension, which are not decoration ==
 *
 * `l1` and `l2` are both required non-empty, and each rules out a different collapse. With `l1`
 * empty the clause says any member, extended by any right-hand side, is a member, which makes the
 * closure far larger than the set the bound is proved about. With `l2` empty the rule `l1 -> r` is
 * applied at the right end of a member, which is already inside reduction, so the clause would be
 * a second copy of one that is there. The first is unsound for the purpose and the second is
 * merely redundant, and they are stated as one conjunction because the source does.
 *
 * == What [[Forward.Step]] is, and why it is not [[Concatenation.Factor]] ==
 *
 * `WORD_STEP R u v` says `u` and `v` differ by one application of a rule of `R`: there are `x` and
 * `y` with `u = x l y` and `v = x r y` for some rule `l -> r`. The card that asked for this work
 * describes the clause as saying the left-hand side is a **factor**, which is the right reading and
 * is not the definition, because `WORD_FACTOR l u` quantifies its own context away and the two
 * sides of one step need the *same* context. A definition written with `WORD_FACTOR` would say
 * that `l` occurs in `u` and that `r` occurs in `v`, which is true of far more pairs than one step
 * relates.
 *
 * That reading is a consequence and it is **not proved here**, deliberately rather than by
 * omission: `WORD_STEP R u v ==> ?l r. R l r /\ WORD_FACTOR l u /\ WORD_FACTOR r v` follows by
 * taking the step's own `x` and `y` as the factor's witnesses, it is strictly weaker than the
 * definition, and nothing below needs it. It is worth having the day a consumer wants the
 * occurrence without the context, and not before.
 */
final class Forward private (
  val inductive: Inductive,
  val concatenation: Concatenation,
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

object Forward {

  /** `WORD_STEP R u v` — one application of a rule of `R`, anywhere in `u`. */
  val Step: String = "WORD_STEP"

  /** `WORD_RFC R w` — `w` is in the right forward closure of `R`. */
  val Name: String = "WORD_RFC"

  /** `|- !R l r. R l r ==> WORD_RFC R r` — a right-hand side is in the closure. */
  val RightSide: String = "WORD_RFC_RIGHT"

  /** `|- !R u v. WORD_RFC R u /\ WORD_STEP R u v ==> WORD_RFC R v` — inside reduction. */
  val Inside: String = "WORD_RFC_INSIDE"

  /**
   * `|- !R p a b r. WORD_RFC R (WORD_CONCAT p a) /\ R (WORD_CONCAT a b) r /\
   * ~(a = WORD_EMPTY) /\ ~(b = WORD_EMPTY) ==> WORD_RFC R (WORD_CONCAT p r)` — right extension.
   */
  val Extend: String = "WORD_RFC_EXTEND"

  /**
   * The induction principle over the closure, with the operator already unfolded.
   *
   * [[Inductive.Induction]] at this operator, put into the three-clause shape a consumer writes,
   * so that reasoning about a member of the closure is not also unfolding a definition and
   * splitting a disjunction of three by hand. It asks **nothing** of `R`, which is
   * [[Inductive.Induction]]'s own asymmetry inherited: the half that decides a non-membership is
   * free and the half that decides a membership pays for monotonicity.
   */
  val Induction: String = "WORD_RFC_INDUCT"

  /* ------------------------------------------------------------------ the types */

  private val Element: Type = TyVar(Classical.TypeVariable)
  private val Words: Type = TyApp(Word.TypeName, List(Element))

  /** A rewrite system: a relation between a left-hand side and a right-hand side. */
  val Systems: Type = Type.fun(Words, Type.fun(Words, Type.Bool))

  private val System: FVar = Term.variable("R", Systems)
  private val Carrier: FVar = Term.variable("S", Type.fun(Words, Type.Bool))
  private val Point: FVar = Term.variable("w", Words)

  /* ------------------------------------------------------------------ the text */

  private val StepBody: String =
    "\\R:word('a)->word('a)->bool. \\u:word('a). \\v:word('a). " +
      "?x:word('a). ?l:word('a). ?r:word('a). ?y:word('a). R l r /\\ " +
      "u = WORD_CONCAT (WORD_CONCAT x l) y /\\ v = WORD_CONCAT (WORD_CONCAT x r) y"

  /**
   * The three disjuncts, in the order the source gives them: contains, reduces inside, extends
   * right. Written once here and read back out of the definition everywhere else, so the operator
   * the proofs run over and the operator the constant is defined by cannot drift apart.
   */
  private val ClauseText: String =
    "(?l:word('a). R l w) \\/ " +
      "(?u:word('a). S u /\\ WORD_STEP R u w) \\/ " +
      "(?p:word('a). ?a:word('a). ?b:word('a). ?r:word('a). " +
      "S (WORD_CONCAT p a) /\\ R (WORD_CONCAT a b) r /\\ " +
      "~(a = WORD_EMPTY) /\\ ~(b = WORD_EMPTY) /\\ w = WORD_CONCAT p r)"

  private val Body: String =
    "\\R:word('a)->word('a)->bool. " +
      "INDUCTIVE (\\S:word('a)->bool. \\w:word('a). " + ClauseText + ")"

  /** Every statement this development publishes, as text, for the reader and for the spec. */
  val Statements: Vector[(String, String)] = Vector(
    RightSide -> "!R:word('a)->word('a)->bool. !l:word('a). !r:word('a). R l r ==> WORD_RFC R r",
    Inside ->
      ("!R:word('a)->word('a)->bool. !u:word('a). !v:word('a). " +
        "WORD_RFC R u /\\ WORD_STEP R u v ==> WORD_RFC R v"),
    Extend ->
      ("!R:word('a)->word('a)->bool. !p:word('a). !a:word('a). !b:word('a). !r:word('a). " +
        "WORD_RFC R (WORD_CONCAT p a) /\\ R (WORD_CONCAT a b) r /\\ " +
        "~(a = WORD_EMPTY) /\\ ~(b = WORD_EMPTY) ==> WORD_RFC R (WORD_CONCAT p r)"),
    Induction ->
      ("!R:word('a)->word('a)->bool. !S:word('a)->bool. " +
        "(!w:word('a). (?l:word('a). R l w) ==> S w) /\\ " +
        "(!w:word('a). (?u:word('a). S u /\\ WORD_STEP R u w) ==> S w) /\\ " +
        "(!w:word('a). (?p:word('a). ?a:word('a). ?b:word('a). ?r:word('a). " +
        "S (WORD_CONCAT p a) /\\ R (WORD_CONCAT a b) r /\\ " +
        "~(a = WORD_EMPTY) /\\ ~(b = WORD_EMPTY) /\\ w = WORD_CONCAT p r) ==> S w) " +
        "==> (!w:word('a). WORD_RFC R w ==> S w)")
  )

  /* ------------------------------------------------------------------ construction */

  /**
   * The development, built over `Concatenation` for the word and `Inductive` for the closure.
   *
   * Two constants and no axiom. [[Step]] is a plain definition; [[Name]] is `INDUCTIVE` at an
   * operator, so everything below is derived in the `INDUCTIVE op` vocabulary and carried across
   * the defining equation on the way out. The set occurs **inside** the clause as well as outside
   * it, which is why the equation is used as a rewrite rule rather than applied pointwise: a
   * pointwise conversion reaches the occurrence at the top and misses the two under the clause.
   */
  def construct(
    inductive: Inductive,
    concatenation: Concatenation,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Forward] =
    for {
      stepBody <- Parser.term(base, notation, StepBody)
      stepDefined <- LogicError.lift(Kernel.defineConstant(base, Step, stepBody))
      (withStep, stepDefinition) = stepDefined

      body <- Parser.term(withStep, notation, Body)
      defined <- LogicError.lift(Kernel.defineConstant(withStep, Name, body))
      (theory, definition) = defined

      logic <- inductive.classical.logic.over(theory)

      unfolding <- Conv.unfold(definition, List(System))
      operator <- operatorOf(unfolding)

      inductiveInduct <- inductive.fact(Inductive.Induction)
      inductiveIntro <- inductive.fact(Inductive.Introduction)

      monotonicity <- Monotone.prove(logic, inductive, operator)
      clauses <- introductionClauses(logic, inductiveIntro, monotonicity, operator)

      rfcRule <- Conv.sym(unfolding).flatMap(rule => Rewrite.Rule.of(logic, rule))
      unfoldRule <- Rewrite.Rule.of(logic, unfolding)

      right <- rightSideRule(logic, theory, notation, clauses, rfcRule)
      inside <- insideRule(logic, theory, notation, clauses, unfoldRule, rfcRule)
      extend <- extendRule(logic, theory, notation, clauses, unfoldRule, rfcRule)
      induction <- inductionPrinciple(logic, inductiveInduct, operator, unfolding)
    } yield new Forward(
      inductive,
      concatenation,
      theory,
      notation,
      Map(Step -> stepDefinition, Name -> definition),
      Map(
        RightSide -> right,
        Inside -> inside,
        Extend -> extend,
        Induction -> induction
      )
    )

  /* ------------------------------------------------------------------ shared pieces */

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def impliesOf(term: Term, logic: Logic): Either[LogicError, (Term, Term)] =
    logic.destImp(term).toRight(NotOfForm("an implication", term))

  private def disjunctsOf(term: Term, logic: Logic): Either[LogicError, (Term, Term)] =
    logic.destDisj(term).toRight(NotOfForm("a disjunction", term))

  private def existsBody(term: Term, logic: Logic): Either[LogicError, Term] =
    logic.destExistsPredicate(term).toRight(NotOfForm("an existential", term))

  /** A proof of the beta normal form of `target` becomes a proof of `target`. */
  private def shaped(target: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv
      .betaNormalise(target)
      .flatMap(Conv.sym)
      .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

  private def operatorOf(unfolding: Kernel.Thm): Either[LogicError, Term] =
    rightOf(unfolding).flatMap {
      case App(_, operator) => Right(operator)
      case other => Left(NotOfForm("INDUCTIVE applied to an operator", other))
    }

  /* ------------------------------------------------------------------ the proofs */

  /**
   * `|- !w. op (INDUCTIVE op) w ==> INDUCTIVE op w`, which the three introduction rules share.
   *
   * [[Inductive.Introduction]] at this operator with the monotonicity discharged. It is done once
   * rather than in each of the three because the monotonicity is what it costs and paying it three
   * times would be three copies of the same theorem.
   */
  private def introductionClauses(
    logic: Logic,
    inductiveIntro: Kernel.Thm,
    monotonicity: Kernel.Thm,
    operator: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val atWords = Kernel.instType(Map(Classical.TypeVariable -> Words), inductiveIntro)
    rules.spec(operator, atWords).flatMap(rules.mp(_, monotonicity))
  }

  /**
   * The clause of the operator at a named point, split into its three disjuncts.
   *
   * Every introduction rule below needs the same three terms and gets them the same way: the
   * premise of the specialised clause, beta reduced, taken apart as `first \/ (second \/ third)`.
   * Reading them off the operator rather than parsing them again is what keeps a change to
   * [[ClauseText]] from leaving these functions proving something the definition no longer says.
   */
  private def disjunctsAt(
    logic: Logic,
    clauses: Kernel.Thm,
    point: Term
  ): Either[LogicError, (Kernel.Thm, Term, Term, Term, Term)] =
    for {
      clause <- logic.rules.spec(point, clauses)
      parts <- impliesOf(clause.conclusion, logic)
      (premise, _) = parts
      normalising <- Conv.betaNormalise(premise)
      normal <- rightOf(normalising)
      outer <- disjunctsOf(normal, logic)
      (first, rest) = outer
      inner <- disjunctsOf(rest, logic)
      (second, third) = inner
    } yield (clause, premise, first, second, third)

  /** [[RightSide]]: a right-hand side is in the closure, which is the first disjunct. */
  private def rightSideRule(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    clauses: Kernel.Thm,
    rfcRule: Rewrite.Rule
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      left <- Parser.term(theory, notation, "l:word('a)", Words)
      right <- Parser.term(theory, notation, "r:word('a)", Words)
      leftVar <- asVariable(left)
      rightVar <- asVariable(right)

      pieces <- disjunctsAt(logic, clauses, right)
      (clause, premise, first, second, third) = pieces

      // The hypothesis is `R l r`; the disjunct is `?l. R l r`, so one witness closes it.
      hypothesis <- applied(System, List(left, right))
      assumed <- LogicError.lift(Kernel.assume(hypothesis))
      predicate <- existsBody(first, logic)
      witnessed <- rules.existsIntro(predicate, left, assumed)

      rest <- logic.mkDisj(second, third)
      disjunction <- rules.disjIntro1(rest, witnessed)
      shapedPremise <- shaped(premise, disjunction)
      inClosure <- rules.mp(clause, shapedPremise)
      named <- Rewrite.inTheorem(Vector(rfcRule), inClosure)

      result <- rules
        .disch(hypothesis, named)
        .flatMap(rules.gen(rightVar, _))
        .flatMap(rules.gen(leftVar, _))
        .flatMap(rules.gen(System, _))
    } yield result
  }

  private def asVariable(term: Term): Either[LogicError, FVar] = term match {
    case variable: FVar => Right(variable)
    case other => Left(NotOfForm("a variable", other))
  }

  /** `f a b c`, built left to right, with the kernel's type check at each step. */
  private def applied(head: Term, arguments: List[Term]): Either[LogicError, Term] =
    arguments.foldLeft[Either[LogicError, Term]](Right(head)) { (accumulated, argument) =>
      accumulated.flatMap(function => LogicError.lift(Term.app(function, argument)))
    }

  /**
   * The instantiated bodies of a nest of existentials, outermost first, and its predicates.
   *
   * `?p a b r. body` is four terms rather than one, and introducing it means proving the innermost
   * body and then closing four times from the inside out. Both halves need the same intermediate
   * terms, so they are computed once here: `levels(i)` is what remains to be proved after `i`
   * witnesses have been supplied, and `predicates(i)` is what [[Rules.existsIntro]] wants at that
   * level.
   */
  private def nest(
    logic: Logic,
    existential: Term,
    witnesses: List[Term]
  ): Either[LogicError, (Vector[Term], Vector[Term])] =
    witnesses.foldLeft[Either[LogicError, (Vector[Term], Vector[Term])]](
      Right((Vector(existential), Vector.empty))
    ) { (accumulated, witness) =>
      for {
        state <- accumulated
        (levels, predicates) = state
        current <- levels.lastOption.toRight(NotOfForm("a level to open", existential))
        predicate <- existsBody(current, logic)
        instance <- LogicError.lift(Term.app(predicate, witness))
        contraction <- Conv.betaRoot(instance)
        next <- rightOf(contraction)
      } yield (levels :+ next, predicates :+ predicate)
    }

  /** Close a nest of existentials from the inside out, given a proof of the innermost body. */
  private def close(
    logic: Logic,
    predicates: Vector[Term],
    witnesses: List[Term],
    innermost: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    predicates.zip(witnesses).foldRight[Either[LogicError, Kernel.Thm]](Right(innermost)) {
      case ((predicate, witness), accumulated) =>
        accumulated.flatMap(theorem => logic.rules.existsIntro(predicate, witness, theorem))
    }

  /**
   * [[Inside]] and [[Extend]], which differ in which disjunct they supply and in nothing else.
   *
   * Both take the caller's hypothesis in the **readable** vocabulary, where the closure is named
   * `WORD_RFC R`, move it into the clause's vocabulary where the same set is `INDUCTIVE op`, close
   * the existentials over it, and name the result again on the way out. The two conversions are
   * the same equation read in its two directions, which is why they are built from one `unfolding`
   * rather than parsed twice.
   */
  private def disjunctRule(
    logic: Logic,
    clauses: Kernel.Thm,
    unfoldRule: Rewrite.Rule,
    rfcRule: Rewrite.Rule,
    point: Term,
    witnesses: List[Term],
    which: Int,
    generalise: List[FVar]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      pieces <- disjunctsAt(logic, clauses, point)
      (clause, premise, first, second, third) = pieces
      chosen <- which match {
        case 1 => Right(first)
        case 2 => Right(second)
        case _ => Right(third)
      }

      opened <- nest(logic, chosen, witnesses)
      (levels, predicates) = opened
      body <- levels.lastOption.toRight(NotOfForm("an innermost body", chosen))

      // The same body with the closure named, which is the shape the caller's hypothesis is in.
      // Read off the rewriter rather than written out, so a change to the clause cannot leave this
      // function asking for a hypothesis the definition no longer implies.
      legible <- Rewrite.rewrite(Vector(rfcRule), body).flatMap(rightOf)

      // The clause's last conjunct is `w = <the point>`, and this rule supplies the point, so at
      // this instance it is `t = t`. Asking a consumer for it would be asking them to prove
      // reflexivity, so it is discharged here and the hypothesis that comes out is the rest.
      trimmed <- withoutTrailingReflexivity(logic, legible)
      (wanted, rebuild) = trimmed
      assumed <- LogicError.lift(Kernel.assume(wanted))
      complete <- rebuild(assumed)
      inClauseVocabulary <- Rewrite.inTheorem(Vector(unfoldRule), complete)
      reshaped <- reshape(body, inClauseVocabulary)

      closed <- close(logic, predicates, witnesses, reshaped)
      disjunction <- which match {
        case 1 => logic.mkDisj(second, third).flatMap(rules.disjIntro1(_, closed))
        case 2 => rules.disjIntro1(third, closed).flatMap(rules.disjIntro2(first, _))
        case _ => rules.disjIntro2(second, closed).flatMap(rules.disjIntro2(first, _))
      }

      shapedPremise <- shaped(premise, disjunction)
      inClosure <- rules.mp(clause, shapedPremise)
      named <- Rewrite.inTheorem(Vector(rfcRule), inClosure)

      result <- generalise.foldLeft(rules.disch(wanted, named)) { (accumulated, variable) =>
        accumulated.flatMap(rules.gen(variable, _))
      }
    } yield result
  }

  /**
   * The conversion back into the clause's vocabulary landed on the clause's own term, or it did
   * not and that is a defect worth a name rather than a repair.
   *
   * It refuses instead of trying harder on purpose. The two terms are the same clause written with
   * the closure named and unnamed, and the rewriter is given the equation that relates exactly
   * those two spellings, so a mismatch here means the clause says something the rewrite rule does
   * not reach. Patching it with a second conversion would hide which.
   */
  private def reshape(target: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    if (theorem.conclusion == target) Right(theorem)
    else Left(NotOfForm(s"the clause as the operator writes it, $target", theorem.conclusion))

  /** [[Inside]]: a step of `R` anywhere in a member lands in the closure. */
  private def insideRule(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    clauses: Kernel.Thm,
    unfoldRule: Rewrite.Rule,
    rfcRule: Rewrite.Rule
  ): Either[LogicError, Kernel.Thm] =
    for {
      source <- Parser.term(theory, notation, "u:word('a)", Words)
      landing <- Parser.term(theory, notation, "v:word('a)", Words)
      sourceVar <- asVariable(source)
      landingVar <- asVariable(landing)
      result <- disjunctRule(
        logic, clauses, unfoldRule, rfcRule, landing, List(source), which = 2,
        generalise = List(landingVar, sourceVar, System))
    } yield result

  /** [[Extend]]: a member ending in `a`, and a rule `a b -> r`, give the member with `r` for `a`. */
  private def extendRule(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    clauses: Kernel.Thm,
    unfoldRule: Rewrite.Rule,
    rfcRule: Rewrite.Rule
  ): Either[LogicError, Kernel.Thm] =
    for {
      prefix <- Parser.term(theory, notation, "p:word('a)", Words)
      head <- Parser.term(theory, notation, "a:word('a)", Words)
      tail <- Parser.term(theory, notation, "b:word('a)", Words)
      right <- Parser.term(theory, notation, "r:word('a)", Words)
      point <- Parser.term(theory, notation, "WORD_CONCAT (p:word('a)) (r:word('a))", Words)
      prefixVar <- asVariable(prefix)
      headVar <- asVariable(head)
      tailVar <- asVariable(tail)
      rightVar <- asVariable(right)
      result <- disjunctRule(
        logic, clauses, unfoldRule, rfcRule, point, List(prefix, head, tail, right), which = 3,
        generalise = List(rightVar, tailVar, headVar, prefixVar, System))
    } yield result

  /**
   * [[Induction]]: [[Inductive.Induction]] at this operator, in the shape a consumer writes.
   *
   * The general principle asks one thing, that the carrier is closed under the operator, and this
   * operator is a disjunction of three. A consumer given only the general principle would unfold
   * the definition and split that disjunction every time it reasoned about a member, so it is done
   * once here: three hypotheses go in as a conjunction and the disjunction is discharged inside.
   *
   * It asks **nothing of `R`**, and that is the asymmetry [[Inductive]] is built on rather than an
   * oversight: monotonicity is what an introduction rule costs and an induction principle is free.
   * So a non-membership is provable here without the operator being well behaved at all.
   */
  private def inductionPrinciple(
    logic: Logic,
    inductiveInduct: Kernel.Thm,
    operator: Term,
    unfolding: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      atWords <- Right(Kernel.instType(Map(Classical.TypeVariable -> Words), inductiveInduct))
      instance <- rules.specAll(atWords, List(operator, Carrier))
      parts <- impliesOf(instance.conclusion, logic)
      (rawPremise, _) = parts

      normalising <- Conv.betaNormalise(rawPremise)
      normal <- rightOf(normalising)
      stripped <- Logic.stripForall(normal)
      point <- stripped._1.lift(0).toRight(NotOfForm("a claim about every word", normal))
      clause <- impliesOf(stripped._2, logic)
      (antecedent, consequent) = clause
      outer <- disjunctsOf(antecedent, logic)
      (isRightSide, rest) = outer
      inner <- disjunctsOf(rest, logic)
      (hasSource, wasExtended) = inner

      // The three hypotheses a consumer supplies, each built from its own disjunct by binding the
      // disjunct's own witnesses and asking for the carrier at the point. Built from the clause
      // rather than parsed a second time, for the reason `Reaching` gives about a second parse.
      firstHypothesis <- closedUnder(logic, isRightSide, consequent, point)
      secondHypothesis <- closedUnder(logic, hasSource, consequent, point)
      thirdHypothesis <- closedUnder(logic, wasExtended, consequent, point)

      tailHypothesis <- logic.mkConj(secondHypothesis, thirdHypothesis)
      hypothesis <- logic.mkConj(firstHypothesis, tailHypothesis)

      assumed <- LogicError.lift(Kernel.assume(hypothesis))
      assumedFirst <- rules.conjElim1(assumed)
      assumedTail <- rules.conjElim2(assumed)
      assumedSecond <- rules.conjElim1(assumedTail)
      assumedThird <- rules.conjElim2(assumedTail)

      firstCase <- caseOf(logic, isRightSide, consequent, point, assumedFirst)
      secondCase <- caseOf(logic, hasSource, consequent, point, assumedSecond)
      thirdCase <- caseOf(logic, wasExtended, consequent, point, assumedThird)

      assumedRest <- LogicError.lift(Kernel.assume(rest))
      tailSplit <- rules.disjElim(assumedRest, secondCase, thirdCase)
      assumedAntecedent <- LogicError.lift(Kernel.assume(antecedent))
      split <- rules.disjElim(assumedAntecedent, firstCase, tailSplit)

      premiseProof <- rules.disch(antecedent, split).flatMap(rules.gen(point, _))
      shapedPremise <- shaped(rawPremise, premiseProof)
      everywhere <- rules.mp(instance, shapedPremise)

      specialised <- rules.spec(point, everywhere)
      rfcAt <- Conv.apThm(unfolding, point)
      rfcTerm <- Term.destEq(rfcAt.conclusion).map(_._1).toRight(NotOfForm("an equation", rfcAt.conclusion))
      assumedRfc <- LogicError.lift(Kernel.assume(rfcTerm))
      converted <- LogicError.lift(Kernel.eqMp(rfcAt, assumedRfc))
      inside <- rules.mp(specialised, converted)

      result <- rules
        .disch(rfcTerm, inside)
        .flatMap(rules.gen(point, _))
        .flatMap(rules.disch(hypothesis, _))
        .flatMap(rules.gen(Carrier, _))
        .flatMap(rules.gen(System, _))
    } yield result
  }

  /**
   * One disjunct turned into the hypothesis a consumer supplies for it.
   *
   * `disjunct ==> S w`, universally quantified over `w` and over whatever the disjunct binds. The
   * witnesses stay bound where the disjunct bound them, so a consumer discharging this case gets
   * them named rather than having to take an existential apart.
   */
  private def closedUnder(
    logic: Logic,
    disjunct: Term,
    consequent: Term,
    point: FVar
  ): Either[LogicError, Term] =
    for {
      body <- logic.mkImp(disjunct, consequent)
      quantified <- logic.mkForall(point, body)
    } yield quantified

  /** The consumer's hypothesis for one disjunct, applied to that disjunct assumed. */
  private def caseOf(
    logic: Logic,
    disjunct: Term,
    consequent: Term,
    point: FVar,
    hypothesis: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      assumed <- LogicError.lift(Kernel.assume(disjunct))
      instance <- logic.rules.spec(point, hypothesis)
      result <- logic.rules.mp(instance, assumed)
    } yield result

  /**
   * A conjunction whose last conjunct is a reflexive equation, minus that conjunct.
   *
   * Returns what a consumer is actually asked for, and the function that puts the conjunct back so
   * the clause still gets the shape it wants. Where the last conjunct is **not** a reflexive
   * equation the pair is the term unchanged and the identity, so the two callers that have nothing
   * to trim are unaffected and the trimming is not a special case anybody has to know about.
   *
   * Why it is here rather than left in the published statement: `WORD_RFC_EXTEND` came out of the
   * first build reading `... /\ WORD_CONCAT y v = WORD_CONCAT y v ==> ...`, which is true, is
   * useless, and asks a reader of `docs/lemmas.md` what that conjunct is protecting against. It is
   * protecting against nothing: the rule chooses the point.
   */
  private def withoutTrailingReflexivity(
    logic: Logic,
    conjunction: Term
  ): Either[LogicError, (Term, Kernel.Thm => Either[LogicError, Kernel.Thm])] = {
    val rules = logic.rules

    def split(term: Term): List[Term] = logic.destConj(term) match {
      case Some((left, right)) => left :: split(right)
      case None => List(term)
    }

    val conjuncts = split(conjunction)
    val last = conjuncts.last

    val isReflexive = Term.destEq(last).exists { case (left, right) => left == right }

    if (!isReflexive || conjuncts.sizeIs < 2) Right((conjunction, theorem => Right(theorem)))
    else {
      val kept = conjuncts.init
      val rebuilt = kept.reduceRight((left, right) => logic.mkConj(left, right).getOrElse(left))

      val rebuild: Kernel.Thm => Either[LogicError, Kernel.Thm] = assumed => {
        val reflexivity = Term.destEq(last).map(_._1).map(Conv.refl)

        def assemble(remaining: List[Term], proof: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          remaining match {
            case Nil => reflexivity.toRight(NotOfForm("an equation", last)).flatMap(rules.conjIntro(proof, _))
            case _ :: rest =>
              for {
                head <- rules.conjElim1(proof)
                tail <- rules.conjElim2(proof)
                behind <- assemble(rest, tail)
                joined <- rules.conjIntro(head, behind)
              } yield joined
          }

        if (kept.sizeIs == 1)
          reflexivity.toRight(NotOfForm("an equation", last)).flatMap(rules.conjIntro(assumed, _))
        else assemble(kept.tail, assumed)
      }

      Right((rebuilt, rebuild))
    }
  }
}
