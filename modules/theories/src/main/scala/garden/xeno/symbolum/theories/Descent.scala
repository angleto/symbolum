package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Definition by recursion where the step may consult **every** earlier value, not only the last.
 *
 * `Recursion` gives `fn (SUC n) = f (fn n) n`, which is the step reading one value back. A great
 * deal of arithmetic is not of that shape: the syntactic predicates a Goedel numbering needs are
 * all "this code is well formed if its parts, whose codes are smaller, are", and a part's code is
 * not the predecessor of the whole. What this holds is the theorem that covers those:
 *
 * {{{
 *   |- !H. (!u v n. (!m. NUM_LT m n ==> u m = v m) ==> H u n = H v n)
 *          ==> ?f. !n. f n = H f n
 * }}}
 *
 * `H` takes the whole function so far and the index, and the hypothesis is what makes that
 * legitimate: **`H` may only consult the values below `n`**. Two histories agreeing below `n` must
 * send `H` to the same answer. Without it the statement is false, `H u n = SUC (u n)` having no
 * fixed point at all, so the hypothesis is not bookkeeping and a reader should check it first.
 *
 * == It costs no axiom and no new primitive, which is the reason it was written now ==
 *
 * The session that scoped a Goedel development proposed building out `Word` first, on the argument
 * that a recursion consulting every earlier value needs somewhere to keep them and `word` is the
 * type that keeps them. **That argument is wrong and the measurement is this file.** The history
 * does not have to be a canonical object: it only has to answer at each index, so it can be a
 * function `num -> 'a`, and `Recursion.theorem` is polymorphic in the result type, so it can
 * produce one. `'a` instantiated to `num -> 'a` is the whole trick, and what is built by simple
 * recursion is the sequence of partial functions
 *
 * {{{
 *   h ZERO      = (\i. PAD)
 *   h (SUC n)   = (\i. COND (i = n) (H (h n) n) (h n i))
 * }}}
 *
 * each extending the last by one entry, with `f n = H (h n) n` read off the end. `Word` is not
 * used here and is not needed here. What `Word` buys is an object with **equality**, which a
 * development about the syntax of a formal language will want for other reasons; it is not on the
 * path to this theorem and the earlier scoping had it on the critical path.
 *
 * `NUM_LEAST` is not used either, and that was the second thing the same scoping got wrong. The
 * least number principle is what the *arguments* about descent need; the *definition* by descent
 * needs only induction, which is where `Induct` comes in.
 *
 * == What the derivation actually does ==
 *
 * One induction and one case split. The induction is [[Descent.AgreementText]],
 * `!i n. NUM_LT i n ==> h n i = H (h i) i`: every partial function agrees below its own index with
 * the answer. It is stated with `i` **first** so that the induction runs on `n` with `i` fixed,
 * which is what `Induct.proveBy` can drive: that driver inducts on the last leading quantifier and
 * generalises the others outside it, and a statement written `!n i. ...` would be inducted on `i`
 * and prove something else. The fixed `i` is enough, and checking that it is enough is the one
 * place a reader should slow down: at `SUC k` the induction hypothesis is needed at the same `i`
 * and at `k`, which is exactly what it gives.
 *
 * The case split is on `i = k`, by [[Classical.cases]] and not by the order, because what the
 * conditional in `h (SUC k)` tests is an equation and not an inequality. The branch where they
 * differ is where `NUM_LT_SUC_CASES` is spent, to turn `i < SUC k` into `i < k`.
 *
 * == Where it sits ==
 *
 * Beside the chain rather than in it, the way `Bounded` does and for the same reason: it declares
 * no constant and holds no lemma of its own, so it adds nothing to any signature and nothing to
 * `docs/lemmas.md`. What it publishes is one theorem, built on request, in the manner of
 * `Recursion.theorem` rather than of a development's `facts` map.
 *
 * It cannot live in `Recursion.scala`, which is below `Peano`: the statement mentions `NUM_LT`, and
 * the order on `num` is `Peano`'s. That is the whole reason this is a separate file.
 */
final class Descent private (
  val peano: Peano,
  val induct: Induct,
  val logic: Logic,
  val recursion: Kernel.Thm,
  val condTrue: Kernel.Thm,
  val condFalse: Kernel.Thm,
  val notBelowZero: Kernel.Thm,
  val belowSuccessorCases: Kernel.Thm
) {

  private val rules = logic.rules
  private val classical = peano.naturals.classical
  private val alpha = TyVar(Classical.TypeVariable)
  private val numbers = TyApp(Natural.TypeName, Nil)

  /** `num -> 'a`: a history, which answers at an index and is not an object with an equality. */
  private val histories = Type.fun(numbers, alpha)

  /**
   * The theorem, built once.
   *
   * `lazy` for the reason `Natural.recursion` is: it runs an induction and a case split over terms
   * that are not small, and not every caller of this class wants it.
   */
  lazy val theorem: Either[LogicError, Kernel.Thm] = derive()

  /** Read a proposition against this development's signature. */
  private def term(text: String): Either[LogicError, Term] =
    Parser.term(peano.theory, peano.notation, text)

  private def derive(): Either[LogicError, Kernel.Thm] =
    for {
      statement <- term(Descent.StatementText)
      stripped <- Logic.stripForall(statement)
      operator <- stripped._1.headOption.toRight(NotOfForm("a claim about every step", statement))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (admissible, existential) = parts
      assumedAdmissible <- LogicError.lift(Kernel.assume(admissible))

      start <- padding()
      step <- stepping(operator)

      atHistories = Kernel.instType(Map(Classical.TypeVariable -> histories), recursion)
      instance <- rules.specAll(atHistories, List(start, step))
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))

      predicate <- logic
        .destExistsPredicate(opened.conclusion)
        .toRight(NotOfForm("an existential", opened.conclusion))
      history = Conv.freshVariable(
        "h",
        Type.fun(numbers, histories),
        Term.freeVariables(statement) ++ Term.freeVariables(opened.conclusion)
      )
      applied <- LogicError.lift(Term.app(predicate, history))
      contraction <- Conv.betaRoot(applied)
      recurrence <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      assumedRecurrence <- LogicError.lift(Kernel.assume(recurrence))

      found <- withHistory(operator, history, assumedRecurrence, assumedAdmissible, existential)
      discharged <- rules.existsElim(opened, history, found)
      implied <- rules.disch(admissible, discharged)
      result <- rules.gen(operator, implied)

      // The statement as it is written, and not merely something that follows from the same work.
      // `Induct.proveBy` makes the same check for the same reason: a theorem about a variable the
      // reader did not see named is the failure this file would be least likely to notice.
      _ <-
        if (result.conclusion == statement) Right(())
        else Left(NotOfForm("the statement as it is written", result.conclusion))
    } yield result

  /** `\i:num. select (\x:'a. T)`: the history before anything is known, which nothing reads. */
  private def padding(): Either[LogicError, Term] = {
    val index = Term.variable("i", numbers)
    val anything = Term.variable("x", alpha)
    for {
      select <- classical.select(alpha)
      always <- LogicError.lift(Term.abs(anything, logic.truth))
      pad <- LogicError.lift(Term.app(select, always))
      start <- LogicError.lift(Term.abs(index, pad))
    } yield start
  }

  /** `\z n i. COND (i = n) (H z n) (z i)`: extend the history by the one entry `H` computes. */
  private def stepping(operator: FVar): Either[LogicError, Term] = {
    val carried = Term.variable("z", histories)
    val index = Term.variable("n", numbers)
    val at = Term.variable("i", numbers)
    for {
      conditional <- classical.conditional(alpha)
      test <- LogicError.lift(Term.eq(at, index))
      here <- LogicError.lift(Term.appAll(operator, List(carried, index)))
      earlier <- LogicError.lift(Term.app(carried, at))
      body <- LogicError.lift(Term.appAll(conditional, List(test, here, earlier)))
      step <- LogicError.lift(Term.absAll(List(carried, index, at), body))
    } yield step
  }

  /**
   * The whole argument, with the history in hand as a variable rather than as the chosen term.
   *
   * Through a variable because the alternative is `select` of the recurrence, which is a term
   * several lines long that then appears inside every rewrite below it. The existential is
   * eliminated by the caller, so nothing here is weaker for it.
   */
  private def withHistory(
    operator: FVar,
    history: FVar,
    recurrence: Kernel.Thm,
    admissible: Kernel.Thm,
    existential: Term
  ): Either[LogicError, Kernel.Thm] = {
    val index = Term.variable("n", numbers)
    for {
      extension <- rules.conjElim2(recurrence)
      agreement <- agreementBelow(operator, history, extension)

      // `\n. H (h n) n`, the function read off the ends of the histories. Left as a lambda, because
      // `Rules.existsIntro` wants the theorem over the unreduced application of the predicate to
      // this very term, and beta-reducing it here would have to be undone there.
      applied <- LogicError.lift(Term.app(history, index))
      body <- LogicError.lift(Term.appAll(operator, List(applied, index)))
      answer <- LogicError.lift(Term.abs(index, body))

      reached <- fixedPoint(operator, history, agreement, admissible, answer, index)
      everywhere <- rules.gen(index, reached)
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      found <- rules.existsIntro(predicate, answer, everywhere)
    } yield found
  }

  /**
   * `|- !i n. NUM_LT i n ==> h n i = H (h i) i`, by induction on `n` with `i` fixed.
   *
   * The base is vacuous and the step is the case split. Nothing here is about `H` beyond its being
   * applied, so admissibility is not used and is not available: this half is true of any step
   * function, and it is the next half that needs `H` to be blind above `n`.
   */
  private def agreementBelow(
    operator: FVar,
    history: FVar,
    extension: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val at = Term.variable("i", numbers)
    val bound = Term.variable("n", numbers)

    for {
      order <- LogicError.lift(
        peano.theory.constant(Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
      below <- LogicError.lift(Term.appAll(order, List(at, bound)))
      left <- LogicError.lift(Term.appAll(history, List(bound, at)))
      earlier <- LogicError.lift(Term.app(history, at))
      right <- LogicError.lift(Term.appAll(operator, List(earlier, at)))
      equation <- LogicError.lift(Term.eq(left, right))
      implication <- logic.mkImp(below, equation)
      inner <- logic.mkForall(bound, implication)
      statement <- logic.mkForall(at, inner)

      proved <- induct.proveBy(
        statement,
        goal => vacuousBelowZero(goal),
        step => agreementStep(operator, history, extension, step)
      )
    } yield proved
  }

  /** `NUM_LT i 0 ==> anything`: nothing is below zero, so the base costs one lemma. */
  private def vacuousBelowZero(goal: Term): Either[LogicError, Kernel.Thm] =
    for {
      parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
      (below, consequent) = parts
      argument <- below match {
        case App(App(_, left), _) => Right(left)
        case other => Left(NotOfForm("a comparison", other))
      }
      never <- rules.spec(argument, notBelowZero)
      assumed <- LogicError.lift(Kernel.assume(below))
      absurd <- rules.notElim(never, assumed)
      anything <- rules.falsityElim(consequent, absurd)
      result <- rules.disch(below, anything)
    } yield result

  /**
   * The step: `h (SUC k) i = H (h i) i` given the same at `k`, and given `i < SUC k`.
   *
   * Split on `i = k`, which is what the conditional tests. Where they are equal the entry is the
   * one just computed and the induction hypothesis is not used at all; where they differ the entry
   * is copied from `h k`, and `i < SUC k` has to be brought down to `i < k` before the hypothesis
   * applies, which is the one place the order is consulted.
   */
  private def agreementStep(
    operator: FVar,
    history: FVar,
    extension: Kernel.Thm,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] =
    for {
      parts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
      (below, equation) = parts
      sides <- Term.destEq(equation).toRight(NotOfForm("an equation", equation))
      (target, wanted) = sides
      at <- target match {
        case App(_, index) => Right(index)
        case other => Left(NotOfForm("the history applied to an index", other))
      }
      assumedBelow <- LogicError.lift(Kernel.assume(below))

      // `h (SUC k) i = COND (i = k) (H (h k) k) (h k i)`, which is the recurrence at this index.
      atSuccessor <- rules.spec(step.variable, extension)
      unfolded <- Conv.apThm(atSuccessor, at).flatMap(Conv.normaliseSides)
      conditional <- Term
        .destEq(unfolded.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", unfolded.conclusion))
      test <- conditional match {
        case App(App(App(_, proposition), _), _) => Right(proposition)
        case other => Left(NotOfForm("an application of COND to three arguments", other))
      }

      same <- agreementWhenEqual(operator, history, unfolded, conditional, test, wanted)
      differs <- agreementWhenApart(unfolded, conditional, test, wanted, assumedBelow, below, step)
      settled <- classical.cases(test, same, differs)
      result <- rules.disch(below, settled)
    } yield result

  /** The branch where the index is the one just computed: the conditional takes its first arm. */
  private def agreementWhenEqual(
    operator: FVar,
    history: FVar,
    unfolded: Kernel.Thm,
    conditional: Term,
    test: Term,
    wanted: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      assumedEqual <- LogicError.lift(Kernel.assume(test))
      arms <- conditional match {
        case App(App(App(_, _), here), _) => Right(here)
        case other => Left(NotOfForm("an application of COND to three arguments", other))
      }
      taken <- rules
        .specAll(condTrue, List(test, arms, elseArm(conditional)))
        .flatMap(rules.mp(_, assumedEqual))
      reduced <- Conv.trans(unfolded, taken)

      // `H (h i) i = H (h k) k`, which is what the conditional's first arm becomes when read
      // through `i = k`. Built by congruence rather than by a rewrite, so that what is carried is
      // exactly these two occurrences and nothing else that happens to match.
      carriedInner <- Conv.apTerm(history, assumedEqual)
      carried <- congruent(operator, carriedInner, assumedEqual)
      back <- Conv.sym(carried)
      result <- Conv.trans(reduced, back).flatMap(matching(wanted))
    } yield result

  /** `H (h i) i = H (h k) k` from `i = k`, both arguments carried at once. */
  private def congruent(
    operator: FVar,
    inner: Kernel.Thm,
    equal: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- Conv.apTerm(operator, inner)
      sides <- Term.destEq(equal.conclusion).toRight(NotOfForm("an equation", equal.conclusion))
      applied <- Conv.apThm(partial, sides._1)
      right <- Term
        .destEq(partial.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", partial.conclusion))
      moved <- Conv.apTerm(right, equal)
      result <- Conv.trans(applied, moved)
    } yield result

  /** The branch where the index is an earlier one: the conditional takes its second arm. */
  private def agreementWhenApart(
    unfolded: Kernel.Thm,
    conditional: Term,
    test: Term,
    wanted: Term,
    assumedBelow: Kernel.Thm,
    below: Term,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] =
    for {
      negation <- logic.mkNot(test)
      assumedApart <- LogicError.lift(Kernel.assume(negation))
      here <- conditional match {
        case App(App(App(_, _), arm), _) => Right(arm)
        case other => Left(NotOfForm("an application of COND to three arguments", other))
      }
      taken <- rules
        .specAll(condFalse, List(test, here, elseArm(conditional)))
        .flatMap(rules.mp(_, assumedApart))
      copied <- Conv.trans(unfolded, taken)

      at <- Term.destEq(test).map(_._1).toRight(NotOfForm("an equation", test))
      cases <- rules.specAll(belowSuccessorCases, List(step.variable, at)).flatMap(rules.mp(_, assumedBelow))
      disjuncts <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (strictly, equally) = disjuncts

      fromBelow <- LogicError
        .lift(Kernel.assume(strictly))
        .flatMap(rules.mp(step.hypothesis, _))
        .flatMap(hypothesis => Conv.trans(copied, hypothesis))
        .flatMap(matching(wanted))
      fromEqual <- for {
        assumedEqual <- LogicError.lift(Kernel.assume(equally))
        absurd <- rules.notElim(assumedApart, assumedEqual)
        anything <- rules.falsityElim(fromBelow.conclusion, absurd)
      } yield anything
      result <- rules.disjElim(cases, fromBelow, fromEqual)
    } yield result

  /** The third argument of a `COND` application. */
  private def elseArm(conditional: Term): Term = conditional match {
    case App(App(App(_, _), _), otherwise) => otherwise
    case other => other
  }

  /** Refuse a derivation that reached an equation other than the goal's. */
  private def matching(wanted: Term)(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Term.destEq(theorem.conclusion) match {
      case Some((_, right)) if right == wanted => Right(theorem)
      case _ => Left(NotOfForm("the value the goal asks for", theorem.conclusion))
    }

  /**
   * `|- (\m. H (h m) m) n = H (\m. H (h m) m) n`, which is the fixed point at `n`.
   *
   * The left side is left as a redex on purpose: `Rules.existsIntro` compares against the
   * unreduced application of the predicate to the witness, so a reduced left side here would have
   * to be expanded again there, and expanding is the direction with a choice in it.
   */
  private def fixedPoint(
    operator: FVar,
    history: FVar,
    agreement: Kernel.Thm,
    admissible: Kernel.Thm,
    answer: Term,
    index: FVar
  ): Either[LogicError, Kernel.Thm] =
    for {
      // `!m. NUM_LT m n ==> h n m = (\m. H (h m) m) m`, which is the agreement with the quantifiers
      // in the order admissibility wants them and the right side expanded back into a redex.
      swapped <- swapForAgreement(agreement, answer, index)
      here <- LogicError.lift(Term.app(history, index))
      instance <- rules
        .specAll(admissible, List(here, answer, index))
        .flatMap(implication => rules.mp(implication, swapped))
      applied <- LogicError.lift(Term.app(answer, index))
      contraction <- Conv.betaRoot(applied)
      result <- Conv.trans(contraction, instance)
    } yield result

  /**
   * Turn `!i n. NUM_LT i n ==> h n i = H (h i) i` into the instance admissibility asks for.
   *
   * Two things happen and both are mechanical: the quantifiers swap, since the induction was run
   * with the index fixed and admissibility quantifies the other way round, and the right side is
   * put back under the lambda, since admissibility is about the function and not about its values.
   */
  private def swapForAgreement(
    agreement: Kernel.Thm,
    answer: Term,
    index: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val at = Conv.freshVariable("m", numbers, Term.freeVariables(agreement.conclusion) + index)
    for {
      instance <- rules.specAll(agreement, List(at, index))
      parts <- logic.destImp(instance.conclusion).toRight(NotOfForm("an implication", instance.conclusion))
      (below, _) = parts
      assumedBelow <- LogicError.lift(Kernel.assume(below))
      value <- rules.mp(instance, assumedBelow)
      applied <- LogicError.lift(Term.app(answer, at))
      contraction <- Conv.betaRoot(applied)
      expanded <- Conv.sym(contraction)
      restated <- Conv.trans(value, expanded)
      implied <- rules.disch(below, restated)
      result <- rules.gen(at, implied)
    } yield result
  }
}

object Descent {

  /**
   * The theorem, as text, which is the form a reader compares against the informal statement.
   *
   * `H` is the step, taking the function built so far and the index. The hypothesis is the
   * admissibility condition and is the whole content of the statement: see the class comment for
   * what goes wrong without it.
   */
  val StatementText: String =
    "!H:(num -> 'a) -> num -> 'a. " +
      "(!u:num -> 'a. !v:num -> 'a. !n:num. " +
      "(!m:num. NUM_LT m n ==> u m = v m) ==> H u n = H v n) " +
      "==> (?f:num -> 'a. !n:num. f n = H f n)"

  /** The induction the derivation runs, named here so a failure can be read against it. */
  val AgreementText: String = "!i:num. !n:num. NUM_LT i n ==> h n i = H (h i) i"

  /** Build it over a development that has the order, and an induction driver to run. */
  def construct(peano: Peano, induct: Induct): Either[LogicError, Descent] = {
    val classical = peano.naturals.classical
    for {
      logic <- classical.logic.over(peano.theory)
      recursion <- peano.naturals.recursion
      condTrue <- classical.fact(Classical.CondTrue)
      condFalse <- classical.fact(Classical.CondFalse)
      notBelowZero <- peano.fact(Peano.NotBelowZero)
      belowSuccessorCases <- peano.fact(Peano.BelowSuccessorCases)
    } yield new Descent(
      peano,
      induct,
      logic,
      recursion,
      condTrue,
      condFalse,
      notBelowZero,
      belowSuccessorCases
    )
  }
}
