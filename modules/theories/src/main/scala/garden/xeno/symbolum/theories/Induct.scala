package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A statement about every natural number, proved by induction with a rewrite and a closer.
 *
 * The shape is always the same and it was written out by hand seven times in one consumer's file
 * before it was written once here. Point 2 of the card that asked for it lists the steps, and the
 * useful part of the list is which two of them go wrong silently:
 *
 *  - **using a fresh variable instead of the one the induction binds.** The step then proves a
 *    theorem about some number rather than the one asked for, and the mismatch surfaces several
 *    inferences later, where it reads as a different problem.
 *  - **the side condition on `gen`.** A variable free in a hypothesis cannot be generalised, and
 *    getting that wrong is a refusal whose message is about the wrong step.
 *
 * Fixing both once is most of what this is for. What it does otherwise is short: strip the leading
 * quantifiers that are not the number, instantiate induction at the predicate, rewrite each half
 * with the equations it was given, and hand what is left to the closer it was built with.
 *
 * **That closer was a `Ring` until 2026-09-15 and is now a parameter**, which is what lets this
 * driver be built below the reals. The field comment on it carries the measurement.
 *
 * == The separation that makes it work ==
 *
 * `Ring` does the algebra and the rewriter does the substitution, and neither does the other's job.
 * `Ring` has never heard of `Sum` or `Power`: an application it cannot take apart is an atom, which
 * is the right reading of a sum whose length is a variable, and it is why the step of a summation
 * by parts is a ring identity in the atoms `Sum g n`, `a n`, `a (SUC n)` and their neighbours.
 * Trying to make either of the two do the whole thing closes none of the goals this exists for.
 *
 * == Where it lives, and why not in `modules/tactics` ==
 *
 * The card proposed `modules/tactics`, which is the module that sees the algebra system as well.
 * Nothing here needs it: this is `Ring`, the rewriter and the induction theorem, all of which are
 * in the proof half. A tactic that also wanted the algebra system could call this; putting it there
 * would mean a development in `theories` could not.
 */
final class Induct private (
  val logic: Logic,
  /**
   * What finishes a goal the rewriting did not, and a parameter rather than a held `Ring`.
   *
   * It was a `Ring` until 2026-09-15, which made this driver unbuildable below the reals: four
   * developments that are entirely about `num`, `Modular`, `Coding`, `Numbering` and `Language`,
   * each thread a `Ring` through their own construction for no other purpose than to hand it here,
   * and every one of them uses [[proveBy]] alone and never reaches the closer at all.
   *
   * The measurement that turned that from a suspicion into a fact: `Ring.prove` refuses a goal of
   * type `num` **by type**, including one whose two sides are identical, so it never closed a step
   * about the naturals and could not have. `Peano`'s own stages take the induction skeleton from
   * [[proveBy]] and close with a normaliser of their own.
   *
   * So a caller over the reals passes `ring.prove` and a caller over `num` passes what it has,
   * which today is nothing: see [[Induct.overNaturals]] and the refusal it carries.
   */
  val closer: Term => Either[LogicError, Kernel.Thm],
  val induction: Kernel.Thm
) {

  private val rules = logic.rules

  /**
   * The statement, proved by induction over its **last** universal quantifier.
   *
   * The last rather than a named one, because that is where a claim about every number puts it:
   * `!a f g n. ...` is about `n`. The others are stripped and put back, so one function proves a
   * fact about one function and a fact about three.
   *
   * `equations` are the facts the rewriter may use on both halves: the recurrences that define
   * whatever the statement mentions, and any theorem already proved that the step needs. The
   * induction hypothesis is added to that list inside the step and nowhere else, which is the one
   * asymmetry between the two halves.
   */
  def prove(statement: Term, equations: Vector[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    Rewrite.Rule.all(logic, equations).flatMap(proveWith(statement, _))

  /** The same, for rules that have already been read, which is what a caller in a loop holds. */
  def proveWith(statement: Term, equations: Vector[Rewrite.Rule]): Either[LogicError, Kernel.Thm] =
    proveBy(
      statement,
      goal => settle(equations)(goal, Vector.empty),
      step =>
        Rewrite.Rule
          .of(logic, step.hypothesis)
          .flatMap(rule => settle(equations)(step.goal, Vector(rule)))
    )

  /**
   * Rewrite a goal with the rules given and close what is left with this driver's closer.
   *
   * Public because it is what a caller writing its own step wants to reach for, and because the
   * default step is one line of it: there is no reason to make somebody re-derive it in order to
   * add one waypoint to it.
   *
   * == `extra` goes first, and it is not a preference ==
   *
   * `Rewrite.stepConv` is a depth conversion over `firstConv`, so on any one node the first rule
   * that applies wins. `extra` is the induction hypothesis and nothing else in any caller here, and
   * its left side is the goal's own subterm at the variable the driver just opened: it is the most
   * specific rule in the step by construction. A recurrence that unfolds the same node is more
   * general, and putting it first takes the redex apart before the hypothesis can see it, which
   * leaves a goal with no link at all to the step before.
   *
   * Measured rather than argued. Summation by parts over a run-length form,
   *
   * {{{
   *   !i. Z (SUC i) = P i * Y i
   *      |- !k. Sum (\i. Z i - Y i) (SUC k) = Z ZERO - Y k + Sum (\i. Y i * (P i - 1)) k
   * }}}
   *
   * was refused with `equations ++ extra` and is proved with `extra ++ equations`, from the same
   * three rules. The refusal named a residue carrying `Sum f k` and `Sum g k` with nothing between
   * them, which is the hypothesis having never fired, reported as a false identity. Found by a
   * consumer, which wrote its own step to get round it.
   *
   * == The same symptom, two more causes ==
   *
   * That residue -- the two sides of the step with nothing of the step before between them -- is
   * what a reader sees whenever the hypothesis did not fire, and the ordering above is only one of
   * the ways that happens. Both of the others were met writing lemmas in this file, and both print
   * something that reads as a false claim about the algebra.
   *
   * **A rule that is MISSING rather than mis-ordered.** `SUM_GEOMETRIC` is
   * `(q - 1) * Sum (\i. Power q i) n = Power q n - 1`. Its step rewrites to
   * `(q - 1) * (Sum f n + Power q n) = q * Power q n - 1`, and the hypothesis's left side,
   * `(q - 1) * Sum f n`, is not a subterm of that at all: the scalar multiplies the whole of the
   * extended sum. No ordering reaches it, because there is nothing to reach. What closes it is
   * DISTRIBUTIVITY, `a * (b + c) = a * b + a * c`, added to the rule set -- and not because
   * anything needs deciding, since `Ring` would decide that equation in one line. It is there for
   * SHAPE: it moves the scalar onto each summand and so puts the hypothesis's left side where the
   * rewriter can see it. **A decision procedure cannot supply a shape.** When the hypothesis has
   * nowhere to match, a stronger closer is not the answer and a rewrite is.
   *
   * [[proveAssuming]] is the other way out of that, and it is not available to every caller: it
   * hands the hypothesis over as a FACT and asks the closer for an implication, which `Ring` does
   * not read. `Ring.prove` takes an equation and refuses an arrow, so a step closing with `Ring`
   * has the rule set and nothing else.
   *
   * **An ARITHMETIC rule that is missing, one layer further down.** `POWER_NEG_DOUBLE` is stated at
   * `NUM_ADD n n`, and its step meets `NUM_ADD (SUC n) (SUC n)`. With `NUM_ADD_ZERO` and
   * `NUM_ADD_SUC` alone the rewriting peels the RIGHT successor and stalls at `NUM_ADD (SUC n) n`,
   * where the hypothesis's exponent `NUM_ADD n n` never appears; `NUM_SUC_ADD` peels the left one
   * and the step closes. The refusal names a term that looks like the algebra failing and is a
   * rewrite rule that was not supplied.
   */
  def settle(equations: Vector[Rewrite.Rule])(
    goal: Term,
    extra: Vector[Rewrite.Rule]
  ): Either[LogicError, Kernel.Thm] =
    Induct.afterRewriting(extra ++ equations, goal)(closer)

  /**
   * The same driver where the step is an **inequality**, which `Ring` cannot close and `settle`
   * therefore could not drive.
   *
   * The asymmetry is not in the rewriting, it is in what the induction hypothesis is **for**.
   * [[proveWith]] hands the hypothesis to the step as a rewrite rule, which is right for an equation
   * and impossible for anything else: `Sum f n <= Sum g n` is not a rule and `Rule.of` says so. Here
   * it is handed over as a **fact**: the step goal is rewritten, the hypothesis is put on the left of
   * an arrow in front of it, the closer is asked for that implication, and modus ponens takes the
   * hypothesis back off.
   *
   * `close` is the caller's procedure and is LINARITH in every use so far. A step needing more than
   * the hypothesis — the positivity of a power, typically — is outside this and belongs in
   * [[proveBy]], where the caller writes the step and can derive whatever it needs from the goal it
   * is handed.
   *
   * Found on the Collatz conversion audit, which reported "the induction driver proves only
   * EQUATIONS" as one of its blockers.
   */
  def proveAssuming(statement: Term, equations: Vector[Kernel.Thm])(
    close: Term => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    Rewrite.Rule.all(logic, equations).flatMap { rewrites =>
      proveBy(
        statement,
        goal => Induct.afterRewriting(rewrites, goal)(close),
        step =>
          Induct.afterRewriting(rewrites, step.goal) { rewritten =>
            for {
              implication <- logic.mkImp(step.hypothesis.conclusion, rewritten)
              proved <- close(implication)
              result <- rules.mp(proved, step.hypothesis)
            } yield result
          }
      )
    }

  /**
   * The induction itself, with the two halves left to the caller.
   *
   * What [[proveWith]] cannot do, and the reason the card that asked for this proposed a list of
   * waypoints: **the induction hypothesis has to be usable as a rewrite**, so its left side has to
   * be a subterm of the step goal. `!n. Sum f n = Power 2 n - 1` has that shape and
   * `!n. Sum f n + 1 = Power 2 n` does not, and they are the same statement. When the second is the
   * one somebody wants stated, the step is a chain: reach a waypoint with `Ring`, leave it by
   * rewriting with the hypothesis or with a theorem already proved, and go on.
   *
   * The two halves arrive here rather than being described in advance, because a caller cannot
   * name the variable the step is about: the driver opens the quantifier itself and the variable is
   * fresh.
   *
   * == And the step is told what that variable is ==
   *
   * It was not until 2026-09-11, and the paragraph above is the reason the omission was easy to
   * miss: it argues correctly that a caller cannot name the variable, and then does not hand it
   * over. A step that has to **build** a term over it — instantiate a lemma, name an atom, derive a
   * ground fact — had to dig it back out of the hypothesis, and every caller in this repository
   * does exactly that by matching on the goal's shape.
   *
   * What makes it a defect rather than an inconvenience is how it fails. A step that guesses the
   * letter the caller wrote in the statement builds terms that simply do not occur in the goal;
   * nothing complains there, and the refusal arrives later from another procedure with a message
   * about the merits. A consumer met it twice in one day and reported it as two different
   * problems, one of them as LINARITH accusing its own reader.
   *
   * It is the first of the two silent mistakes this file's own opening lists, standing on the
   * interface after being fixed on the inside.
   */
  def proveBy(
    statement: Term,
    base: Term => Either[LogicError, Kernel.Thm],
    step: Induct.Step => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    for {
      stripped <- Logic.stripForall(statement)
      variables = stripped._1
      number <- variables.lastOption.toRight(NotOfForm("a claim about every number", statement))
      others = variables.dropRight(1)

      predicate <- LogicError.lift(Term.abs(number, stripped._2))
      instance <- rules.spec(predicate, induction)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic.destImp(opened.conclusion).toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      provedBase <- base(baseTerm)

      stepStripped <- Logic.stripForall(stepTerm)
      k <- stepStripped._1.headOption.toRight(NotOfForm("a claim about every number", stepTerm))
      stepParts <- logic.destImp(stepStripped._2).toRight(NotOfForm("an implication", stepStripped._2))
      (before, after) = stepParts
      assumed <- LogicError.lift(Kernel.assume(before))
      reached <- step(Induct.Step(after, assumed, k))
      provedStep <- rules.disch(before, reached).flatMap(rules.gen(k, _))

      everywhere <- rules.conjIntro(provedBase, provedStep).flatMap(rules.mp(opened, _))
      result <- rules.genAll(everywhere, others.toList)

      // The statement as written, not merely something that follows. A driver that returned a
      // theorem about a variable the caller did not name would be the first of the two silent
      // mistakes above, surviving into the caller's hands.
      _ <-
        if (result.conclusion == statement) Right(())
        else Left(NotOfForm("the statement as it is written", result.conclusion))
    } yield result
  }
}

object Induct {

  /**
   * What the driver opened for the step to work on.
   *
   * A record rather than three arguments, because the reason it exists is that a caller cannot see
   * inside the driver, and the next thing the step turns out to need should be added here rather
   * than by changing the shape of every step in the repository a second time.
   *
   * `variable` is the one the induction is on, freshened by `Logic.stripForall` against everything
   * free in the statement. The other quantified variables are freshened too and stay free in
   * `goal`, which is where a step that needs one reads it off; they are not carried here because no
   * caller has needed them by name and this is not the place to guess at that.
   */
  final case class Step(goal: Term, hypothesis: Kernel.Thm, variable: FVar)

  /**
   * Rewrite a goal with the rules given and close what is left with something.
   *
   * Static and here rather than on the class, because it uses none of what a class instance holds:
   * the rewriting is the rules', the closing is the caller's, and the induction theorem takes no
   * part. It was written twice before 2026-09-11, once as `Induct.settle` with `Ring` fixed and once
   * inside `Series` as `afterRewriting` with the closer handed over, and the two agreed, which is
   * the state in which a duplicate is hardest to notice.
   *
   * == The question it asks after the closer refuses ==
   *
   * `Rewrite.rewrite` returns the theorem it had built when the step limit ran out, and that theorem
   * is true: nothing in it says whether the rewriting had finished. So a step whose rules do not
   * settle looks exactly like a step whose claim is false, and the caller is sent to check something
   * that was never the problem. Asked only after the refusal, because that is where the answer
   * changes what the refusal means, and it costs one more pass of the conversion.
   */
  def afterRewriting(rules: Vector[Rewrite.Rule], goal: Term)(
    close: Term => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      equation <- Rewrite.rewrite(rules, goal)
      rewritten <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", goal))

      proved <- close(rewritten).left.flatMap { refusal =>
        Rewrite
          .finished(rules, rewritten)
          .flatMap(settled => if (settled) Left(refusal) else Left(NotNormalised(rewritten)))
      }

      backwards <- Conv.sym(equation)
      result <- LogicError.lift(Kernel.eqMp(backwards, proved))
    } yield result

  /**
   * Over a development that has the naturals and the reals in one signature.
   *
   * The order matters and it is the chain's business rather than this one's: `Chain` builds it, and
   * its comment says why the naturals come first.
   */
  def construct(naturals: Natural, ring: Ring): Either[LogicError, Induct] =
    for {
      logic <- naturals.classical.logic.over(ring.reals.theory)
      induction <- naturals.fact(Natural.Induction)
    } yield new Induct(logic, ring.prove, induction)

  /** Over a logic and an induction theorem chosen by the caller, closing with `Ring`. */
  def apply(logic: Logic, ring: Ring, induction: Kernel.Thm): Induct =
    new Induct(logic, ring.prove, induction)

  /** The same, for a caller that holds a closer of its own rather than a `Ring`. */
  def withCloser(
    logic: Logic,
    closer: Term => Either[LogicError, Kernel.Thm],
    induction: Kernel.Thm
  ): Induct =
    new Induct(logic, closer, induction)

  /**
   * The driver over `num` alone, which has no algebraic closer and says so.
   *
   * Every consumer of this driver below the reals uses [[Induct.proveBy]] and writes its own two
   * halves, so the closer is never reached; what this refuses to do is let a caller believe
   * otherwise. Handing it `Ring.prove` would be worse than refusing: `Ring` refuses a goal of type
   * `num` by type, so [[Induct.settle]] would fail on every step with a message about the wrong
   * thing.
   *
   * When a decision procedure for the identities of `num` can be built below the reals, it goes
   * here and this factory stops refusing. `Semiring` is that procedure and cannot be used: it is
   * built **over** `Peano`, so a `Peano` built over it is a cycle.
   */
  def overNaturals(logic: Logic, induction: Kernel.Thm): Induct =
    new Induct(logic, goal => Left(NoCloser(goal, "the induction driver over num")), induction)
}
