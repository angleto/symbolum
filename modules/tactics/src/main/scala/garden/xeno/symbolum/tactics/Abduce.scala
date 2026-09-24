package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Farkas, Linarith, LinearFact, LinearForm, Numeral, Rational, Real, RealTheory, Region}

/**
 * What would have to be assumed for a claim to follow, when it does not.
 *
 * The question a hostile reviewer asks. `Linarith` answers whether a conclusion follows and
 * `Refutation` answers where it fails; neither answers what is missing, and that is the one an
 * author acts on. Given premises that do not give the conclusion, this proposes propositions that
 * would, and **proves that each one does** before reporting it.
 *
 * == Why this is not the conjecture generator ==
 *
 * `docs/evaluation.md` argues, and keeps arguing, that pointing a model at `Discovery.identities`
 * is not on the list of steps: the fragment that gets certified is decidable and exhausted, so a
 * candidate that survives screening and gets certified carries no information about novelty, and
 * the expected number of new theorems is zero. That argument is about **generation**, and this is
 * not generation. Nothing here proposes a theorem for the kernel to bless. It answers a question
 * about an argument somebody already wrote, which is the family the same document says the return
 * is in, beside deciding a premise set, exhibiting the point that refutes an entailment, and
 * naming the premises a proof rests on.
 *
 * == The proposal is untrusted and the check is not ==
 *
 * Candidates are guessed from the shape of the goal. Each is then put back to `Linarith` as a real
 * premise, and only a candidate that makes the goal provable is reported. A bad guess costs a
 * refusal, which is the same arrangement the certificate search runs on one level down.
 *
 * == The one way this could mislead, and what stops it ==
 *
 * A premise that contradicts the premises already there makes **every** conclusion follow, so it
 * passes the check above while answering nothing. The prototype of this file proposed `x < 0` as
 * the missing premise for a goal that already assumed `0 < x`, which is exactly that failure
 * wearing the face of an answer. So every candidate that survives the proof is put to
 * `Refutation.satisfying` with the premises it joins, and one that leaves them unsatisfiable is
 * reported as [[Abduce.Gap.vacuous]] and never as something to assume.
 *
 * **That check answers a good deal less often than this paragraph used to imply**, and until
 * 2026-09-11 the difference was invisible because the code read a decline as a pass.
 * `Refutation.satisfying` has five answers here and only two of them decide anything: a point where
 * the premises hold, or a proof that no point does. The other three say the question was not
 * settled, and on miniF2F they were the majority on 2026-09-11 — 275 of the 422 candidates that
 * closed a goal. A candidate under one of those is [[Abduce.Gap.unchecked]], which is neither an
 * answer nor a warning but the absence of both, and the field's own docstring carries the
 * measurement.
 *
 * The four are kept apart for the reason `Refutation` keeps seven outcomes apart.
 *
 * == The other answer that is not one ==
 *
 * A candidate that proves the conclusion **on its own**, without the premises taking any part, is
 * the conclusion wearing the face of a premise. Assuming it is assuming what was to be shown, and
 * it passes every check above: it closes the goal, and it contradicts nothing. Measured on
 * 2026-09-10, `x < 1 ==> 0 < x` came back proposing `0 < x`, which is its own conclusion. Such a
 * candidate is reported as [[Abduce.Gap.circular]] and never as something to assume, for the same
 * reason [[Abduce.Gap.vacuous]] exists: an answer that cannot be acted on has to be told from one
 * that can.
 *
 * == What it cannot propose ==
 *
 * The candidate language is a bound on a **linear form the goal already writes**: `k < e` and
 * `e < k`, for `e` a variable or a side of one of the goal's relations, and `k` a numeral the goal
 * mentions, or zero. A bound on a combination is in the language since 2026-09-10 and was not
 * before, which mattered because that is the shape a missing premise often has.
 *
 * Two things are still outside it. `x <= y ==> x < y` gets nothing, because what it needs is
 * `~(x = y)`, which is not a bound at all. And the bound itself is drawn from the goal rather than
 * computed, so a goal needing `x + y <= 9` is answered only if it happens to mention nine: the
 * exact bound is the value of a linear program over the region the goal fails in, which this does
 * not solve. Reporting nothing is the right answer in both cases: a tool that widened the language
 * until it always found something would be guessing, and a guess presented as the missing premise
 * is worse than silence.
 */
final class Abduce private (val linarith: Linarith, val refutation: Refutation) {

  val reals: RealTheory = linarith.reals

  import Abduce.*

  /** What is missing, for a goal written in the theory's notation. */
  def missing(text: String): Either[TacticError, Gap] =
    TacticError.lift(reals.proposition(text)).flatMap(missing)

  /**
   * What is missing, for a goal that does not follow.
   *
   * A goal that already follows is refused rather than answered with an empty list, because
   * "nothing is missing" and "nothing was found" are opposite answers and an empty list reads as
   * the second.
   */
  def missing(goal: Term): Either[TacticError, Gap] =
    for {
      _ <-
        if (linarith.prove(goal).isLeft) Right(())
        else
          Left(
            FromLogic(
              NotOfForm("a goal that does not follow; this one already does", goal)
            )
          )

      opened <- TacticError.lift(Logic.stripForall(goal))
      shape = split(opened._2)

      candidates = proposals(opened._2, shape)
      judged = candidates.map(candidate => (candidate, judge(shape, candidate)))
      witness = pointOf(shape)
    } yield Gap(
      point = witness,
      // A point among values the model computes exactly is a refutation and not a sample, and the
      // caller is told which it is rather than being left to guess from the shape of the claim.
      decisive =
        witness.isDefined && refutation.exactly(shape.hypotheses :+ shape.conclusion),
      found = weakest(shape, judged.collect { case (candidate, Verdict.Closes) => candidate }),
      vacuous = judged.collect { case (candidate, Verdict.Contradicts) => candidate },
      circular = weakest(shape, judged.collect { case (candidate, Verdict.Circular) => candidate }),
      // Not through [[weakest]], and for the reason its own docstring gives for keeping `vacuous`
      // out of it: comparing candidates with each other assumes the premises they join are
      // satisfiable, since under impossible premises every candidate implies every other and the
      // list collapses onto whichever came first. These are the candidates nobody knows that
      // about. It is also where the cost was: `mathd_numbertheory_234` spent 111 seconds in this
      // file, of which about eleven were the candidates and the rest was a quadratic comparison
      // over twenty-five candidates that should never have reached it.
      unchecked = judged.collect { case (candidate, Verdict.Unchecked) => candidate }
    )

  /* ------------------------------------------------------------------- the candidates */

  /**
   * A bound on a linear form the goal writes, against zero and against every numeral it mentions.
   *
   * Both halves are drawn from the goal rather than from a fixed list, which is what keeps this
   * from guessing: a goal about thirds proposes a bound at three and a goal about percentages
   * proposes one at a hundred, and a goal that writes `x + y` proposes bounds on `x + y`.
   *
   * **The forms are the variables and the sides of the goal's relations**, so `x + y + z <= 12`
   * offers `x + y + z` and, through the sum inside it, `x + y`. Until 2026-09-10 the forms were the
   * variables alone, and a missing premise that is a relation between two quantities could not be
   * proposed at all, which is the shape one usually has. A side that is already a variable or a
   * numeral adds nothing and is dropped, so the language grows by the combinations and by nothing
   * else.
   *
   * What this costs is one pass of the checks below per candidate, and the candidates are the forms
   * times the bounds times two. Measured on 2026-09-10, warm, single runs, so read them as orders
   * of magnitude: `x + y <= 10 /\ z <= 3 ==> x + y + z <= 12` has three variables and two
   * combinations, so it goes from 24 candidates to 40, and from 70 ms to 212 ms. A goal with no
   * combination in it is unchanged, 6.1 ms against 6.7 ms on `0 < x ==> 0 < x * y`. The widening is
   * paid at the size of the goal and not at the size of the search, and it is paid only by a goal
   * that writes a combination. Rather more than the ratio of the candidate counts, because the
   * survivors are compared with each other and there are now more of them to compare.
   */
  private def proposals(body: Term, shape: Shape): Vector[Term] = {
    val variables = Term.freeVariables(body).toVector.sortBy(_.name)
    val combinations = (shape.hypotheses :+ shape.conclusion)
      .flatMap(sidesIn)
      .filter(side => Numeral.valueOf(reals, side).isEmpty && !variables.contains(side))
      .distinct
    val forms = variables ++ combinations

    regionOf(shape) match {
      case Some(region) => forms.flatMap(form => solvedBounds(region, form))
      case None => drawnBounds(body, forms)
    }
  }

  /**
   * A bound at the value the linear program says, rather than at a numeral the goal happens to
   * write.
   *
   * This is the difference between proposing candidates and **solving for the missing premise**.
   * The region where the premises hold and the conclusion fails is a polyhedron; a premise `c < f`
   * closes the goal exactly when no point of that region has `f > c`, which is to say exactly when
   * `c` is at or above the supremum of `f` there. So there is one weakest candidate of that shape
   * and the simplex computes it.
   *
   * Measured on 2026-09-11, before this existed: `0 < x /\ 3 * y < 2 ==> y < x` was offered
   * `2 < x`, which closes it and is stronger than the truth by an unbounded amount, because the
   * threshold is two thirds and two thirds is not a numeral the goal writes. `2 * x < 5 ==> x < y`
   * was offered `5 < y` where `5 <= 2 * y` is what is needed. Five of six goals in that measurement
   * were offered something strictly stronger than necessary.
   *
   * **Both strictnesses are offered and the check decides between them.** `f > sup` always closes;
   * `f >= sup` closes exactly when the supremum is not attained on the region, which is a question
   * about a single point and is answered by the same machinery that judges every other candidate.
   * Deciding it here would be a second implementation of a question already answered next door.
   *
   * A threshold of `p / q` is written `p < q * f` rather than as a fractional literal, because the
   * numerals of this theory are integers and a fractional one is refused by name.
   */
  private def solvedBounds(region: Vector[LinearFact], term: Term): Vector[Term] =
    LinearForm.of(reals, term).toOption.toVector.flatMap { form =>
      val above = Region.largest(region, form) match {
        case Farkas.Extreme.At(value) => scaled(value, term, form = true)
        case _ => Vector.empty
      }
      val below = Region.largest(region, -form) match {
        case Farkas.Extreme.At(value) => scaled(-value, term, form = false)
        case _ => Vector.empty
      }
      above ++ below
    }

  /**
   * `p < q * f` and `p <= q * f` for a threshold `p / q`, or the same with the sides swapped.
   *
   * `q` is positive because a `Rational` keeps its sign on the numerator, so multiplying through by
   * it does not turn the relation round.
   */
  private def scaled(threshold: Rational, term: Term, form: Boolean): Vector[Term] = {
    val scaledTerm =
      if (threshold.denominator == 1) Some(term)
      else multiply(threshold.denominator, term)

    (numeral(threshold.numerator), scaledTerm) match {
      case (Some(bound), Some(scaled)) =>
        val (left, right) = if (form) (bound, scaled) else (scaled, bound)
        Vector(relation(Real.Order, left, right), relation(Real.NonStrictOrder, left, right)).flatten
      case _ => Vector.empty
    }
  }

  /**
   * The region where the premises hold and the conclusion does not, as linear facts.
   *
   * `None` when any premise or the conclusion is not one of the three relations over the reals, or
   * when the conclusion is an equality: denying `a = b` is a disjunction and this file has one
   * region, not two. Such a goal falls back to [[drawnBounds]], which asks nothing about shape.
   */
  private def regionOf(shape: Shape): Option[Vector[LinearFact]] = {
    val premises = shape.hypotheses.map(LinearFact.relation(reals, _))

    for {
      _ <- Option.when(premises.forall(_.isRight))(())
      conclusion <- LinearFact.relation(reals, shape.conclusion).toOption
      denial <- conclusion.kind match {
        case LinearFact.Kind.Strict => Some(LinearFact(LinearFact.Kind.NonStrict, -conclusion.form))
        case LinearFact.Kind.NonStrict => Some(LinearFact(LinearFact.Kind.Strict, -conclusion.form))
        case LinearFact.Kind.Equal => None
      }
    } yield premises.collect { case Right(fact) => fact } :+ denial
  }

  /**
   * A bound on a form against zero and against every numeral the goal mentions.
   *
   * What this file did for every goal until 2026-09-11 and now does only where the region is not a
   * linear one: a goal with a premise this reader cannot take apart, or one concluding an equality.
   * The bounds are drawn from the goal rather than from a fixed list, which is what kept it from
   * guessing, and it is still what keeps it from guessing here.
   */
  private def drawnBounds(body: Term, forms: Vector[Term]): Vector[Term] = {
    val bounds = (BigInt(0) +: numeralsIn(body)).distinct.sorted

    for {
      form <- forms
      bound <- bounds
      proposition <- Vector(below(bound, form), below(form, bound)).flatten
    } yield proposition
  }

  /** A numeral, negated where it has to be, since the numerals of this theory are non-negative. */
  private def numeral(value: BigInt): Option[Term] =
    if (value >= 0) Numeral.of(reals, value).toOption
    else
      for {
        magnitude <- Numeral.of(reals, -value).toOption
        negation <- reals.theory
          .constant(Real.Negation, Type.fun(Real.realType, Real.realType))
          .toOption
        applied <- Term.app(negation, magnitude).toOption
      } yield applied

  private def multiply(factor: BigInt, term: Term): Option[Term] =
    for {
      numeral <- numeral(factor)
      constant <- reals.theory
        .constant(
          Real.Multiplication,
          Type.fun(Real.realType, Type.fun(Real.realType, Real.realType))
        )
        .toOption
      applied <- Term.appAll(constant, List(numeral, term)).toOption
    } yield applied

  private def relation(name: String, left: Term, right: Term): Option[Term] =
    for {
      constant <- reals.theory
        .constant(name, Type.fun(Real.realType, Type.fun(Real.realType, Type.Bool)))
        .toOption
      applied <- Term.appAll(constant, List(left, right)).toOption
    } yield applied

  /**
   * Both sides of every relation and every arithmetic operator over the reals, at any depth.
   *
   * Taken by shape rather than by naming the constants, because what makes a term a side here is
   * that it is an argument of a two-place application between reals, and a theory of one's own may
   * have declared the operator. Recursion continues through a match rather than stopping at it,
   * which is what turns `x + y + z` into that form and `x + y` both.
   *
   * **It stops at a binder**, and both reasons matter. A side underneath one mentions a variable
   * that does not exist outside it, so it could never be offered as a premise: what came back would
   * be an open term the caller cannot state. And asking the kernel for its type is not a mistake
   * that shows up as a bad candidate, it is `KernelInvariantViolation` thrown out of a tactic that
   * is supposed to refuse; `Term.typeOf` is total on closed terms only, and a loose index is what a
   * body under a binder is made of. `Logic.stripForall` takes the leading quantifiers off and a
   * nested one stays, so this is reached by any goal with a quantifier inside it: `?y. !x. x < y`
   * did, before the case below was written.
   *
   * The closedness guard on the sides is not made redundant by that case. It is what makes the
   * function total on whatever it is handed rather than on whatever the one caller happens to hand
   * it, and the argument from the caller is the one that was true here until a nested quantifier
   * arrived.
   */
  private def sidesIn(term: Term): Vector[Term] = term match {
    case App(App(Const(_, _), left), right)
        if Term.isLocallyClosed(left) && Term.isLocallyClosed(right) &&
          Term.typeOf(left) == Real.realType && Term.typeOf(right) == Real.realType =>
      Vector(left, right) ++ sidesIn(left) ++ sidesIn(right)
    case App(function, argument) => sidesIn(function) ++ sidesIn(argument)
    case Abs(_, _) => Vector.empty
    case _ => Vector.empty
  }

  private def numeralsIn(term: Term): Vector[BigInt] = term match {
    case _ if Numeral.valueOf(reals, term).isDefined =>
      Numeral.valueOf(reals, term).toVector
    case App(function, argument) => numeralsIn(function) ++ numeralsIn(argument)
    case Abs(_, body) => numeralsIn(body)
    case _ => Vector.empty
  }

  private def below(left: BigInt, right: Term): Option[Term] =
    Numeral.of(reals, left).flatMap(order(_, right)).toOption

  private def below(left: Term, right: BigInt): Option[Term] =
    Numeral.of(reals, right).flatMap(order(left, _)).toOption

  private def order(left: Term, right: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(
        reals.theory.constant(
          garden.xeno.symbolum.theories.Real.Order,
          Type.fun(Real.realType, Type.fun(Real.realType, Type.Bool))
        )
      )
      applied <- LogicError.lift(Term.appAll(constant, List(left, right)))
    } yield applied

  /* -------------------------------------------------------------------- the verdicts */

  private enum Verdict {
    case Closes, Contradicts, Circular, Unchecked, Useless
  }

  /**
   * Whether a candidate closes the goal, and whether it closes it for nothing.
   *
   * The order is the point. A candidate that contradicts the premises proves the goal, so asking
   * "does it prove the goal" first and stopping there would report it as an answer. Satisfiability
   * is asked of exactly the premises the candidate would join, which is the set the author would
   * end up holding.
   *
   * **And the answer to that question has three values, not two.** `Contradictory` says the
   * premises cannot all hold; `Found` and `Solved` produce a point at which they do; everything
   * else says the question was not settled, and a candidate under one of those is
   * [[Verdict.Unchecked]] rather than an answer. Matching `Contradictory` against a default case
   * put the third group with the second until 2026-09-11, and [[Abduce.Gap]] carries the
   * measurement of what that cost.
   */
  private def judge(shape: Shape, candidate: Term): Verdict = {
    val premises = shape.hypotheses :+ candidate

    val closes = (for {
      antecedent <- conjoin(premises)
      goal <- reals.logic.mkImp(antecedent, shape.conclusion)
      proved <- linarith.prove(goal)
    } yield proved).isRight

    if (!closes) Verdict.Useless
    else
      refutation.satisfying(premises) match {
        case Refutation.Contradictory(_) => Verdict.Contradicts

        // The circular test is asked only where the premises are known to stand up, because it
        // reads as a statement about the argument: "your candidate is your conclusion" presumes
        // there is an argument left to make. Under premises nobody has checked it would be a
        // second claim on top of an unchecked one.
        case Refutation.Found(_, _) | Refutation.Solved(_, _) =>
          if (alone(candidate, shape.conclusion)) Verdict.Circular else Verdict.Closes

        case _ => Verdict.Unchecked
      }
  }

  /**
   * Whether the candidate proves the conclusion with no premise taking any part.
   *
   * Asked after satisfiability and not before, because a candidate that contradicts the premises is
   * the more urgent thing to say about it: it is usually a sign that the premises are tighter than
   * the author remembers, while a circular one is a sign only that the search had nothing better.
   */
  private def alone(candidate: Term, conclusion: Term): Boolean =
    (for {
      goal <- reals.logic.mkImp(candidate, conclusion)
      proved <- linarith.prove(goal)
    } yield proved).isRight

  /**
   * The weakest of what was **proposed**, which is not the weakest premise that would work.
   *
   * The distinction is worth the sentence, because the report reads as the second. The candidates
   * are the goal's forms bounded by the goal's numerals, and the weakest premise that closes a goal
   * is usually at a bound the goal never writes: `x + y + z <= 12` from `x + y <= 10` and `z <= 3`
   * comes back with `z < 0` because that is the weakest of what was offered, while `z <= 2` would
   * have done and was never proposed. What the filter removes is a candidate stronger than another
   * candidate, and that is all it claims.
   *
   * `0 < y`, `1 < y` and `3 < y` all close the same goal, and only the first is worth reporting: a
   * reviewer asking for the strongest of them is asking for more than the argument needs. So a
   * candidate is dropped when **it implies** another one that also closes the goal, which
   * `Linarith` decides, and the ordering is a decision rather than a guess about which looks
   * smaller.
   *
   * The direction is worth stating because the first version had it backwards and the mistake was
   * invisible on the goals where only one candidate survived: on `x < y ==> 2 * x < y` both
   * `x < 0` and `y < 0` close it, `y < 0` is the stronger, and the filter reported that one.
   *
   * **Two candidates that imply each other are one answer**, and only the first of them is kept.
   * The strict test above cannot do that, since neither is stronger, and it used to report both;
   * that was tolerable while the candidates were bounds on variables and a pair like `x < 0` and
   * `2 * x < 0` could not both be proposed. Once a bound on a combination is in the language such a
   * pair is the ordinary case, so an author was being handed the same premise twice in different
   * arithmetic. The one kept is the earlier in the order the candidates were generated, which puts
   * a variable before a combination and a smaller bound before a larger one, so the representative
   * is the plainer way of writing the class rather than whichever the fold reached first.
   *
   * This is not applied to [[Abduce.Gap.vacuous]] and must not be. Those candidates make the
   * premises impossible, so under them everything implies everything, every pair comes back
   * equivalent, and the whole list would collapse to whichever member came first.
   */
  private def weakest(shape: Shape, found: Vector[Term]): Vector[Term] = {
    val strongest = found.filterNot { candidate =>
      found.exists { other =>
        other != candidate &&
        implies(shape, candidate, other) &&
        !implies(shape, other, candidate)
      }
    }

    strongest.foldLeft(Vector.empty[Term]) { (kept, candidate) =>
      val equivalent =
        kept.exists(other => implies(shape, candidate, other) && implies(shape, other, candidate))
      if (equivalent) kept else kept :+ candidate
    }
  }

  private def implies(shape: Shape, stronger: Term, weaker: Term): Boolean =
    (for {
      antecedent <- conjoin(shape.hypotheses :+ stronger)
      goal <- reals.logic.mkImp(antecedent, weaker)
      proved <- linarith.prove(goal)
    } yield proved).isRight

  /* ---------------------------------------------------------------------- the shape */

  private final case class Shape(hypotheses: Vector[Term], conclusion: Term)

  private def split(body: Term): Shape =
    reals.logic.destImp(body) match {
      case None => Shape(Vector.empty, body)
      case Some((antecedent, consequent)) => Shape(conjuncts(antecedent), consequent)
    }

  private def conjuncts(term: Term): Vector[Term] =
    reals.logic.destConj(term) match {
      case Some((left, right)) => conjuncts(left) ++ conjuncts(right)
      case None => Vector(term)
    }

  private def conjoin(parts: Vector[Term]): Either[LogicError, Term] =
    parts.toList match {
      case Nil => Left(NotOfForm("at least one premise", reals.logic.truth))
      case first :: rest =>
        rest.foldLeft(Right(first): Either[LogicError, Term])((acc, next) =>
          acc.flatMap(reals.logic.mkConj(_, next))
        )
    }

  /** The point the missing premise has to exclude, when the search can name one. */
  private def pointOf(shape: Shape): Option[String] =
    refutation.counterexample(shape.hypotheses, shape.conclusion) match {
      // Both halves of the point, since 2026-09-11: the premise that has to be excluded may be the
      // one about an agent rather than the one about a quantity, and a point that named only the
      // quantities would be asking a caller to exclude something it could not see.
      case Refutation.Solved(values, finite) if values.nonEmpty || finite.nonEmpty =>
        Some(
          (values.toVector.map { case (name, value) => name -> value.toString } ++
            finite.toVector.map { case (name, value) => name -> Model.show(value) })
            .sortBy(_._1)
            .map { case (name, value) => s"$name = $value" }
            .mkString(", ")
        )
      case Refutation.Found(values, _) if values.nonEmpty =>
        Some(values.toVector.sortBy(_._1).map { case (name, value) => s"$name = ${Model.show(value)}" }.mkString(", "))
      case _ => None
    }

}

object Abduce {

  /**
   * What was missing, in five parts that are not each other.
   *
   * `found` is what to assume. `vacuous` is what would close the goal by making the premises
   * impossible, kept because it is worth seeing and dangerous to report as an answer. `circular` is
   * what would close it without the premises taking any part, which is the conclusion asked for
   * back. `unchecked` closes the goal and **which of those three it is was not decided**. `point`
   * is where the claim fails as it stands, which is what any missing premise has to exclude and is
   * the only part a reader can check without trusting anything here.
   *
   * The four lists are kept apart for the reason `Refutation` keeps seven outcomes apart. Three of
   * them close the goal and none of the three is an answer, and a report that merged any into
   * `found` would hand an author something to assume that is impossible, or already what they were
   * trying to prove, or not known to be either.
   *
   * == Why the fourth list exists, with the number that made it ==
   *
   * It was not there until 2026-09-11 and its members were in `found`. `judge` asked
   * `Refutation.satisfying` and matched `Contradictory` against everything else, so `Undecided`,
   * `NeverAsked` and `Survived` — the three answers that mean *the question was not settled* — were
   * read as *the premises stay satisfiable*. Measured over miniF2F at that date: of 422 candidates
   * that close one of the eighteen goals this system attempts and does not prove, 264 came back
   * `Undecided` and 11 `Survived`, against 17 `Solved` and 11 `Found`. **Sixty-five per cent of
   * what was reported as a missing premise had never been checked for the one failure this class
   * says it checks for.**
   *
   * Six of the eighteen had every candidate undecided, and five of those six are statements about
   * the reals that predate any of the work on the naturals: an equality between reals that the
   * solver cannot read as a linear system sends the question to the sampler, and the sampler
   * declines it because such a premise holds on a set of measure zero. The witness that found it is
   * `mathd_numbertheory_234`, whose reported missing premise was `real_of_num x < 0` under the
   * hypothesis `1 <= real_of_num x`, which is the failure the class comment above describes as the
   * prototype's and as fixed.
   *
   * An empty `found` means nothing in the candidate language closed it, which is not the same as
   * nothing existing: `x <= y ==> x < y` needs `~(x = y)` and no bound will do. And since this list
   * exists, an empty `found` beside a full `unchecked` is a third thing again: candidates were
   * found and nobody can say whether they are worth anything.
   */
  final case class Gap(
    point: Option[String],
    found: Vector[Term],
    vacuous: Vector[Term],
    circular: Vector[Term],
    unchecked: Vector[Term] = Vector.empty,
    /**
     * Whether `point` settles the claim rather than being evidence about a model.
     *
     * True when a point was found **and** every value the search could have produced is exact, which
     * over `Model.Numbers` means the claim is about the naturals and never crosses into the reals.
     * A counterexample at `x = 3, y = 5` to a claim about `NUM_ADD` is arithmetic on `BigInt` and is
     * the end of the question; the same shape of answer about `real` is a fact about `Double` and is
     * not. `Cost` reads this and nothing else does.
     *
     * `Refutation.Solved` is exact too and is deliberately **not** counted here: its values are
     * rationals satisfying a linear system over the reals, so it decides as much as this does, and
     * promoting it would change what every real-side claim reports. That is a second question and
     * this is not the file to settle it in.
     */
    decisive: Boolean = false
  )

  /** Over the standard theory. */
  lazy val standard: Abduce = new Abduce(Linarith.standard, Refutation.standard)

  /** Over a theory of one's own. */
  def apply(linarith: Linarith, refutation: Refutation): Abduce = new Abduce(linarith, refutation)
}
