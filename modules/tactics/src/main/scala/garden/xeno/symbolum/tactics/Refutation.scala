package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.{Conv, Logic}
import garden.xeno.symbolum.theories.{Linarith, LinearFact, LinearForm, Natural, Order, Rational, Real, Region}

/**
 * Searching a model for the assignment that shows an entailment false, or a hypothesis set
 * satisfiable.
 *
 * One search, two questions, and the second is the one nothing in this repository could ask before.
 * A sequent `h1..hn |- c` carries its undischarged premises, which is what makes it an audit of what
 * a claim rests on, and it is **vacuously true when those premises contradict each other**. The
 * kernel will print `H |- c` and `H |- ~c` with equal cheer, because both are correct. Over a domain
 * of uninterpreted constants an inconsistent premise set is easy to write and invisible to read, so
 * a premise set with no satisfying assignment is worth more attention than most proofs.
 *
 * Nothing here produces a theorem: this is the untrusted side, where `docs/adr/0003` puts everything
 * that guesses. What it produces is of two kinds, and keeping them apart is what the file is for. A
 * **decision** is about every assignment there is: [[Refutation.Solved]] carries a point that
 * satisfies the premises exactly, and [[Refutation.Contradictory]] and
 * [[Refutation.NoCounterexample]] say that no point does. A **sample** is about the points that were
 * tried: [[Refutation.Found]] is a fact about one of them, [[Refutation.Survived]] is a count of the
 * ones that answered and is not a proof of anything, and [[Refutation.NeverAsked]] says that none of
 * them answered at all.
 *
 * == What is solved, what is sampled, and what is still refused ==
 *
 * A premise set that reads as a linear system over the reals is decided rather than sampled, since
 * 2026-09-05. `{x = 1}`, which a sampler lands on with probability zero, comes back with the point;
 * `{x < y, y < z, z < x}` comes back as a decision rather than as a hundred failures to find
 * anything. `Linarith` holds the machine, since the simplex that weighs hypotheses for a proof also
 * finds a point satisfying them. Refuting an entailment is the same question with one more premise,
 * the conclusion denied, so that search is solved too wherever the denial is one relation.
 *
 * **The decision was all-or-nothing until 2026-09-11, and a premise set about entities is made the
 * other way.** One premise the linear reader could not take sent every other premise to the grid,
 * so `{0 < cost, threatens a b}` was sampled entire while half of it is a system and the other half
 * is three agents. It is partitioned now: the premises whose every atom is a free variable of type
 * `real` are one system, the rest are evaluated at each assignment of their own variables over the
 * carriers the model sized, and the two halves share no variable, because an atom admitted to the
 * system is of type `real` and `real` has no carrier. `solved` is the partition and says why each
 * half is what it is.
 *
 * What is still sampled is the half that cannot be either: a product of two unknowns, a premise at a
 * type the model has not sized, anything mentioning `num`, which is sampled rather than enumerated.
 * The solver would have to give such an atom a value of its own, and a point that assigns `x * y`
 * freely does not satisfy the premise it was found for. The proof side has no such limit, and
 * `solved` says why.
 *
 * **A decision over a declared type is a decision about this model**, which is what every answer
 * here already is. `Contradictory` over the reals is close to absolute because the intended model of
 * the reals is the reals; over a carrier the model sized at three it says that none of the nine
 * assignments satisfies the premises, and another model may size the type differently. The
 * distinction the seven outcomes keep is a decision against a sample, not an absolute against a
 * model-relative one, and enumerating a carrier exhaustively is deciding.
 *
 * A premise that has to make an equality between reals true, in a set the solver could not read as a
 * system, is refused by name rather than sampled. It holds on a set of measure zero, so no number of
 * points is evidence either way, and answering `Survived` there would say the same thing about
 * `{x = 1 /\ 0 < x}` as about `{0 < x, x < 0}` while one of the two is satisfiable. Refusing is what
 * `Linarith` does with a multiplier and `Translate` with a quotient.
 *
 * == Why the conclusion is stripped and the premises are not ==
 *
 * A universal conclusion is refuted by one point, so `!x. Q x` is turned into `Q` at a fresh
 * variable and that variable is sampled: finding an `x` where `Q` fails refutes the whole thing, and
 * the premises cannot object because they do not mention that `x`, which was bound.
 *
 * A universal premise is the other way round. It has to hold at every point for the entailment to
 * be in question at all, and checking the one point sampled would let this report a counterexample
 * standing on a premise that is false elsewhere. So a premise is evaluated as written, and a premise
 * that cannot be evaluated, which over the reals is every universal one, makes the point unusable.
 * The search says so rather than counting it: [[Refutation.NeverAsked]] is not the same answer as
 * [[Refutation.Survived]], and reading one as the other is the mistake this distinction exists to
 * prevent.
 */
final class Refutation private (val evaluate: Evaluate) {

  import Model.*

  /**
   * An assignment where every premise holds and the conclusion does not.
   *
   * The witness is what makes this worth running: a counterexample nobody can inspect is a rumour.
   */
  def counterexample(
    premises: Vector[Term],
    conclusion: Term,
    points: Int = Refutation.Points
  ): Refutation.Outcome = {
    val opened = open(conclusion)

    denied(opened)
      .flatMap(negation => solved(premises :+ negation, refuting = true))
      .orElse(impossible(premises))
      .getOrElse(
        pinned(premises) match {
          case Some(reason) => Refutation.Undecided(reason)
          case None =>
            search(
              premises,
              premises :+ opened,
              points,
              assignment => evaluate.proposition(opened, assignment).map(!_)
            )
        }
      )
  }

  /**
   * The premises decided unable to hold together, where that can be decided, before any sampling.
   *
   * A conclusion that cannot be denied as one linear relation, an equation above all, used to go
   * straight to the sampler, and the sampler counts a point at which a premise is false as a point
   * that answered: `{x < 0, 0 < x}` with the conclusion `x = 7` came back `Survived(100)`, a hundred
   * points of which none was a point where the premises held. Found by the proof language, whose
   * report printed that a goal under contradictory hypotheses had survived a hundred points. The
   * order conclusions never had the defect, because their denial goes to the solver with the
   * premises and the solver sees the contradiction.
   *
   * Only `Contradictory` is taken from here. Every other answer `satisfying` gives is about the
   * premises alone, and the question asked of this method is about the conclusion too.
   */
  private def impossible(premises: Vector[Term]): Option[Refutation.Outcome] =
    if (premises.isEmpty) None
    else satisfying(premises) match {
      case contradictory: Refutation.Contradictory => Some(contradictory)
      case _ => None
    }

  /**
   * The conclusion denied, as a premise, when denying it is one linear relation.
   *
   * An entailment fails exactly where its premises hold and its conclusion does not, so refuting
   * one is asking whether a premise set is satisfiable, which is the question next door. Over a
   * total order the denial of `a < b` is `b <= a` and of `a <= b` is `b < a`; the step is sound and
   * is taken here rather than in the kernel, where it would need trichotomy and a derivation.
   *
   * An equality is not denied, because its denial is a disjunction and that is two systems rather
   * than one. Such a conclusion goes back to the sampler, which is where it already was.
   */
  private def denied(conclusion: Term): Option[Term] = {
    val reals = evaluate.reals

    Order.destOrder(reals, conclusion).flatMap { case (left, right, strict) =>
      val name = if (strict) Real.NonStrictOrder else Real.Order
      val relation = Type.fun(
        TyApp(Real.TypeName, Nil),
        Type.fun(TyApp(Real.TypeName, Nil), Type.Bool)
      )

      (for {
        constant <- reals.theory.constant(name, relation)
        applied <- Term.appAll(constant, List(right, left))
      } yield applied).toOption
    }
  }

  /**
   * Whether a point found among these terms would be a refutation rather than a sample.
   *
   * `Evaluate.exact` is the question; this is the door onto it, because a caller holding a search
   * has no other way to ask. See `Abduce.Gap.decisive` for what is done with the answer.
   */
  def exactly(terms: Vector[Term]): Boolean = terms.forall(evaluate.exact)

  /**
   * An assignment satisfying every premise, which is what says the set is not contradictory.
   *
   * The premises are taken as written here too. A universal premise over the reals therefore makes
   * every point unusable and the answer is `NeverAsked`, which is the truth: this cannot tell you
   * whether such a set is consistent, and saying so is better than a reassuring number.
   */
  def satisfying(premises: Vector[Term], points: Int = Refutation.Points): Refutation.Outcome =
    solved(premises, refuting = false).getOrElse(
      pinned(premises) match {
        case Some(reason) => Refutation.Undecided(reason)
        case None => search(premises, premises, points, _ => Some(true))
      }
    )

  /**
   * The same question decided rather than sampled, over the half of the premises that is a system
   * and the half that is a finite enumeration.
   *
   * This is where the answer stops being a number of points. A set of linear premises over the
   * reals is a system, its satisfiability has a finite certificate either way, and `Linarith`
   * already holds the machine that finds one. So `{x = 1}`, which a sampler misses with
   * probability one, comes back with the point; and `{x < y, y < z, z < x}` comes back as a
   * decision rather than as a count of failures to find anything.
   *
   * **The premises are partitioned rather than judged together, since 2026-09-11.** Before that one
   * premise the linear reader could not take sent every other premise to the sampler, and a premise
   * set about entities is written exactly the other way round: some constraints over the reals and
   * some over a type the model has sized. `{0 < cost, threatens a b}` was a hundred sampled points;
   * it is now one system and nine assignments.
   *
   * The split is sound because the two halves **share no variable**, and that is a consequence of
   * the admission test rather than an assumption about the caller. An atom of the system is a free
   * variable of type `real`; a variable of the other half is required below to have a finite
   * carrier; and `real` has none. So the region is the same region at every finite assignment, and
   * the simplex is run once rather than once per assignment.
   *
   * `None` here means the question is not one this can decide, so the sampler is still the answer.
   * That happens when a premise outside the system mentions a variable with no carrier: a real, a
   * natural, a product of two unknowns, a type nobody sized. It also happens when the enumeration
   * would be larger than [[Refutation.Assignments]], and when some assignment could not be
   * evaluated and no witness was found anywhere, because `Contradictory` is a decision over every
   * assignment and never a count of the ones that failed.
   *
   * **The proof side is not held to the same rule, and the asymmetry is not an oversight.** Since
   * 2026-09-10 `LinearForm.of` multiplies a product of two unknowns out and keys the result
   * through `productAtom`, so a certificate may range over product atoms: it weighs the hypotheses
   * and adds them, `Ring` checks the sum against the goal, and nothing is proved about an atom, so
   * the step is sound whatever it denotes. A witness has to denote. A point that gives `x * y` a
   * value of its own, unrelated to the ones it gives `x` and `y`, does not satisfy the premises it
   * was found for, and reporting it as one would be a wrong answer wearing the form a reader is
   * invited to check. `docs/adr/0005` records this as the reason the solving route stops here.
   */
  private def solved(premises: Vector[Term], refuting: Boolean): Option[Refutation.Outcome] = {
    val read = premises.map(premise => premise -> constraint(premise))
    val system = read.collect { case (_, Some(fact)) => fact }
    val rest = read.collect { case (premise, None) => premise }

    def decision: Refutation.Outcome =
      if (refuting) Refutation.NoCounterexample(premises.length)
      else Refutation.Contradictory(premises.length)

    enumerated(rest).flatMap { assignments =>
      Region.satisfying(system) match {
        // The system alone has no point, so no assignment of the other half can rescue it: a
        // conjunction is unsatisfiable as soon as one of its parts is. This is the one branch that
        // decides without every assignment having answered, and it decides for that reason rather
        // than by counting anything.
        case None => Some(decision)

        case Some(point) =>
          // The count and the witness are carried together because they have to stop together:
          // the count only says what it means when the walk reached the end, and a walk that
          // stopped early at a witness is one whose count nobody may read.
          @annotation.tailrec
          def search(
            remaining: List[Map[String, Model.Value]],
            answered: Int
          ): (Int, Option[Refutation.Outcome]) =
            remaining match {
              case Nil => (answered, None)
              case assignment :: tail =>
                evaluate.all(rest, assignment) match {
                  // A place the model has nothing to say about is not a place the premises failed,
                  // which is the rule `search` already follows and the reason for the count.
                  case None => search(tail, answered)
                  case Some(false) => search(tail, answered + 1)
                  case Some(true) =>
                    (
                      answered + 1,
                      Some(
                        Refutation.Solved(
                          point.collect { case (FVar(name, _), value) => name -> value },
                          assignment
                        )
                      )
                    )
                }
            }

          val (answered, witness) = search(assignments.toList, 0)

          // One assignment this model could not evaluate withdraws the claim to have decided
          // anything, so the question goes back to the sampler with nothing asserted about it.
          // Answering `Contradictory` on a count of the assignments that happened to answer is the
          // conflation the rest of this file exists to prevent.
          witness.orElse(Option.when(answered == assignments.length)(decision))
      }
    }
  }

  /**
   * A premise as a constraint of the system, and only where a point could realise it.
   *
   * `LinearFact.relation` rather than `LinearFact.of`, because the fallthrough is right for a
   * procedure that proves and wrong for one that answers: it reads a bare `p:bool` as the fact
   * `0 < p`, which is a reading of the proposition that nobody checked. A premise it declines is
   * not lost, it goes to the other half of the partition and is evaluated there.
   *
   * A free variable, and of type `real`. The type test is what keeps this from answering a question
   * nobody asked: without it an atom at another type would come back `Solved` with a rational for
   * something that is not a number. It also settles the keying of the witness, which keeps the name
   * and drops the type: two atoms of one name at different types cannot both be admitted, so they
   * cannot collide into one entry.
   */
  private def constraint(premise: Term): Option[LinearFact] =
    LinearFact
      .relation(evaluate.reals, premise)
      .toOption
      .filter(_.form.atoms.forall {
        case FVar(_, ty) => ty == Real.realType
        case _ => false
      })

  /**
   * Every assignment of these terms' free variables, or nothing where there is no finite every.
   *
   * The enumeration is [[Refutation.grid]]'s and not a second one: its strides are a mixed-radix
   * counter over the carriers, so asking it for exactly as many points as the product has members
   * yields each member once and none twice. What is added here is the precondition it does not
   * check, that **every** variable has a carrier: grid samples the ones that do not, and a sampled
   * coordinate would turn this enumeration back into the thing it exists not to be.
   *
   * `None` is therefore the honest answer for a real, a natural, or a declared type the model never
   * sized, and it sends the premises back to the sampler where they already were.
   */
  private def enumerated(terms: Vector[Term]): Option[Vector[Map[String, Model.Value]]] = {
    val carriers =
      terms.flatMap(Term.freeVariables).distinct.map(variable => evaluate.inhabitants(variable.ty))

    Option.unless(carriers.exists(_.isEmpty)) {
      // Capped one past the bound at every step rather than multiplied out and then tested. A model
      // may size a type at anything an `Int` holds, so thirty booleans, or four types of two
      // billion, would overflow an accumulator on the way to a number that was going to be refused
      // anyway; capped, the largest product this ever forms is the cap times one carrier.
      val span = carriers.flatten.foldLeft(1L)((total, inhabitants) =>
        (total * inhabitants.length).min(Refutation.Assignments + 1L)
      )

      Option.when(span <= Refutation.Assignments)(
        Refutation.grid(evaluate, terms, span.toInt)
      )
    }.flatten
  }

  /**
   * Why sampling cannot settle anything about these premises, if it cannot.
   *
   * A premise that has to make an equality between reals true is satisfied on a set of measure
   * zero, and a sampler will miss it every time however many points it tries. Without this check
   * that came back as `Survived`, which is the same answer a genuinely contradictory set gives:
   * `{x = 1}` and `{0 < x, x < 0}` were indistinguishable, and one of them is satisfiable.
   *
   * `solved` runs first and now answers `{x = 1}` with the point, so what reaches here is the
   * equalities it could not read as a system: a compound premise, a disjunction, anything whose
   * atoms it will not admit. Those are refused by name, which is what `Linarith` and `Translate` do
   * with the goals they do not decide, and `{x = 1 /\ 0 < x}` is the shape that arrives.
   *
   * Only a **positive** occurrence counts, so `~(x = 0)`, which is `MUL_INVERSE`'s side condition
   * and one of the most common premises there is, does not trip it: an equality that has to be
   * false is false almost everywhere, which is exactly where a sampler looks.
   */
  private def pinned(premises: Vector[Term]): Option[String] =
    premises.zipWithIndex.collectFirst {
      case (premise, index) if pins(premise, positive = true) =>
        s"premise ${index + 1} of ${premises.length} holds only where an equality between reals " +
          "does, which is a set this search samples with probability zero; deciding it needs " +
          "solving rather than sampling"
    }

  /**
   * Whether the term forces an equality at a type with no finite carrier.
   *
   * Polarity is tracked because it decides the answer. A conjunction in positive position is pinned
   * when either side is; a disjunction when both are, since either one may be the side that holds;
   * an implication is `~p \/ q`; and a negation flips. In negative position an equality has to be
   * false, and that is the generic case, so nothing there is pinned.
   */
  private def pins(term: Term, positive: Boolean): Boolean = term match {
    case App(App(Const(Logic.Conjunction, _), left), right) =>
      if (positive) pins(left, positive) || pins(right, positive)
      else pins(left, positive) && pins(right, positive)

    case App(App(Const(Logic.Disjunction, _), left), right) =>
      if (positive) pins(left, positive) && pins(right, positive)
      else pins(left, positive) || pins(right, positive)

    case App(App(Const(Logic.Implication, _), antecedent), consequent) =>
      if (positive) pins(antecedent, !positive) && pins(consequent, positive)
      else pins(antecedent, !positive) || pins(consequent, positive)

    case App(Const(Logic.Negation, _), proposition) => pins(proposition, !positive)

    // The variables, not the type. An equality at `real` whose every free variable is drawn from a
    // small range is determined at each point of the grid and is settled there: `real_of_num n = 3`
    // is an equality between reals and is true at one of the twelve naturals the grid draws. What
    // makes an equality unreachable is a **coordinate** the search draws from a continuum.
    case equality @ App(App(Const(Term.EqualityName, _), _), _) =>
      positive && Term.freeVariables(equality).exists(variable => continuous(variable.ty))

    case _ => false
  }

  /**
   * Whether the sampler draws this type from a continuum, which is what makes an equality at it a
   * set the search misses every time.
   *
   * The test used to be "no finite carrier", and that was the same test while the reals were the
   * only thing sampled. It stopped being the same test on 2026-09-11, when `num` began to be
   * sampled as a small range of whole numbers: `x:num = y:num` has no finite carrier and is hit by
   * the grid about one point in twelve, so refusing it as measure-zero refused a question the
   * search could answer, and did so in a message that said "an equality between reals" about an
   * equality between naturals.
   *
   * The other two cases are not pinned either and for different reasons. A declared type with a
   * carrier is enumerated, so an equality at it is decided by trying every pair. A declared type
   * **without** one is not sampled at all: the variable is left out of the point, nothing has a
   * value, and the answer is `NeverAsked`, which says what happened. Calling any of those
   * measure-zero would be saying something false about a question that was asked or never put.
   *
   * Asked of the equality's **free variables** and not of its type, which is the second half of the
   * same repair: `real_of_num n = 3` is an equality between reals, and it is true at one of the
   * twelve naturals the grid draws. A reader that looked at the type alone refused it.
   */
  private def continuous(ty: Type): Boolean = ty == Real.realType

  /**
   * Try every point, and report the first that answers.
   *
   * A point where any premise, or the question itself, has no value in this model is skipped
   * entirely rather than counted as a failure to find anything: a place where the question was not
   * asked is not evidence, which is the rule `Discovery` already follows for an undefined
   * logarithm.
   */
  private def search(
    premises: Vector[Term],
    sampled: Vector[Term],
    points: Int,
    holds: Map[String, Value] => Option[Boolean]
  ): Refutation.Outcome = {
    // Over `sampled` and not over `premises`: a variable the conclusion alone mentions, which is
    // every variable a universal conclusion was opened into, would otherwise have no value and
    // every point would come back unanswered.
    val grid = Refutation.grid(evaluate, sampled, points)

    // The count travels with the search rather than beside it: `Found` reports how many points
    // had answered when the witness turned up, so a count kept outside a lazy walk would be
    // reporting the state of an iterator instead of the state of the search.
    @annotation.tailrec
    def walk(
      remaining: List[Map[String, Value]],
      asked: Int
    ): (Int, Option[Map[String, Value]]) =
      remaining match {
        case Nil => (asked, None)
        case assignment :: tail =>
          val answer =
            for {
              all <- evaluate.all(premises, assignment)
              here <- holds(assignment)
            } yield all && here

          answer match {
            case None => walk(tail, asked)
            case Some(false) => walk(tail, asked + 1)
            case Some(true) => (asked + 1, Some(assignment))
          }
      }

    val (asked, found) = walk(grid.toList, 0)

    found match {
      case Some(assignment) => Refutation.Found(assignment, asked)
      case None if asked == 0 => Refutation.NeverAsked(grid.length)
      case None => Refutation.Survived(asked)
    }
  }

  /**
   * The body of a goal, with its leading universal quantifiers replaced by free variables.
   *
   * `Logic.stripForall` is the move and the reason is there: a quantified statement is a constant
   * applied to a lambda, and there is nothing in that to evaluate. A statement that cannot be
   * opened is returned as it stands, since the caller's next step refuses it either way.
   */
  private def open(term: Term): Term =
    Logic.stripForall(term).map(_._2).getOrElse(term)
}

object Refutation {

  /**
   * How many assignments a search tries by default.
   *
   * A hundred, which is what `DocumentationSpec` already hands `Discovery.grid`, and for the same
   * reason: enough that agreement means something, few enough that the search is cheaper than the
   * certification it feeds. It is an argument on every method here because the right number depends
   * on how many variables there are, and nothing can pick it for the caller.
   */
  val Points: Int = 100

  /**
   * How many finite assignments the partition will enumerate before handing the question back.
   *
   * Four thousand and ninety-six, and both halves of the number are counted rather than timed: the
   * wall clock on the machine this was measured on gave the same enumeration 39 ms and 145 ms in
   * two consecutive runs, so it decides nothing.
   *
   * **What it buys**, counted. The enumeration is the one cost here a caller does not choose: a
   * model may size a declared type at anything, and the work is the product over the variables, so
   * two variables of a type sized at sixty-four is already this number and three of them is
   * sixty-four times past it. A set whose every assignment is infeasible puts all of them, so at
   * the bound the search evaluates each premise outside the system 4096 times, against the 100 of
   * [[Points]] that the sampler would have spent on the same question: forty-one times the budget
   * of the thing it replaces, and that is the ceiling rather than the usual case.
   *
   * **What it cuts**, counted. Twelve propositional variables; four variables of a type sized at
   * eight; three of a type sized at sixteen; two of a type sized at sixty-four; one of a type sized
   * at 4096. Each of those is decided and one more variable is not: it goes back to the sampler for
   * the answer the sampler has, which is a count of a hundred points. Nothing this was written for
   * comes near it, and that is the other half of the measurement: a premise set about entities has
   * two or three variables over three or four inhabitants, which is nine to sixty-four.
   */
  val Assignments: Int = 4096

  sealed trait Outcome {

    /** How many assignments actually produced an answer. */
    def asked: Int
  }

  /** The assignment, and how many points answered up to and including it. */
  final case class Found(witness: Map[String, Model.Value], asked: Int) extends Outcome

  /**
   * Every point answered and none of them was the one wanted.
   *
   * Carries the count for the reason `Discovery.Unsettled` does: agreement at three points is
   * nothing and agreement at three hundred is a lead, and a reader cannot tell them apart from a
   * bare "no".
   */
  final case class Survived(asked: Int) extends Outcome

  /**
   * No point could be evaluated at all, so nothing was learned.
   *
   * A different answer from [[Survived]] and never to be read as it. It means the model had nothing
   * to say here: a constant nobody interpreted, or a universally quantified premise over the reals,
   * which cannot be checked at a point at all.
   */
  final case class NeverAsked(offered: Int) extends Outcome {
    def asked: Int = 0
  }

  /**
   * A point where every premise holds, found by solving rather than by sampling.
   *
   * Exact, and told apart from [[Found]] on purpose: this one satisfies the premises and can be
   * checked against them by hand, including the equalities, where a sampled point can only ever
   * come close. The values are rationals for the same reason, and turning one into a double may
   * stop it satisfying the premise it was found for.
   *
   * `finite` is the other half of the point, and it is empty exactly when the premises were a
   * system and nothing else. It names the inhabitant each variable of a sized type was given, and
   * those values are exact in the same sense the rationals are: an inhabitant is the inhabitant it
   * is, not something near it.
   *
   * **What was checked at the finite half is the model's arithmetic and not a solution.** The
   * system half is solved; the premises that mention a sized type are evaluated there by
   * [[Evaluate]], so where that evaluation goes through `Double` it carries the tolerance
   * `Model.Reals` carries, and an equality between reals that holds to within it is reported as
   * holding. `asked` stays zero for the same reason it does on every other decision: assignments
   * were enumerated rather than sampled, and a count of them is not evidence anybody should weigh.
   */
  final case class Solved(
    witness: Map[String, Rational],
    finite: Map[String, Model.Value] = Map.empty
  ) extends Outcome {
    def asked: Int = 0
  }

  /**
   * No point satisfies the premises, and this is a decision rather than a count of failures.
   *
   * Distinct from [[Survived]], which says only that a number of sampled points were not it. This
   * says there is no such point at all, which for a linear premise set is something the same
   * machinery can also hand to the kernel: `Linarith` proves `h1 /\ ... /\ hn ==> F` from the
   * certificate that shows it.
   *
   * **Over a declared type it is a decision about this model**, and that is not a weaker kind of
   * answer, it is the only kind anything in this file gives. A carrier the model sized at three has
   * nine pairs and all nine were tried; a model that sized it differently is a different question.
   * What separates this from [[Survived]] is that every assignment there is was put, not that the
   * answer is true of every model there is.
   */
  final case class Contradictory(premises: Int) extends Outcome {
    def asked: Int = 0
  }

  /**
   * Nothing satisfies the premises together with the denied conclusion, so the entailment holds.
   *
   * The same decision as [[Contradictory]] about a different set, and named apart from it because
   * the two are read in opposite directions: one says the premises are worthless, the other says
   * the claim is good. Reporting `Contradictory` for both would be exactly the conflation the rest
   * of this file exists to prevent.
   *
   * It is a decision over the linear fragment and not a theorem. `Linarith` is what turns it into
   * one, from the same certificate.
   */
  final case class NoCounterexample(constraints: Int) extends Outcome {
    def asked: Int = 0
  }

  /**
   * The search declined, because sampling cannot settle a question of this shape.
   *
   * Not a result about the premises and not to be read as either of the others. It means a premise
   * has to make an equality between reals true, in a set the solver could not read as a system, and
   * that happens on a set of measure zero, so no number of sampled points is evidence either way.
   * The alternative was to return [[Survived]], which made `{x = 1 /\ 0 < x}` and `{0 < x, x < 0}`
   * the same answer while one of them is satisfiable.
   *
   * `reason` names the shape rather than describing the failure, because what a caller does about
   * this is ask a procedure that solves instead of sampling, and it has to know which shape sent it
   * there. `Remedy` reports it as [[AskDifferently]] for that reason.
   */
  final case class Undecided(reason: String) extends Outcome {
    def asked: Int = 0
  }

  /** Over the standard theory of the reals under its intended model. */
  lazy val standard: Refutation = new Refutation(Evaluate.standard)

  def apply(evaluate: Evaluate): Refutation = new Refutation(evaluate)

  /**
   * Assignments over the free variables of the terms, one per point.
   *
   * A variable of a finite type is enumerated, one of type `num` gets a small natural number, and
   * everything else is sampled as a real: the finite ones cycle through their inhabitants at
   * different rates, so a hundred points cover the whole product whenever the product is small,
   * while the reals get the quasi-random sequence `Discovery` uses and explains. Mixing them matters
   * for the case this was built for, where a claim is about some agents and some quantities at once.
   *
   * **The naturals arrived on 2026-09-11 and they are the third case rather than a special real.**
   * Before that a variable of type `num` was handed a `Model.Quantity`, which is of the wrong shape
   * for every operation on `num`, so every such point had no value and every claim about the
   * naturals came back "nobody could ask". `Model.Numbers` is the other half of that repair.
   */
  def grid(evaluate: Evaluate, terms: Vector[Term], points: Int): Vector[Map[String, Model.Value]] = {
    val variables = terms.flatMap(term => Term.freeVariables(term)).distinct.sortBy(_.name)
    val finite = variables.map(variable => evaluate.inhabitants(variable.ty))

    // A position's stride is the product of the carrier sizes before it, which is a running
    // product read one step behind. `scanLeft` yields exactly that, since zipping a scan of
    // length n + 1 against the n carriers drops its last element. A position with no carrier is
    // never indexed into and keeps the 0 the strides always gave it.
    val running = finite.scanLeft(1) {
      case (stride, Some(inhabitants)) => stride * inhabitants.length
      case (stride, None) => stride
    }
    val strides = finite.zip(running).map {
      case (Some(_), stride) => stride
      case (None, _) => 0
    }

    // A variable with nothing to put in it is **left out** rather than given a real, which is the
    // repair of 2026-09-11. Handing a `Quantity` to a variable of function type made `!f g. f = g`
    // come back refuted "at f = -0.51, g = 1.39", and those are not values of `f` and `g`: the
    // claim happens to be false and the witness was not a witness to it. An omitted variable has no
    // value, so the point has no value and the answer is `NeverAsked`, which is what "this search
    // cannot ask about that" has always meant here.
    (1 to points).toVector.map { step =>
      variables.indices.flatMap { position =>
        val variable = variables(position)
        val value = finite(position) match {
          case Some(inhabitants) =>
            Some(inhabitants(((step - 1) / strides(position)) % inhabitants.length))
          case None => sampled(variable.ty, position, step)
        }
        value.map(variable.name -> _)
      }.toMap
    }
  }

  /**
   * The value the `step`-th sample gives a variable of this type, where there is one to give.
   *
   * Three shapes and then a refusal. A natural gets a small whole number, a real gets the quasi-random
   * coordinate, a truth value gets the sign of one, and **a function of the naturals gets a function**,
   * which is the case worth the recursion: six of the proposals this was written for quantify over a
   * summand rather than over a number, and `!f n. 0 <= Sum f n` cannot be refuted by any assignment
   * that has nothing to put in `f`.
   *
   * A sampled function is a real function and not a table: it answers the same way every time it is
   * asked about the same index, because the index is what perturbs the step. A function that answered
   * differently on two applications would let a claim come back refuted by a witness that is not one.
   *
   * `None` for everything else, which today means a function of a real or of a declared type. Those
   * are sampleable by the same trick and are not sampled, because nothing has asked: the refusal is
   * one line away from being an answer and building it now would be building it blind.
   */
  private def sampled(ty: Type, position: Int, step: Int): Option[Model.Value] =
    if (ty == naturalType) Some(Model.Whole(whole(position, step)))
    else if (ty == Real.realType) Some(Model.Quantity(Discovery.coordinate(position, step)))
    else if (ty == Type.Bool) Some(Model.Truth(Discovery.coordinate(position, step) > 0))
    else
      Type.destFun(ty) match {
        case Some((domain, codomain)) if domain == naturalType =>
          Some(Model.Mapping(domain, {
            case Model.Whole(index) => sampled(codomain, position, step + Stride * within(index))
            case _ => None
          }))
        case _ => None
      }

  /** How far apart two indices of a sampled function sit in the sequence. */
  private val Stride: Int = 7

  /** An index, kept inside what an `Int` holds, since the sequence only needs it to differ. */
  private def within(index: BigInt): Int = (index % 1000).toInt

  /**
   * The natural number the `step`-th sample gives the variable in the `position`-th place.
   *
   * The same Kronecker sequence `Discovery.coordinate` uses, pushed into a small range of whole
   * numbers. Small on purpose: a claim about the naturals that is false is nearly always false at
   * nought, one or two, and what the sequence buys over counting up from nought is that two
   * variables in one claim do not walk in step. Counting would test `NUM_ADD m n = NUM_ADD n m` at
   * `m = n` a hundred times.
   *
   * Nought is in the range and is the first thing a reader should check for, because it is where the
   * base case of an induction lives and where half of the false claims about `num` fail.
   */
  def whole(position: Int, step: Int): BigInt = {
    val spread = (Discovery.coordinate(position, step) - Low) / (High - Low)
    BigInt((spread * Span).toInt.max(0).min(Span - 1))
  }

  /** How many different naturals [[whole]] draws from. */
  private val Span: Int = 12

  private val Low: Double = -3.0
  private val High: Double = 3.0

  /** The type the naturals are sampled at, which is a type of `theories` and not of this module. */
  private val naturalType: Type = TyApp(Natural.TypeName, Nil)
}
