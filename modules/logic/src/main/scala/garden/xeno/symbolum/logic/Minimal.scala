package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * A decision for the propositional fragment with no negation in it, which costs no axiom at all.
 *
 * == Why the fragment is drawn there ==
 *
 * The obvious version of this file is a truth-table or a DPLL over all of propositional logic. It
 * would be shorter and it would cost the most expensive thing this development has: the excluded
 * middle is derived here rather than assumed, and what it is derived from is the choice operator,
 * one of the two axioms `docs/adr/0009` records. Every theorem it produced would rest on that.
 *
 * A statement built from atoms with `/\`, `\/` and `==>` and no negation needs none of it. The
 * rules are the ones `Rules` already derives from the kernel's ten, the search below is an ordinary
 * intuitionistic sequent search, and what comes out reaches **zero axioms**. That is the whole
 * reason this exists beside a classical procedure rather than instead of one.
 *
 * **What it is NOT, and the card that asked for this got it slightly wrong in a way worth writing
 * down.** "Negation-free" does not mean "derivable in minimal logic". Peirce's law,
 * `((p ==> q) ==> p) ==> p`, has no negation in it and is not intuitionistically provable. So this
 * is a search that succeeds or refuses, not a decision procedure for classical validity, and a
 * classical tautology it cannot reach comes back refused rather than proved. Every obligation the
 * handbook's monotonicity generates is an implication between positive combinations of atoms and is
 * inside what this reaches; Peirce's law is the boundary and `MinimalSpec` holds it.
 *
 * == Refusing by name ==
 *
 * A formula with a negation in it is not *hard* here, it is **out**, and the refusal says so by
 * naming the negation. A caller told only "cannot prove this" reformulates for ever; a caller told
 * "this fragment has no negation in it" goes somewhere else on the first try. `Remedy` has the arm.
 */
final class Minimal private (val logic: Logic) {

  import Minimal.*

  private val rules = logic.rules

  /** Prove a goal of the fragment, in the notation of whatever theory the logic reads. */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Logic.stripForall(goal)
      (variables, body) = stripped
      _ <- inside(body)
      proved <- search(Vector.empty, body, Depth)
      closed <- rules.genAll(proved, variables.toList)
    } yield closed

  /**
   * Whether a goal is one this could take at all, without attempting it.
   *
   * The address question, answered before anything is spent, the way `Prove.addressOf` answers it
   * for the arithmetic fragments.
   */
  def reads(goal: Term): Boolean =
    Logic.stripForall(goal).toOption.exists { case (_, body) =>
      inside(body).isRight && connective(body)
    }

  /**
   * Why this fragment turns a goal away, when the goal is one it recognises as propositional.
   *
   * The other half of the address, and it exists so that a caller is told the **useful** thing. A
   * goal like `p \/ ~p` is not a shape the arithmetic procedures have an opinion about, so without
   * this it came back "restate it as an inequality, an equation between reals, a denial of one, or a
   * conjunction", which is true, unhelpful, and sends the author to rewrite a statement that has
   * nothing wrong with it. What they need to know is that the fragment costing no axiom has no
   * negation in it.
   *
   * Narrow on purpose: the atoms have to be propositional variables or constants, not applications.
   * `~(x = 0)` is a negation over an arithmetic atom, LINARITH has a route for it, and this must not
   * take the message away from the procedure that can actually settle it.
   */
  def declines(goal: Term): Option[String] =
    Logic.stripForall(goal).toOption.flatMap { case (_, body) =>
      if (!propositional(body)) None
      else inside(body).left.toOption.map(_.message)
    }

  /** Whether the term uses any of the connectives this fragment is about. */
  private def connective(term: Term): Boolean =
    logic.destConj(term).isDefined || logic.destDisj(term).isDefined ||
      logic.destImp(term).isDefined || logic.destNot(term).isDefined ||
      (term match {
        case App(fn, argument) => connective(fn) || connective(argument)
        case Abs(_, body) => connective(body)
        case _ => false
      })

  /** Whether every atom under the connectives is a bare proposition rather than an application. */
  private def propositional(term: Term): Boolean =
    logic.destConj(term).orElse(logic.destDisj(term)).orElse(logic.destImp(term)) match {
      case Some((left, right)) => propositional(left) && propositional(right)
      case None =>
        logic.destNot(term) match {
          case Some(inner) => propositional(inner)
          case None =>
            term match {
              case _: FVar => Term.typeOf(term) == Type.Bool
              case Const(_, ty) => ty == Type.Bool
              case _ => false
            }
        }
    }

  /* ----------------------------------------------------------------- the fragment */

  private def inside(term: Term): Either[LogicError, Unit] =
    if (mentions(term, Logic.Negation))
      Left(NotOfForm("a statement with no negation in it, which is the whole of this fragment", term))
    else if (mentions(term, Logic.Falsity))
      Left(NotOfForm("a statement with no falsity in it; deriving one needs the classical axioms", term))
    else if (Term.typeOf(term) != Type.Bool)
      Left(NotOfForm("a proposition", term))
    else Right(())

  private def mentions(term: Term, name: String): Boolean = term match {
    case Const(constant, _) => constant == name
    case App(fn, argument) => mentions(fn, name) || mentions(argument, name)
    case Abs(_, body) => mentions(body, name)
    case _ => false
  }

  /* -------------------------------------------------------------------- the search */

  /**
   * A theorem concluding the goal, with the sequent's hypotheses among those given.
   *
   * The order is what makes this terminate and what makes it cheap: the rules that can be applied
   * without ever having to be undone come first, and only what is left branches. `depth` is the
   * safety net rather than the argument, and a goal that reaches it is refused by name.
   */
  private def search(hypotheses: Vector[Term], goal: Term, depth: Int): Either[LogicError, Kernel.Thm] =
    if (depth <= 0)
      Left(NotOfForm(s"a goal this search settles within $Depth steps", goal))
    else if (hypotheses.contains(goal)) LogicError.lift(Kernel.assume(goal))
    else if (goal == logic.truth) rules.truth
    else
      right(hypotheses, goal, depth)
        .orElse(left(hypotheses, goal, depth))
        .orElse(branching(hypotheses, goal, depth))

  /** The right rules that never have to be undone: a conjunction and an implication. */
  private def right(
    hypotheses: Vector[Term],
    goal: Term,
    depth: Int
  ): Either[LogicError, Kernel.Thm] =
    logic.destConj(goal) match {
      case Some((left, right)) =>
        for {
          first <- search(hypotheses, left, depth - 1)
          second <- search(hypotheses, right, depth - 1)
          result <- rules.conjIntro(first, second)
        } yield result

      case None =>
        logic.destImp(goal) match {
          case Some((antecedent, consequent)) =>
            search(hypotheses :+ antecedent, consequent, depth - 1)
              .flatMap(rules.disch(antecedent, _))

          case None => Left(NotOfForm("a conjunction or an implication", goal))
        }
    }

  /**
   * The left rules that never have to be undone: taking a conjunction apart, and a case analysis.
   *
   * A disjunction on the left is invertible even though it branches, which is the reason it belongs
   * here and not below: both branches have to be proved whatever else is tried, so nothing is lost
   * by committing to it.
   *
   * == Nothing is ever removed, and that is the termination argument ==
   *
   * A first version replaced the hypothesis it took apart. It did not terminate, and the way it
   * failed is worth keeping: [[branching]] re-derives a consequent it does not already have, so a
   * conjunction taken apart and removed was manufactured again by the implication that concluded
   * it, taken apart again, and so on until the depth ran out — sixty-four levels of branching, which
   * is an out-of-memory rather than a refusal. Found by running it, not by reading it.
   *
   * So every rule here **adds** and each fires only where it has something to add: a conjunction
   * whose halves are both present is not taken apart, a disjunction with a disjunct already
   * assumed is not split, and an implication whose consequent is present is not used. Every step
   * therefore adds a subformula of a formula already in the sequent, of which there are finitely
   * many, and the search terminates on its own. [[Minimal.Depth]] is the net under that argument
   * and not the argument.
   */
  private def left(
    hypotheses: Vector[Term],
    goal: Term,
    depth: Int
  ): Either[LogicError, Kernel.Thm] = {
    val conjunction = hypotheses.collectFirst {
      case hypothesis if logic.destConj(hypothesis).exists { case (first, second) =>
            !hypotheses.contains(first) || !hypotheses.contains(second)
          } =>
        hypothesis
    }

    conjunction match {
      case Some(hypothesis) =>
        val (first, second) = logic.destConj(hypothesis).get
        val gained = Vector(first, second).filterNot(hypotheses.contains)

        for {
          assumed <- LogicError.lift(Kernel.assume(hypothesis))
          leftHalf <- rules.conjElim1(assumed)
          rightHalf <- rules.conjElim2(assumed)
          proved <- search(hypotheses ++ gained, goal, depth - 1)
          // The two halves were assumed to prove it; they are discharged against the conjunction,
          // so what comes back rests on the conjunction as the caller gave it.
          withFirst <- rules.proveHyp(leftHalf, proved)
          result <- rules.proveHyp(rightHalf, withFirst)
        } yield result

      case None =>
        hypotheses.collectFirst {
          case hypothesis if logic.destDisj(hypothesis).exists { case (first, second) =>
                !hypotheses.contains(first) && !hypotheses.contains(second)
              } =>
            hypothesis
        } match {
          case None => Left(NotOfForm("a conjunction or a disjunction among the hypotheses", goal))

          case Some(hypothesis) =>
            val (first, second) = logic.destDisj(hypothesis).get

            for {
              assumed <- LogicError.lift(Kernel.assume(hypothesis))
              leftCase <- search(hypotheses :+ first, goal, depth - 1)
              rightCase <- search(hypotheses :+ second, goal, depth - 1)
              result <- rules.disjElim(assumed, leftCase, rightCase)
            } yield result
        }
    }
  }

  /**
   * What is left, and every case here can be the wrong choice.
   *
   * An implication among the hypotheses is used when its antecedent is already there, which is the
   * terminating half of the left implication rule and is all the fragment this file exists for
   * needs: a monotonicity obligation carries `p ==> p'` beside `p`. A disjunctive goal is tried on
   * one side and then the other.
   */
  private def branching(
    hypotheses: Vector[Term],
    goal: Term,
    depth: Int
  ): Either[LogicError, Kernel.Thm] = {
    val usable = hypotheses.flatMap { hypothesis =>
      logic.destImp(hypothesis) match {
        case Some((antecedent, consequent))
          if hypotheses.contains(antecedent) && !hypotheses.contains(consequent) =>
          Vector((hypothesis, antecedent, consequent))
        case _ => Vector.empty
      }
    }

    val advanced = usable.view
      .map { case (hypothesis, antecedent, consequent) =>
        for {
          implication <- LogicError.lift(Kernel.assume(hypothesis))
          held <- LogicError.lift(Kernel.assume(antecedent))
          gained <- rules.mp(implication, held)
          proved <- search(hypotheses :+ consequent, goal, depth - 1)
          result <- rules.proveHyp(gained, proved)
        } yield result
      }
      .collectFirst { case Right(theorem) => theorem }

    advanced match {
      case Some(theorem) => Right(theorem)

      case None =>
        logic.destDisj(goal) match {
          case None => Left(NotOfForm("a goal this fragment reaches", goal))

          case Some((first, second)) =>
            search(hypotheses, first, depth - 1)
              .flatMap(rules.disjIntro1(second, _))
              .orElse(search(hypotheses, second, depth - 1).flatMap(rules.disjIntro2(first, _)))
        }
    }
  }
}

object Minimal {

  /**
   * How deep the search goes before it says so.
   *
   * The safety net and not the termination argument: the invertible rules strictly shrink the
   * problem and the two that branch are bounded by the hypotheses, so a goal of this fragment
   * terminates without it. It exists because that argument is a paragraph and this is a number, and
   * a search that ran away would be worse than one that stops.
   */
  val Depth: Int = 64

  /** Over the plain logic, which is where a statement with no arithmetic in it lives. */
  lazy val standard: Minimal = new Minimal(Logic.standard)

  /** Over a development of one's own, so that its own declared predicates can be atoms. */
  def apply(logic: Logic): Minimal = new Minimal(logic)
}
