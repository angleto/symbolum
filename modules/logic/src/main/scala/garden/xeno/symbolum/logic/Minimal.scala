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
 * A statement built from atoms with `/\`, `\/` and `==>` and no negation needs none of it. The rules
 * are the ones `Rules` already derives from the kernel's ten, the search is [[Intuitionistic]]'s,
 * and what comes out reaches **zero axioms**. That is the whole reason this exists beside a
 * classical procedure rather than instead of one.
 *
 * == What is left here, since the search went ==
 *
 * The search was this file's own until the contraction-free calculus landed, and it is not any more:
 * one implementation rather than two, for the reason [[calculus]] gives. What did not move is the
 * fragment, which is the useful half at a call site. A goal with a negation in it is **out** here and
 * is taken by the wider procedure, so the two answer different questions: this one says "is the
 * statement inside the fragment that costs nothing and is it provable", and the wider one says "is
 * it intuitionistically provable", which is a question about a statement nobody promised to keep
 * positive.
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

  /**
   * The search, which is [[Intuitionistic]]'s and is no longer this file's.
   *
   * What lives here is the **fragment**: the gate below, the address, and the refusal that names the
   * negation. What used to live here as well was a sequent search of its own, and when a calculus
   * arrived that decides all of intuitionistic propositional logic at the same zero axioms, keeping
   * both would have been two implementations of one thing — the weaker of them incomplete even for
   * the fragment it published, since its left rule for an implication fired only where the
   * antecedent was already among the hypotheses.
   *
   * So this is the same promise over a wider search, and the promise is what the callers read: a
   * goal with a negation in it is refused here by name, and Peirce's law is still out of reach,
   * because it is out of reach of intuitionistic logic rather than of this file's old rule set.
   */
  private val calculus: Intuitionistic = Intuitionistic(logic)

  /** Prove a goal of the fragment, in the notation of whatever theory the logic reads. */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Logic.stripForall(goal)
      (_, body) = stripped
      _ <- inside(body)
      proved <- calculus.prove(goal)
    } yield proved

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
}

object Minimal {

  /** Over the plain logic, which is where a statement with no arithmetic in it lives. */
  lazy val standard: Minimal = new Minimal(Logic.standard)

  /** Over a development of one's own, so that its own declared predicates can be atoms. */
  def apply(logic: Logic): Minimal = new Minimal(logic)
}
