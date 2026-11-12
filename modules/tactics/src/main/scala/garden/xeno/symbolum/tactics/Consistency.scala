package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.Signature

/**
 * Whether a set of propositions can all hold at once, decided and never certified.
 *
 * This produces **no `Kernel.Thm`** and it lives where `Refutation` and `Quantified` live, under
 * `docs/adr/0005`: something answers, nothing is proved, and nothing downstream may read what comes
 * back as a proof. A test scans this file and fails if it names an inference rule, which is how
 * `Quantified` says the same thing about itself, and it is written as a scan rather than a runtime
 * check because `Kernel.Thm` erases to a pair and a type assertion about it would pass whatever the
 * file did.
 *
 * **It costs no axiom, and that is why it is worth having beside `Minimal`.** A classical decision
 * that *produced a theorem* would want the excluded middle under every answer. One that produces no
 * theorem is free, and the question it answers is the one somebody actually asks of a formalised
 * register of rules: **do two rules oblige and forbid the same thing?**
 *
 * == The asymmetry, which is the whole of what a reader has to understand ==
 *
 * The two answers are not two sides of one coin and merging them is how this machinery would
 * mislead.
 *
 * [[Consistency.Verdict.Contradictory]] is a **decision about the world**. If no assignment of
 * truth values to the atoms satisfies the premises, then they cannot all hold whatever those atoms
 * turn out to mean, because every real situation induces some assignment. That answer is sound and
 * final.
 *
 * [[Consistency.Verdict.NotContradictory]] is a statement about **propositional structure only**.
 * The atoms are uninterpreted here: `x = y` and `y = x` are two atoms, not one, so a set of
 * premises this calls not contradictory may still be unsatisfiable for a reason living inside an
 * atom. It is the honest name for the weaker answer, and it is why the name is not "consistent".
 *
 * == What it refuses, and the mistake it was written to avoid ==
 *
 * A quantifier, by name. `!x. p x` is a proposition and is not a connective, so a reader looking for
 * maximal non-connective subterms would happily take it as an atom — and then `(!x. p x)` and
 * `p a` are unrelated atoms, a genuine contradiction is missed, and the caller is told "not
 * contradictory" about premises that cannot hold. Refusing is the only honest answer for a
 * procedure that does not look inside a binder.
 *
 * **The leaves are read here and not through a reader built for a proving procedure.** On
 * 2026-09-10 `Quantified` answered `Holds` to `p \/ ~p` because it read its leaves with
 * `LinearFact.of`, whose documented fallback turns an unreadable proposition into the fact
 * `0 < p`, and `0 < p \/ ~(0 < p)` is a tautology over an ordered field. This is the third file that
 * could have made that mistake, so an atom here is exactly a bool-typed subterm that is not one of
 * the five connectives and is given no meaning at all.
 */
final class Consistency private (val reals: Signature) {

  import Consistency.*

  private val logic = reals.logic

  /**
   * Whether the premises, read in this development's notation, can all hold.
   *
   * Named apart from [[of]] rather than overloading it, because `Vector[String]` and `Vector[Term]`
   * erase to the same signature and the compiler refuses the pair. Saying so here rather than
   * leaving a reader to wonder why one entry point is spelled differently.
   */
  def reading(texts: Vector[String]): Verdict =
    texts.foldLeft(Right(Vector.empty): Either[String, Vector[Term]]) { (acc, text) =>
      acc.flatMap(done => reals.proposition(text).left.map(_.render(reals.show)).map(done :+ _))
    } match {
      case Left(why) => Verdict.Refused(s"a proposition this development can read: $why")
      case Right(premises) => of(premises)
    }

  /** Whether the premises can all hold. */
  def of(premises: Vector[Term]): Verdict =
    atomsOf(premises) match {
      case Left(why) => Verdict.Refused(why)

      case Right(atoms) if atoms.length > Atoms =>
        Verdict.Refused(s"a question over at most $Atoms atoms; this one has ${atoms.length}")

      case Right(atoms) =>
        val found = (0 until (1 << atoms.length)).view
          .map(row => atoms.zipWithIndex.map { case (atom, at) => atom -> ((row >> at) % 2 == 1) }.toMap)
          .find(assignment => premises.forall(holds(_, assignment)))

        found match {
          case None => Verdict.Contradictory
          case Some(assignment) =>
            Verdict.NotContradictory(
              atoms.map(atom => reals.show(atom) -> assignment(atom))
            )
        }
    }

  /**
   * Whether the claim holds under every assignment, which is validity and not provability.
   *
   * Asked as the contradiction of its denial, which is the same computation and keeps one reader of
   * the fragment rather than two. What comes back says [[Consistency.Verdict.Contradictory]] when
   * the claim is a tautology, and that reading is deliberately not hidden behind a friendlier name:
   * a caller that wants "valid" has to notice it is being told something about the denial.
   */
  def denialOf(claim: Term): Verdict =
    logic.mkNot(claim) match {
      case Left(error) => Verdict.Refused(error.render(reals.show))
      case Right(denied) => of(Vector(denied))
    }

  /* ------------------------------------------------------------------- reading the fragment */

  /** Every atom the premises rest on, in a fixed order, or why they are not of this fragment. */
  private def atomsOf(premises: Vector[Term]): Either[String, Vector[Term]] = {
    val found = collection.mutable.LinkedHashSet.empty[Term]

    def walk(term: Term): Option[String] =
      if (logic.destForallPredicate(term).isDefined)
        Some(s"a statement with no quantifier in it; ${reals.show(term)} has one")
      else if (logic.destExistsPredicate(term).isDefined)
        Some(s"a statement with no quantifier in it; ${reals.show(term)} has one")
      else
        logic
          .destConj(term)
          .orElse(logic.destDisj(term))
          .orElse(logic.destImp(term)) match {
          case Some((left, right)) => walk(left).orElse(walk(right))
          case None =>
            logic.destNot(term) match {
              case Some(inner) => walk(inner)
              case None =>
                if (Term.typeOf(term) != Type.Bool)
                  Some(s"a proposition; ${reals.show(term)} is not one")
                else if (term == logic.truth || term == logic.falsity) None
                else { found += term; None }
            }
        }

    premises.foldLeft(Option.empty[String])((why, premise) => why.orElse(walk(premise))) match {
      case Some(why) => Left(why)
      case None => Right(found.toVector)
    }
  }

  /** What a formula says under one assignment. Nothing here is a rule; it is arithmetic on booleans. */
  private def holds(term: Term, assignment: Map[Term, Boolean]): Boolean =
    logic.destConj(term) match {
      case Some((left, right)) => holds(left, assignment) && holds(right, assignment)
      case None =>
        logic.destDisj(term) match {
          case Some((left, right)) => holds(left, assignment) || holds(right, assignment)
          case None =>
            logic.destImp(term) match {
              case Some((left, right)) => !holds(left, assignment) || holds(right, assignment)
              case None =>
                logic.destNot(term) match {
                  case Some(inner) => !holds(inner, assignment)
                  case None =>
                    if (term == logic.truth) true
                    else if (term == logic.falsity) false
                    else assignment(term)
                }
            }
        }
    }
}

object Consistency {

  /**
   * What a set of premises came out as, and the three are kept apart on purpose.
   *
   * Collapsing [[Consistency.Verdict.Contradictory]] into [[Consistency.Verdict.Refused]] would
   * turn "they cannot all hold" into "I could not tell", which is the merge `Refutation` keeps
   * its answers apart to avoid one layer over.
   */
  enum Verdict {

    /**
     * No assignment satisfies them, so they cannot all hold. A decision about the world.
     *
     * Sound whatever the atoms mean: every situation induces an assignment, and none of them works.
     */
    case Contradictory

    /**
     * Some assignment satisfies them, and it is reported.
     *
     * **Not "consistent".** The atoms are uninterpreted, so `x = y` and `y = x` are two of them and
     * a set this calls not contradictory may still be unsatisfiable for a reason living inside an
     * atom. The name is the weaker claim because the answer is the weaker claim.
     */
    case NotContradictory(assignment: Vector[(String, Boolean)])

    /** Outside the fragment, and `why` names what stopped it. */
    case Refused(why: String)
  }

  /**
   * The most atoms this enumerates over, which is a bound on 2^n and not a taste.
   *
   * Sixteen is sixty-five thousand rows, which is milliseconds, and a register of rules that
   * reaches it wants a solver rather than an enumeration. A question over more is refused by name
   * rather than attempted, for the reason every bound in this repository is named: a procedure that
   * ran for an hour without saying why would be worse than one that stops.
   */
  val Atoms: Int = 16

  /** Over the standard theory of the reals, where an atom is anything it can read. */
  lazy val standard: Consistency = new Consistency(Prove.standard.reals)

  /** Over a development of one's own, which is what a domain theory wants. */
  def apply(reals: Signature): Consistency = new Consistency(reals)
}
