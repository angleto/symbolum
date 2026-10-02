package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Linarith, LinearFact, LinearForm, RealTheory}

/**
 * Whether a quantified linear claim holds over the reals, decided and not proved.
 *
 * The one shape nothing here could settle. `Ring`, `Field` and `Linarith` open a goal's leading
 * universals and work on the body, so a statement whose quantifiers alternate is outside all three,
 * and `Refutation` declines a universal premise because there is no finite domain to enumerate.
 * `docs/evaluation.md` calls that the failure autoformalisation is most known for, and track T
 * reported it as the one trap of nine this system could not separate: `!x. ?y. x < y` is true over
 * the reals and `?y. !x. x < y` is false, and until now nothing here could tell them apart. This is
 * what tells them apart, so all nine are separated and the swap is the ninth. Its row in that table
 * is its own: the other eight are separated by a point where the two readings disagree, or by a
 * proof of one reading beside a refusal of the other, and this one by a decision that eliminates
 * the quantifiers, which is different evidence and is reported as such.
 *
 * == It produces no theorem, and that is the design rather than a shortfall ==
 *
 * This is Fourier-Motzkin elimination over untrusted linear forms, in the same position as
 * `Refutation` and under the same record, `docs/adr/0005`: a model of the reals answers, nothing is
 * certified, and no `Kernel.Thm` is built or claimed. What it gives a reader is a decision they can
 * act on, and what it does not give them is a proof. Making it produce one is a different piece of
 * work, and a real one: each elimination step would need the density and unboundedness of the order
 * as derived lemmas.
 *
 * Nothing downstream may treat a [[Quantified.Holds]] as a theorem. It is evidence of the same kind
 * as a sampled point, decided rather than sampled.
 *
 * == What it decides, and what it turns away ==
 *
 * Quantifiers over the reals, nested and alternating as they like, over a body built from `<`,
 * `<=`, `=` between linear forms and combined with `~`, `/\`, `\/` and `==>`. Free variables are
 * read as universally quantified outermost, which is what asking whether a claim holds means.
 *
 * It refuses, by name, a body whose linear reading keeps an atom that is not one of the quantified
 * variables: a product of two unknowns, an inverse, anything `LinearForm.of` holds opaque. Such a
 * statement is not linear and this procedure is for the linear fragment; saying so is better than
 * eliminating the variables it can and reporting the rest as an answer.
 *
 * It also refuses when the elimination grows past [[Quantified.Bound]] disjuncts. Negation turns a
 * disjunction into a product of choices, so an alternating prefix over a wide body grows as the
 * product rather than the sum, and a procedure that took an hour without saying why would be worse
 * than one that stops.
 */
final class Quantified private (val linarith: Linarith) {

  import Quantified.*

  val reals: RealTheory = linarith.reals

  /** Whether the claim holds, for a statement written in the theory's notation. */
  def decide(text: String): Either[TacticError, Verdict] =
    TacticError.lift(reals.proposition(text)).flatMap(decide)

  /**
   * Whether the claim holds over the reals.
   *
   * Free variables are quantified universally first, so what is decided is the claim and not one
   * instance of it.
   */
  def decide(statement: Term): Either[TacticError, Verdict] = {
    val free = Term.freeVariables(statement).toVector.sortBy(_.name)

    eliminate(statement, free.map(variable => variable: Term).toSet) match {
      case Left(why) => Right(Refused(why))
      case Right(disjuncts) =>
        // The free variables are universal, so the claim holds when its negation is unsatisfiable
        // for any of them. Eliminating them one by one is the same computation as a universal
        // prefix, so it is done the same way rather than by a second route.
        free.foldLeft[Either[String, Dnf]](Right(disjuncts)) { (acc, variable) =>
          acc.flatMap(current => negate(current).flatMap(exists(variable, _)).flatMap(negate))
        } match {
          case Left(why) => Right(Refused(why))
          case Right(closed) => Right(ground(closed))
        }
    }
  }

  /* ------------------------------------------------------------ the elimination */

  /** A disjunction of conjunctions of facts, each fact read as `0 < f`, `0 <= f` or `0 = f`. */
  private type Dnf = Vector[Vector[LinearFact]]

  private val True: Dnf = Vector(Vector.empty)
  private val False: Dnf = Vector.empty

  /** The statement as a quantifier-free disjunction, or why it could not be read as one. */
  private def eliminate(term: Term, bound: Set[Term]): Either[String, Dnf] = {
    def opened(predicate: Term): Either[String, (Term, Term)] =
      Type.destFun(Term.typeOf(predicate)) match {
        case None => Left("a quantifier over something this procedure can range over")
        case Some((domain, _)) =>
          val variable =
            Conv.freshVariable("q", domain, Term.freeVariables(term) ++ bound.collect { case v: FVar => v })
          for {
            applied <- Term.app(predicate, variable).left.map(_.render(reals.show))
            body <- Term.betaReduce(applied).toRight("a quantifier applied to a lambda")
          } yield (variable, body)
      }

    reals.logic.destForallPredicate(term) match {
      case Some(predicate) =>
        for {
          pair <- opened(predicate)
          inner <- eliminate(pair._2, bound + pair._1)
          negated <- negate(inner)
          eliminated <- exists(pair._1, negated)
          result <- negate(eliminated)
        } yield result

      case None =>
        reals.logic.destExistsPredicate(term) match {
          case Some(predicate) =>
            for {
              pair <- opened(predicate)
              inner <- eliminate(pair._2, bound + pair._1)
              result <- exists(pair._1, inner)
            } yield result

          case None => connective(term, bound)
        }
    }
  }

  private def connective(term: Term, bound: Set[Term]): Either[String, Dnf] =
    reals.logic.destNot(term) match {
      case Some(inner) => eliminate(inner, bound).flatMap(negate)

      case None =>
        reals.logic.destConj(term) match {
          case Some((left, right)) =>
            for {
              a <- eliminate(left, bound)
              b <- eliminate(right, bound)
              result <- cross(a, b)
            } yield result

          case None =>
            reals.logic.destDisj(term) match {
              case Some((left, right)) =>
                for {
                  a <- eliminate(left, bound)
                  b <- eliminate(right, bound)
                  result <- union(a, b)
                } yield result

              case None =>
                reals.logic.destImp(term) match {
                  case Some((left, right)) =>
                    for {
                      a <- eliminate(left, bound).flatMap(negate)
                      b <- eliminate(right, bound)
                      result <- union(a, b)
                    } yield result

                  case None => atom(term, bound)
                }
            }
        }
    }

  /**
   * A leaf of the body as one fact, or the reason it is not one.
   *
   * It reads through `LinearFact.relation` and not `factOf`, and the difference is the whole of
   * what this procedure is allowed to claim. `factOf` turns a proposition it cannot read into a
   * strict fact over an atom nobody else mentions, which is right for a procedure that ends in a
   * theorem or in nothing: such a column can only fail to help. This one ends in a **verdict**, and
   * a column carrying an unchecked reading of a proposition would be answered about. A bare
   * proposition `p` would arrive as `0 < p`, and `0 < p \/ ~(0 < p)` is a tautology over an ordered
   * field, so this would report that `p \/ ~p` **holds** over the reals: a formula this logic does
   * not have, about a claim that is not about the reals at all, in the one place `docs/adr/0005`
   * says an answer must never be manufactured. So it refuses, and the refusal names the leaf.
   *
   * == The atom check, which used to be at the other end ==
   *
   * A fact may only rest on atoms this procedure can range over, which is the variables in scope:
   * the ones a quantifier opened plus the free ones, which are universal. That check used to live
   * in [[ground]], on what survived the elimination, and **an atom can vanish during it**.
   *
   * Measured, on somebody else's benchmark. `!x. x * (2 - x) <= 1` is true and this said it was
   * false. Its negation reads as `0 < 2x - a - 1` with `a` the opaque atom for `x * x`; eliminating
   * `x`, which has a lower bound and no upper one, leaves nothing at all, so the negation is
   * satisfiable, so the claim is false — and `a` is gone by then, so the guard at the end saw a
   * clean answer. Two more of miniF2F's 244 came back the same way.
   *
   * A wrong `Fails` is the worst answer this system can give. It is not an unsound theorem: nothing
   * is certified and `docs/adr/0005` says a verdict is not a proof. It is worse in use, because a
   * reader deletes a true conjecture on the strength of it, and the whole argument for keeping
   * seven answers in `Refutation` and five in `Cost` is that "I could not decide" and "I decided it
   * is false" must never be the same output.
   */
  private def atom(term: Term, bound: Set[Term]): Either[String, Dnf] =
    if (term == reals.logic.truth) Right(True)
    else if (term == reals.logic.falsity) Right(False)
    else
      LinearFact.relation(reals, term).left.map(_.render(reals.show)).flatMap { fact =>
        fact.form.atoms.find(!bound.contains(_)) match {
          case Some(opaque) =>
            Left(s"a linear statement; ${reals.show(opaque)} is an atom this procedure cannot range over")
          case None => Right(Vector(Vector(fact)))
        }
      }

  /* ---------------------------------------------------------- the algebra of a Dnf */

  private def sized(disjuncts: Dnf): Either[String, Dnf] =
    if (disjuncts.size <= Bound) Right(disjuncts)
    else Left(s"a statement whose elimination stays under $Bound cases; this one reached ${disjuncts.size}")

  private def union(left: Dnf, right: Dnf): Either[String, Dnf] = sized(left ++ right)

  private def cross(left: Dnf, right: Dnf): Either[String, Dnf] =
    sized(for { a <- left; b <- right } yield a ++ b)

  /**
   * The negation, as a disjunction again.
   *
   * Negating a disjunction of conjunctions gives a conjunction of disjunctions, and turning that
   * back into a disjunction is a product over the cases. That is where the size goes, and why the
   * bound above is checked at every step rather than only at the end.
   */
  private def negate(disjuncts: Dnf): Either[String, Dnf] =
    disjuncts.foldLeft[Either[String, Dnf]](Right(True)) { (acc, conjunct) =>
      for {
        current <- acc
        alternatives = conjunct.flatMap(opposite).map(Vector(_))
        result <- cross(current, if (conjunct.isEmpty) False else alternatives)
      } yield result
    }

  /** The negation of one fact, which is one fact except for an equality. */
  private def opposite(fact: LinearFact): Vector[LinearFact] = fact.kind match {
    case LinearFact.Kind.Strict => Vector(LinearFact(LinearFact.Kind.NonStrict, -fact.form))
    case LinearFact.Kind.NonStrict => Vector(LinearFact(LinearFact.Kind.Strict, -fact.form))
    case LinearFact.Kind.Equal =>
      Vector(
        LinearFact(LinearFact.Kind.Strict, fact.form),
        LinearFact(LinearFact.Kind.Strict, -fact.form)
      )
  }

  /* ------------------------------------------------------- Fourier-Motzkin, one variable */

  private def exists(variable: Term, disjuncts: Dnf): Either[String, Dnf] =
    disjuncts
      .foldLeft[Either[String, Dnf]](Right(False)) { (acc, conjunct) =>
        for {
          current <- acc
          eliminated <- eliminateFrom(variable, conjunct)
          result <- union(current, eliminated)
        } yield result
      }

  /**
   * One variable out of one conjunction.
   *
   * An equality is split into the two inequalities that say the same thing, so the elimination has
   * one shape rather than three. Every lower bound is paired with every upper bound, and the pair
   * is the same non-negative combination `Farkas` builds one level down: scaling the upper by the
   * lower's coefficient and the lower by minus the upper's, both of which are positive, so the
   * direction survives and the variable cancels.
   *
   * A variable with no lower bound, or none above, is unbounded on that side and the pairs are
   * empty, which is the elimination reporting that nothing constrains it.
   */
  private def eliminateFrom(
    variable: Term,
    conjunct: Vector[LinearFact]
  ): Either[String, Dnf] = {
    val split = conjunct.flatMap { fact =>
      fact.kind match {
        case LinearFact.Kind.Equal =>
          Vector(
            LinearFact(LinearFact.Kind.NonStrict, fact.form),
            LinearFact(LinearFact.Kind.NonStrict, -fact.form)
          )
        case _ => Vector(fact)
      }
    }

    val free = split.filter(_.form.at(variable).isZero)
    val lower = split.filter(_.form.at(variable).isPositive)
    val upper = split.filter(fact => !fact.form.at(variable).isZero && !fact.form.at(variable).isPositive)

    val combined = for {
      low <- lower
      high <- upper
      coefficient = low.form.at(variable)
      opposing = -high.form.at(variable)
      kind =
        if (low.kind == LinearFact.Kind.Strict || high.kind == LinearFact.Kind.Strict)
          LinearFact.Kind.Strict
        else LinearFact.Kind.NonStrict
    } yield LinearFact(kind, high.form.scaled(coefficient) + low.form.scaled(opposing))

    Right(Vector(free ++ combined))
  }

  /* --------------------------------------------------------------- reading the answer */

  /**
   * What a disjunction with nothing left to eliminate says.
   *
   * The leftover check here is now unreachable, and it is kept rather than deleted: [[atom]] turns
   * an unrangeable atom away before any elimination happens, so nothing should arrive with one, and
   * a procedure that answered anyway if something did would be answering about a form it cannot
   * read. It costs one traversal of a Dnf that is empty or small by this point.
   */
  private def ground(disjuncts: Dnf): Verdict = {
    val leftover = disjuncts.flatten.flatMap(_.form.atoms).distinct

    if (leftover.nonEmpty)
      Refused(
        s"a linear statement; ${reals.show(leftover.head)} is an atom this procedure cannot range over"
      )
    else if (disjuncts.exists(_.forall(satisfied))) Holds
    else Fails
  }

  private def satisfied(fact: LinearFact): Boolean = fact.kind match {
    case LinearFact.Kind.Strict => fact.form.constant.isPositive
    case LinearFact.Kind.NonStrict => fact.form.constant.isPositive || fact.form.constant.isZero
    case LinearFact.Kind.Equal => fact.form.constant.isZero
  }
}

object Quantified {

  /**
   * How many cases an elimination may reach before it stops.
   *
   * Negation turns a disjunction into a product of choices, so an alternating prefix over a wide
   * body grows as the product and not the sum. The number is a budget rather than a measurement of
   * anything: what it protects is a caller waiting without being told why.
   */
  val Bound: Int = 4096

  /** What the procedure decided, or that it would not. */
  sealed trait Verdict

  /** True over the reals, decided rather than proved, and never a theorem. */
  case object Holds extends Verdict

  /** Not true over the reals. */
  case object Fails extends Verdict

  /** Neither, with what it could not do. */
  final case class Refused(why: String) extends Verdict

  /** Over the standard theory. */
  lazy val standard: Quantified = new Quantified(Linarith.standard)

  /** Over a theory of one's own. */
  def apply(linarith: Linarith): Quantified = new Quantified(linarith)
}
