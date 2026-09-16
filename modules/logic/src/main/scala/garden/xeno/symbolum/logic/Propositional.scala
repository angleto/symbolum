package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.sat.{Cnf, Derivation, Solver, Step}
import garden.xeno.symbolum.sat.Cnf.Literal

/**
 * The classical propositional fragment, decided by search and certified by the kernel.
 *
 * The solver in `modules/sat` finds the refutation and this file replays it. Nothing the solver says
 * is believed: what comes back from it is a list of resolution steps over numbers, and a theorem
 * exists here only because every one of those steps was re-derived through [[Rules]], which is
 * `docs/adr/0003` applied one level down from where it usually is.
 *
 * == What it is beside `Minimal`, and why neither replaces the other ==
 *
 * [[Minimal]] searches the fragment with no negation in it and reaches **zero axioms**. This one
 * reaches every classical tautology and costs the choice axiom. They are not two settings of one
 * procedure and a caller should not read them as one: a goal `Minimal` can take should go there,
 * because a theorem that rests on nothing is worth more than the same theorem resting on something.
 *
 * `Minimal` is also incomplete for this fragment rather than merely narrower, which is worth knowing
 * before choosing. Peirce's law, `((p ==> q) ==> p) ==> p`, has no negation in it, is classically
 * valid, and `Minimal` refuses it; `MinimalSpec` holds that boundary and `PropositionalSpec` holds
 * the other side of it.
 *
 * == The encoding, which is where the interesting decision is ==
 *
 * A goal is put to the solver by the Tseitin transformation: every subformula gets a variable, and
 * the connective that built it gets two or three clauses saying what it means. The naive route,
 * pushing negations in and then distributing `\/` over `/\`, is exponential in the goal and was not
 * taken.
 *
 * The usual objection to Tseitin in a proof assistant is that it introduces **new symbols**, and a
 * new symbol here is a constant in the theory, which this development does not hand out for the
 * duration of one proof. That objection does not apply, and the reason is the whole trick: the
 * variable standing for a subformula **is that subformula**. Nothing new is introduced. The clause
 * that says `x_{a /\ b}` implies `x_a` is, read back, `(a /\ b) ==> a`, and its proof is one
 * application of [[Rules.conjElim1]].
 *
 * So the encoding is linear in the goal, and each of its clauses costs between one and three
 * inference rules.
 *
 * == What it costs, and the shape of the answer is worth more than the number ==
 *
 * **Every step of a refutation is intuitionistic.** A clause `C` is carried as the theorem whose
 * hypotheses are the complements of its literals and whose conclusion is falsity, and a resolution
 * step is [[Rules.notIntro]] to discharge the pivot from one side, giving a negation, and
 * [[Rules.proveHyp]] to cut that negation into the other. Neither is classical. The clauses of the
 * encoding are intuitionistic too, every one of them.
 *
 * The classical step is **one**, at the very end: the refutation concludes falsity from the assumed
 * negation of the goal, which gives `~~goal`, and `Classical.DOUBLE_NEGATION` turns that into the
 * goal. That is Glivenko's theorem arriving as a property of the construction rather than as
 * something aimed at: the double negation of a classical propositional tautology is intuitionistically
 * provable, and this is what that looks like when a machine does it.
 *
 * Measured on the compiled tree of 2026-09-15, one resolution step is 90 primitive inferences for
 * the [[Rules.notIntro]] and 2 for the [[Rules.proveHyp]]. **92 per step, and the cost is linear in
 * the refutation, not in the goal.** The scope condition follows and is stated rather than
 * discovered: a refutation of ten thousand steps is about nine hundred thousand primitive
 * inferences, and one of a million steps is not on the table. `docs/adr/0010` is why that is the
 * price of a theorem here rather than a defect, and the ninety are the definition of `~` being
 * unfolded once per step, which is a known lever on the constant factor and is not pulled here.
 *
 * == The asymmetry, which is the one way this could mislead ==
 *
 * A subterm of type `bool` that is not built from the five connectives is an **atom**, and it is
 * given no meaning at all. That includes a quantified statement: `!x. P x` is an atom here.
 *
 * For [[prove]] that is sound and is a widening rather than a hole. The replay never looks inside an
 * atom, so a theorem it produces is a theorem whatever the atom means; `(!x. P x) \/ ~(!x. P x)` is
 * proved here and is a correct theorem.
 *
 * For the other answer it is **not** symmetric, and the name says so. [[Propositional.Verdict.Countermodel]]
 * reports an assignment under which the goal is false *with its atoms read as independent*. Two
 * atoms that are the same statement written differently, `x = y` and `y = x`, are two atoms, so a
 * goal that really is valid can come back with a countermodel. It is a refutation of the goal **as
 * a propositional schema** and never a statement that the goal is unprovable, and a caller that
 * reads it as the second has been misled by a name this file refuses to give it.
 * `garden.xeno.symbolum.tactics.Consistency` keeps the same two answers apart for the same reason
 * and calls its weak one `NotContradictory`.
 */
final class Propositional private (
  val classical: Classical,
  /**
   * What it READS a goal in, which need not be the logic the classical facts were proved over.
   *
   * The same arrangement `Prove` has between its procedures and its signature, and it is needed for
   * the same reason. A theory of a domain declares constants `Classical.standard` has never heard
   * of, so a goal about one can be **built** only against a logic widened to that theory; what is
   * decided is the propositional skeleton either way, because an atom here is given no meaning at
   * all.
   *
   * Reading wider than the facts were proved in is sound because the only thing taken from
   * [[classical]] is `DOUBLE_NEGATION`, a theorem about `bool` that says nothing about any domain.
   */
  val logic: Logic,
  val conflictLimit: Int
) {

  import Propositional.*

  private val rules: Rules = logic.rules

  /**
   * The goal, proved, or why not.
   *
   * Leading universal quantifiers come off before the search and go back on after it, which is what
   * [[Minimal.prove]] does and for the same reason: the body is what the fragment is about, and a
   * quantifier left on would make the whole goal one atom and the answer trivially a countermodel.
   */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    decide(goal) match {
      case Verdict.Proved(theorem) => Right(theorem)
      case Verdict.Countermodel(assignment) => Left(SkeletonFailsAt(goal, assignment))
      case Verdict.Undecided(why) => Left(NotOfForm(why, goal))
      case Verdict.Refused(why) => Left(NotOfForm(why, goal))
    }

  /** Whether this would take the goal at all, answered without spending anything on it. */
  def reads(goal: Term): Boolean =
    Logic.stripForall(goal).toOption.exists { case (_, body) => Term.typeOf(body) == Type.Bool }

  /** The goal, with the answer that is not a theorem kept apart from the answer that is. */
  def decide(goal: Term): Verdict =
    Logic.stripForall(goal) match {
      case Left(error) => Verdict.Refused(error.message)
      case Right((variables, body)) =>
        if (Term.typeOf(body) != Type.Bool) Verdict.Refused("a proposition")
        else
          settle(body) match {
            case Verdict.Proved(theorem) =>
              rules.genAll(theorem, variables.toList) match {
                case Right(closed) => Verdict.Proved(closed)
                case Left(error) => Verdict.Refused(error.message)
              }
            case other => other
          }
    }

  /* ------------------------------------------------------------------- reading the goal */

  /**
   * Every subformula of the goal, numbered, with the clauses that say what each connective means.
   *
   * Built bottom up so that a subformula is numbered before anything that contains it, which is what
   * lets a clause name its children by number. Two occurrences of the same subformula share a
   * number, because they are the same term and a `Map` keyed by terms says so; that is not an
   * optimisation but the thing that makes the encoding linear on a goal that repeats itself.
   */
  private final class Encoding {
    private val numbers = collection.mutable.LinkedHashMap.empty[Term, Int]
    private val order = collection.mutable.ArrayBuffer.empty[Term]
    val clauses = collection.mutable.ArrayBuffer.empty[(Vector[Literal], () => Either[LogicError, Kernel.Thm])]

    def variables: Int = order.length
    def termOf(variable: Int): Term = order(variable - 1)
    def atoms: Vector[Term] = order.toVector.filter(term => shapeOf(term).isEmpty)

    def number(term: Term): Int =
      numbers.getOrElse(
        term, {
          order += term
          val assigned = order.length
          numbers.put(term, assigned)
          assigned
        }
      )
  }

  /** What connective built a term, if one did. */
  private def shapeOf(term: Term): Option[(String, Term, Term)] =
    logic
      .destConj(term)
      .map { case (a, b) => ("and", a, b) }
      .orElse(logic.destDisj(term).map { case (a, b) => ("or", a, b) })
      .orElse(logic.destImp(term).map { case (a, b) => ("imp", a, b) })
      .orElse(logic.destNot(term).map(a => ("not", a, a)))

  private def assume(term: Term): Either[LogicError, Kernel.Thm] = LogicError.lift(Kernel.assume(term))

  /** The hypothesis a literal contributes to a clause's theorem: the complement of what it says. */
  private def complementOf(encoding: Encoding, literal: Literal): Either[LogicError, Term] = {
    val term = encoding.termOf(math.abs(literal))
    if (literal > 0) logic.mkNot(term) else Right(term)
  }

  /**
   * The goal read as clauses, each with the derivation that proves it.
   *
   * A clause is paired with a thunk rather than with a theorem because a refutation reads a fraction
   * of the clauses it is given and building the rest would be inference nobody asked for. On the
   * pigeonhole problems the core is every clause, so the saving is nothing there; on a goal with a
   * large irrelevant hypothesis it is most of them.
   */
  private def encode(body: Term): Either[LogicError, (Encoding, Int)] = {
    val encoding = new Encoding

    def walk(term: Term): Either[LogicError, Int] =
      shapeOf(term) match {
        case None =>
          if (Term.typeOf(term) != Type.Bool) Left(NotOfForm("a proposition", term))
          else if (term == logic.truth) {
            val at = encoding.number(term)
            encoding.clauses += ((Vector(at), () => rules.truth.flatMap(t => assume(negatedOf(term)).flatMap(rules.notElim(_, t)))))
            Right(at)
          } else if (term == logic.falsity) {
            val at = encoding.number(term)
            encoding.clauses += ((Vector(-at), () => assume(term)))
            Right(at)
          } else Right(encoding.number(term))

        case Some((connective, left, right)) =>
          for {
            l <- walk(left)
            r <- walk(right)
            at = encoding.number(term)
            _ = defining(encoding, connective, term, at, left, l, right, r)
          } yield at
      }

    walk(body).map(at => (encoding, at))
  }

  private def negatedOf(term: Term): Term =
    logic.mkNot(term).getOrElse(term)

  /**
   * The clauses that say what one connective means, each with its proof.
   *
   * Read back through the encoding, every one of them is a tautology of two or three literals and
   * every proof is two or three rule applications. That is the whole of what the Tseitin
   * transformation costs when the variables are the subformulas themselves.
   */
  private def defining(
    encoding: Encoding,
    connective: String,
    whole: Term,
    at: Int,
    left: Term,
    l: Int,
    right: Term,
    r: Int
  ): Unit = {
    def add(literals: Vector[Literal])(proof: => Either[LogicError, Kernel.Thm]): Unit =
      encoding.clauses += ((literals, () => proof))

    connective match {
      case "and" =>
        add(Vector(-at, l))(for { w <- assume(whole); h <- rules.conjElim1(w); n <- assume(negatedOf(left)); f <- rules.notElim(n, h) } yield f)
        add(Vector(-at, r))(for { w <- assume(whole); h <- rules.conjElim2(w); n <- assume(negatedOf(right)); f <- rules.notElim(n, h) } yield f)
        add(Vector(at, -l, -r))(for {
          a <- assume(left); b <- assume(right); both <- rules.conjIntro(a, b)
          n <- assume(negatedOf(whole)); f <- rules.notElim(n, both)
        } yield f)

      case "or" =>
        add(Vector(-at, l, r))(for {
          w <- assume(whole)
          leftCase <- assume(left).flatMap(a => assume(negatedOf(left)).flatMap(rules.notElim(_, a)))
          rightCase <- assume(right).flatMap(b => assume(negatedOf(right)).flatMap(rules.notElim(_, b)))
          f <- rules.disjElim(w, leftCase, rightCase)
        } yield f)
        add(Vector(at, -l))(for { a <- assume(left); d <- rules.disjIntro1(right, a); n <- assume(negatedOf(whole)); f <- rules.notElim(n, d) } yield f)
        add(Vector(at, -r))(for { b <- assume(right); d <- rules.disjIntro2(left, b); n <- assume(negatedOf(whole)); f <- rules.notElim(n, d) } yield f)

      case "imp" =>
        add(Vector(-at, -l, r))(for {
          w <- assume(whole); a <- assume(left); b <- rules.mp(w, a)
          n <- assume(negatedOf(right)); f <- rules.notElim(n, b)
        } yield f)
        // From `~left` the implication holds vacuously, which is where falsity elimination earns its
        // place: the branch proves the consequent from a contradiction rather than from anything the
        // consequent is about.
        add(Vector(at, l))(for {
          a <- assume(left); n <- assume(negatedOf(left)); absurd <- rules.notElim(n, a)
          anything <- rules.falsityElim(right, absurd); implication <- rules.disch(left, anything)
          d <- assume(negatedOf(whole)); f <- rules.notElim(d, implication)
        } yield f)
        add(Vector(at, -r))(for {
          b <- assume(right); implication <- rules.disch(left, b)
          d <- assume(negatedOf(whole)); f <- rules.notElim(d, implication)
        } yield f)

      case _ =>
        add(Vector(-at, -l))(for { a <- assume(left); n <- assume(whole); f <- rules.notElim(n, a) } yield f)
        add(Vector(at, l))(for { n <- assume(whole); d <- assume(negatedOf(whole)); f <- rules.notElim(d, n) } yield f)
    }
  }

  /* --------------------------------------------------------------------------- the decision */

  private def settle(body: Term): Verdict =
    encode(body) match {
      case Left(error) => Verdict.Refused(error.message)
      case Right((encoding, goalVariable)) =>
        val negated = negatedOf(body)
        // The goal's own clause: the assumption that it is false. Its theorem carries `~body` as an
        // extra hypothesis, which is the only hypothesis any clause theorem carries beyond the
        // complements of its literals, and it is the one discharged at the end.
        encoding.clauses += ((
          Vector(-goalVariable),
          () => for { n <- assume(negated); b <- assume(body); f <- rules.notElim(n, b) } yield f
        ))

        // The clauses are built in the order the connective reads, and the solver wants them
        // canonical. Normalising here keeps each clause beside the proof that justifies it, which
        // `Cnf.problem` cannot do because it drops what it cannot normalise and renumbers the rest.
        // Nothing is dropped: a defining clause of a connective names a subformula and one of its
        // own children, which are different terms and so never the same variable, so none of them
        // is a tautology and the `flatMap` below loses nothing. A clause that did would be a defect
        // here rather than a case to handle, and the count is asserted.
        val prepared = encoding.clauses.toVector.flatMap { case (literals, proof) =>
          Cnf.normalise(literals).map(clause => (clause, proof))
        }
        val problem = Cnf.Problem(encoding.variables, prepared.map(_._1))

        problem.check match {
          case Some(why) => Verdict.Refused(s"the encoding built a malformed problem, which is a defect here: $why")
          case None =>
            Solver.solve(problem, conflictLimit) match {
              case Solver.Answer.Malformed(why) => Verdict.Refused(why)
              case Solver.Answer.Undecided(why) => Verdict.Undecided(why)

              case Solver.Answer.Satisfiable(assignment) =>
                if (assignment(goalVariable - 1))
                  Verdict.Refused("a model falsifying the goal; the solver returned one satisfying it, which is a defect here")
                else
                  Verdict.Countermodel(
                    encoding.atoms.map(atom => atom -> assignment(indexOf(encoding, atom) - 1))
                  )

              case Solver.Answer.Unsatisfiable(derivation) =>
                derivation.check(problem) match {
                  case Left(why) => Verdict.Refused(s"a refutation that checks; the solver produced one that does not, which is a defect there: $why")
                  case Right(_) =>
                    replay(encoding, prepared, derivation, body, negated) match {
                      case Right(theorem) => Verdict.Proved(theorem)
                      case Left(error) => Verdict.Refused(error.message)
                    }
                }
            }
        }
    }

  private def indexOf(encoding: Encoding, term: Term): Int =
    (1 to encoding.variables).find(at => encoding.termOf(at) == term).getOrElse(1)

  /**
   * The refutation, re-derived through the rules, and then the one classical step.
   *
   * Every step is built from the two before it and nothing is searched for again, so this is linear
   * in the derivation and the constant is the 92 inferences the class comment measures.
   */
  private def replay(
    encoding: Encoding,
    clauses: Vector[(Vector[Literal], () => Either[LogicError, Kernel.Thm])],
    derivation: Derivation,
    body: Term,
    negated: Term
  ): Either[LogicError, Kernel.Thm] = {
    // Folded rather than looped, because this module is written without a mutable local and
    // `StyleSpec` asserts it over the sources. The `Either` short-circuits, so a step that cannot be
    // rebuilt stops the replay at the step that failed rather than at the end of the derivation.
    val rebuilt = derivation.steps.foldLeft(Right(Vector.empty[Kernel.Thm]): Either[LogicError, Vector[Kernel.Thm]]) {
      (carried, step) =>
        carried.flatMap { proved =>
          val outcome: Either[LogicError, Kernel.Thm] = step match {
            case Step.Input(index) => clauses(index)._2()

            case Step.Resolve(left, right, pivot) =>
              // `pivot` is positive by `Solver.resolveStep`, so the right antecedent holds the
              // negative literal and carries the subformula itself as a hypothesis. Discharging it
              // gives the negation the left antecedent is assuming, and cutting it in is the
              // resolvent.
              complementOf(encoding, -pivot).flatMap { held =>
                rules.notIntro(held, proved(right)).flatMap(rules.proveHyp(_, proved(left)))
              }
          }

          outcome.map(proved :+ _)
        }
    }

    rebuilt.flatMap { proved =>
      for {
        doubleNegated <- rules.notIntro(negated, proved(derivation.empty))
        scheme <- classical.fact(Classical.DoubleNegation)
        instance <- rules.spec(body, scheme)
        theorem <- rules.mp(instance, doubleNegated)
      } yield theorem
    }
  }
}

object Propositional {

  /**
   * What a goal came out as, and the four are not one answer with a flag on it.
   *
   * [[Countermodel]] is the weak answer and the class comment says at length why it is not the
   * negation of [[Proved]]: the atoms are uninterpreted, so a goal that is valid for a reason living
   * inside an atom comes back here. [[Undecided]] is the bound being reached and is a statement
   * about this procedure rather than about the goal. [[Refused]] is the goal being outside what this
   * reads at all.
   */
  enum Verdict {
    case Proved(theorem: Kernel.Thm)
    case Countermodel(assignment: Vector[(Term, Boolean)])
    case Undecided(why: String)
    case Refused(why: String)
  }

  /** Over the standard classical logic, which is the least this procedure can be built on. */
  lazy val standard: Propositional = new Propositional(Classical.standard, Classical.standard.logic, Solver.Conflicts)

  /** Over a development of one's own, so that its declared predicates are the atoms. */
  def apply(classical: Classical, conflictLimit: Int = Solver.Conflicts): Propositional =
    new Propositional(classical, classical.logic, conflictLimit)

  /**
   * The same, reading in a logic wider than the one the classical facts were proved over.
   *
   * The call a theory of a domain needs: its constants are not in `Classical.standard`'s theory, so
   * a goal naming them cannot be built against that logic at all, and the procedure would refuse a
   * statement that has nothing wrong with it. `Prove.construct(order, reals)` is the same call one
   * layer up and its docstring carries the argument.
   */
  def over(classical: Classical, logic: Logic, conflictLimit: Int = Solver.Conflicts): Propositional =
    new Propositional(classical, logic, conflictLimit)
}
