package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * An equation that follows from the equations among a goal's hypotheses by ring arithmetic,
 * proved through a certificate.
 *
 * `!a b x y. a * x + b * y = 3 /\ ... ==> a * x^5 + b * y^5 = 20` is not a ring identity, so `Ring`
 * refuses it, and it is not linear, so `Linarith` does not reach it. What it is, is a member of an
 * ideal: `G = c1 * D1 + ... + ck * Dk`, where `Di` is `Li - Ri` for the hypothesis `Li = Ri`, `G` is
 * the conclusion's own difference and the cofactors `ci` are polynomials. The search for the
 * cofactors is [[Groebner]], which is not trusted; this file turns its answer into a theorem, and
 * a wrong answer is refused by the kernel rather than believed.
 *
 * == How the certificate becomes a theorem, and why not by rewriting ==
 *
 * `Algebraic` does the triangular case of this by stating the cofactor identity, having `Ring`
 * prove it, and rewriting with the assumed equations. Rewriting is fragile in general: an
 * assumption `b = a + 1` rewrites every `b`, including the ones inside the other hypotheses'
 * differences, which then no longer vanish. So the substitution here is done by **congruence on a
 * term this file built**, which involves no matching at all:
 *
 * {{{
 *   Ring:        Gl = Gr + (c1 * D1 + ... + ck * Dk)
 *   congruence:  Gr + (c1 * D1 + ... ) = Gr + (c1 * 0 + ...)      each Di = 0 from its hypothesis
 *   Ring:        Gr + (c1 * 0 + ...) = Gr
 * }}}
 *
 * and the three compose to `Gl = Gr` under the hypotheses, which are then discharged in the order
 * the goal states them. Nothing here is asserted, no constant is introduced, and the only
 * procedure trusted with arithmetic is `Ring`, which decides ring identities and is the one
 * reading of the certificate that does not depend on how it was found.
 *
 * == What it reads, and what it does not ==
 *
 * Sums, differences, negations, products and quotients by a non-zero rational constant, as
 * [[LinearForm]] reads them, with products multiplied out rather than kept as atoms. Everything
 * else is an atom, which costs a proof rather than yielding a wrong one: `inv y` is an unknown here,
 * and `y * inv y = 1` is not something this file knows. Hypotheses that are not equations between
 * reals stay assumed and unused, so a goal whose conclusion needs an order fact is refused by
 * `OutsideTheIdeal` and never decided.
 */
final class Ideal private (val ring: Ring, val budget: Long) {

  val reals: RealTheory = ring.reals

  private val rules: Rules = reals.logic.rules
  private val real: Type = Real.realType
  private val binary: Type = Type.fun(real, Type.fun(real, real))

  /** Prove a goal written in the theory's notation. */
  def prove(text: String): Either[LogicError, Kernel.Thm] = reals.proposition(text).flatMap(prove)

  /**
   * `!vars. H1 ==> ... ==> Hn ==> L = R`, each `Hi` possibly a conjunction, proved or refused.
   *
   * The refusals keep apart what a caller acts on differently: a goal of the wrong shape is
   * `NotOfForm`; a conclusion outside the ideal of the equations is `OutsideTheIdeal`, which is
   * never decided; the search running out of [[Groebner.Budget]] is `BoundReached`; and a
   * certificate the kernel would not rebuild is `NotRebuilt`, which is a defect here and not a
   * fact about the goal.
   */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    for {
      problem <- read(goal)
      proved <- certify(goal, problem, Groebner.membership(problem.generators, problem.target, problem.atoms.length, budget))
      discharged <- problem.antecedents.foldRight(Right(proved): Either[LogicError, Kernel.Thm]) {
        (antecedent, acc) => acc.flatMap(inner => rules.disch(antecedent, inner))
      }
      general <- problem.variables.reverse.foldLeft(Right(discharged): Either[LogicError, Kernel.Thm]) {
        (acc, variable) => acc.flatMap(inner => rules.gen(variable, inner))
      }
      result <-
        if (general.hypotheses.nonEmpty) LogicError.lift(Left(TheoremHasHypotheses(general.hypotheses)))
        else if (general.conclusion == goal) Right(general)
        else Left(NotOfForm("the goal as stated", general.conclusion))
    } yield result

  /**
   * What the untrusted search answers for a goal, with nothing rebuilt.
   *
   * Public for the reason `Prove.searchFor` is: the theorem does not say what the search spent, and
   * [[Groebner.Budget]] is a bound that is only worth anything measured against what goals cost.
   */
  def search(goal: Term): Either[LogicError, Groebner.Membership] =
    read(goal).map(problem => Groebner.membership(problem.generators, problem.target, problem.atoms.length, budget))

  /* ---------------------------------------------------------------- the search */

  /** A goal taken apart: its binders, its antecedents, its equations and their polynomials. */
  private final case class Problem(
    variables: Vector[FVar],
    antecedents: Vector[Term],
    left: Term,
    right: Term,
    equations: Vector[(Kernel.Thm, Term, Term)],
    atoms: Vector[Term],
    generators: Vector[Groebner.Poly],
    target: Groebner.Poly
  )

  private def read(goal: Term): Either[LogicError, Problem] =
    for {
      stripped <- Logic.stripForall(goal)
      (variables, body) = stripped
      (antecedents, conclusion) = peel(body, Vector.empty)
      sides <- Term.destEq(conclusion)
        .filter((left, _) => Term.typeOf(left) == real)
        .toRight(NotOfForm("an equation between reals as the conclusion", conclusion))
      assumed <- traverse(antecedents)(term => LogicError.lift(Kernel.assume(term)))
      facts <- traverse(assumed)(project).map(_.flatten)
      equations = facts.flatMap(fact => Term.destEq(fact.conclusion).collect {
        case (left, right) if Term.typeOf(left) == real => (fact, left, right)
      })
      _ <- if (equations.isEmpty) Left(NotOfForm("a goal with an equation among its hypotheses", goal)) else Right(())
    } yield {
      val (left, right) = sides
      val atoms = (equations.flatMap((_, l, r) => Vector(l, r)) ++ Vector(left, right)).flatMap(atomsOf).distinct
      val index = atoms.zipWithIndex.toMap
      def poly(term: Term): Groebner.Poly = polynomialOf(term, index, atoms.length)
      Problem(
        variables,
        antecedents,
        left,
        right,
        equations,
        atoms,
        equations.map((_, l, r) => Groebner.subtract(poly(l), poly(r))),
        Groebner.subtract(poly(left), poly(right))
      )
    }

  private def certify(goal: Term, problem: Problem, membership: Groebner.Membership): Either[LogicError, Kernel.Thm] =
    membership match {
      case Groebner.Membership.Exhausted(spent, budget) =>
        Left(BoundReached("Groebner.Budget", spent.min(Int.MaxValue).toInt, budget.min(Int.MaxValue).toInt, goal))
      case Groebner.Membership.NotMember(remainder, _) =>
        Left(OutsideTheIdeal(goal, show(remainder, problem.atoms)))
      case Groebner.Membership.Member(cofactors, _) =>
        rebuild(problem.left, problem.right, problem.equations, cofactors, problem.atoms)
          .left.map(reason => NotRebuilt(goal, "IDEAL", reason))
    }

  /* ---------------------------------------------------------------- the kernel half */

  private def rebuild(
    left: Term,
    right: Term,
    equations: Vector[(Kernel.Thm, Term, Term)],
    cofactors: Vector[Groebner.Poly],
    atoms: Vector[Term]
  ): Either[LogicError, Kernel.Thm] =
    for {
      plus <- constant(Real.Addition, binary)
      times <- constant(Real.Multiplication, binary)
      zero <- Numeral.of(reals, 0)
      used = equations.indices.filter(i => cofactors(i).nonEmpty).toVector
      summands <- traverse(used) { i =>
        val (fact, l, r) = equations(i)
        for {
          coefficient <- termOf(cofactors(i), atoms)
          difference <- Linarith.difference(reals, l, r)
          vanishes <- vanishing(fact, l, difference)
        } yield (coefficient, difference, vanishes)
      }
      combination <- sumOf(plus, summands.map((c, d, _) => (c, d)), times, zero)
      collapsed <- sumOf(plus, summands.map((c, _, _) => (c, zero)), times, zero)
      congruent <- congruence(plus, times, summands)
      withRight <- Linarith.sum(reals, right, combination)
      identityGoal <- LogicError.lift(Term.eq(left, withRight))
      identity <- ring.prove(identityGoal)
      plusRight <- LogicError.lift(Term.app(plus, right))
      shifted <- LogicError.lift(Kernel.mkComb(Kernel.refl(plusRight), congruent))
      residue <- Linarith.sum(reals, right, collapsed)
      closingGoal <- LogicError.lift(Term.eq(residue, right))
      closing <- ring.prove(closingGoal)
      step <- LogicError.lift(Kernel.trans(identity, shifted))
      whole <- LogicError.lift(Kernel.trans(step, closing))
    } yield whole

  /** `|- L - R = 0` from `|- L = R`, by congruence and one ring step. */
  private def vanishing(fact: Kernel.Thm, left: Term, difference: Term): Either[LogicError, Kernel.Thm] =
    for {
      minus <- constant(Real.Subtraction, binary)
      // `L - L = L - R`, turned round, then `L - L = 0`.
      minusLeft <- LogicError.lift(Term.app(minus, left))
      same <- LogicError.lift(Kernel.mkComb(Kernel.refl(minusLeft), fact))
      turned <- Conv.sym(same)
      zero <- Numeral.of(reals, 0)
      selfDifference <- Linarith.difference(reals, left, left)
      cancels <- LogicError.lift(Term.eq(selfDifference, zero)).flatMap(ring.prove)
      result <- LogicError.lift(Kernel.trans(turned, cancels))
      _ <- if (Term.destEq(result.conclusion).exists(_._1 == difference)) Right(())
           else Left(NotOfForm("the hypothesis's difference equal to zero", result.conclusion))
    } yield result

  /**
   * `p1 + (p2 + (... + pn))` with `pi = ci * ai`, or `0` for no summands.
   *
   * One nesting rule, shared with [[congruence]] through [[nest]], because the congruence theorem is
   * built on this exact shape and two folds written separately are two chances to disagree on it.
   */
  private def sumOf(plus: Term, parts: Vector[(Term, Term)], times: Term, zero: Term): Either[LogicError, Term] =
    traverse(parts)((c, a) => LogicError.lift(Term.appAll(times, List(c, a)))).flatMap { products =>
      nest(products, Right(zero), (head, rest) => LogicError.lift(Term.appAll(plus, List(head, rest))))
    }

  /** `c1 * D1 + (...) = c1 * 0 + (...)`, summand by summand, on the shape [[sumOf]] built. */
  private def congruence(
    plus: Term,
    times: Term,
    summands: Vector[(Term, Term, Kernel.Thm)]
  ): Either[LogicError, Kernel.Thm] =
    traverse(summands)((c, _, vanishes) =>
      LogicError.lift(Term.app(times, c).flatMap(scaled => Kernel.mkComb(Kernel.refl(scaled), vanishes)))
    )
      .flatMap { equations =>
        nest(
          equations,
          Numeral.of(reals, 0).map(Kernel.refl),
          (head, rest) =>
            LogicError.lift(Kernel.mkComb(Kernel.refl(plus), head).flatMap(Kernel.mkComb(_, rest)))
        )
      }

  /** The right-nested fold both [[sumOf]] and [[congruence]] use: the last item alone, the rest consed on. */
  private def nest[A](
    items: Vector[A],
    empty: => Either[LogicError, A],
    cons: (A, A) => Either[LogicError, A]
  ): Either[LogicError, A] =
    items.lastOption match {
      case None => empty
      case Some(last) =>
        items.init.foldRight(Right(last): Either[LogicError, A])((head, acc) => acc.flatMap(cons(head, _)))
    }

  /* ---------------------------------------------------------------- reading and writing */

  private def peel(current: Term, taken: Vector[Term]): (Vector[Term], Term) =
    reals.logic.destImp(current) match {
      case Some((antecedent, consequent)) => peel(consequent, taken :+ antecedent)
      case None => (taken, current)
    }

  /** Every conjunct of an assumed antecedent, as a theorem of its own. */
  private def project(theorem: Kernel.Thm): Either[LogicError, Vector[Kernel.Thm]] =
    reals.logic.destConj(theorem.conclusion) match {
      case None => Right(Vector(theorem))
      case Some(_) =>
        for {
          left <- rules.conjElim1(theorem)
          right <- rules.conjElim2(theorem)
          leftParts <- project(left)
          rightParts <- project(right)
        } yield leftParts ++ rightParts
    }

  /** The atoms of a term as [[polynomialOf]] will see it: whatever is not arithmetic on constants. */
  private def atomsOf(term: Term): Vector[Term] =
    if (LinearForm.coefficient(reals, term).isDefined) Vector.empty
    else term match {
      case App(App(Const(Real.Addition, _), l), r) => atomsOf(l) ++ atomsOf(r)
      case App(App(Const(Real.Subtraction, _), l), r) => atomsOf(l) ++ atomsOf(r)
      case App(App(Const(Real.Multiplication, _), l), r) => atomsOf(l) ++ atomsOf(r)
      case App(Const(Real.Negation, _), a) => atomsOf(a)
      case App(App(Const(Real.Division, _), l), r) if divisor(r).isDefined => atomsOf(l)
      case other => Vector(other)
    }

  private def divisor(term: Term): Option[Rational] = LinearForm.coefficient(reals, term).filter(!_.isZero)

  private def polynomialOf(term: Term, index: Map[Term, Int], arity: Int): Groebner.Poly =
    LinearForm.coefficient(reals, term) match {
      case Some(value) => Groebner.constant(value, arity)
      case None =>
        term match {
          case App(App(Const(Real.Addition, _), l), r) => Groebner.add(polynomialOf(l, index, arity), polynomialOf(r, index, arity))
          case App(App(Const(Real.Subtraction, _), l), r) => Groebner.subtract(polynomialOf(l, index, arity), polynomialOf(r, index, arity))
          case App(App(Const(Real.Multiplication, _), l), r) => Groebner.multiply(polynomialOf(l, index, arity), polynomialOf(r, index, arity))
          case App(Const(Real.Negation, _), a) => Groebner.negate(polynomialOf(a, index, arity))
          case App(App(Const(Real.Division, _), l), r) if divisor(r).isDefined =>
            Groebner.multiply(polynomialOf(l, index, arity), Groebner.constant(Rational.one / divisor(r).get, arity))
          case other => Groebner.variable(index(other), arity)
        }
    }

  /** A polynomial over the atoms as a term: a sum of coefficient-times-monomial, or `0`. */
  private def termOf(polynomial: Groebner.Poly, atoms: Vector[Term]): Either[LogicError, Term] = {
    val ordered = polynomial.toVector.sortWith((a, b) => Groebner.compare(a._1, b._1) > 0)
    val monomials = traverse(ordered) { (monomial, c) =>
      val factors = atoms.indices.flatMap(i => Vector.fill(monomial(i))(atoms(i))).toVector
      // A coefficient of one is left out, so the remainder in a refusal reads `x + -2` and not
      // `1 * x + -2`; `Ring` reads both alike, so the certificate does not care which.
      val start: Either[LogicError, Option[Term]] =
        if (c == Rational.one && factors.nonEmpty) Right(None) else Linarith.constant(reals, c).map(Some(_))
      start.flatMap { coefficient =>
        val leading = coefficient.getOrElse(factors.head)
        val rest = if (coefficient.isDefined) factors else factors.tail
        rest.foldLeft(Right(leading): Either[LogicError, Term])((acc, factor) => acc.flatMap(Linarith.product(reals, _, factor)))
      }
    }
    monomials.flatMap { terms =>
      terms.headOption match {
        case None => Numeral.of(reals, 0)
        case Some(first) =>
          terms.tail.foldLeft(Right(first): Either[LogicError, Term])((acc, next) => acc.flatMap(Linarith.sum(reals, _, next)))
      }
    }
  }

  /** The remainder as a reader would write it, for the refusal. */
  private def show(polynomial: Groebner.Poly, atoms: Vector[Term]): String =
    termOf(polynomial, atoms).map(reals.show).getOrElse(polynomial.toString)

  private def constant(name: String, ty: Type): Either[LogicError, Term] =
    LogicError.lift(reals.theory.constant(name, ty))

  private def traverse[A, B](items: Vector[A])(f: A => Either[LogicError, B]): Either[LogicError, Vector[B]] =
    items.foldLeft(Right(Vector.empty): Either[LogicError, Vector[B]]) { (acc, item) =>
      for { done <- acc; next <- f(item) } yield done :+ next
    }
}

object Ideal {

  /** Over the ring the order was built on, which is the one every other arithmetic procedure uses. */
  def construct(ring: Ring): Ideal = new Ideal(ring, Groebner.Budget)

  /**
   * The same procedure with the search's budget somewhere else, which is how the bound is measured
   * and how its refusal is seen. `Linarith.at` is the precedent and its comment the argument: a
   * bound that cannot be moved cannot be measured.
   */
  def at(ring: Ring, budget: Long): Ideal = new Ideal(ring, budget)

  lazy val standard: Ideal = construct(Ring.standard)
}
