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
 * [[LinearForm]] reads them, with products multiplied out rather than kept as atoms. A quotient by
 * anything else is read as a product with `inv r`, which is what `/` abbreviates. Everything else
 * is an atom, which costs a proof rather than yielding a wrong one. Hypotheses that are not
 * equations between reals stay assumed, and only two kinds are spent, both below.
 *
 * == A denominator the hypotheses say is not zero ==
 *
 * `inv y` is an unknown like any other atom, and `y * inv y = 1` is true only where `y` is not
 * zero, which is `MUL_INVERSE`'s antecedent. So that equation joins the generators exactly when a
 * hypothesis says so: `~(y = 0)`, or `0 < y`, which `NON_ZERO` turns into it. The fact is a theorem
 * resting on that hypothesis, so it enters the certificate the way an assumed equation does and
 * the kernel sees the side condition being paid. A denominator whose sign nobody stated stays an
 * unknown, and a goal that needed it is refused rather than proved by assuming it away.
 *
 * == The radical ==
 *
 * `x * x = 0 ==> x = 0` is true of the reals and `x` is not in the ideal of `x * x`, so ideal
 * membership alone refuses it, and `amc12_2000_p20` is that case after its denominators are
 * cleared: `(x * y * z - 1)^2` is in the ideal and `x * y * z - 1` is not. When the difference `D`
 * is not a member, the search asks for `D^2`, then `D^4`, up to [[Ideal.Squarings]] times; a member
 * `D^(2^m) = 0` is rebuilt as above, and `SQUARE_ZERO`, `m` times, brings it down to `D = 0`. Only
 * the powers of two are asked, because they are the ones a square root takes back in one step, and
 * every power is below one of them: `D^k = 0` puts every larger power in the ideal too.
 *
 * What this is **not** is a decision about the radical. The reals are not algebraically closed, so
 * the real radical is larger than the one any power of `D` reaches: `x * x + y * y = 0 ==> x = 0`
 * is true and `x` has no power in that ideal. A refusal after every squaring is still
 * `OutsideTheIdeal`, read as unread and never as decided.
 */
final class Ideal private (val order: Order, val budget: Long) {

  val ring: Ring = order.ring

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
      proved <- settle(goal, problem)
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
      (left, right) = sides
      stated = (equations.flatMap((_, l, r) => Vector(l, r)) ++ Vector(left, right)).flatMap(atomsOf).distinct
      nonZero <- traverse(facts)(nonZeroOf).map(_.flatten.toMap)
      inverses <- traverse(stated.collect { case App(Const(Real.Inverse, _), r) if nonZero.contains(r) => r })(
        r => inverseEquation(r, nonZero(r))
      )
    } yield assemble(variables, antecedents, left, right, equations ++ inverses)

  /** The problem over a set of equations: their atoms, and every side as a polynomial over them. */
  private def assemble(
    variables: Vector[FVar],
    antecedents: Vector[Term],
    left: Term,
    right: Term,
    all: Vector[(Kernel.Thm, Term, Term)]
  ): Problem = {
    val atoms = (all.flatMap((_, l, r) => Vector(l, r)) ++ Vector(left, right)).flatMap(atomsOf).distinct
    val index = atoms.zipWithIndex.toMap
    def poly(term: Term): Groebner.Poly = polynomialOf(term, index, atoms.length)
    Problem(
      variables,
      antecedents,
      left,
      right,
      all,
      atoms,
      all.map((_, l, r) => Groebner.subtract(poly(l), poly(r))),
      Groebner.subtract(poly(left), poly(right))
    )
  }

  /** `G |- ~(r = 0)` from a fact `~(r = 0)` or `0 < r`, keyed by `r`; nothing from any other fact. */
  private def nonZeroOf(fact: Kernel.Thm): Either[LogicError, Option[(Term, Kernel.Thm)]] =
    reals.logic.destNot(fact.conclusion).flatMap(Term.destEq) match {
      case Some((r, zero)) if Term.typeOf(r) == real && LinearForm.coefficient(reals, zero).exists(_.isZero) =>
        Right(Some((r, fact)))
      case _ =>
        Order.destLess(reals, fact.conclusion).toOption match {
          case Some((zero, r)) if LinearForm.coefficient(reals, zero).exists(_.isZero) =>
            order.nonZero.flatMap(rules.spec(r, _)).flatMap(rules.mp(_, fact)).map(proved => Some((r, proved)))
          case _ => Right(None)
        }
    }

  /** `G |- r * inv r = 1`, from `MUL_INVERSE` and the fact that `r` is not zero. */
  private def inverseEquation(r: Term, nonZero: Kernel.Thm): Either[LogicError, (Kernel.Thm, Term, Term)] =
    for {
      law <- reals.law("MUL_INVERSE")
      fact <- rules.spec(r, law).flatMap(rules.mp(_, nonZero))
      sides <- Term.destEq(fact.conclusion).toRight(NotOfForm("an equation", fact.conclusion))
    } yield (fact, sides._1, sides._2)

  /**
   * The conclusion from the search: a member, or failing that a member at a power of two of its
   * difference, up to [[Ideal.Squarings]]. A budget run out at any stage is reported as such
   * rather than as a refusal, because a search that stopped has not said the goal is outside.
   */
  private def settle(goal: Term, problem: Problem): Either[LogicError, Kernel.Thm] =
    radicalOrNot(goal, problem) match {
      case Left(remainder) => ordered(goal, problem, remainder)
      case Right(settled) => settled
    }

  /**
   * The difference or one of its squarings as a member, settled; or `Left` with the plain
   * difference's remainder when every one of them is outside the ideal, which is the one answer
   * the order may still change.
   */
  private def radicalOrNot(goal: Term, problem: Problem): Either[Groebner.Poly, Either[LogicError, Kernel.Thm]] = {
    def ask(target: Groebner.Poly) = Groebner.membership(problem.generators, target, problem.atoms.length, budget)
    ask(problem.target) match {
      case Groebner.Membership.NotMember(remainder, _) =>
        val powers = Iterator.iterate(problem.target)(t => Groebner.multiply(t, t)).drop(1).take(Ideal.Squarings)
        val answers = powers.map(ask).zipWithIndex.map((answer, i) => (answer, i + 1))
        answers.find(!_._1.isInstanceOf[Groebner.Membership.NotMember]) match {
          case Some((Groebner.Membership.Member(cofactors, _), squarings)) =>
            Right(radical(problem, cofactors, squarings).left.map(reason => NotRebuilt(goal, "IDEAL", reason)))
          case Some((other, _)) => Right(certify(goal, problem, other))
          case None => Left(remainder)
        }
      case answer => Right(certify(goal, problem, answer))
    }
  }

  /**
   * The order's turn, once the difference `D` and its squarings are all outside the ideal.
   *
   * The search asks for the least `p` with `p(D)` in the ideal, written `D^m * q(D)` with `q(0)`
   * not zero. Where `m` is at least one and `q` is not a constant, `D` is zero at every common zero
   * where `q(D)` is not, so the goal follows from `q(D)` having a sign. That sign is asked of
   * `Linarith`, positive and then negative, and one it proves makes `Q * inv Q = 1` a theorem for
   * the signed cofactor `Q`, which joins the equations exactly as a denominator does. In that larger
   * ideal `D^m` is a member, so the radical above finishes the proof. The kernel never sees `p`: it
   * sees memberships, an inverse justified by a proved sign, and squarings.
   *
   * == Why the sign is asked in normal form ==
   *
   * `Linarith` multiplies the hypotheses as they are written, and the sign often needs a product
   * of hypotheses the equations have rewritten. In `amc12b_2002_p7` the cofactor reduces to
   * `3 * (c - 1)^2`, and what makes it positive is `(c - 2)^2 > 0`, which is the square of
   * `0 < a` once `a` is written as `c - 2`. So every order hypothesis `l < r` or `l <= r` whose
   * atoms the ideal knows is reduced first: `r - l = N` is a member of the ideal, rebuilt like any
   * other, `0 < N` follows from it linearly, and `Linarith` is asked for the cofactor's own normal
   * form from those reduced facts. Reducing changes nothing modulo the ideal, so the cofactor's
   * normal form serves wherever the cofactor did.
   *
   * Every refusal here is the one the plain difference earned, `OutsideTheIdeal` with its
   * remainder, except a budget run out, which is reported as such.
   */
  private def ordered(goal: Term, problem: Problem, remainder: Groebner.Poly): Either[LogicError, Kernel.Thm] = {
    val arity = problem.atoms.length
    lazy val outside = certify(goal, problem, Groebner.Membership.NotMember(remainder, 0L))
    Groebner.minimalPolynomial(problem.generators, problem.target, arity, Ideal.Degree, budget) match {
      case Left(exhausted) => certify(goal, problem, exhausted)
      case Right(None) => outside
      case Right(Some(coefficients)) =>
        val m = coefficients.indexWhere(!_.isZero)
        val q = coefficients.drop(m)
        if (m == 0 || q.length < 2) outside
        else {
          val powers = Vector.iterate(Groebner.one(arity), q.length)(Groebner.multiply(_, problem.target))
          val cofactor = q.indices.foldLeft(Groebner.zero)((acc, k) =>
            Groebner.add(acc, Groebner.multiply(Groebner.constant(q(k), arity), powers(k)))
          )
          val bounds = orderFacts(problem)
          Groebner.remainders(problem.generators, cofactor +: bounds.map(_.difference), arity, budget) match {
            case Left(exhausted) => certify(goal, problem, exhausted)
            case Right(normal) =>
              val reduced = bounds.zip(normal.tail).flatMap((bound, n) => reduce(problem, bound, n))
              Iterator(normal.head, Groebner.negate(normal.head))
                .map(signed => signedInverse(problem, reduced, signed))
                .collectFirst { case Some(equation) => equation }
                .fold(outside) { equation =>
                  val larger =
                    assemble(problem.variables, problem.antecedents, problem.left, problem.right, problem.equations :+ equation)
                  radicalOrNot(goal, larger).getOrElse(outside)
                }
          }
        }
    }
  }

  /** An order hypothesis `l < r` or `l <= r` over atoms the ideal knows, with `r - l` as a polynomial. */
  private final case class Bound(fact: Kernel.Thm, left: Term, right: Term, strict: Boolean, difference: Groebner.Poly)

  private def orderFacts(problem: Problem): Vector[Bound] = {
    val index = problem.atoms.zipWithIndex.toMap
    val facts = traverse(problem.antecedents)(a => LogicError.lift(Kernel.assume(a)).flatMap(project))
      .map(_.flatten).getOrElse(Vector.empty)
    facts.flatMap { fact =>
      val read = Order.destLess(reals, fact.conclusion).toOption.map((l, r) => (l, r, true))
        .orElse(Order.destLessEqual(reals, fact.conclusion).toOption.map((l, r) => (l, r, false)))
      read.collect {
        case (l, r, strict) if Term.typeOf(l) == real && (atomsOf(l) ++ atomsOf(r)).forall(index.contains) =>
          val poly = (t: Term) => polynomialOf(t, index, problem.atoms.length)
          Bound(fact, l, r, strict, Groebner.subtract(poly(r), poly(l)))
      }
    }
  }

  /**
   * `G |- 0 < N`, or `0 <= N`, from an order hypothesis and `r - l = N`, `N` being the normal form
   * of `r - l`; `None` when anything on the way is refused, which only drops the fact.
   */
  private def reduce(problem: Problem, bound: Bound, normal: Groebner.Poly): Option[Kernel.Thm] =
    (for {
      prover <- linarith
      written <- termOf(normal, problem.atoms)
      difference <- Linarith.difference(reals, bound.right, bound.left)
      cofactors <- Groebner.membership(problem.generators, Groebner.subtract(bound.difference, normal), problem.atoms.length, budget) match {
        case Groebner.Membership.Member(found, _) => Right(found)
        case _ => Left(NotOfForm("the difference of an order hypothesis equal to its normal form", bound.fact.conclusion))
      }
      equal <- rebuild(difference, written, problem.equations, cofactors, problem.atoms)
      signed <- signOf(written, bound.strict)
      claim <- implications(Vector(bound.fact.conclusion, equal.conclusion), signed)
      closed <- prover.prove(claim)
      opened <- rules.mp(closed, bound.fact).flatMap(rules.mp(_, equal))
    } yield opened).toOption

  /**
   * `G |- Q * inv Q = 1` for the polynomial `Q` written as a term, when `Linarith` proves `0 < Q`
   * from the reduced order facts; `None` when it does not, or when anything on the way is refused,
   * since a sign nobody proved is a goal this procedure does not settle.
   */
  private def signedInverse(problem: Problem, reduced: Vector[Kernel.Thm], q: Groebner.Poly): Option[(Kernel.Thm, Term, Term)] =
    (for {
      prover <- linarith
      written <- termOf(q, problem.atoms)
      positive <- signOf(written, strict = true)
      claim <- implications(reduced.map(_.conclusion), positive)
      closed <- prover.prove(claim)
      opened <- reduced.foldLeft(Right(closed): Either[LogicError, Kernel.Thm])((acc, fact) => acc.flatMap(rules.mp(_, fact)))
      nonZero <- order.nonZero.flatMap(rules.spec(written, _)).flatMap(rules.mp(_, opened))
      equation <- inverseEquation(written, nonZero)
    } yield equation).toOption

  /** `0 < t`, or `0 <= t`. */
  private def signOf(term: Term, strict: Boolean): Either[LogicError, Term] =
    for {
      zero <- Numeral.of(reals, 0)
      relation <- constant(if (strict) Real.Order else Real.NonStrictOrder, Type.fun(real, Type.fun(real, Type.Bool)))
      signed <- LogicError.lift(Term.appAll(relation, List(zero, term)))
    } yield signed

  /** `a1 ==> ... ==> an ==> c`. */
  private def implications(antecedents: Vector[Term], conclusion: Term): Either[LogicError, Term] =
    antecedents.foldRight(Right(conclusion): Either[LogicError, Term])((a, acc) => acc.flatMap(reals.logic.mkImp(a, _)))

  /** Built once and only when a goal reaches the order, over the same order as everything here. */
  private lazy val linarith: Either[LogicError, Linarith] = Linarith.construct(order)

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

  /**
   * `L = R` from `D^(2^m)` in the ideal, `D` being `L - R`: the member rebuilt as `H = 0`, where
   * `H` is `D` squared `m` times as a term, then `SQUARE_ZERO` once per squaring, then one ring
   * step from `L - R = 0` to `L = R`.
   */
  private def radical(problem: Problem, cofactors: Vector[Groebner.Poly], squarings: Int): Either[LogicError, Kernel.Thm] =
    for {
      difference <- Linarith.difference(reals, problem.left, problem.right)
      tower <- (1 to squarings).foldLeft(Right(Vector(difference)): Either[LogicError, Vector[Term]]) { (acc, _) =>
        acc.flatMap(terms => Linarith.product(reals, terms.last, terms.last).map(terms :+ _))
      }
      zero <- Numeral.of(reals, 0)
      top <- rebuild(tower.last, zero, problem.equations, cofactors, problem.atoms)
      squareZero <- order.squareZero
      vanishes <- tower.init.foldRight(Right(top): Either[LogicError, Kernel.Thm]) { (base, acc) =>
        acc.flatMap(above => rules.spec(base, squareZero).flatMap(rules.mp(_, above)))
      }
      plus <- constant(Real.Addition, binary)
      withDifference <- Linarith.sum(reals, problem.right, difference)
      identity <- LogicError.lift(Term.eq(problem.left, withDifference)).flatMap(ring.prove)
      plusRight <- LogicError.lift(Term.app(plus, problem.right))
      shifted <- LogicError.lift(Kernel.mkComb(Kernel.refl(plusRight), vanishes))
      residue <- Linarith.sum(reals, problem.right, zero)
      closing <- LogicError.lift(Term.eq(residue, problem.right)).flatMap(ring.prove)
      step <- LogicError.lift(Kernel.trans(identity, shifted))
      whole <- LogicError.lift(Kernel.trans(step, closing))
    } yield whole

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
      case App(App(Const(Real.Division, _), l), r) =>
        reciprocal(r).fold(Vector(term))(inverse => atomsOf(l) :+ inverse)
      case other => Vector(other)
    }

  /** `inv r`, which a quotient by a non-constant `r` abbreviates a product with. */
  private def reciprocal(r: Term): Option[Term] =
    reals.theory.constant(Real.Inverse, Type.fun(real, real)).toOption.flatMap(inverse => Term.app(inverse, r).toOption)

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
          case App(App(Const(Real.Division, _), l), r) if reciprocal(r).isDefined =>
            Groebner.multiply(polynomialOf(l, index, arity), Groebner.variable(index(reciprocal(r).get), arity))
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

  /**
   * How many times the difference is squared before the search gives up on the radical: `D^2`
   * and `D^4`. Chosen and not measured: the one goal that asks for the radical, `amc12_2000_p20`,
   * needs one squaring, and a higher power doubles the degree the search works at each time.
   */
  val Squarings: Int = 2

  /**
   * The highest degree at which the search looks for a polynomial in the difference that the
   * ideal holds, when the order is asked. Chosen and not measured: the two statements that ask for
   * the order need two by hand, `t * (t + 1440)` and `t * (t + 75)`, and degree one is shown
   * short by `tools/verify/perturb-ideal-order.sh`. A higher degree costs one more reduction each
   * and a longer cofactor for `Linarith` to sign.
   */
  val Degree: Int = 4

  /**
   * Over an order, for `NON_ZERO` and `SQUARE_ZERO`, and the ring it was built on, which is the one
   * every other arithmetic procedure uses.
   */
  def construct(order: Order): Ideal = new Ideal(order, Groebner.Budget)

  /**
   * The same procedure with the search's budget somewhere else, which is how the bound is measured
   * and how its refusal is seen. `Linarith.at` is the precedent and its comment the argument: a
   * bound that cannot be moved cannot be measured.
   */
  def at(order: Order, budget: Long): Ideal = new Ideal(order, budget)

  lazy val standard: Ideal = construct(Order.standard)
}
