package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Theorems about the primes that are results rather than infrastructure.
 *
 * `Modular` holds the arithmetic of divisibility, congruence and the greatest common divisor, and
 * everything in it is there because something above it needs it. This is the other kind: a theorem
 * somebody would want to read.
 *
 * **It is here and not in `Modular` because of one constant.** Euclid's theorem is proved from
 * `NUM_FACT`, and the factorial is defined in `Coding`, which is built over `Modular` rather than
 * under it. So the theorem cannot be stated one floor down, and putting it in `Coding` would make
 * that development's own first sentence false: `Coding` says it is the bottom of the Goedel
 * numbering, and this is not that.
 *
 * **It declares nothing**: no type, no constant, no definition, no axiom, so `Chain.widest` does
 * not move to it. `Deduction` is the other link of that kind and landed the same day.
 */
final class Primes private (
  val coding: Coding,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The arithmetic of divisibility this rests on. */
  val modular: Modular = coding.modular

  /** A derived fact of this development, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Primes {

  /**
   * `|- !n. ?p. NUM_PRIME p /\ NUM_LT n p`
   *
   * Euclid's theorem: there is a prime above every number, which is what "there are infinitely many
   * primes" says in a logic with no notion of an infinite set. Stating it this way is not a
   * workaround for the missing notion, it is the statement Euclid proved.
   *
   * The proof is his. `n! + 1` is above one, so it has a prime factor `p` by
   * `Modular.NUM_PRIME_FACTOR`. If `p` were at most `n` it would divide `n!`, because every
   * positive number up to `n` does, and it divides `n! + 1` by choice, so it would divide their
   * difference, which is one. A prime is above one, and nothing above one divides one.
   *
   * **What it cost to prove was one missing lemma, and finding it is the point.**
   * `NUM_PRIME_FACTOR` did not exist: `NUM_PRIME_DIVISOR` is a letter away and says the opposite
   * direction, that a prime's divisors are one and itself. The theorem is reachable today only
   * because stating it exposed that.
   *
   * The subtraction the informal proof does is not done here. `NUM_DIVIDES_SUMMAND` says that a
   * number dividing `a` and dividing `a + b` divides `b`, which is the same step without ever
   * writing a difference, and `num` has only a truncated subtraction to write one with.
   */
  val Unbounded: String = "NUM_PRIME_UNBOUNDED"

  /**
   * `|- !p q. NUM_LT ZERO q ==> ~(NUM_MUL p p = NUM_MUL (SUC (SUC ZERO)) (NUM_MUL q q))`
   *
   * No square is twice a square, except where the denominator is zero. This is the arithmetic
   * content of the irrationality of the square root of two, and it is **not** that statement:
   * there is no square root on the reals in this system, so the classical sentence cannot be
   * written. What can be written is the thing the classical proof actually establishes, which is
   * that the equation has no solution in positive naturals, and the name says that rather than
   * promising a constant that does not exist.
   *
   * The proof is the descent, run through `NUM_LEAST` rather than through an infinite regress: take
   * the **least** `q` for which some `p` solves it. Two divides `p * p`, hence `p`, because two is
   * prime, so `p` is `2k`; cancelling the two leaves `q * q = 2 * (k * k)`, which makes `k` another
   * solution's denominator. It is positive, or `q * q` would be zero, and it is below `q`, or the
   * squares would satisfy `x + x <= x`. The least one had no smaller one, and that is the
   * contradiction.
   *
   * **Three lemmas had to be proved before this could be**, and all three were absent for the same
   * reason: nothing in the development had needed to multiply an inequality.
   * `Peano.NUM_MUL_CANCEL_LEFT` does the cancelling, `Peano.NUM_MUL_MONOTONE` compares the squares,
   * and `Modular.NUM_PRIME_TWO` is what Euclid's lemma is applied at.
   */
  val SquareNotDouble: String = "NUM_SQUARE_NOT_DOUBLE"

  val Statements: Vector[(String, String)] = Vector(
    Unbounded -> "!n:num. ?p:num. NUM_PRIME p /\\ NUM_LT n p",
    SquareNotDouble ->
      ("!p:num q:num. NUM_LT ZERO q ==> " +
        "~(NUM_MUL p p = NUM_MUL (SUC (SUC ZERO)) (NUM_MUL q q))")
  )

  /** Build it over the arithmetic that holds the factorial. It extends nothing. */
  def construct(coding: Coding): Either[LogicError, Primes] = {
    val builder = new Builder(coding)
    try
      Right(
        new Primes(
          coding,
          coding.theory,
          coding.notation,
          coding.logic,
          Map(
            Unbounded -> builder.checked(Unbounded, builder.unbounded),
            SquareNotDouble -> builder.checked(SquareNotDouble, builder.squareNotDouble)
          )
        )
      )
    catch { case refused: RefusedHere => Left(refused.error) }
  }

  /** Carry a refusal out of a derivation written in direct style. */
  private final class RefusedHere(val error: LogicError) extends RuntimeException

  /**
   * Euclid's argument, written in direct style for the reason `Provability` gives.
   *
   * The proof is a case analysis whose branches are independent, and a `for` comprehension over
   * `Either` turns "which obligation failed" into "which binding came first".
   */
  private final class Builder(coding: Coding) {
    private val theory = coding.theory
    private val notation = coding.notation
    private val logic = coding.logic
    private val rules = logic.rules
    private val modular = coding.modular
    private val peano = coding.peano
    private val numbers = TyApp(Natural.TypeName, Nil)
    private val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    private val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))

    private def force[T](result: Either[LogicError, T]): T =
      result.fold(error => throw new RefusedHere(error), identity)

    private def app(head: Term, args: List[Term]): Term =
      force(LogicError.lift(Term.appAll(head, args)))
    private def text(source: String): Term =
      force(Parser.term(theory, notation, source, numbers))
    private def pf(name: String): Kernel.Thm = force(peano.fact(name))
    private def mf(name: String): Kernel.Thm = force(modular.fact(name))
    private def cf(name: String): Kernel.Thm = force(peano.naturals.classical.fact(name))

    private val dividesConstant =
      force(LogicError.lift(theory.constant(Modular.DividesName, relation)))
    private val primeConstant = force(LogicError.lift(
      theory.constant(Modular.PrimeName, Type.fun(numbers, Type.Bool))))
    private val belowConstant =
      force(LogicError.lift(theory.constant(Peano.StrictOrder, relation)))
    private val atMostConstant =
      force(LogicError.lift(theory.constant(Peano.NonStrictOrder, relation)))
    private val plus = force(LogicError.lift(theory.constant(Peano.Addition, arithmetic)))
    private val times =
      force(LogicError.lift(theory.constant(Peano.Multiplication, arithmetic)))
    private val semiring = force(Semiring.construct(peano))
    private val factorial = force(LogicError.lift(
      theory.constant(Coding.FactorialName, Type.fun(numbers, numbers))))

    private def divides(a: Term, b: Term): Term = app(dividesConstant, List(a, b))
    private def mul(a: Term, b: Term): Term = app(times, List(a, b))
    private def square(x: Term): Term = mul(x, x)
    private def doubled(x: Term): Term = mul(two, x)
    private def eq(a: Term, b: Term): Term = force(LogicError.lift(Term.eq(a, b)))
    private def isPrime(a: Term): Term = app(primeConstant, List(a))
    private def below(a: Term, b: Term): Term = app(belowConstant, List(a, b))
    private val one = text("SUC ZERO")
    private val zero = text("ZERO")
    private val two = text("SUC (SUC ZERO)")

    private def assume(claim: Term): Kernel.Thm = force(LogicError.lift(Kernel.assume(claim)))
    private def conj(a: Term, b: Term): Term = force(logic.mkConj(a, b))
    private def absurd(negation: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
      force(rules.notElim(negation, held))

    private def open(existential: Kernel.Thm, name: String, taken: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val predicate = logic.destExistsPredicate(existential.conclusion)
        .getOrElse(throw new RefusedHere(NotOfForm("an existential", existential.conclusion)))
      val fresh = Conv.freshVariable(
        name, numbers, taken ++ Term.freeVariables(existential.conclusion))
      val body = Term
        .destEq(force(Conv.betaRoot(app(predicate, List(fresh)))).conclusion)
        .map(_._2)
        .getOrElse(throw new RefusedHere(NotOfForm("an equation", fresh)))
      force(rules.existsElim(existential, fresh, reach(fresh, assume(body))))
    }

    def unbounded: Kernel.Thm = {
      val n = Term.variable("n", numbers)
      val fact = app(factorial, List(n))
      val bigger = app(plus, List(fact, one))

      // `1 < n! + 1`, because `0 < n!` and adding one to both keeps the order.
      val biggerAboveOne = {
        val positive = force(rules.spec(n, force(coding.fact(Coding.FactorialPositive))))
        val shifted = force(rules.specAll(pf(Peano.AddStrictlyMonotone), List(one, zero, fact))
          .flatMap(rules.mp(_, positive)))
        val identity = force(rules.spec(one, pf(Peano.AddAtZero)))
        val commuted = force(rules.specAll(pf(Peano.AddCommutative), List(one, fact)))
        val carried = force(
          Conv.apThm(force(Conv.apTerm(belowConstant, identity)), app(plus, List(one, fact)))
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, shifted))))
        force(Conv.apTerm(app(belowConstant, List(one)), commuted)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, carried))))
      }

      val hasFactor = force(
        rules.spec(bigger, mf(Modular.PrimeFactor)).flatMap(rules.mp(_, biggerAboveOne)))

      val above = open(hasFactor, "p", Set(n)) { (prime, atPrime) =>
        val prime_ = force(rules.conjElim1(atPrime))
        val dividesBigger = force(rules.conjElim2(atPrime))
        val target = below(n, prime)
        val aboveOne =
          force(rules.spec(prime, mf(Modular.PrimeAboveOne)).flatMap(rules.mp(_, prime_)))

        /** From `p <= n`, falsity: `p` divides `n!` and `n! + 1`, so it divides one. */
        def whenAtMost(atMostN: Kernel.Thm): Kernel.Thm = {
          val positive = force(rules.conjIntro(
            force(rules.specAll(pf(Peano.StrictTransitive), List(zero, one, prime))
              .flatMap(rules.mp(_, force(rules.conjIntro(
                force(rules.spec(zero, pf(Peano.SuccessorPositive))), aboveOne))))),
            atMostN))
          val dividesFactorial = force(
            rules.specAll(force(coding.fact(Coding.FactorialDivides)), List(prime, n))
              .flatMap(rules.mp(_, positive)))
          val dividesOne = force(rules.specAll(mf(Modular.DividesSummand), List(prime, fact, one))
            .flatMap(rules.mp(_, dividesFactorial))
            .flatMap(rules.mp(_, dividesBigger)))
          val equalsOne = force(
            rules.spec(prime, mf(Modular.DividesOne)).flatMap(rules.mp(_, dividesOne)))
          val reflexive = force(Conv.apTerm(app(belowConstant, List(one)), equalsOne)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, aboveOne))))
          absurd(force(rules.spec(one, pf(Peano.StrictIrreflexive))), reflexive)
        }

        val cases = force(rules.specAll(pf(Peano.Trichotomy), List(prime, n)))
        val first = logic.destDisj(cases.conclusion)
          .getOrElse(throw new RefusedHere(NotOfForm("a disjunction", cases.conclusion)))
        val rest = logic.destDisj(first._2)
          .getOrElse(throw new RefusedHere(NotOfForm("a disjunction", first._2)))

        val fromBelow = force(rules.falsityElim(target, whenAtMost(
          force(rules.specAll(pf(Peano.AtMostFromBelow), List(prime, n))
            .flatMap(rules.mp(_, assume(first._1)))))))
        val fromEqual = force(rules.falsityElim(target, whenAtMost(
          force(Conv.apTerm(app(atMostConstant, List(prime)), assume(rest._1))
            .flatMap(equation => LogicError.lift(
              Kernel.eqMp(equation, force(rules.spec(prime, pf(Peano.Reflexive))))))))))
        val fromAbove = assume(rest._2)

        val tail = assume(force(logic.mkDisj(rest._1, rest._2)))
        val reached = force(rules.disjElim(cases, fromBelow,
          force(rules.disjElim(tail, fromEqual, fromAbove))))

        val witness = Conv.freshVariable("q", numbers, Set(n, prime))
        val wanted = force(logic.mkExists(witness, conj(isPrime(witness), below(n, witness))))
        force(rules.existsIntro(
          logic.destExistsPredicate(wanted)
            .getOrElse(throw new RefusedHere(NotOfForm("an existential", wanted))),
          prime,
          force(rules.conjIntro(prime_, reached))))
      }

      force(rules.gen(n, above))
    }

    private def disjunctsOf(subject: Term, count: Int): Vector[Term] =
      if (count == 1) Vector(subject)
      else {
        val (first, rest) = logic.destDisj(subject)
          .getOrElse(throw new RefusedHere(NotOfForm("a disjunction", subject)))
        first +: disjunctsOf(rest, count - 1)
      }

    /** A number that is not zero is above it, which the descent needs twice. */
    private def positiveFromNonZero(notZero: Kernel.Thm, x: Term): Kernel.Thm = {
      val cases = force(rules.specAll(pf(Peano.BelowOrEqual), List(zero, x))
        .flatMap(rules.mp(_, force(rules.spec(x, pf(Peano.ZeroIsLeast))))))
      val parts = disjunctsOf(cases.conclusion, 2)
      val fromEqual = force(rules.falsityElim(below(zero, x),
        absurd(notZero, force(Conv.sym(assume(parts(1)))))))
      force(rules.disjElim(cases, assume(parts(0)), fromEqual))
    }

    /** [[SquareNotDouble]]. The descent is written out in that name's docstring. */
    def squareNotDouble: Kernel.Thm = {
      val twoPositive = force(rules.spec(one, pf(Peano.SuccessorPositive)))
      val p = Term.variable("p", numbers)
      val q = Term.variable("q", numbers)

      /** `?y. y * y = 2 * (x * x)`, the claim that `x` is a solution's denominator. */
      def solutionFor(x: Term): Term = {
        val y = Conv.freshVariable("y", numbers, Set(p, q) ++ Term.freeVariables(x))
        force(logic.mkExists(y, eq(square(y), doubled(square(x)))))
      }
      def propertyAt(x: Term): Term = conj(below(zero, x), solutionFor(x))
      def witnessSolution(x: Term, witness: Term, proof: Kernel.Thm): Kernel.Thm =
        force(rules.existsIntro(
          logic.destExistsPredicate(solutionFor(x))
            .getOrElse(throw new RefusedHere(NotOfForm("an existential", solutionFor(x)))),
          witness, proof))

      val positiveQ = assume(below(zero, q))
      val equationTerm = eq(square(p), doubled(square(q)))
      val equation = assume(equationTerm)

      val subject = Conv.freshVariable("x", numbers, Set(p, q))
      val property = force(LogicError.lift(Term.abs(subject, propertyAt(subject))))

      val inhabited = {
        val existential = force(logic.mkExists(subject, propertyAt(subject)))
        force(rules.existsIntro(
          logic.destExistsPredicate(existential)
            .getOrElse(throw new RefusedHere(NotOfForm("an existential", existential))),
          q,
          force(rules.conjIntro(positiveQ, witnessSolution(q, p, equation)))))
      }

      val least = {
        val instance = force(rules.spec(property, pf(Peano.LeastNumber)))
        val reduced = force(Conv.betaNormalise(instance.conclusion)
          .flatMap(step => LogicError.lift(Kernel.eqMp(step, instance))))
        force(rules.mp(reduced, inhabited))
      }

      val descent = open(least, "b", Set(p, q)) { (b, atB) =>
        val holds = force(rules.conjElim1(atB))
        val isLeast = force(rules.conjElim2(atB))
        val positiveB = force(rules.conjElim1(holds))

        open(force(rules.conjElim2(holds)), "a", Set(p, q, b)) { (a, atA) =>
          // Two divides `a * a`, hence `a`, because two is prime.
          val dividesSquare = force(
            rules.specAll(mf(Modular.DividesIntro), List(two, square(a), square(b)))
              .flatMap(rules.mp(_, atA)))
          val split = force(rules.specAll(mf(Modular.Euclid), List(two, a, a))
            .flatMap(rules.mp(_, mf(Modular.PrimeTwo)))
            .flatMap(rules.mp(_, dividesSquare)))
          val parts = disjunctsOf(split.conclusion, 2)
          val dividesA = force(rules.disjElim(split, assume(parts(0)), assume(parts(1))))
          val halves = force(rules.specAll(mf(Modular.DividesElim), List(two, a))
            .flatMap(rules.mp(_, dividesA)))

          open(halves, "k", Set(p, q, b, a)) { (k, isDouble) =>
            // `(2k)(2k) = a * a = 2 * (b * b)`, and the two cancels off both sides.
            val rebuilt = force(LogicError.lift(Kernel.mkComb(
              force(Conv.apTerm(times, isDouble)), isDouble)))
            val asDouble = force(Conv.sym(rebuilt).flatMap(Conv.trans(_, atA)))
            val expanded = force(
              semiring.prove(mul(doubled(k), doubled(k)), doubled(doubled(square(k)))))
            val stacked = force(Conv.sym(expanded).flatMap(Conv.trans(_, asDouble)))
            val cancelled = force(rules
              .specAll(pf(Peano.MulCancelsLeft), List(two, doubled(square(k)), square(b)))
              .flatMap(rules.mp(_, twoPositive))
              .flatMap(rules.mp(_, stacked)))
            val squareOfB = force(Conv.sym(cancelled))

            val squarePositive = force(rules.specAll(pf(Peano.MulPositive), List(b, b))
              .flatMap(rules.mp(_, positiveB))
              .flatMap(rules.mp(_, positiveB)))

            // `k` is not zero, or `b * b` would be.
            val positiveK = {
              val isZero = eq(k, zero)
              val cases = force(rules.spec(isZero, cf(Classical.ExcludedMiddle)))
              val caseParts = disjunctsOf(cases.conclusion, 2)
              val fromZero = {
                val atZero = assume(caseParts(0))
                val squareIsZero = force(LogicError.lift(Kernel.mkComb(
                  force(Conv.apTerm(times, atZero)), atZero)))
                val moved = force(Conv.trans(squareOfB, force(Conv.trans(
                  force(Conv.apTerm(app(times, List(two)), squareIsZero)),
                  force(semiring.prove(doubled(square(zero)), zero))))))
                val absurdity = force(Conv.apTerm(app(belowConstant, List(zero)), moved)
                  .flatMap(step => LogicError.lift(Kernel.eqMp(step, squarePositive))))
                force(rules.falsityElim(below(zero, k),
                  absurd(force(rules.spec(zero, pf(Peano.StrictIrreflexive))), absurdity)))
              }
              force(rules.disjElim(cases, fromZero,
                positiveFromNonZero(assume(caseParts(1)), k)))
            }

            val squareOfKPositive = force(rules.specAll(pf(Peano.MulPositive), List(k, k))
              .flatMap(rules.mp(_, positiveK))
              .flatMap(rules.mp(_, positiveK)))

            /** From `b <= k`, falsity: the squares would then satisfy `x + x <= x`. */
            def whenNotBelow(atMostK: Kernel.Thm): Kernel.Thm = {
              val first = force(rules.specAll(pf(Peano.MulMonotone), List(b, b, k))
                .flatMap(rules.mp(_, atMostK)))
              val second = force(rules.specAll(pf(Peano.MulMonotone), List(k, b, k))
                .flatMap(rules.mp(_, atMostK)))
              val commuted = force(rules.specAll(pf(Peano.MulCommutative), List(b, k)))
              val aligned = force(
                Conv.apThm(force(Conv.apTerm(atMostConstant, commuted)), square(k))
                  .flatMap(Conv.sym)
                  .flatMap(step => LogicError.lift(Kernel.eqMp(step, second))))
              val chained = force(
                rules.specAll(pf(Peano.Transitive), List(square(b), mul(b, k), square(k)))
                  .flatMap(rules.mp(_, force(rules.conjIntro(first, aligned)))))

              val asSum = force(semiring.prove(
                doubled(square(k)), app(plus, List(square(k), square(k)))))
              val moved = force(Conv
                .apThm(force(Conv.apTerm(atMostConstant,
                  force(Conv.trans(squareOfB, asSum)))), square(k))
                .flatMap(step => LogicError.lift(Kernel.eqMp(step, chained))))
              val other = force(rules.specAll(pf(Peano.AtMostSum), List(square(k), square(k))))
              val equal = force(rules.specAll(pf(Peano.AntiSymmetric),
                List(app(plus, List(square(k), square(k))), square(k)))
                .flatMap(rules.mp(_, force(rules.conjIntro(moved, other)))))
              val isZero = force(rules.specAll(pf(Peano.AddCancels), List(square(k), square(k)))
                .flatMap(rules.mp(_, equal)))
              val absurdity = force(Conv.apTerm(app(belowConstant, List(zero)), isZero)
                .flatMap(step => LogicError.lift(Kernel.eqMp(step, squareOfKPositive))))
              absurd(force(rules.spec(zero, pf(Peano.StrictIrreflexive))), absurdity)
            }

            val belowB = {
              val cases = force(rules.specAll(pf(Peano.Trichotomy), List(k, b)))
              val three = disjunctsOf(cases.conclusion, 3)
              val target = below(k, b)
              val fromEqual = force(rules.falsityElim(target, whenNotBelow(
                force(Conv.apTerm(app(atMostConstant, List(b)), force(Conv.sym(assume(three(1)))))
                  .flatMap(step => LogicError.lift(
                    Kernel.eqMp(step, force(rules.spec(b, pf(Peano.Reflexive))))))))))
              val fromAbove = force(rules.falsityElim(target, whenNotBelow(
                force(rules.specAll(pf(Peano.AtMostFromBelow), List(b, k))
                  .flatMap(rules.mp(_, assume(three(2))))))))
              val tail = assume(force(logic.mkDisj(three(1), three(2))))
              force(rules.disjElim(cases, assume(three(0)),
                force(rules.disjElim(tail, fromEqual, fromAbove))))
            }

            val refused = {
              val instance = force(rules.spec(k, isLeast).flatMap(rules.mp(_, belowB)))
              force(Conv.betaNormalise(instance.conclusion)
                .flatMap(step => LogicError.lift(Kernel.eqMp(step, instance))))
            }
            absurd(refused, force(rules.conjIntro(positiveK, witnessSolution(k, b, squareOfB))))
          }
        }
      }

      force(rules.notIntro(equationTerm, descent)
        .flatMap(rules.disch(below(zero, q), _))
        .flatMap(rules.genAll(_, List(p, q))))
    }

    /** A finished derivation against the statement this development publishes for it. */
    def checked(name: String, theorem: Kernel.Thm): Kernel.Thm = {
      val wanted = force(
        Statements
          .collectFirst { case (published, source) if published == name => source }
          .toRight(MissingDefinition(name))
          .flatMap(Parser.proposition(theory, notation, _))
      )
      if (theorem.conclusion == wanted) theorem
      else
        throw new RefusedHere(
          NotOfForm(s"the statement published for $name", theorem.conclusion))
    }
  }
}
