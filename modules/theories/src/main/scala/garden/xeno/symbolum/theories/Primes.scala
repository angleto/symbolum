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

  val Statements: Vector[(String, String)] = Vector(
    Unbounded -> "!n:num. ?p:num. NUM_PRIME p /\\ NUM_LT n p"
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
          Map(Unbounded -> builder.checked(Unbounded, builder.unbounded))
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
    private val factorial = force(LogicError.lift(
      theory.constant(Coding.FactorialName, Type.fun(numbers, numbers))))

    private def divides(a: Term, b: Term): Term = app(dividesConstant, List(a, b))
    private def isPrime(a: Term): Term = app(primeConstant, List(a))
    private def below(a: Term, b: Term): Term = app(belowConstant, List(a, b))
    private val one = text("SUC ZERO")
    private val zero = text("ZERO")

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
