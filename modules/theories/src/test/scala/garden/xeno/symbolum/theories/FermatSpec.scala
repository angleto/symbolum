package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Fermat's little theorem on `num`, and the route to it.
 *
 * `PrimesSpec` already compares every statement `Primes` publishes with its text, and
 * `NothingOverNumRestsOnTheRealsSpec` already refuses any of them reaching an axiom of the reals.
 * What is asserted here is what neither can see: that the theorem is **usable**, by detaching it at
 * a prime with nothing left assumed; that it came the way `Freshman` says, through the binomial
 * theorem and the divisibility of the middle coefficients; and that its hypothesis is carried
 * because the statement needs it, by refuting the statement without it at a composite modulus.
 */
class FermatSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val primes = chain.primes
  private val logic = primes.logic
  private val rules = logic.rules
  private val numbers = TyApp(Natural.TypeName, Nil)

  private def proposition(text: String): Term =
    force(Parser.proposition(primes.theory, primes.notation, text))

  private def term(text: String): Term =
    force(Parser.term(primes.theory, primes.notation, text, numbers))

  private def peano(name: String): Kernel.Thm = force(chain.peano.fact(name))
  private def modular(name: String): Kernel.Thm = force(chain.modular.fact(name))

  /**
   * At two, which `Modular.NUM_PRIME_TWO` discharges, and at a free `a`: the theorem hands back a
   * congruence about every number with no hypothesis left over, which is what a consumer gets.
   */
  "Fermat's little theorem" should "detach at a prime with nothing assumed" in {
    val a = Term.variable("a", numbers)
    val two = term("SUC (SUC ZERO)")
    val detached = force(
      rules
        .specAll(force(primes.fact(Primes.Fermat)), List(two, a))
        .flatMap(rules.mp(_, modular(Modular.PrimeTwo))))

    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition(
      "NUM_CONG (SUC (SUC ZERO)) (NUM_POW (a:num) (SUC (SUC ZERO))) a")
  }

  /**
   * The route, asserted rather than described. A theorem proved some other way would read the same
   * word for word, and one proved by carrying the binomial theorem across `real_of_num` would be
   * refused elsewhere; this says it went through the three facts `Freshman` builds it from.
   */
  it should "rest on the freshman's dream, the binomial theorem and the middle coefficients" in {
    val route = Set(Primes.Freshman, Primes.Binomial, Primes.DividesChoose)
      .map(name => force(primes.fact(name)).conclusion)
    Derivation.restingOn(force(primes.fact(Primes.Fermat)), route) shouldBe route
  }

  /**
   * What each fact `Freshman.derive` hands back costs, the list below being those names, compared
   * as a set with what Euclid's theorem costs, for the reason `PrimesSpec` compares the fundamental
   * theorem that way: a count of two would pass whichever two they were.
   */
  it should "cost what Euclid's theorem costs and nothing else" in {
    val euclid = Derivation.axiomsOf(force(primes.fact(Primes.Unbounded)))
    Vector(
      Primes.SumAdd,
      Primes.SumTimes,
      Primes.Binomial,
      Primes.DividesSum,
      Primes.NotDividesFactorial,
      Primes.DividesChoose,
      Primes.Freshman,
      Primes.Fermat
    ).foreach { name =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(force(primes.fact(name))) shouldBe euclid
      }
    }
  }

  /**
   * The hypothesis is there because the statement needs it, and four is the witness.
   *
   * `2^4 = 16` leaves nought on division by four and not two, so the conclusion is false at
   * `p = 4, a = 2`; that is derived here, in successor form so that the recursion equations alone
   * evaluate the arithmetic, and through `NUM_MOD_OF_CONG` at the two remainders. Four is chosen
   * over nought and one, which the hypothesis also excludes, because it is above one: what fails
   * there is primality and not the size of the modulus, which `NUM_LT (SUC ZERO) 4` beside it says.
   */
  it should "carry a hypothesis that cannot be dropped, and four is why" in {
    val zero = term("ZERO")
    val one = term("SUC ZERO")
    val two = term("SUC (SUC ZERO)")
    val three = term("SUC (SUC (SUC ZERO))")
    val four = term("SUC (SUC (SUC (SUC ZERO)))")
    val power = term("NUM_POW (SUC (SUC ZERO)) (SUC (SUC (SUC (SUC ZERO))))")

    val arithmetic = force(
      Rewrite.Rule.all(
        logic,
        Vector(
          Peano.AddAtZero,
          Peano.AddAtSuccessor,
          Peano.MulAtZero,
          Peano.MulAtSuccessor,
          Peano.PowAtZero,
          Peano.PowAtSuccessor
        ).map(peano)))
    def evaluated(text: String): Kernel.Thm = force(Rewrite.rewrite(arithmetic, term(text)))
    val sixteen = force(
      Conv.sym(evaluated("NUM_ADD ZERO (NUM_MUL (SUC (SUC (SUC (SUC ZERO)))) (SUC (SUC (SUC (SUC ZERO)))))"))
        .flatMap(Conv.trans(
          evaluated(
            "NUM_ADD (NUM_POW (SUC (SUC ZERO)) (SUC (SUC (SUC (SUC ZERO))))) " +
              "(NUM_MUL (SUC (SUC (SUC (SUC ZERO)))) ZERO)"),
          _)))

    def below(n: Term): Kernel.Thm = force(rules.spec(n, peano(Peano.BelowSuccessor)))
    def transitive(x: Term, y: Term, z: Term, first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm =
      force(
        rules
          .specAll(peano(Peano.StrictTransitive), List(x, y, z))
          .flatMap(implication => rules.conjIntro(first, second).flatMap(rules.mp(implication, _))))
    val twoBelowFour = transitive(two, three, four, below(two), below(three))
    val oneBelowFour = transitive(one, two, four, below(one), twoBelowFour)
    val zeroBelowFour = force(rules.spec(three, peano(Peano.SuccessorPositive)))

    val claimText =
      "NUM_CONG (SUC (SUC (SUC (SUC ZERO)))) " +
        "(NUM_POW (SUC (SUC ZERO)) (SUC (SUC (SUC (SUC ZERO))))) (SUC (SUC ZERO))"
    val claim = proposition(claimText)
    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    def remainder(congruence: Kernel.Thm, value: Term, bound: Kernel.Thm): Kernel.Thm =
      force(
        rules
          .specAll(modular(Modular.ModOfCong), List(four, power, value))
          .flatMap(rules.mp(_, congruence))
          .flatMap(rules.mp(_, bound)))
    val atTwo = remainder(assumed, two, twoBelowFour)
    val congruentToZero = force(
      rules
        .specAll(modular(Modular.CongIntro), List(four, power, zero, zero, four))
        .flatMap(rules.mp(_, sixteen)))
    val atZero = remainder(congruentToZero, zero, zeroBelowFour)
    val absurd = force(
      Conv.sym(atTwo)
        .flatMap(Conv.trans(_, atZero))
        .flatMap(twoIsZero =>
          rules
            .spec(one, force(chain.peano.naturals.fact(Natural.SuccessorNotZero)))
            .flatMap(rules.notElim(_, twoIsZero))))
    val refuted = force(rules.notIntro(claim, absurd))

    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(s"~($claimText)")
    oneBelowFour.conclusion shouldBe proposition("NUM_LT (SUC ZERO) (SUC (SUC (SUC (SUC ZERO))))")
    Derivation.axiomsOf(refuted) should have size 2
  }
}
