package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The p-adic valuation on `num`, and the laws `Primes` publishes about it.
 *
 * `PrimesSpec` already compares every statement `Primes` publishes with its text, and
 * `NothingOverNumRestsOnTheRealsSpec` already refuses any of them reaching an axiom of the reals.
 * What is asserted here is what neither can see: that the laws **compose** to a value at a point
 * with nothing assumed; that the product law's primality and the register reading's positivity
 * are carried because the statements are false without them, each refuted in the kernel at a
 * witness where every other hypothesis holds; and that the product law came through Euclid's
 * lemma and divisibility by registers through a prime factor.
 */
class ValuationSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val primes = chain.primes
  private val logic = primes.logic
  private val rules = logic.rules
  private val numbers = TyApp(Natural.TypeName, Nil)
  private lazy val library = Library.of(chain)

  private def lemma(name: String): Kernel.Thm =
    library.entries.find(_.name == name).map(_.theorem).getOrElse(fail(s"no lemma $name"))

  private def published(name: String): Kernel.Thm = force(primes.fact(name))

  private def proposition(text: String): Term =
    force(Parser.proposition(primes.theory, primes.notation, text))

  private def term(text: String): Term =
    force(Parser.term(primes.theory, primes.notation, text, numbers))

  private def assumed(text: String): Kernel.Thm =
    force(LogicError.lift(Kernel.assume(proposition(text))))

  private def use(theorem: Kernel.Thm, arguments: List[Term], premises: Kernel.Thm*): Kernel.Thm =
    force(premises.foldLeft(rules.specAll(theorem, arguments).flatMap(Limit.normalised))((acc, p) => acc.flatMap(rules.mp(_, p))))

  private def numeral(n: Int): String = (1 to n).foldLeft("0")((inner, _) => s"SUC ($inner)")

  private val zero = term("0")
  private val one = term(numeral(1))
  private val two = term(numeral(2))
  private val three = term(numeral(3))
  private val four = term(numeral(4))

  /** Ground arithmetic in successor form, by the recursion equations alone. */
  private lazy val arithmetic = force(
    Rewrite.Rule.all(
      logic,
      Vector(
        Peano.AddAtZero,
        Peano.AddAtSuccessor,
        Peano.MulAtZero,
        Peano.MulAtSuccessor,
        Peano.PowAtZero,
        Peano.PowAtSuccessor
      ).map(lemma)))

  private def evaluated(text: String): Kernel.Thm = force(Rewrite.rewrite(arithmetic, term(text)))

  /** `SUC^i 0 < SUC^j 0`, by a chain of `NUM_LT_SUC`. */
  private def below(i: Int, j: Int): Kernel.Thm =
    ((i + 1) until j).foldLeft(use(lemma("NUM_LT_SUC"), List(term(numeral(i))))) { (acc, k) =>
      val step = use(lemma("NUM_LT_SUC"), List(term(numeral(k))))
      use(lemma("NUM_LT_TRANS"), List(term(numeral(i)), term(numeral(k)), term(numeral(k + 1))), force(rules.conjIntro(acc, step)))
    }

  /** `~(NUM_DIVIDES x y)` for ground `0 < y < x`: a divisor of a positive number is no larger than it. */
  private def notDivides(x: Int, y: Int): Kernel.Thm = {
    val (tx, ty) = (term(numeral(x)), term(numeral(y)))
    val claim = proposition(s"NUM_DIVIDES (${numeral(x)}) (${numeral(y)})")
    val sizes = use(lemma("NUM_DIVIDES_LE"), List(tx, ty), force(LogicError.lift(Kernel.assume(claim))))
    val notAtMost = use(lemma("NUM_LT_NOT_LE"), List(ty, tx), below(y, x))
    val atMostCase = force(rules.notElim(notAtMost, assumed(s"NUM_LE (${numeral(x)}) (${numeral(y)})")))
    val zeroCase = force(
      rules.notElim(use(lemma("NUM_SUC_NOT_ZERO"), List(term(numeral(y - 1)))), assumed(s"${numeral(y)} = 0")))
    force(rules.disjElim(sizes, atMostCase, zeroCase).flatMap(rules.notIntro(claim, _)))
  }

  private def rewritten(equation: Kernel.Thm, theorem: Kernel.Thm): Kernel.Thm =
    force(Limit.rewriteInProposition(equation, theorem))

  /** `P b` from `P a` and `a = b`, for `P` written as a lambda: only where `P` puts its argument. */
  private def transported(lambdaText: String, equation: Kernel.Thm, theorem: Kernel.Thm): Kernel.Thm = {
    val lambda = force(Parser.term(primes.theory, primes.notation, lambdaText))
    force(Conv.apTerm(lambda, equation).flatMap(Conv.betaSides).flatMap(e => LogicError.lift(Kernel.eqMp(e, theorem))))
  }

  /**
   * `NUM_VALUATION 2 12 = 2`, from the laws alone: twelve is `2^2 * 3`, the product law splits it,
   * the power law reads the first factor and three is not divisible by two. Every hypothesis is
   * discharged, primality by `NUM_PRIME_TWO` and positivity by `NUM_POW_POSITIVE`.
   */
  "The valuation" should "compose to a value at twelve with nothing assumed" in {
    val twoPositive = use(lemma("NUM_ZERO_LT_SUC"), List(one))
    val fourPositive = use(lemma("NUM_POW_POSITIVE"), List(two, two), twoPositive)
    val threePositive = use(lemma("NUM_ZERO_LT_SUC"), List(two))
    val prime = lemma("NUM_PRIME_TWO")
    val product = use(published(Primes.ValuationMul), List(two, term(s"NUM_POW (${numeral(2)}) (${numeral(2)})"), three),
      prime, fourPositive, threePositive)
    val power = use(published(Primes.ValuationPower), List(two, two), prime)
    // ~(2 | 3): 3 = 2 z would make 2 * 1 + 1 and 2 * z + 0 two divisions of one number
    val threeClaim = proposition(s"NUM_DIVIDES (${numeral(2)}) (${numeral(3)})")
    val z = Term.variable("z", numbers)
    val witness = force(
      LogicError.lift(Kernel.assume(proposition(s"${numeral(3)} = ${numeral(2)} * (z:num)"))))
    val asDivisions = force(
      Conv.trans(evaluated(s"${numeral(2)} * ${numeral(1)} + ${numeral(1)}"), witness)
        .flatMap(Conv.trans(_, force(Conv.sym(use(lemma("NUM_ADD_ZERO"), List(term(s"${numeral(2)} * (z:num)"))))))))
    val remainders = use(
      lemma("NUM_DIVISION_UNIQUE"),
      List(two, one, one, z, zero),
      force(rules.conjIntro(asDivisions, force(rules.conjIntro(below(1, 2), below(0, 2)))))
    )
    val oneIsZero = force(rules.conjElim2(remainders))
    val absurd = force(rules.notElim(use(lemma("NUM_SUC_NOT_ZERO"), List(zero)), oneIsZero))
    val opened = use(lemma("NUM_DIVIDES_ELIM"), List(two, three), force(LogicError.lift(Kernel.assume(threeClaim))))
    val oddThree = force(rules.existsElim(opened, z, absurd).flatMap(rules.notIntro(threeClaim, _)))
    val atThree = use(published(Primes.ValuationNotDivides), List(two, three), oddThree)

    val assembled = rewritten(evaluated(s"NUM_POW (${numeral(2)}) (${numeral(2)}) * ${numeral(3)}"),
      rewritten(use(lemma("NUM_ADD_ZERO"), List(two)), rewritten(atThree, rewritten(power, product))))

    assembled.hypotheses shouldBe empty
    assembled.conclusion shouldBe proposition(s"NUM_VALUATION (${numeral(2)}) (${numeral(12)}) = ${numeral(2)}")
  }

  /**
   * The product law is false without primality, and four is the witness: `4 = 2 * 2`, the valuation
   * at four of four is one and of two is nought. Both factors are positive, so what fails there is
   * the primality alone. A law proved without using Euclid's lemma could not tell these apart.
   */
  it should "carry a primality hypothesis that cannot be dropped" in {
    val claimText =
      s"NUM_VALUATION (${numeral(4)}) (${numeral(2)} * ${numeral(2)}) = " +
        s"NUM_VALUATION (${numeral(4)}) (${numeral(2)}) + NUM_VALUATION (${numeral(4)}) (${numeral(2)})"
    val atTwo = use(published(Primes.ValuationNotDivides), List(four, two), notDivides(4, 2))
    val fourDividesFour = transported(s"\\x:num. NUM_DIVIDES x (${numeral(4)})",
      force(Conv.sym(evaluated(s"NUM_POW (${numeral(4)}) (${numeral(1)})"))), use(lemma("NUM_DIVIDES_REFL"), List(four)))
    val sixteenRefused = transported(s"\\x:num. ~(NUM_DIVIDES x (${numeral(4)}))",
      force(Conv.sym(evaluated(s"NUM_POW (${numeral(4)}) (SUC (${numeral(1)}))"))), notDivides(16, 4))
    val atFour = use(published(Primes.ValuationUnique), List(four, four, one), fourDividesFour, sixteenRefused)
    val fourIsProduct = evaluated(s"${numeral(2)} * ${numeral(2)}")
    val collapsed = rewritten(evaluated("0 + 0"),
      rewritten(atFour, rewritten(fourIsProduct, rewritten(atTwo, assumed(claimText)))))
    val refuted = force(
      rules.notElim(use(lemma("NUM_SUC_NOT_ZERO"), List(zero)), collapsed).flatMap(rules.notIntro(proposition(claimText), _)))

    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(s"~($claimText)")
  }

  /**
   * The register reading is false at nought whatever the valuation of nought is, which is why it
   * asks for `0 < n`: every power divides nought, and no `k` past the valuation is at most it. The
   * witness is `k = SUC (NUM_VALUATION 2 0)`, so nothing about the unnamed value is needed.
   */
  it should "carry a positivity hypothesis in the register reading that cannot be dropped" in {
    val v = term(s"NUM_VALUATION (${numeral(2)}) 0")
    val sv = term(s"SUC (NUM_VALUATION (${numeral(2)}) 0)")
    val claimText =
      s"NUM_DIVIDES (NUM_POW (${numeral(2)}) (SUC (NUM_VALUATION (${numeral(2)}) 0))) 0 = " +
        s"NUM_LE (SUC (NUM_VALUATION (${numeral(2)}) 0)) (NUM_VALUATION (${numeral(2)}) 0)"
    val claim = assumed(claimText)
    val divides = use(lemma("NUM_DIVIDES_ZERO"), List(term(s"NUM_POW (${numeral(2)}) (SUC (NUM_VALUATION (${numeral(2)}) 0))")))
    val atMost = force(LogicError.lift(Kernel.eqMp(claim, divides)))
    val notAtMost = use(lemma("NUM_LT_NOT_LE"), List(v, sv), use(lemma("NUM_LT_SUC"), List(v)))
    val refuted = force(rules.notElim(notAtMost, atMost).flatMap(rules.notIntro(proposition(claimText), _)))

    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(s"~($claimText)")
  }

  /** The product law's route, asserted rather than described: through Euclid's lemma. */
  it should "rest the product law on Euclid's lemma" in {
    val route = Set(lemma("NUM_EUCLID").conclusion)
    Derivation.restingOn(published(Primes.ValuationMul), route) shouldBe route
  }

  /**
   * Divisibility by registers, backwards, is the induction on `b` that takes a prime factor off: it
   * rests on there being one, and on the strong induction that reaches the smaller cofactor.
   */
  it should "read divisibility off the registers by taking a prime factor off" in {
    val route = Set(lemma("NUM_PRIME_FACTOR").conclusion, lemma("NUM_STRONG_INDUCTION").conclusion)
    Derivation.restingOn(published(Primes.DividesByValuations), route) shouldBe route
  }

  /** What the fourteen facts cost, as a set equal to what Euclid's theorem costs, for `FermatSpec`'s reason. */
  it should "cost what Euclid's theorem costs and nothing else" in {
    val euclid = Derivation.axiomsOf(published(Primes.Unbounded))
    Vector(
      Primes.BelowPower,
      Primes.PowerDividesPower,
      Primes.ValuationUnique,
      Primes.ValuationSpec,
      Primes.ValuationDivides,
      Primes.ValuationNotDivides,
      Primes.ValuationPower,
      Primes.ValuationMul,
      Primes.ValuationOtherPrime,
      Primes.DividesByValuations,
      Primes.ValuationDetermines,
      Primes.FractionApplies,
      Primes.FractionEffect,
      Primes.FractionLands
    ).foreach { name =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(published(name)) shouldBe euclid
      }
    }
  }
}
