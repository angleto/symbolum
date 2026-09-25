package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Euler's theorem on `num`, the permutation it was waiting on, and the totient it is stated with.
 *
 * `PrimesSpec` already compares every statement `Primes` publishes with its text, and
 * `NothingOverNumRestsOnTheRealsSpec` already refuses any of them reaching an axiom of the reals.
 * What is asserted here is what neither can see: that the theorem is **usable** at a composite
 * modulus with nothing assumed; that it came through the permutation of a product rather than some
 * other way; that `NUM_TOTIENT` counts what it says at a point; and that the coprimality hypothesis
 * is carried because the statement needs it.
 */
class EulerSpec extends AnyFlatSpec with Matchers {

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

  private def proposition(text: String): Term =
    force(Parser.proposition(primes.theory, primes.notation, text))

  private def term(text: String): Term =
    force(Parser.term(primes.theory, primes.notation, text, numbers))

  private def lambda(text: String): Term =
    force(Parser.term(primes.theory, primes.notation, text))

  private def assumed(text: String): Kernel.Thm =
    force(LogicError.lift(Kernel.assume(proposition(text))))

  private val zero = term("0")
  private val one = term("SUC 0")
  private val two = term("SUC (SUC 0)")
  private val three = term("SUC (SUC (SUC 0))")
  private val four = term("SUC (SUC (SUC (SUC 0)))")

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

  /** `left = right` for two ground terms the recursion equations evaluate to one numeral. */
  private def same(left: String, right: String): Kernel.Thm =
    force(Conv.sym(evaluated(right)).flatMap(Conv.trans(evaluated(left), _)))

  /**
   * At four and three, where the coprimality is `3 * 3 = 9`, which is one more than twice four: the
   * hypothesis is discharged by `NUM_UNIT_COPRIME` rather than by computing a greatest common
   * divisor, and the theorem hands back a congruence about `3` to the power `NUM_TOTIENT 4` with
   * nothing left assumed.
   */
  "Euler's theorem" should "detach at a composite modulus with nothing assumed" in {
    val nine = same(
      "SUC (SUC (SUC 0)) * SUC (SUC (SUC 0)) + SUC (SUC (SUC (SUC 0))) * 0",
      "SUC 0 + SUC (SUC (SUC (SUC 0))) * SUC (SUC 0)")
    val unit = force(
      rules
        .specAll(lemma("NUM_CONG_INTRO"), List(four, term("SUC (SUC (SUC 0)) * SUC (SUC (SUC 0))"), one, zero, two))
        .flatMap(rules.mp(_, nine)))
    val fourPositive = force(rules.spec(three, lemma("NUM_ZERO_LT_SUC")))
    val coprime = force(
      rules
        .specAll(force(primes.fact(Primes.UnitCoprime)), List(four, three, three))
        .flatMap(rules.mp(_, fourPositive))
        .flatMap(rules.mp(_, unit)))
    val detached = force(
      rules
        .specAll(force(primes.fact(Primes.Euler)), List(four, three))
        .flatMap(rules.mp(_, fourPositive))
        .flatMap(rules.mp(_, coprime)))

    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition(
      "NUM_CONG (SUC (SUC (SUC (SUC 0)))) (NUM_POW (SUC (SUC (SUC 0))) (NUM_TOTIENT (SUC (SUC (SUC (SUC 0)))))) (SUC 0)")
  }

  /**
   * The route, asserted rather than described: through the permutation of a product, the inverse
   * of a coprime residue, and the product of the `a`s named as a power. A theorem proved some other
   * way would read the same word for word.
   */
  it should "rest on the permutation, the inverse and the product named as a power" in {
    val route = Set(Primes.ProdPermute, Primes.Inverse, Primes.ProdCondPow)
      .map(name => force(primes.fact(name)).conclusion)
    Derivation.restingOn(force(primes.fact(Primes.Euler)), route) shouldBe route
  }

  /** What the nine facts cost, as a set equal to what Euclid's theorem costs, for `FermatSpec`'s reason. */
  it should "cost what Euclid's theorem costs and nothing else" in {
    val euclid = Derivation.axiomsOf(force(primes.fact(Primes.Unbounded)))
    Vector(
      Primes.ProdPoint,
      Primes.ProdPermute,
      Primes.ProdCongMod,
      Primes.ProdMul,
      Primes.ProdCondPow,
      Primes.Inverse,
      Primes.GcdMod,
      Primes.UnitCoprime,
      Primes.Euler
    ).foreach { name =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(force(primes.fact(name))) shouldBe euclid
      }
    }
  }

  /**
   * `NUM_TOTIENT 2 = 1`, derived from the definition: nought is not coprime to two, since two divides
   * both and so bounds their greatest common divisor from below, and one is. A count that answered
   * two here, or nought, would satisfy every assertion above it.
   */
  private lazy val totientOfTwo: Kernel.Thm = {
    val condTrue = Kernel.instType(Map(Classical.TypeVariable -> numbers), lemma(Classical.CondTrue))
    val condFalse = Kernel.instType(Map(Classical.TypeVariable -> numbers), lemma(Classical.CondFalse))
    val twoNonZero = force(rules.spec(one, lemma("NUM_SUC_NOT_ZERO")))
    def eitherSide(left: String) = force(rules.disjIntro2(proposition(left), twoNonZero))

    val twoBelowGcd = force(
      rules
        .specAll(lemma("NUM_GCD_GREATEST"), List(zero, two, two))
        .flatMap(rules.mp(_, eitherSide("~((0:num) = 0)")))
        .flatMap(greatest =>
          rules
            .conjIntro(force(rules.spec(two, lemma("NUM_DIVIDES_ZERO"))), force(rules.spec(two, lemma("NUM_DIVIDES_REFL"))))
            .flatMap(rules.mp(greatest, _))))
    val noughtCoprime = proposition("NUM_GCD 0 (SUC (SUC 0)) = SUC 0")
    val noughtIsNot = {
      val twoAtMostOne = force(Limit.rewriteInProposition(assumed("NUM_GCD 0 (SUC (SUC 0)) = SUC 0"), twoBelowGcd))
      val notAtMost = force(
        rules.specAll(lemma("NUM_LT_NOT_LE"), List(one, two)).flatMap(rules.mp(_, force(rules.spec(one, lemma("NUM_LT_SUC"))))))
      force(rules.notElim(notAtMost, twoAtMostOne).flatMap(rules.notIntro(noughtCoprime, _)))
    }
    val oneIs = force(
      rules
        .specAll(lemma("NUM_GCD_DIVIDES_LEFT"), List(one, two))
        .flatMap(rules.mp(_, eitherSide("~(SUC 0 = 0)")))
        .flatMap(divides => rules.spec(term("NUM_GCD (SUC 0) (SUC (SUC 0))"), lemma("NUM_DIVIDES_ONE")).flatMap(rules.mp(_, divides))))

    val atNought = force(rules.specAll(condFalse, List(noughtCoprime, one, zero)).flatMap(rules.mp(_, noughtIsNot)))
    val atOne = force(
      rules.specAll(condTrue, List(proposition("NUM_GCD (SUC 0) (SUC (SUC 0)) = SUC 0"), one, zero)).flatMap(rules.mp(_, oneIs)))
    val summand = lambda("\\k:num. COND (NUM_GCD k (SUC (SUC 0)) = SUC 0) (SUC 0) 0")
    val steps = Vector(
      force(rules.specAll(lemma("NUM_SUM_SUC"), List(summand, one)).flatMap(Limit.normalised)),
      force(rules.specAll(lemma("NUM_SUM_SUC"), List(summand, zero)).flatMap(Limit.normalised)),
      force(rules.spec(summand, lemma("NUM_SUM_ZERO"))),
      atNought,
      atOne,
      lemma(Peano.AddAtZero),
      lemma(Peano.AddAtSuccessor)
    )
    val definition = force(chain.modular.definition(Modular.TotientName))
    val unfolded = force(Conv.unfold(definition, List(two)))
    val sum = force(Limit.rightOf(unfolded))
    val counted = force(Rewrite.Rule.all(logic, steps).flatMap(Rewrite.rewrite(_, sum)))
    force(Conv.trans(unfolded, counted))
  }

  "NUM_TOTIENT" should "count the residues coprime to two as one" in {
    totientOfTwo.hypotheses shouldBe empty
    totientOfTwo.conclusion shouldBe proposition("NUM_TOTIENT (SUC (SUC 0)) = SUC 0")
  }

  /**
   * The coprimality hypothesis is there because the statement needs it, and two is the witness:
   * `2` to the power `NUM_TOTIENT 2`, which is one, is two, and two leaves nought on division by two
   * and not one. `0 < 2` holds, so what fails there is the coprimality alone.
   */
  "Euler's theorem" should "carry a coprimality hypothesis that cannot be dropped" in {
    val claimText = "NUM_CONG (SUC (SUC 0)) (NUM_POW (SUC (SUC 0)) (NUM_TOTIENT (SUC (SUC 0)))) (SUC 0)"
    val claim = proposition(claimText)
    val atOne = force(Limit.rewriteInProposition(totientOfTwo, assumed(claimText)))
    val twoToTwo = force(Limit.rewriteInProposition(evaluated("NUM_POW (SUC (SUC 0)) (SUC 0)"), atOne))
    val remainderOne = force(
      rules
        .specAll(lemma("NUM_MOD_OF_CONG"), List(two, two, one))
        .flatMap(rules.mp(_, twoToTwo))
        .flatMap(rules.mp(_, force(rules.spec(one, lemma("NUM_LT_SUC"))))))
    val twoIsNought = force(
      rules
        .specAll(lemma("NUM_CONG_INTRO"), List(two, two, zero, zero, one))
        .flatMap(rules.mp(_, same("SUC (SUC 0) + SUC (SUC 0) * 0", "0 + SUC (SUC 0) * SUC 0"))))
    val remainderNought = force(
      rules
        .specAll(lemma("NUM_MOD_OF_CONG"), List(two, two, zero))
        .flatMap(rules.mp(_, twoIsNought))
        .flatMap(rules.mp(_, force(rules.spec(one, lemma("NUM_ZERO_LT_SUC"))))))
    val oneIsNought = force(Conv.sym(remainderOne).flatMap(Conv.trans(_, remainderNought)))
    val refuted = force(
      rules.spec(zero, lemma("NUM_SUC_NOT_ZERO")).flatMap(rules.notElim(_, oneIsNought)).flatMap(rules.notIntro(claim, _)))

    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(s"~($claimText)")
  }
}
