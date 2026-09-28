package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Wilson's theorem detached at every prime up to seven, and each detachment compared with the same
 * number computed in Scala.
 *
 * `WilsonSpec` detaches at five and refutes at four. What this adds is the comparison with an
 * independent reference at more than one point, and two controls on what the conclusion says:
 *
 *   - **At 2, 3, 5 and 7** the theorem detaches with nothing assumed, the primality of each derived
 *     here by trial division in the kernel (for two it is also `NUM_PRIME_TWO`, and the two
 *     derivations are compared). The kernel's value of `SUC (NUM_FACT (PRE p))` is compared with
 *     `(p - 1)! + 1` computed by `BigInt`, and `BigInt` is asked separately whether `p` divides it.
 *     Seven is the first prime where the pairing has two pairs, `2 * 4` and `3 * 5`.
 *   - **At the composites 4 and 6** the conclusion is refuted, with the reference agreeing that
 *     `n` does not divide `(n - 1)! + 1`: primality carries weight at more than one composite, and
 *     at six the factorial is divisible by `n` itself rather than by a square of a prime.
 *   - **The `+ 1` is the one that holds**: at five, `4!` and `4! + 2` are not divisible by five, so a
 *     conclusion written `NUM_FACT (PRE p)` or with the wrong successor count would be false there.
 *
 * Written for the verification of Mycelium card `943e4091`, 2026-09-27.
 */
class WilsonAtSmallPrimesSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private lazy val chain = Chain.standard
  private lazy val primes = chain.primes
  private lazy val logic = primes.logic
  private lazy val rules = logic.rules
  private val numbers = TyApp(Natural.TypeName, Nil)
  private lazy val library = Library.of(chain)
  private lazy val moves = new Pigeonhole.Builder(chain)
  private lazy val fixture = ResolutionFixture(moves, chain, term => primes.show(term))
  import fixture.{numeral, below, distinct, belowBound, implication}

  private def lemma(name: String): Kernel.Thm =
    library.entries.find(_.name == name).map(_.theorem).getOrElse(fail(s"no lemma $name"))
  private def proposition(text: String): Term = force(Parser.proposition(primes.theory, primes.notation, text))
  private def term(text: String): Term = force(Parser.term(primes.theory, primes.notation, text, numbers))
  private def specAll(theorem: Kernel.Thm, arguments: String*): Kernel.Thm = {
    val specialised = arguments.foldLeft(theorem) { (current, text) =>
      val predicate = logic.destForallPredicate(current.conclusion).getOrElse(fail("a universal"))
      val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(fail("a predicate"))
      force(rules.spec(force(Parser.term(primes.theory, primes.notation, text, domain)), current))
    }
    force(Limit.normalised(specialised))
  }
  private def mp(implication: Kernel.Thm, premises: Kernel.Thm*): Kernel.Thm =
    premises.foldLeft(implication)((current, premise) => force(rules.mp(current, premise)))
  private def assumed(text: String): Kernel.Thm = force(LogicError.lift(Kernel.assume(proposition(text))))

  private lazy val arithmetic = force(
    Rewrite.Rule.all(
      logic,
      Vector(Peano.AddAtZero, Peano.AddAtSuccessor, Peano.MulAtZero, Peano.MulAtSuccessor, Peano.PreAtSuccessor,
        "NUM_FACT_ZERO", "NUM_FACT_SUC").map(lemma)))

  /** The limit is raised because a unary 721 is built one successor per pass. */
  private def evaluated(text: String): Kernel.Thm = force(Rewrite.rewrite(arithmetic, term(text), 5000))
  private def valueOf(text: String): Term = force(Limit.rightOf(evaluated(text)))

  /** The reference, outside the kernel. */
  private def factorial(n: Int): BigInt = (1 to n).map(BigInt(_)).product
  private def reference(p: Int): BigInt = factorial(p - 1) + 1
  private def referenceIsPrime(p: Int): Boolean = p > 1 && (2 until p).forall(p % _ != 0)

  /** `~(NUM_DIVIDES c v)` for numerals, from `v = c * q + r` with `0 < r < c`. */
  private def notDividing(c: Int, v: Int): Kernel.Thm = {
    val (q, r) = (v / c, v % c)
    require(r != 0, s"$c divides $v")
    val statement = proposition(s"NUM_DIVIDES ${numeral(c)} ${numeral(v)}")
    force(rules.notIntro(statement, {
      val divides = force(LogicError.lift(Kernel.assume(statement)))
      val product = mp(specAll(lemma("NUM_DIVIDES_ELIM"), numeral(c), numeral(v)), divides)
      val predicate = logic.destExistsPredicate(product.conclusion).getOrElse(fail("an existential"))
      val k = Term.variable("k", numbers)
      val body = Term.destEq(force(Conv.betaRoot(force(LogicError.lift(Term.app(predicate, k))))).conclusion)
        .map(_._2).getOrElse(fail("an equation"))
      val vIs = force(LogicError.lift(Kernel.assume(body)))
      val lhs = force(rules.spec(term(s"NUM_MUL ${numeral(c)} k"), lemma(Peano.AddAtZero)))
      val divided = force(Conv.sym(evaluated(s"NUM_ADD (NUM_MUL ${numeral(c)} ${numeral(q)}) ${numeral(r)}")))
      val joined = force(Conv.trans(lhs, force(Conv.sym(vIs))).flatMap(Conv.trans(_, divided)))
      val bounds = force(rules.conjIntro(below(0, c), below(r, c)).flatMap(b => rules.conjIntro(joined, b)))
      val unique = force(rules.specAll(lemma("NUM_DIVISION_UNIQUE"),
        List(numeral(c), "k", "0", numeral(q), numeral(r)).map(term)).flatMap(rules.mp(_, bounds)))
      val remainders = force(rules.conjElim2(unique))
      val falsity = force(rules.notElim(distinct(term("0"), term(numeral(r))), remainders))
      force(rules.existsElim(product, k, falsity))
    }))
  }

  /** `NUM_PRIME p` by trial division: above one, and every divisor below `p + 1` is one or `p`. */
  private def isPrime(p: Int): Kernel.Thm = {
    require(referenceIsPrime(p), s"$p is not prime")
    val prime = numeral(p)
    val definition = force(chain.modular.definition(Modular.PrimeName))
    val unfolded = force(Conv.unfold(definition, List(term(prime))))
    val opened = force(Conv.trans(unfolded, force(Conv.betaNormalise(force(Limit.rightOf(unfolded))))))
    val body = force(Limit.rightOf(opened))
    val (aboveOne, divisors) = logic.destConj(body).getOrElse(fail("a conjunction"))
    val oneBelow = below(1, p)
    oneBelow.conclusion shouldBe aboveOne

    val goal = proposition(s"!w:num. NUM_LT w ${numeral(p + 1)} ==> NUM_DIVIDES w $prime ==> w = SUC 0 \\/ w = $prime")
    val bounded = belowBound(goal, p + 1) { (c, atC) =>
      val (dividesT, conclusion) = implication(atC)
      val proof =
        if (c == 1) force(rules.disjIntro1(proposition(s"SUC 0 = $prime"), Conv.refl(term("SUC 0"))))
        else if (c == p) force(rules.disjIntro2(proposition(s"$prime = SUC 0"), Conv.refl(term(prime))))
        else if (c == 0) {
          val divides = force(LogicError.lift(Kernel.assume(dividesT)))
          val product = mp(specAll(lemma("NUM_DIVIDES_ELIM"), "0", prime), divides)
          val predicate = logic.destExistsPredicate(product.conclusion).getOrElse(fail("an existential"))
          val k = Term.variable("k", numbers)
          val bodyAtK = Term.destEq(force(Conv.betaRoot(force(LogicError.lift(Term.app(predicate, k))))).conclusion)
            .map(_._2).getOrElse(fail("an equation"))
          val vIs = force(LogicError.lift(Kernel.assume(bodyAtK)))
          val toZero = force(Conv.trans(vIs, force(rules.spec(term("k"), lemma(Peano.ZeroTimes)))))
          val falsity = force(rules.notElim(distinct(term(prime), term("0")), toZero))
          force(rules.existsElim(product, k, force(rules.falsityElim(conclusion, falsity))))
        } else {
          val divides = force(LogicError.lift(Kernel.assume(dividesT)))
          force(rules.falsityElim(conclusion, force(rules.notElim(notDividing(c, p), divides))))
        }
      force(rules.disch(dividesT, proof))
    }
    val every = {
      val d = Term.variable("d", numbers)
      val divides = assumed(s"NUM_DIVIDES d $prime")
      val atMost = mp(specAll(lemma("NUM_DIVIDES_LE"), "d", prime), divides)
      val underNext = force(rules.disjElim(atMost,
        mp(specAll(lemma("NUM_LE_LT_TRANS"), "d", prime, numeral(p + 1)),
          force(rules.conjIntro(assumed(s"NUM_LE d $prime"), below(p, p + 1)))),
        force(rules.falsityElim(proposition(s"NUM_LT d ${numeral(p + 1)}"),
          force(rules.notElim(distinct(term(prime), term("0")), assumed(s"$prime = 0")))))))
      val result = mp(specAll(bounded, "d"), underNext, divides)
      force(rules.disch(proposition(s"NUM_DIVIDES d $prime"), result).flatMap(rules.gen(d, _)))
    }
    every.conclusion shouldBe divisors
    force(LogicError.lift(Kernel.eqMp(force(Conv.sym(opened)), force(rules.conjIntro(oneBelow, every)))))
  }

  "Wilson's theorem" should "detach at 2, 3, 5 and 7 with nothing assumed, at the value BigInt computes" in {
    val primesUpToSeven = (2 to 7).filter(referenceIsPrime)
    primesUpToSeven shouldBe Vector(2, 3, 5, 7)
    isPrime(2).conclusion shouldBe lemma("NUM_PRIME_TWO").conclusion
    for (p <- primesUpToSeven) withClue(s"at $p: ") {
      val prime = isPrime(p)
      prime.hypotheses shouldBe empty
      val detached = mp(specAll(force(primes.fact(Primes.Wilson)), numeral(p)), prime)
      detached.hypotheses shouldBe empty
      detached.conclusion shouldBe proposition(s"NUM_DIVIDES ${numeral(p)} (SUC (NUM_FACT (PRE ${numeral(p)})))")
      // The kernel's value of the successor of the factorial, against the reference.
      valueOf(s"SUC (NUM_FACT (PRE ${numeral(p)}))") shouldBe term(numeral(reference(p).toInt))
      (reference(p) % p) shouldBe BigInt(0)
    }
  }

  it should "be refuted at the composites 4 and 6, where the reference agrees" in {
    for (n <- Vector(4, 6)) withClue(s"at $n: ") {
      referenceIsPrime(n) shouldBe false
      (reference(n) % n) should not be BigInt(0)
      val value = evaluated(s"SUC (NUM_FACT (PRE ${numeral(n)}))")
      force(Limit.rightOf(value)) shouldBe term(numeral(reference(n).toInt))
      val refuted = force(Limit.rewriteInProposition(force(Conv.sym(value)), notDividing(n, reference(n).toInt)))
      refuted.hypotheses shouldBe empty
      refuted.conclusion shouldBe proposition(s"~(NUM_DIVIDES ${numeral(n)} (SUC (NUM_FACT (PRE ${numeral(n)}))))")
    }
  }

  it should "say + 1 and nothing near it: at five, 4! and 4! + 2 are not divisible" in {
    val five = numeral(5)
    for ((text, value) <- Vector(s"NUM_FACT (PRE $five)" -> 24, s"SUC (SUC (NUM_FACT (PRE $five)))" -> 26)) withClue(text) {
      (BigInt(value) % 5) should not be BigInt(0)
      val evaluation = evaluated(text)
      force(Limit.rightOf(evaluation)) shouldBe term(numeral(value))
      val refuted = force(Limit.rewriteInProposition(force(Conv.sym(evaluation)), notDividing(5, value)))
      refuted.hypotheses shouldBe empty
      refuted.conclusion shouldBe proposition(s"~(NUM_DIVIDES $five ($text))")
    }
  }
}
