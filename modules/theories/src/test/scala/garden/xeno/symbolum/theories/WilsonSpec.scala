package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Wilson's theorem on `num`, and the product over paired indices it was waiting on.
 *
 * `PrimesSpec` compares both statements with their text and `NothingOverNumRestsOnTheRealsSpec`
 * keeps the reals out of them. What is asserted here is what neither can see:
 *
 *   - **It detaches at five**, where the pairing is exercised: the residues `2` and `3` are each
 *     other's inverse, `2 * 3 = 6 = 1 (mod 5)`. At two the theorem is a computation that never
 *     reaches the pairing, so a detachment there would say nothing about it. Five's primality is
 *     derived here, since the library proves only two's.
 *   - **Primality is load-bearing**: at four, `3! + 1 = 7` and four does not divide it.
 *   - **The pairing needs its involution to move every index**: at one index, the identity is an
 *     involution, `2 * 2 = 1 (mod 3)`, and the product `2` is not `1`.
 *   - **It came through the pairing and the permutation**, asserted rather than described.
 */
class WilsonSpec extends AnyFlatSpec with Matchers {

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
  /** Specialise the leading quantifiers at texts, each read at its binder's type, and reduce. */
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

  /** Ground arithmetic in successor form, by the recursion equations alone. */
  private lazy val arithmetic = force(
    Rewrite.Rule.all(
      logic,
      Vector(Peano.AddAtZero, Peano.AddAtSuccessor, Peano.MulAtZero, Peano.MulAtSuccessor, Peano.PreAtSuccessor,
        "NUM_FACT_ZERO", "NUM_FACT_SUC").map(lemma)))

  private def evaluated(text: String): Kernel.Thm = force(Rewrite.rewrite(arithmetic, term(text)))
  private def valueOf(text: String): Term = force(Limit.rightOf(evaluated(text)))

  /** `~(NUM_DIVIDES c v)` for numerals, from `v = c * q + r` with `0 < r < c`: division is unique. */
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
      // c * k + 0 = c * k = v = c * q + r.
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

  /** `NUM_PRIME 5`: above one, and a divisor of five is at most five and neither 0, 2, 3 nor 4. */
  private lazy val fiveIsPrime: Kernel.Thm = {
    val five = numeral(5)
    val definition = force(chain.modular.definition(Modular.PrimeName))
    val unfolded = force(Conv.unfold(definition, List(term(five))))
    val opened = force(Conv.trans(unfolded, force(Conv.betaNormalise(force(Limit.rightOf(unfolded))))))
    val body = force(Limit.rightOf(opened))
    val (aboveOne, divisors) = logic.destConj(body).getOrElse(fail("a conjunction"))
    val oneBelow = below(1, 5)
    oneBelow.conclusion shouldBe aboveOne

    val goal = proposition(s"!w:num. NUM_LT w ${numeral(6)} ==> NUM_DIVIDES w $five ==> w = SUC 0 \\/ w = $five")
    val bounded = belowBound(goal, 6) { (c, atC) =>
      val (dividesT, conclusion) = implication(atC)
      val proof = c match {
        case 1 => force(rules.disjIntro1(proposition(s"SUC 0 = $five"), Conv.refl(term("SUC 0"))))
        case 5 => force(rules.disjIntro2(proposition(s"$five = SUC 0"), Conv.refl(term(five))))
        case 0 =>
          val divides = force(LogicError.lift(Kernel.assume(dividesT)))
          val product = mp(specAll(lemma("NUM_DIVIDES_ELIM"), "0", five), divides)
          val predicate = logic.destExistsPredicate(product.conclusion).getOrElse(fail("an existential"))
          val k = Term.variable("k", numbers)
          val bodyAtK = Term.destEq(force(Conv.betaRoot(force(LogicError.lift(Term.app(predicate, k))))).conclusion)
            .map(_._2).getOrElse(fail("an equation"))
          val vIs = force(LogicError.lift(Kernel.assume(bodyAtK)))
          val toZero = force(Conv.trans(vIs, force(rules.spec(term("k"), lemma(Peano.ZeroTimes)))))
          val falsity = force(rules.notElim(distinct(term(five), term("0")), toZero))
          force(rules.existsElim(product, k, force(rules.falsityElim(conclusion, falsity))))
        case other =>
          val divides = force(LogicError.lift(Kernel.assume(dividesT)))
          force(rules.falsityElim(conclusion, force(rules.notElim(notDividing(other, 5), divides))))
      }
      force(rules.disch(dividesT, proof))
    }
    val every = {
      val d = Term.variable("d", numbers)
      val divides = assumed(s"NUM_DIVIDES d $five")
      val atMost = mp(specAll(lemma("NUM_DIVIDES_LE"), "d", five), divides)
      val underSix = force(rules.disjElim(atMost,
        mp(specAll(lemma("NUM_LE_LT_TRANS"), "d", five, numeral(6)),
          force(rules.conjIntro(assumed(s"NUM_LE d $five"), below(5, 6)))),
        force(rules.falsityElim(proposition(s"NUM_LT d ${numeral(6)}"),
          force(rules.notElim(distinct(term(five), term("0")), assumed(s"$five = 0")))))))
      val result = mp(specAll(bounded, "d"), underSix, divides)
      force(rules.disch(proposition(s"NUM_DIVIDES d $five"), result).flatMap(rules.gen(d, _)))
    }
    every.conclusion shouldBe divisors
    force(LogicError.lift(Kernel.eqMp(force(Conv.sym(opened)), force(rules.conjIntro(oneBelow, every)))))
  }

  "Wilson's theorem" should "detach at five, where the pairing is exercised, with nothing assumed" in {
    fiveIsPrime.hypotheses shouldBe empty
    fiveIsPrime.conclusion shouldBe proposition(s"NUM_PRIME ${numeral(5)}")
    val detached = mp(specAll(force(primes.fact(Primes.Wilson)), numeral(5)), fiveIsPrime)
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition(s"NUM_DIVIDES ${numeral(5)} (SUC (NUM_FACT (PRE ${numeral(5)})))")
    // And what it says there: four factorial plus one is twenty-five.
    valueOf(s"SUC (NUM_FACT (PRE ${numeral(5)}))") shouldBe term(numeral(25))
  }

  it should "be false without primality: four does not divide 3! + 1" in {
    val four = numeral(4)
    val seven = evaluated(s"SUC (NUM_FACT (PRE $four))")
    force(Limit.rightOf(seven)) shouldBe term(numeral(7))
    val refuted = force(Limit.rewriteInProposition(force(Conv.sym(seven)), notDividing(4, 7)))
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(s"~(NUM_DIVIDES $four (SUC (NUM_FACT (PRE $four))))")
  }

  it should "rest on the pairing, the permutation, the inverse and Euclid's lemma" in {
    val route = Set(Primes.ProdPaired, Primes.ProdPermute, Primes.Inverse).map(name => force(primes.fact(name)).conclusion) +
      lemma("NUM_EUCLID").conclusion
    Derivation.restingOn(force(primes.fact(Primes.Wilson)), route) shouldBe route
  }

  it should "cost what Euclid's theorem costs and nothing else" in {
    val euclid = Derivation.axiomsOf(force(primes.fact(Primes.Unbounded)))
    Vector(Primes.ProdPaired, Primes.Wilson).foreach { name =>
      withClue(s"$name: ")(Derivation.axiomsOf(force(primes.fact(name))) shouldBe euclid)
    }
  }

  /**
   * At one index, the identity on `[0, 1)` is an involution into the range and `2 * 2 = 4 = 1
   * (mod 3)`, so the three other hypotheses hold; the product is `2`, and `2 = 1 (mod 3)` is
   * refuted. So the pairing without "no fixed point" is false, and that is derived.
   */
  "The pairing" should "need its involution to move every index" in {
    val three = numeral(3)
    val two = numeral(2)
    val general = specAll(force(primes.fact(Primes.ProdPaired)), three, s"\\z0:num. $two", "\\z0:num. z0", numeral(1))
    val (hypotheses, conclusion) = fixture.antecedents(general.conclusion, 4)

    def everyIndex(goal: Term)(atZero: Term => Kernel.Thm): Kernel.Thm = belowBound(goal, 1)((_, body) => atZero(body))
    val range = everyIndex(hypotheses(0))(_ => below(0, 1))
    val involution = everyIndex(hypotheses(1))(_ => Conv.refl(term("0")))
    val pairs = everyIndex(hypotheses(3)) { body =>
      val four = force(Conv.trans(evaluated(s"NUM_ADD (NUM_MUL $two $two) (NUM_MUL $three 0)"),
        force(Conv.sym(evaluated(s"NUM_ADD (SUC 0) (NUM_MUL $three (SUC 0))")))))
      val congruent = mp(specAll(lemma("NUM_CONG_INTRO"), three, s"NUM_MUL $two $two", "SUC 0", "0", "SUC 0"), four)
      congruent.conclusion shouldBe body
      congruent
    }
    range.conclusion shouldBe hypotheses(0)
    involution.conclusion shouldBe hypotheses(1)
    pairs.conclusion shouldBe hypotheses(3)

    // The product over one index is `f 0 = 2`.
    val atOne = force(Limit.rewriteInProposition(specAll(lemma("NUM_PROD_ZERO"), s"\\z0:num. $two"),
      specAll(lemma("NUM_PROD_SUC"), s"\\z0:num. $two", "0")))
    val value = force(Conv.trans(atOne, evaluated(s"NUM_MUL (SUC 0) $two")))
    force(Limit.rightOf(value)) shouldBe term(two)

    val refuted = force(rules.notIntro(conclusion, {
      val claim = force(Limit.rewriteInProposition(value, force(LogicError.lift(Kernel.assume(conclusion)))))
      val toOne = mp(specAll(lemma("NUM_MOD_OF_CONG"), three, two, "SUC 0"), claim, below(1, 3))
      val toTwo = mp(specAll(lemma("NUM_MOD_OF_CONG"), three, two, two), specAll(lemma("NUM_CONG_REFL"), three, two), below(2, 3))
      force(rules.notElim(distinct(term("SUC 0"), term(two)), force(Conv.trans(force(Conv.sym(toOne)), toTwo))))
    }))
    refuted.hypotheses shouldBe empty
    // And the fourth hypothesis, the one this is about, is false there: `0` is its own image.
    hypotheses(2) shouldBe proposition(s"!i:num. NUM_LT i ${numeral(1)} ==> ~(i = i)")
  }

}
