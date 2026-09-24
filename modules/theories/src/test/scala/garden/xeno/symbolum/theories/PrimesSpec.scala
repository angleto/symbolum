package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Euclid's theorem, and the lemma that had to be found before it could be proved.
 *
 * The statement check below is the ordinary one. What is worth more here is the assertion that
 * `NUM_PRIME_UNBOUNDED` is **usable**: a theorem of the form `!n. ?p. ...` is only as good as the
 * witness it hands back, so the last test takes the prime above a concrete number and reads its two
 * properties off, which is the thing a reader of `docs/examples.md` would try first.
 */
class PrimesSpec extends AnyFlatSpec with Matchers {

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

  "Primes" should "be the statements this development publishes" in {
    Primes.Statements.foreach { case (name, text) =>
      val theorem = force(primes.fact(name))
      withClue(s"$name: ") {
        theorem.conclusion shouldBe proposition(text)
        theorem.hypotheses shouldBe empty
      }
    }
  }

  /**
   * What Euclid's theorem costs, which is what the naturals cost and nothing more.
   *
   * An equality rather than a ceiling. It is worth pinning here because the proof reaches across
   * four developments, `Modular`, `Coding`, `Peano` and the classical extension, and a theorem that
   * quietly started spending one of the reals' sixteen would be spending it on the naturals' behalf.
   */
  it should "cost the naturals' two axioms and nothing else" in {
    Derivation.axiomsOf(force(primes.fact(Primes.Unbounded))) should have size 2
  }

  /**
   * The lemma Euclid's theorem needed and the library did not have.
   *
   * `NUM_PRIME_DIVISOR` is a letter away and says the other direction, so this asserts the two are
   * different statements rather than trusting that nobody will read one for the other: the first
   * concludes that a divisor of a prime is trivial, the second that a number above one **has** a
   * prime divisor.
   */
  it should "rest on a prime factor lemma that is not the one it is a letter away from" in {
    val factor = force(chain.modular.fact(Modular.PrimeFactor))
    val divisor = force(chain.modular.fact(Modular.PrimeDivisor))

    factor.conclusion should not be divisor.conclusion
    factor.hypotheses shouldBe empty
    Derivation.axiomsOf(factor) should have size 2

    // Two above one, and the factor it hands back.
    val two = term("SUC (SUC ZERO)")
    // `1 < 2` is `NUM_LT_SUC` at ONE, not at two: the lemma is `!x. x < SUC x`.
    val aboveOne =
      force(rules.spec(term("SUC ZERO"), force(chain.peano.fact(Peano.BelowSuccessor))))
    val found = force(rules.spec(two, factor).flatMap(rules.mp(_, aboveOne)))

    found.hypotheses shouldBe empty
    found.conclusion shouldBe proposition(
      "?p:num. NUM_PRIME p /\\ NUM_DIVIDES p (SUC (SUC ZERO))")
  }

  /**
   * The side condition on the irrationality is real, and this is the witness that it is.
   *
   * `!p q. ZERO < q ==> ~(p * p = 2 * (q * q))` carries a hypothesis, and a reader is entitled to
   * ask whether it is there because the proof wanted it or because the statement needs it. It is
   * the second, and at `q = ZERO` the equation has a solution: `ZERO * ZERO = 2 * (ZERO * ZERO)`,
   * both sides being zero. So the theorem without its condition is false, not merely unproved.
   *
   * That equation is proved here rather than asserted, by the semiring procedure over `num`, which
   * is the same instrument the descent itself uses and costs the same two axioms.
   */
  it should "carry a hypothesis that cannot be dropped, and the zero case is why" in {
    val semiring = force(Semiring.construct(chain.peano))
    val zero = term("ZERO")
    val two = term("SUC (SUC ZERO)")

    def applied(head: Term, arguments: List[Term]): Term =
      force(LogicError.lift(Term.appAll(head, arguments)))
    val times = force(LogicError.lift(primes.theory.constant(
      Peano.Multiplication, Type.fun(numbers, Type.fun(numbers, numbers)))))
    def mul(a: Term, b: Term): Term = applied(times, List(a, b))

    val solved = force(semiring.prove(mul(zero, zero), mul(two, mul(zero, zero))))
    solved.hypotheses shouldBe empty
    Derivation.axiomsOf(solved) should have size 2

    // And the theorem, at a positive denominator, says the opposite of that shape.
    val one = term("SUC ZERO")
    val refused = force(
      rules
        .specAll(force(primes.fact(Primes.SquareNotDouble)), List(one, one))
        .flatMap(rules.mp(_, force(rules.spec(zero, force(chain.peano.fact(Peano.SuccessorPositive))))))
    )
    refused.hypotheses shouldBe empty
    refused.conclusion shouldBe proposition(
      "~(NUM_MUL (SUC ZERO) (SUC ZERO) = NUM_MUL (SUC (SUC ZERO)) (NUM_MUL (SUC ZERO) (SUC ZERO)))")
  }

  /* ------------------------------------ the fundamental theorem of arithmetic */

  private def impParts(term: Term): (Term, Term) =
    logic.destImp(term).getOrElse(fail(s"an implication was expected: $term"))

  private def conjParts(term: Term): (Term, Term) =
    logic.destConj(term).getOrElse(fail(s"a conjunction was expected: $term"))

  private def peel(term: Term, count: Int): (Vector[Term], Term) =
    if (count == 0) (Vector.empty, term)
    else {
      val (antecedent, rest) = impParts(term)
      val (others, conclusion) = peel(rest, count - 1)
      (antecedent +: others, conclusion)
    }

  private def openAt(quantified: Term, argument: Term): Term = {
    val predicate = logic
      .destForallPredicate(quantified)
      .orElse(logic.destExistsPredicate(quantified))
      .getOrElse(fail(s"a quantification was expected: $quantified"))
    val contracted = force(LogicError.lift(Term.app(predicate, argument)).flatMap(Conv.betaRoot))
    Term.destEq(contracted.conclusion).map(_._2).getOrElse(fail("an equation was expected"))
  }

  private def normalise(term: Term): Term =
    Term
      .destEq(force(Conv.betaNormalise(term)).conclusion)
      .map(_._2)
      .getOrElse(fail("an equation was expected"))

  /**
   * What the two halves cost, which is what everything over the naturals costs and nothing more.
   *
   * An equality rather than a ceiling, for the reason Euclid's theorem is pinned that way above:
   * the proof reaches across `Modular`, `Coding`, `Peano` and the classical extension, and a
   * derivation that quietly started spending one of the reals' sixteen would be spending it on a
   * claim about `num`.
   */
  it should "prove the fundamental theorem of arithmetic at the naturals' two axioms" in {
    // The same two Euclid's theorem reaches, compared as a **set** and not as a count: the
    // naturals as a theory ask for choice, eta and infinity, and `Derivation.axiomsOf`'s own
    // docstring lists the entries of the library that reached `ETA` when it was measured on
    // 2026-09-14. A count of two would pass whichever two they were, and one of these derivations
    // picking up `ETA` instead of `SELECT` would be one more fact spending eta rather than a
    // theorem costing the same as the one above it.
    val euclid = Derivation.axiomsOf(force(primes.fact(Primes.Unbounded)))
    euclid should have size 2

    Vector(
      Primes.PrimeDividesProduct,
      Primes.PrimeProductIsOne,
      Primes.Factorisation,
      Primes.FactorisationUnique
    ).foreach { name =>
      withClue(s"$name: ") {
        val theorem = force(primes.fact(name))
        theorem.hypotheses shouldBe empty
        Derivation.axiomsOf(theorem) shouldBe euclid
      }
    }
  }

  /**
   * The guarantees the existence half hands back are the premises the uniqueness half asks for.
   *
   * This is the one thing neither statement can say about itself, and the failure it guards is
   * silent: two statements that are each true and do not fit leave the theorem unusable while every
   * test above passes. The comparison is between terms, so a monotonicity written with the two
   * indices the other way round, or over the wrong bound, fails here.
   */
  it should "hand the existence half's guarantees straight to the uniqueness half" in {
    val subject = Conv.freshVariable("n", numbers, Set.empty)
    val (_, existential) =
      impParts(force(rules.spec(subject, force(primes.fact(Primes.Factorisation)))).conclusion)

    val family = Conv.freshVariable("f", Type.fun(numbers, numbers), Set(subject))
    val length = Conv.freshVariable("k", numbers, Set(subject, family))
    val body = normalise(openAt(openAt(existential, family), length))

    val (_, afterPositive) = conjParts(body)
    val (primesBelow, afterPrimes) = conjParts(afterPositive)
    val (monotoneBelow, _) = conjParts(afterPrimes)

    val unique = force(
      rules.specAll(
        force(primes.fact(Primes.FactorisationUnique)),
        List(family, length, family, length)))
    val (premises, _) = peel(unique.conclusion, 5)

    primesBelow shouldBe premises(0)
    monotoneBelow shouldBe premises(1)
  }

  /**
   * The theorem as somebody would state it informally, assembled in one place.
   *
   * Two sorted families of primes with the same product have the same length and the same entries.
   * The two factorisations cannot be existentially bound here, because what comes out mentions
   * them, so they are assumptions and the hypotheses are what says so: five of them, and the fifth
   * is the equality of the two products, which is what makes this a statement about one number.
   */
  it should "settle any two sorted prime factorisations of one number against each other" in {
    val theorem = force(primes.fact(Primes.FactorisationUnique))
    val (binders, _) = force(Logic.stripForall(theorem.conclusion))
    val instance = force(rules.specAll(theorem, binders.toList))
    val (premises, conclusion) = peel(instance.conclusion, 5)

    val assumed = premises.map(premise => force(LogicError.lift(Kernel.assume(premise))))
    val reached = assumed.foldLeft(instance)((implication, premise) =>
      force(rules.mp(implication, premise)))

    reached.conclusion shouldBe conclusion
    reached.hypotheses should have size 5

    val (sameLength, sameEntries) = conjParts(conclusion)
    sameLength shouldBe force(LogicError.lift(Term.eq(binders(1), binders(3))))

    // And the second half is an equation between the two families at one index, below the length,
    // read by opening it rather than by rebuilding it: a rebuilt term compares what this test
    // wrote with what this test wrote.
    val index = Conv.freshVariable("i", numbers, binders.toSet)
    val (isBelow, entriesAgree) = impParts(openAt(sameEntries, index))
    isBelow shouldBe force(LogicError.lift(Term.appAll(
      force(LogicError.lift(primes.theory.constant(
        Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool))))),
      List(index, binders(1)))))
    entriesAgree shouldBe force(LogicError.lift(Term.eq(
      force(LogicError.lift(Term.app(binders(0), index))),
      force(LogicError.lift(Term.app(binders(2), index))))))
  }

  /**
   * The hypothesis `SUC ZERO < n` cannot be dropped, and one is the witness that it cannot.
   *
   * At `n = SUC ZERO` the existential is **false**, not merely unproved: a factorisation of one
   * with a positive length would have a last prime factor dividing one, which
   * `NUM_PRIME_PROD_ONE` refuses. So this derives the negation rather than asserting that nobody
   * managed to prove the positive, which is the difference the card for this work asked for.
   */
  it should "be false at one, which is why the hypothesis is there" in {
    val one = term("SUC ZERO")
    val (_, existential) =
      impParts(force(rules.spec(one, force(primes.fact(Primes.Factorisation)))).conclusion)

    val family = Conv.freshVariable("f", Type.fun(numbers, numbers), Set.empty)
    val inner = openAt(existential, family)
    val length = Conv.freshVariable("k", numbers, Set(family))
    val body = openAt(inner, length)
    val opened = force(LogicError.lift(Kernel.assume(body)))

    val positive = force(rules.conjElim1(opened))
    val afterPositive = force(rules.conjElim2(opened))
    val primesBelow = force(rules.conjElim1(afterPositive))
    val product = force(rules.conjElim2(force(rules.conjElim2(afterPositive))))

    val lengthIsZero = force(
      rules
        .specAll(force(primes.fact(Primes.PrimeProductIsOne)), List(family, length))
        .flatMap(rules.mp(_, primesBelow))
        .flatMap(rules.mp(_, product)))
    val absurdity = force(
      Conv
        .apTerm(
          force(LogicError.lift(Term.app(
            force(LogicError.lift(primes.theory.constant(
              Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool))))),
            term("ZERO")))),
          lengthIsZero)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, positive))))
    val contradiction = force(
      rules.notElim(
        force(rules.spec(term("ZERO"), force(chain.peano.fact(Peano.StrictIrreflexive)))),
        absurdity))

    val refused = force(
      rules
        .existsElim(force(LogicError.lift(Kernel.assume(inner))), length, contradiction)
        .flatMap(overLength =>
          rules.existsElim(force(LogicError.lift(Kernel.assume(existential))), family, overLength))
        .flatMap(rules.notIntro(existential, _)))

    refused.hypotheses shouldBe empty
    refused.conclusion shouldBe force(logic.mkNot(existential))
  }

  /**
   * A prime above a concrete number, taken out of the existential and read.
   *
   * The point is that the theorem is usable and not only true: what comes back is opened, its two
   * halves are separated, and each is what it should be about the same witness. A statement that
   * held of no witness anybody could name would pass every test above this one.
   */
  it should "hand back a witness whose two properties can be read off" in {
    val bound = term("SUC (SUC ZERO)")
    val existential = force(rules.spec(bound, force(primes.fact(Primes.Unbounded))))

    val predicate = logic
      .destExistsPredicate(existential.conclusion)
      .getOrElse(fail("an existential was expected"))
    val witness = Conv.freshVariable("p", numbers, Set.empty)
    val body = Term
      .destEq(force(Conv.betaRoot(force(LogicError.lift(Term.app(predicate, witness))))).conclusion)
      .map(_._2)
      .getOrElse(fail("an equation was expected"))
    val opened = force(LogicError.lift(Kernel.assume(body)))

    force(rules.conjElim1(opened)).conclusion shouldBe
      force(LogicError.lift(Term.app(
        force(LogicError.lift(
          primes.theory.constant(Modular.PrimeName, Type.fun(numbers, Type.Bool)))),
        witness)))

    force(rules.conjElim2(opened)).conclusion shouldBe
      force(LogicError.lift(Term.appAll(
        force(LogicError.lift(primes.theory.constant(
          Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool))))),
        List(bound, witness))))
  }
}
