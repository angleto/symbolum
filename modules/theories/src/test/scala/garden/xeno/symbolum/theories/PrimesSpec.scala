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
