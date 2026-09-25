package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The generalisation of `Semiring`, asked about its `int` instance, which is the one it was built
 * for: `Semiring` is its `num` instance and every suite over `num` exercises that half already.
 *
 * == What would make these assertions empty ==
 *
 * A normaliser that proved everything would pass every identity below, so each group carries a
 * false one it must refuse. And a `consequence` that ignored its coefficients would pass the one
 * that is right, so the wrong coefficient is put to it too.
 */
class CommutativeRingSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val integers = chain.integers
  private lazy val ring = force(integers.ring)

  private def proposition(text: String): Term = force(integers.proposition(text))
  private def term(text: String): Term = force(integers.term(text))

  "The ring of int" should "decide identities that need the negation" in {
    List(
      "!a:int. !b:int. INT_MUL (INT_ADD a b) (INT_ADD a (INT_NEG b)) = INT_ADD (INT_MUL a a) (INT_NEG (INT_MUL b b))",
      "!a:int. !b:int. INT_NEG (INT_ADD a b) = INT_ADD (INT_NEG b) (INT_NEG a)",
      "!a:int. !b:int. INT_MUL (INT_NEG a) (INT_NEG b) = INT_MUL a b",
      "!a:int. INT_MUL a INT_ZERO = INT_ZERO"
    ).foreach { text =>
      withClue(s"$text: ") {
        val proved = force(ring.prove(proposition(text)))
        proved.hypotheses shouldBe empty
        proved.conclusion shouldBe proposition(text)
      }
    }
  }

  it should "cancel a monomial against its negation when monomials of the same shape stand between" in {
    // The shape of the case the order got wrong on 2026-09-25, and NOT a test that sees that defect:
    // `tools/verify/perturb-commutative-ring.sh` put the defect back and this stayed green, since
    // three monomials of one shape never reach the level where the negation's node was counted.
    // What does see it is `FractionSpec`, whose first obligation is where it was found; the harness
    // fires both. This stays as the plain statement that cancellation across a neighbour works.
    val text =
      "!x:int. !y:int. !z:int. !w:int. INT_ADD (INT_MUL x y) (INT_ADD (INT_MUL z w) (INT_NEG (INT_MUL x y))) = INT_MUL z w"
    force(ring.prove(proposition(text))).conclusion shouldBe proposition(text)
  }

  it should "refuse an identity that is false, which is what keeps the ones above from being free" in {
    ring.prove(proposition("!a:int. INT_ADD a a = a")).isLeft shouldBe true
    ring.prove(proposition("!a:int. INT_NEG a = a")).isLeft shouldBe true
  }

  it should "derive the rules it runs on from the ring axioms, under the names it publishes them by" in {
    force(ring.fact(CommutativeRing.NegateAdd)).conclusion shouldBe
      proposition("!x:int. !y:int. INT_NEG (INT_ADD x y) = INT_ADD (INT_NEG x) (INT_NEG y)")
    force(ring.fact(CommutativeRing.UniqueInverse)).conclusion shouldBe
      proposition("!x:int. !y:int. INT_ADD x y = INT_ZERO ==> y = INT_NEG x")
    force(ring.fact(CommutativeRing.CancelMiddle)).conclusion shouldBe
      proposition("!x:int. !y:int. INT_ADD x (INT_ADD (INT_NEG x) y) = y")
    ring.facts.values.foreach(_.hypotheses shouldBe empty)
  }

  "A consequence" should "follow from its premises with the right coefficient, and be refused with a wrong one" in {
    // From `a = b`, `a * c = b * c`: the difference is `c * (a - b)`, so the coefficient is `c`.
    val premiseStatement = proposition("(a:int) = b")
    val premise = force(LogicError.lift(Kernel.assume(premiseStatement)))
    val left = term("INT_MUL (a:int) (c:int)")
    val right = term("INT_MUL (b:int) (c:int)")

    val derived = force(ring.consequence(left, right, List(premise -> term("c:int"))))
    derived.conclusion shouldBe proposition("INT_MUL (a:int) (c:int) = INT_MUL b c")
    derived.hypotheses.toSet shouldBe Set(premiseStatement)

    ring.consequence(left, right, List(premise -> term("INT_ONE"))).isLeft shouldBe true
  }
}
