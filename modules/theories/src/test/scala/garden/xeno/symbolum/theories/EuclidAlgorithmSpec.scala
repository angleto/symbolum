package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Euclid's algorithm as a definition, and a computation with it.
 *
 * What distinguishes this from `NUM_GCD` is that its equations run: `NUM_EUCLID_GCD 4 6` is taken to
 * `2` below by the step and the base case alone, with `Value` supplying each remainder and
 * `Successor.distinct` each `~(b = 0)`. A definition whose equations nobody computes with reads
 * exactly like one whose equations are wrong, so the computation is the assertion that matters.
 */
class EuclidAlgorithmSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private lazy val euclid = force(EuclidAlgorithm.construct(chain))
  private lazy val rules = euclid.logic.rules
  private lazy val value = force(Value.construct(chain))
  private val Num = TyApp(Natural.TypeName, Nil)

  private def fact(name: String): Kernel.Thm = force(euclid.fact(name))
  private def numeral(n: Int): Term = force(euclid.term(n.toString, Num))

  "Every fact of the development" should "prove the statement it is published as" in {
    EuclidAlgorithm.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe force(euclid.proposition(text))
        fact(name).hypotheses shouldBe empty
      }
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    euclid.facts.keySet shouldBe EuclidAlgorithm.Statements.map(_._1).toSet
  }

  it should "cost choice and infinity, which is what the recursion under it costs" in {
    val expected = Set(
      force(chain.classical.axiom(Classical.Choice)).conclusion,
      force(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    EuclidAlgorithm.Statements.foreach { case (name, _) =>
      withClue(s"$name: ")(Derivation.axiomsOf(fact(name)) shouldBe expected)
    }
  }

  /** `|- NUM_EUCLID_GCD a b = g`, by the step until the second argument is zero. */
  private def evaluate(a: Int, b: Int): Kernel.Thm =
    if (b == 0) force(rules.spec(numeral(a), fact(EuclidAlgorithm.AtZero)))
    else {
      val next = force(
        for {
          atAB <- rules.specAll(fact(EuclidAlgorithm.Step), List(numeral(a), numeral(b)))
          apart <- chain.successor.distinct(numeral(b), numeral(0))
          stepped <- rules.mp(atAB, apart)
          remainder <- value.of("NUM_MOD", Vector(BigInt(a), BigInt(b)))
          name <- euclid.term(s"${EuclidAlgorithm.Name} ${b}")
          carried <- Conv.apTerm(name, remainder)
          result <- Conv.trans(stepped, carried)
        } yield result
      )
      force(Conv.trans(next, evaluate(b, a % b)))
    }

  "The algorithm" should "compute a greatest common divisor by its equations" in {
    val computed = evaluate(4, 6)
    computed.hypotheses shouldBe empty
    computed.conclusion shouldBe force(euclid.proposition("NUM_EUCLID_GCD 4 6 = 2"))
  }
}
