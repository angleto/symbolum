package garden.xeno.symbolum.theories

import org.scalacheck.Gen
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks

/**
 * The search half of [[Ideal]], checked against the one property that makes its answer worth
 * handing to the kernel: a `Member` is an exact identity, and a `NotMember` is never wrong about a
 * polynomial built to be in the ideal.
 *
 * The cofactors are not trusted downstream, so a wrong one costs a proof rather than a theorem.
 * What this suite guards is the other direction, which nothing downstream can see: a search that
 * returned `NotMember` for a member would make [[Ideal]] refuse goals it should prove, silently.
 */
class GroebnerSpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {

  import Groebner.*

  /**
   * Two hundred systems per property, which on 2026-11-10 cost 244 ms and 47 ms for the two, so the
   * count is not what limits the suite. What chose it is the second property's split, printed by
   * the property itself: two runs that day read 121 members to 79 and 111 to 89, so each branch is
   * met dozens of times. The split moves with the seed, which is why the property asserts that both
   * were met rather than trusting either reading.
   */
  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 200)

  private val arity = 3

  private def x(i: Int): Poly = variable(i, arity)
  private def c(n: Int): Poly = constant(Rational.of(BigInt(n)), arity)

  private def combination(cofactors: Vector[Poly], generators: Vector[Poly]): Poly =
    cofactors.indices.foldLeft(zero)((acc, i) => add(acc, multiply(cofactors(i), generators(i))))

  private val monomial: Gen[Poly] =
    for {
      coefficient <- Gen.chooseNum(-3, 3)
      exponents <- Gen.listOfN(arity, Gen.chooseNum(0, 1))
    } yield term(exponents.toVector, Rational.of(BigInt(coefficient)), one(arity))

  private val polynomial: Gen[Poly] =
    Gen.chooseNum(1, 3).flatMap(n => Gen.listOfN(n, monomial)).map(_.foldLeft(zero)(add))

  private val system: Gen[Vector[Poly]] = Gen.listOfN(3, polynomial).map(_.toVector)

  "A combination of the generators" should "come back a member, with cofactors that are an exact identity" in {
    forAll(system, Gen.listOfN(3, polynomial)) { (generators, multipliers) =>
      val target = combination(multipliers.toVector, generators)
      membership(generators, target, arity) match {
        case Membership.Member(cofactors, _) =>
          combination(cofactors, generators) shouldBe target
        case other => fail(s"a combination of the generators came back $other")
      }
    }
  }

  "Any target" should "never be a member whose cofactors fail to reproduce it" in {
    // Counted, because a property whose every sample took one branch checks nothing about the other,
    // and passes: the guard is only as good as the thought given to what would make it empty.
    var members = 0
    var others = 0
    forAll(system, polynomial) { (generators, target) =>
      membership(generators, target, arity) match {
        case Membership.Member(cofactors, _) =>
          members += 1
          combination(cofactors, generators) shouldBe target
        case Membership.NotMember(remainder, _) =>
          others += 1
          remainder should not be empty
        case Membership.Exhausted(spent, budget) => spent should be > budget
      }
    }
    info(s"$members members, $others not members")
    members should be > 0
    others should be > 0
  }

  "The ideal of x * x" should "not contain x, though x vanishes wherever x * x does" in {
    // The case that makes `NotMember` a statement about the ideal and never about common zeros.
    membership(Vector(multiply(x(0), x(0))), x(0), arity) shouldBe a[Membership.NotMember]
  }

  "A linear system with one solution" should "put every unknown minus its value in the ideal" in {
    // 3a + b + c = -3, a + 3b + c = 9, a + b + 3c = 19, whose solution is a = -4, b = 2, c = 7.
    val generators = Vector(
      add(add(add(multiply(c(3), x(0)), x(1)), x(2)), c(3)),
      add(add(add(x(0), multiply(c(3), x(1))), x(2)), c(-9)),
      add(add(add(x(0), x(1)), multiply(c(3), x(2))), c(-19))
    )
    val product = multiply(multiply(x(0), x(1)), x(2))
    membership(generators, add(product, c(56)), arity) match {
      case Membership.Member(cofactors, _) => combination(cofactors, generators) shouldBe add(product, c(56))
      case other => fail(s"abc + 56 came back $other")
    }
  }

  "A zero generator" should "keep its place in the cofactors and be given nothing" in {
    val generators = Vector(zero, add(x(0), c(-1)))
    membership(generators, add(multiply(x(0), x(1)), negate(x(1))), arity) match {
      case Membership.Member(cofactors, _) =>
        cofactors should have length 2
        cofactors(0) shouldBe empty
      case other => fail(s"came back $other")
    }
  }

  "The budget" should "stop the search and say so rather than answer" in {
    val generators = Vector(add(multiply(x(0), x(1)), c(-1)), add(multiply(x(1), x(2)), c(-1)))
    membership(generators, x(0), arity, budget = 1) shouldBe a[Membership.Exhausted]
  }

  "The order" should "put a higher degree first and break a tie by the last unknown, reversed" in {
    compare(Vector(1, 1, 0), Vector(0, 0, 1)) should be > 0
    compare(Vector(1, 0, 0), Vector(0, 0, 1)) should be > 0
    compare(Vector(0, 1, 0), Vector(0, 0, 1)) should be > 0
    compare(Vector(1, 0, 1), Vector(1, 0, 1)) shouldBe 0
    leading(zero) shouldBe None
  }
}
