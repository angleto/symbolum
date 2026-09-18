package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * `NUM_DIV 17 5 = 3`, which was the sentence a card carried as the thing this system could not say.
 *
 * One value per constant and not twenty, which is the acceptance criterion that card wrote down and
 * the reason is worth keeping: this procedure either produces the theorem or it does not, and
 * twenty values measure that once each. What is asserted beside each value is the **price**, which
 * is the thing a second route would change without changing any of the values.
 */
class ValueSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard

  private lazy val procedure: Value =
    Value.construct(chain).fold(error => fail(s"the procedure does not build: ${error.message}"), identity)

  private def evaluate(constant: String, arguments: BigInt*): Kernel.Thm =
    procedure
      .of(constant, arguments.toVector)
      .fold(error => fail(s"$constant ${arguments.mkString(" ")}: ${error.message}"), identity)

  private def written(text: String): Term =
    chain.widest.proposition(text).fold(error => fail(s"$text does not read: ${error.message}"), identity)

  "A quotient and a remainder" should "be theorems about the constants, not numbers a caller trusts" in {
    val quotient = evaluate(Modular.DivName, 17, 5)
    val remainder = evaluate(Modular.ModName, 17, 5)

    quotient.conclusion shouldBe written("NUM_DIV (17:num) 5 = 3")
    remainder.conclusion shouldBe written("NUM_MOD (17:num) 5 = 2")
    quotient.hypotheses shouldBe empty
    remainder.hypotheses shouldBe empty
  }

  it should "rest on the two axioms the naturals cost, which is the whole design question" in {
    // The measurement that decided the route. Embedding into the reals, computing there and coming
    // back proves the same equations and charges sixteen, because `NUM_REAL_INJECTIVE` rests on
    // the reals; every characterisation this spends rests on two. A change of route would leave
    // every other assertion in this file green and fail here.
    val quotient = evaluate(Modular.DivName, 17, 5)
    val characterisation =
      chain.modular.fact(Modular.DivisionDetermined).fold(error => fail(error.message), identity)

    Derivation.axiomsOf(quotient) should have size 2
    Derivation.axiomsOf(quotient) shouldBe Derivation.axiomsOf(characterisation)
  }

  it should "divide exactly where it divides exactly, and by zero where the lemma cannot reach" in {
    evaluate(Modular.DivName, 144, 12).conclusion shouldBe written("NUM_DIV (144:num) 12 = 12")
    evaluate(Modular.ModName, 144, 12).conclusion shouldBe written("NUM_MOD (144:num) 12 = 0")

    // Division by zero is not a hole: both constants are total and `Modular` says what they are
    // there. It is also the one case `NUM_DIV_MOD_UNIQUE` cannot cover, since `r < ZERO` is
    // unmeetable, so a procedure that only knew the uniqueness would refuse a value that exists.
    evaluate(Modular.DivName, 7, 0).conclusion shouldBe written("NUM_DIV (7:num) 0 = 0")
    evaluate(Modular.ModName, 7, 0).conclusion shouldBe written("NUM_MOD (7:num) 0 = 7")
  }

  "A greatest common divisor" should "be a theorem too, by the characterisation rather than by Euclid" in {
    // The decision the card left open, taken and visible here: Euclid's algorithm is a definition by
    // well-founded recursion, which this system has not got, and the characterisation asks for
    // nothing new. What it costs is more inferences per value, which is a trade only a caller
    // computing many would feel.
    evaluate(Modular.GcdName, 12, 18).conclusion shouldBe written("NUM_GCD (12:num) 18 = 6")
    evaluate(Modular.GcdName, 18, 12).conclusion shouldBe written("NUM_GCD (18:num) 12 = 6")
    evaluate(Modular.GcdName, 7, 13).conclusion shouldBe written("NUM_GCD (7:num) 13 = 1")
    evaluate(Modular.GcdName, 48, 180).conclusion shouldBe written("NUM_GCD (48:num) 180 = 12")

    Derivation.axiomsOf(evaluate(Modular.GcdName, 12, 18)) should have size 2
  }

  it should "answer where one side is zero, which is not the case the lemmas exclude" in {
    // `NUM_GCD a ZERO` is `a`, and every fact about the constant carries "not both zero" rather
    // than "neither zero", so this is inside what is provable. It is a separate case in the
    // derivation for a reason that is arithmetic and not bookkeeping: the Bezout combination
    // `a * x = b * y + c` has no solution when `a` is zero, because `c` is then `b`.
    evaluate(Modular.GcdName, 0, 5).conclusion shouldBe written("NUM_GCD (0:num) 5 = 5")
    evaluate(Modular.GcdName, 5, 0).conclusion shouldBe written("NUM_GCD (5:num) 0 = 5")
  }

  it should "refuse two zeros, which is the one pair nothing is provable about" in {
    val refusal = procedure
      .of(Modular.GcdName, Vector(0, 0))
      .swap
      .fold(theorem => fail(s"proved ${chain.widest.show(theorem.conclusion)}"), identity)

    refusal.message should include("NUM_GCD ZERO ZERO")

    // And the guard against reading that as a limitation of this procedure: what is refused is a
    // term nothing in `Modular` says anything about, and the way to see that is that every fact
    // about the constant carries the same condition.
    for (name <- List(Modular.GcdDividesLeft, Modular.GcdDividesRight, Modular.GcdDivides)) {
      val fact = chain.modular.fact(name).fold(error => fail(error.message), identity)
      chain.widest.show(fact.conclusion) should include("~(x = 0)")
    }
  }

  "The Bezout combination" should "be a witness the derivation checks, not a number it trusts" in {
    // The search is in Scala and what leaves it is a pair of numbers; every value above proves an
    // equation about them through the kernel. This asserts the invariant the search is supposed to
    // have, over every pair up to twelve with a non-zero left side, which is 144 pairs: if it ever
    // returned a pair that did not satisfy the equation, the derivation would refuse rather than
    // prove something false, and the refusal would name the wrong thing.
    var checked = 0
    for (left <- 1 to 12; right <- 1 to 12) {
      val answer = BigInt(left).gcd(BigInt(right))
      val pair = Value
        .combination(left, right, answer)
        .fold(error => fail(s"$left and $right: ${error.message}"), identity)

      withClue(s"$left * ${pair._1} = $right * ${pair._2} + $answer: ") {
        BigInt(left) * pair._1 shouldBe BigInt(right) * pair._2 + answer
      }
      checked += 1
    }
    checked shouldBe 144
  }

  "A constant with no row" should "be refused by name, and the refusal say what there is" in {
    // `NUM_FLOOR` and not `NUM_GCD`, which is what this test named until the gcd got a row. The
    // two rows that are missing are missing for a reason the message does not carry and this
    // comment does: a floor takes a **real** and holds `0 <= x` as a written hypothesis, so its row
    // is the first that widens the table rather than using it.
    val refusal = procedure
      .of(Peano.Floor, Vector(7, 2))
      .swap
      .fold(theorem => fail(s"proved ${chain.widest.show(theorem.conclusion)}"), identity)

    refusal.message should include(Peano.Floor)
    refusal.message should include(Modular.DivName)

    // And it does not say the constant is missing, which is what this refusal said first: there is
    // a `NUM_GCD` and it is where the caller left it. What is missing is the row.
    refusal.message should not include "no definition"
  }

  it should "refuse an argument count that is not the constant's, before computing anything" in {
    val refusal = procedure
      .of(Modular.DivName, Vector(17))
      .swap
      .fold(theorem => fail(s"proved ${chain.widest.show(theorem.conclusion)}"), identity)

    refusal.message should include("2")
    refusal.message should include("1")
  }

  "The table" should "say what each row is read off, so a reader can check the value's provenance" in {
    // A row is the place the reader learns which lemma a value rests on. Asserting that each one
    // names a fact the development actually publishes is what stops a note drifting into prose
    // about a lemma that has been renamed.
    Value.Routes should not be empty

    for ((constant, route) <- Value.Routes) {
      withClue(s"$constant is read off ${route.characterisation}: ") {
        chain.modular.fact(route.characterisation).isRight shouldBe true
      }
      route.note should not be empty
      route.arity should be > 0
    }

    procedure.reachable shouldBe Vector(Modular.DivName, Modular.GcdName, Modular.ModName)
  }
}
