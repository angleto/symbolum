package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Arithmetic on the numerals of `num`, and the one number that says why the file exists.
 *
 * Every assertion here is about the **price**. That a sum of two numerals is provable at all was
 * already true through `Modular.identity` once its rule set is widened by three lemmas `Peano`
 * already publishes, and that route was measured on 2026-09-18 before this was written: it proves
 * `17 = 5 * 3 + 2` and it charges the sixteen axioms of the reals. So the question this file
 * answers is not whether, it is at what cost, and the test below that pins the cost over `num`
 * against the cost over the reals is the one that would notice the answer changing.
 */
class DigitsSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard

  private lazy val semiring: Semiring =
    Semiring.construct(chain.peano).fold(error => fail(error.message), identity)

  private lazy val digits: Digits =
    Digits.construct(semiring).fold(error => fail(s"the digits do not build: ${error.message}"), identity)

  private def show(term: Term): String = chain.widest.show(term)

  "Every lemma of the table" should "say what its text says, quantified over its own letters" in {
    for ((name, text) <- Digits.Lemmas) {
      val theorem = digits.lemma(name).fold(error => fail(error.message), identity)
      val written = chain.peano
        .proposition(text)
        .fold(error => fail(s"$name does not read: ${error.message}"), identity)

      // The lemma is proved open and published closed, which is what makes it a rewrite rule: a
      // rule takes its pattern variables from the quantifiers it strips, so `!x y. ...` matches any
      // pair of numerals and the open equation matches the letters `x` and `y` and nothing else.
      // That was not a hypothesis. The first version of this file published them open, every rule
      // it built matched nothing, and every computation came back as its own statement unrewritten.
      //
      // Compared by specialising back at the text's own letters rather than by stripping the
      // binders, because the binder a theorem carries is not the letter the text was written with:
      // `NUM_ONE + NUM_BIT0 y = NUM_BIT1 y` comes back quantified over `x`, and a comparison that
      // read the name would be asserting something about the rewriting's choice of fresh variable.
      val letters = Term.freeVariables(written).toList.sortBy(_.name)
      val instance = chain.peano.logic.rules
        .specAll(theorem, letters.map(letter => letter: Term))
        .fold(error => fail(s"$name does not specialise: ${error.message}"), identity)

      withClue(s"$name\n  text:    ${show(written)}\n  theorem: ${show(theorem.conclusion)}\n") {
        instance.conclusion shouldBe written
        Logic.stripForall(theorem.conclusion).map(_._1.size) shouldBe Right(letters.size)
      }
      theorem.hypotheses shouldBe empty
    }
  }

  it should "rest on the axioms the naturals cost, and no more" in {
    for ((name, _) <- Digits.Lemmas) {
      val theorem = digits.lemma(name).fold(error => fail(error.message), identity)
      val axioms = Derivation.axiomsOf(theorem)
      withClue(s"$name rests on: ${axioms.map(show).toVector.sorted.mkString(", ")}\n") {
        axioms.size should be <= 2
      }
    }

    // And one of them costs nothing at all, which is worth asserting rather than leaving inside the
    // bound above: `1 + 1 = 2` is the definition of the even digit read backwards and reaches no
    // axiom, so a change that made every lemma here cost two would pass the loop and fail this.
    Derivation.axiomsOf(
      digits.lemma("NUM_ADD_ONE_ONE").fold(error => fail(error.message), identity)
    ) shouldBe empty
  }

  "A sum and a product of numerals" should "be theorems about `num` at what the naturals cost" in {
    val sum = digits.add(2, 3).fold(error => fail(error.message), identity)
    val product = digits.multiply(12, 12).fold(error => fail(error.message), identity)

    sum.conclusion shouldBe
      chain.peano.proposition("(2:num) + 3 = 5").fold(error => fail(error.message), identity)
    product.conclusion shouldBe
      chain.peano.proposition("(12:num) * 12 = 144").fold(error => fail(error.message), identity)

    Derivation.axiomsOf(sum) should have size 2
    Derivation.axiomsOf(product) should have size 2
    sum.hypotheses shouldBe empty
    product.hypotheses shouldBe empty
  }

  it should "rest on none of the axioms the same arithmetic rests on over the reals" in {
    // The measurement the file is for, and the guard on it. `12 * 12 = 144` is a theorem on both
    // sides of the embedding and the two answers rest on different things: over the reals it
    // reaches the axioms of the field that the count below pins, here it reaches choice and
    // infinity and nothing else, and the two sets share nothing. A route
    // for `num` that went through the reals would pass every other test in this file and fail this
    // one, which is exactly the route that was tried and rejected.
    val overTheNaturals = digits.multiply(12, 12).fold(error => fail(error.message), identity)
    val overTheReals = Arithmetic.standard
      .multiply(12, 12)
      .fold(error => fail(error.message), identity)

    val naturals = Derivation.axiomsOf(overTheNaturals)
    val reals = Derivation.axiomsOf(overTheReals)

    info(s"12 * 12 = 144 rests on ${naturals.size} axioms over num and ${reals.size} over the reals")
    naturals should have size 2
    reals should have size 5
    naturals.intersect(reals) shouldBe empty
  }

  "The computation" should "hold across every carry pattern the digits have, not at one value" in {
    // Thirteen by thirteen, sums and products, which is 338 theorems and took 139 ms on 2026-09-18.
    // The bound is chosen rather than round: twelve is `NUM_BIT0 (NUM_BIT0 (NUM_BIT1 NUM_ONE))`,
    // so the sweep reaches every four-bit pattern and every carry between them, including the two
    // the table closes rather than recurses on, which are `ZERO` on either side.
    val bound = 12
    var proved = 0

    for (left <- 0 to bound; right <- 0 to bound) {
      val sum = digits.add(left, right).fold(error => fail(s"$left + $right: ${error.message}"), identity)
      val product =
        digits.multiply(left, right).fold(error => fail(s"$left * $right: ${error.message}"), identity)

      val expectedSum = chain.peano
        .proposition(s"($left:num) + $right = ${left + right}")
        .fold(error => fail(error.message), identity)
      val expectedProduct = chain.peano
        .proposition(s"($left:num) * $right = ${left * right}")
        .fold(error => fail(error.message), identity)

      withClue(s"$left + $right: ${show(sum.conclusion)}\n") { sum.conclusion shouldBe expectedSum }
      withClue(s"$left * $right: ${show(product.conclusion)}\n") {
        product.conclusion shouldBe expectedProduct
      }
      proved += 2
    }

    proved shouldBe 2 * (bound + 1) * (bound + 1)
    info(s"$proved theorems over the pairs up to $bound")
  }

  it should "reach six digits inside the default number of passes" in {
    // The limit is a guard against a rule set that does not terminate rather than a budget, and
    // what says so is that six digits are settled far inside it. The figures are in the file's own
    // docstring and were found by bisecting on the limit; these two are the ones that matter, which
    // is the largest case anybody has asked for and the smallest limit that carries it.
    digits.multiply(999999, 999999, 40).isRight shouldBe true
    digits.multiply(999999, 999999, 39).isLeft shouldBe true
  }

  "A value that is not a numeral of `num`" should "be refused by name rather than computed" in {
    // The convention that a procedure which cannot settle must refuse, and must name what it could
    // not do, read from the other side: the procedure takes two values and there is exactly one way
    // to hand it something it cannot make a numeral of, which is a negative one. The refusal says
    // which of the two facts about `num` stopped it.
    val refusal = digits.add(-1, 3).swap.fold(theorem => fail(s"proved ${show(theorem.conclusion)}"), identity)

    refusal.message should include("-1")
    refusal.message should include("non-negative")
    refusal.message should not include "real"
  }
}
