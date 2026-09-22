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
 *
 * The price is asserted **per row** and not over the table, and that is a repair rather than a
 * style: the three rows about `num` cost the naturals' two axioms, and the two about a floor cost
 * eighteen, because their argument is a real, their characterisation is about reals, and the bounds
 * on a written rational are settled by `Linarith`. A single assertion over the table would have had
 * to be the looser of the two, and would have stopped noticing the thing it was written for.
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

  "A floor and a ceiling" should "be values at a written rational, which is the row that widened the table" in {
    // The fourth and fifth constants, and the two that take a **real**. The row is given a
    // numerator and a denominator and builds `p / q` itself, so `NUM_FLOOR (exp 1)` is not answered
    // badly here — it cannot be asked, which is the honest shape of the limit.
    evaluate(Peano.Floor, 7, 2).conclusion shouldBe written("NUM_FLOOR ((7:real) / 2) = 3")
    evaluate(Peano.Ceiling, 7, 2).conclusion shouldBe written("NUM_CEIL ((7:real) / 2) = 4")

    // Where the division is exact the two agree, and where the value is below one they are zero and
    // one: both are cases the window argument has to get right rather than cases it can guess.
    evaluate(Peano.Floor, 6, 2).conclusion shouldBe written("NUM_FLOOR ((6:real) / 2) = 3")
    evaluate(Peano.Ceiling, 6, 2).conclusion shouldBe written("NUM_CEIL ((6:real) / 2) = 3")
    evaluate(Peano.Floor, 1, 3).conclusion shouldBe written("NUM_FLOOR ((1:real) / 3) = 0")
    evaluate(Peano.Ceiling, 1, 3).conclusion shouldBe written("NUM_CEIL ((1:real) / 3) = 1")
  }

  it should "cost the reals, which is the constant's price and not this procedure's" in {
    // Eighteen against two, and the assertion is the pair rather than either half: a row about a
    // real cannot be cheaper than the reals, and a row about `num` must not become dearer. What
    // would break this is a route for the naturals that went through the embedding, which is the
    // thing `Digits` exists to avoid and which no other test here would notice.
    val floor = Derivation.axiomsOf(evaluate(Peano.Floor, 7, 2))
    val quotient = Derivation.axiomsOf(evaluate(Modular.DivName, 17, 5))

    info(s"a floor rests on ${floor.size} axioms and a quotient on ${quotient.size}")
    floor should have size 18
    quotient should have size 2
    quotient.subsetOf(floor) shouldBe true
  }

  it should "refuse a denominator of zero, and refuse it before dividing by it" in {
    // The refusal is the procedure's and the order matters: the answer this row computes is
    // `numerator / denominator` in Scala as well, so a check that came after it threw where every
    // other refusal here returns. It did, in the first version.
    val refusal = procedure
      .of(Peano.Floor, Vector(7, 0))
      .swap
      .fold(theorem => fail(s"proved ${chain.widest.show(theorem.conclusion)}"), identity)

    refusal.message should include("positive denominator")
    refusal.message should include("7 over 0")
  }

  "A constant with no row" should "be refused by name, and the refusal say what there is" in {
    // `NUM_SUB` and not `NUM_GCD` or `NUM_FLOOR`, which is what this test named while each of those
    // was the constant without a row. It is a better subject than either was: truncated subtraction
    // is **defined** rather than chosen, so a row for it would not be read off a characterisation
    // at all, and the message still has to name it rather than claim it does not exist.
    val refusal = procedure
      .of(Peano.Subtraction, Vector(7, 2))
      .swap
      .fold(theorem => fail(s"proved ${chain.widest.show(theorem.conclusion)}"), identity)

    refusal.message should include(Peano.Subtraction)
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
      // Looked for in `Modular` and then in `Peano`, because the two families are read off
      // different developments: a quotient off `Modular`, a floor off `Peano`. A name in neither is
      // what this catches, which is a note naming a lemma that has been renamed or never existed.
      withClue(s"$constant is read off ${route.characterisation}: ") {
        val held = chain.modular
          .fact(route.characterisation)
          .orElse(chain.peano.fact(route.characterisation))
        held.isRight shouldBe true
      }
      route.note should not be empty
      route.arity should be > 0
    }

    procedure.reachable shouldBe
      Vector(Peano.Ceiling, Peano.Floor, Modular.DivName, Modular.GcdName, Modular.ModName).sorted
  }
  /**
   * The step count in the refusal about a combination, at one and elsewhere.
   *
   * One step is not a corner: the bound is `right / answer + 1` over big integers and is exactly
   * `1` when the answer is zero, which is the first case anybody who calls this reaches. It is
   * also why `Prose.count` gained an overload on `BigInt` rather than the call site gaining a
   * `toInt`, which would print a different number for a bound past the machine word.
   */
  "The refusal about a combination" should "take the singular at one step and the plural elsewhere" in {
    def why(left: BigInt, right: BigInt, answer: BigInt): String =
      Value.combination(left, right, answer) match {
        case Left(error) => error.message
        case Right(found) => fail(s"expected no combination and got $found")
      }

    // `answer == 0` is the branch that makes the bound one; the second case takes the other
    // branch at `right / answer == 1`, and both are chosen so the search finds nothing: a left of
    // zero can never reach a positive answer.
    why(0, 0, 0) should endWith("within 1 step")
    why(0, 2, 2) should endWith("within 2 steps")
  }

  /**
   * The arity in the refusal about a constant applied to the wrong number of arguments.
   *
   * It reached one by construction and read `takes 1 argument(s)`: the branch of `Value` that
   * reads a numeral passes `route.copy(arity = 1)`, so the literal one is in the source. The
   * `(s)` form is not what the card's census finds -- the noun is not a bare plural -- and it is
   * a second name for what `Prose.count` already does in this same file, which is why it went.
   *
   * Both directions, because a message rewritten into the singular everywhere would pass on one.
   */
  "The refusal about a constant's arity" should "take the singular at one and the plural elsewhere" in {
    // A row off the table rather than one built here, so the test says nothing about `Route`'s
    // shape and survives a field being added to it.
    val route = Value.Routes.values.head

    Value.wrongArity("f", route.copy(arity = 1), 3).message should
      include("f takes 1 argument and was given 3")
    Value.wrongArity("f", route.copy(arity = 2), 3).message should
      include("f takes 2 arguments and was given 3")
    // The form it replaced, which reads at one and at two and is neither the singular nor the
    // plural.
    Value.wrongArity("f", route, 3).message should not include "argument(s)"
  }

  /**
   * The counter's two-form overload, which landed with the site above and its neighbour in
   * `Remedy`.
   *
   * `Prose.count` appends an `s` and says of itself that an irregular noun wants both forms
   * written out; until 2026-09-22 there was nowhere to write them, so a caller needing
   * `hypothesis`/`hypotheses` wrote `thing(s)`. The five per-module copies of this counter have
   * taken both forms since 2026-09-20 for `entry`/`entries`, so this is the shared one catching
   * up rather than a new mechanism.
   *
   * Zero takes the plural here as it does in the one-argument body, which is the case a reader
   * of the condition does not picture.
   */
  "The counter with both forms" should "take the first at one and the second everywhere else" in {
    Prose.count(1, "hypothesis", "hypotheses") shouldBe "1 hypothesis"
    Prose.count(2, "hypothesis", "hypotheses") shouldBe "2 hypotheses"
    Prose.count(0, "hypothesis", "hypotheses") shouldBe "0 hypotheses"
  }
}
