package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.logic.BoundReached

/**
 * The three things a consumer met, and the round that came out of meeting them.
 *
 * Every goal here was written by somebody proving something they wanted proved, and refused. None
 * of the three refusals was a missing idea, which is the reason they are pinned together: each was
 * a place where the procedure knew the thing and could not be asked the question.
 *
 *  - a product over a difference was read as one atom, while a manufactured product was multiplied
 *    out, so the two readings of one statement never met;
 *  - the products were formed over the hypotheses and not over the hypotheses with the goal's
 *    negation, which is what `nlinarith` multiplies over;
 *  - an equality took part in no product, on the argument that its product is zero and therefore
 *    carries nothing. The first half is true and the second does not follow.
 *
 * The measurements that produced these are on Mycelium card 53a467e8.
 */
class LinarithProductsSpec extends AnyFlatSpec with Matchers {

  private val linarith = Linarith.standard

  /**
   * The chain, for the goals whose atoms are applications of constants the reals alone do not have.
   *
   * `Power` and `Sum` belong to `Series` and `real_of_num` to `Peano`, so a goal mentioning one
   * cannot be *stated* against `Real.standard`. The procedure under test is the same one: the
   * chain's order is over the same axioms and `Linarith.construct` makes the same three lemmas out
   * of it.
   */
  private val chain = Chain.standard
  private val overChain =
    Linarith.construct(chain.order).fold(error => fail(error.message), identity)

  private def proved(text: String): Unit =
    withClue(s"$text: ") {
      linarith.prove(text).fold(error => fail(error.message), _ => succeed)
    }

  private def refused(text: String): Unit =
    withClue(s"$text: ") { linarith.prove(text).isLeft shouldBe true }

  /* --------------------------------------------- the goal written without distributing */

  "A product over a difference" should "be the same goal as the product distributed" in {
    // Two statements of one thing. Until 2026-09-10 the second was proved and the first refused,
    // and the difference was whether the author had distributed by hand.
    proved("!p:real q:real d:real. 0 < p /\\ d < q ==> 0 < p * q - p * d")
    proved("!p:real q:real d:real. 0 < p /\\ d < q ==> 0 < p * (q - d)")
    proved("!p:real q:real d:real. 0 < p /\\ d < q ==> 0 < (q - d) * p")
  }

  it should "not depend on there being a second unknown in the factor" in {
    // `q + 1` is enough: the point was never how many unknowns the factor had, it was that a
    // product of two non-constants stopped being read at all.
    proved("!p:real q:real. 0 < p /\\ 0 < q ==> 0 < p * (q + 1)")
    proved("!p:real q:real. 0 < p /\\ 0 < q ==> 0 < p * q + p")
  }

  it should "no longer be named as the obstacle when the goal is simply false" in {
    // The refusal used to say `x * y` "multiplies two unknowns, which no linear form has", which
    // stopped being true the moment the form multiplied it out. A caller told to rewrite the
    // product would have rewritten it and been refused again.
    val refusal = linarith.prove("!x:real y:real. 0 < x /\\ 0 < y ==> 1 < x * y")

    refusal.isLeft shouldBe true
    refusal.fold(_.message, _ => "") should not include "multiplies two unknowns"
  }

  /* ------------------------------------------------- the negation of the goal */

  "A factor recovered from a positive product" should "follow, which needs the goal's negation" in {
    // The smallest case of the family the consumer was in: from `n * d = b` with `n` and `b`
    // positive, `d` is positive. It does not follow linearly and it follows at once from `d <= 0`,
    // which is the thing nobody had assumed.
    proved("!n:real d:real b:real. n * d = b /\\ 0 < n /\\ 0 < b ==> 0 < d")
    proved("!x:real y:real. 0 < x * y /\\ 0 < x ==> 0 < y")
  }

  it should "come from LT_TOTAL and not from a classical step" in {
    // There is no excluded middle here to reach for, and none is needed: the three cases of
    // trichotomy are one of the sixteen axioms, and each case is an ordinary run with one more
    // fact. So this reaches no axiom the procedure did not already reach.
    val theorem = linarith
      .prove("!n:real d:real b:real. n * d = b /\\ 0 < n /\\ 0 < b ==> 0 < d")
      .fold(error => fail(error.message), identity)

    theorem.hypotheses shouldBe empty
    garden.xeno.symbolum.kernel.Derivation
      .axiomsOf(theorem)
      .map(Real.standard.show) should contain("!x:real. !y:real. x < y \\/ x = y \\/ y < x")
  }

  /* ------------------------------------------------------- degree three */

  "A product of three positives" should "be proved by the second round" in {
    proved("!x:real y:real z:real. 0 < x /\\ 0 < y /\\ 0 < z ==> 0 < x * y * z")
    proved("!x:real y:real z:real. 0 <= x /\\ 0 <= y /\\ 0 <= z ==> 0 <= x * y * z")
    proved("!x:real. 0 < x ==> 0 < x * x * x")
  }

  it should "reach the consumer's own goal, which is where the round came from" in {
    // The monotonicity of `c_max` in the number of circuits, from the Collatz coefficient
    // calculation. Three unknowns and an ordered difference, and the sign of it was prose in that
    // document because this was refused.
    proved(
      "!r:real e:real q:real d:real. 0 < r /\\ 0 < e /\\ d < q ==> (r * e) * (d - q) < 0"
    )
    proved(
      "!r:real e:real d:real q:real. 0 < r /\\ 0 < e /\\ d < q ==> r * e * d - r * e * q < 0"
    )
  }

  "A degree past the cubic round" should "be refused rather than searched for indefinitely" in {
    refused(
      "!w:real x:real y:real. 0 < w /\\ 0 < x /\\ 0 < y /\\ 0 < z:real ==> 0 < w * x * y * z"
    )
  }

  /* ------------------------------------------------------- what must stay refused */

  "A false claim" should "still be refused, whatever the products manufacture" in {
    // A manufactured fact is a theorem like any other and the ring step still checks the
    // combination against the goal, so nothing here can make the procedure wrong. These are the
    // two that say so.
    refused("!x:real y:real. 0 < x /\\ 0 < y ==> 1 < x * y")
    refused("!x:real. 0 < x ==> x < x * x")
    refused("!x:real y:real. x <= y ==> x < y")
  }

  /* ------------------------------------------------------- the cost */

  "The second round" should "cost nothing on a goal whose atoms the pairs already reach" in {
    // The gate, and the whole of what makes the round affordable. A chain of linear hypotheses
    // names no atom a product could supply, so no cube is built: measured at 67 ms for a refusal
    // on twelve hypotheses against 2918 ms with the round ungated.
    //
    // **Asserted as a count since 2026-09-11, and the wall clock is only reported.** It used to
    // assert the elapsed time, and that assertion fails on a busy machine and passes on a quiet
    // one: it read 67 ms the day it was written and 4267 ms on the same tree at a load average of
    // a hundred and twenty. The card that asks for the constant factor names this file among the
    // three that call `System.nanoTime`, and it is right that a number a machine can move is not a
    // number anybody can be held to.
    //
    // What the gate does is observable without a clock. The search stops at the **pair** round,
    // having manufactured the count the assertion below pins, past the bound `Linarith.Facts` sets,
    // and never enters the cube round at all. Had it entered, the bound it reached would be the
    // other one and the count would be larger. That is a function of the goal and of nothing else.
    val size = 12
    val names = (0 to size).map(index => s"x$index:real").mkString(" ")
    val links = (0 until size).map(index => s"x$index:real < x${index + 1}:real").mkString(" /\\ ")

    linarith.prove(s"!$names. $links ==> x0:real < x$size:real").isRight shouldBe true

    val started = System.nanoTime()
    val refusal = linarith.prove(s"!$names. $links ==> x$size:real < x0:real")
    val elapsed = (System.nanoTime() - started) / 1000000

    refusal match {
      case Left(BoundReached(limit, reached, allowed, _)) =>
        limit shouldBe "Linarith.Facts"
        reached shouldBe 104
        allowed shouldBe linarith.factLimit
      case other => fail(s"expected the pair round to reach its bound, got $other")
    }

    info(s"a refusal on $size hypotheses: $elapsed ms, which is a reading and not an assertion")
  }

  /* ----------------------------------------------- what comes out has nothing on its left */

  /* ------------------------------------------- an application, which is an atom like any other */

  "An applied constant" should "be an atom the search works over, not a term the reader turns away" in {
    // The same story as the product above, found by a consumer on 2026-09-11 and reported as
    // "the reader refuses an applied constant and sends a goal it would decide into refusal". Half
    // right, and the half that is wrong is worth the measurement: `formOf` has always made an atom
    // of whatever it could not take apart, so the search was never stopped. What refused was the
    // *message*, and it said the goal could not be read when the goal had been read and no
    // certificate existed.
    val goals = Vector(
      "!k:num. 0 < Power 3 k /\\ Power 3 k < Power 4 k ==> 3 * Power 3 k < 4 * Power 4 k",
      "!f:num->real. !n:num. 0 <= Sum f n ==> 0 <= Sum f n + 1",
      "!n:num. real_of_num n <= real_of_num n + 1"
    )

    goals.foreach { text =>
      withClue(s"$text: ") {
        val statement = chain.widest.proposition(text).fold(error => fail(error.message), identity)
        overChain.prove(statement).fold(error => fail(error.message), _.hypotheses shouldBe empty)
      }
    }
  }

  it should "no longer be named as the obstacle when the goal simply does not follow" in {
    // `0 < Power 4 k` is not provable here and never was: nothing among the hypotheses — there are
    // none — says a power is positive. What changed is which of the two answers a caller gets.
    // Naming the atom sent a consumer to rewrite a goal it had built correctly, and the consumer
    // wrote forty lines to abstract every unreadable subterm to a fresh variable.
    val refusal = chain.widest
      .proposition("!k:num. 0 < Power 4 k")
      .flatMap(overChain.prove)

    refusal.isLeft shouldBe true
    refusal.fold(_.message, _ => "") should not include "is not a variable, a numeral or a sum"
    refusal.fold(_.message, _ => "") should include("non-negative combination of the hypotheses")
  }

  it should "still name a denominator, which the reader goes on turning away" in {
    // The narrowing is a narrowing and not a removal. A symbolic denominator asks for `~(y = 0)`,
    // which is `Field`'s to assume, and `inv 0` is an atom rather than a denominator: both keep the
    // message that names the denominator and whose price it is.
    Vector("(x:real) / (y:real) < 1", "!x:real. 0 < x ==> 0 < inv x").foreach { text =>
      withClue(s"$text: ") {
        linarith.prove(text).fold(_.message, _ => "") should include("divides by")
      }
    }
  }

  "Every theorem this procedure returns" should "carry no hypothesis at all" in {
    // The conclusion was compared with the goal from the start and the hypothesis list was not, so
    // an assembly defect that failed to discharge an assumption would return `h |- goal` where the
    // caller expects `|- goal`. A caller reading the conclusion and ignoring the turnstile cannot
    // tell those apart, and this procedure charges nothing by design, so a hypothesis on the way
    // out is a defect and never a price.
    //
    // Asserted over the shapes that use every route: the certificate, the products, the refutation
    // split, the cubic round, the denial, and the curried peel. Each of those assembles and
    // discharges differently and each is a place the mistake could live.
    Vector(
      "!x:real y:real. x < y ==> x < y + 1",
      "!x:real y:real. 0 < x /\\ 0 < y ==> 0 < x * y",
      "!n:real d:real b:real. n * d = b /\\ 0 < n /\\ 0 < b ==> 0 < d",
      "!x:real y:real z:real. 0 < x /\\ 0 < y /\\ 0 < z ==> 0 < x * y * z",
      "!x:real. 0 < x ==> ~(x = 0)",
      "!x:real y:real. 0 < x ==> 0 < y ==> 0 < x + y"
    ).foreach { text =>
      withClue(s"$text: ") {
        linarith.prove(text).fold(error => fail(error.message), _.hypotheses shouldBe empty)
      }
    }
  }
}
