package garden.xeno.symbolum.examples

import garden.xeno.symbolum.tactics.Cost
import garden.xeno.symbolum.theories.Chain

/**
 * The proof half, demonstrated: four claims put to the whole tactic surface, and what each one cost.
 *
 * The first demonstration in this directory that is not about the algebra. Until 2026-09-13
 * `examples` depended on `core` alone, so there was nowhere for one to live; `build.sbt` carries
 * why moving it to `tactics` costs the trust boundary nothing.
 *
 * What it is for is the **accounting**, which is the part of this system a reader most often
 * assumes rather than checks. A theorem here is not a verdict: it is a conclusion together with
 * the axioms it actually spent, the number of inferences that produced it, and the named results
 * it rests on. Two claims that are both true are not the same claim if one reaches sixteen axioms
 * and the other reaches none.
 *
 * **One of the four is refused, and that is the point of including it.** A demonstration made only
 * of successes teaches that the tool answers, which is the one thing about it that is not true:
 * `Ring` and `Linarith` decide small fragments and say so by failing on the rest. A reader who has
 * seen only proofs will read the next refusal as a defect.
 *
 * The refused one is **true**: every non-negative real has a square root, and what proves it is
 * `COMPLETENESS`, which no tactic reaches. A false claim in that slot would have demonstrated
 * something else and would have read as the same thing, which is the way this page could mislead.
 *
 * Names are written as the printer prints them, `x` and not `n`, because a page that answers about
 * `x` a question asked about `n` is `docs/adr/0002` being paid for in a demonstration. Here there
 * is no reason to pay it.
 */
object WhatAClaimCosts {

  /** Claims chosen so that the four reach visibly different parts of the trusted base. */
  private val claims: Vector[(String, String)] = Vector(
    "a ring identity over the reals" ->
      "!x:real. (x + 1) * (x + 1) = x * x + 2 * x + 1",
    "an order fact, which reaches the order axioms and not the field ones" ->
      "!x:real y:real. x < y ==> x + 1 < y + 1",
    "a claim about the naturals, whose type is defined rather than assumed" ->
      "!x:num. NUM_LE 0 x",
    "and one that is true and that the decision procedures still do not decide" ->
      "!x:real. 0 <= x ==> ?y:real. y * y = x"
  )

  def main(args: Array[String]): Unit = {
    val cost = Cost
      .construct(Chain.standard)
      .fold(error => throw new IllegalStateException(s"the standard chain does not build: ${error.message}"),
        identity)

    println("=" * 78)
    println("WHAT A CLAIM COSTS")
    println("=" * 78)

    claims.foreach { case (heading, text) =>
      println()
      println(heading)
      val page = for {
        report <- cost.of(text)
        rendered <- cost.render(report)
      } yield rendered
      println(page.fold(error => s"  not put to the surface at all: ${error.message}", identity))
    }
  }
}
