package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.logic.Rewrite
import garden.xeno.symbolum.theories.{Chain, Library, Matrix, Product}

/**
 * The calibration, which comes before trusting the scale and is most of what this file is for.
 *
 * A novelty score nobody has calibrated is a number that looks like evidence. So the assertions
 * here are put the other way round from the usual: instead of checking that the scale reports what
 * I expect, they check that it does not report the things that would prove it broken. If it called
 * `x * 1 = x` surprising, or a claim no procedure can even read the most promising thing on the
 * list, the ordering would be worse than no ordering.
 */
class NoveltySpec extends AnyFlatSpec with Matchers {

  private val novelty = Novelty.standard

  private def reading(text: String): Novelty.Reading =
    novelty.of(text).fold(error => fail(error.message), identity)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  /* ------------------------------------------------- the bottom of the scale */

  "An identity the ring normalisation settles" should "be immediate, which is to say not news" in {
    reading("!x:real. x * 1 = x").standing shouldBe Novelty.Standing.Immediate
    reading("!x:real. x + 0 = x").standing shouldBe Novelty.Standing.Immediate
    reading("!x:real y:real. (x + y) * (x + y) = x * x + 2 * (x * y) + y * y").standing shouldBe
      Novelty.Standing.Immediate
  }

  "A claim no procedure here can read" should "be at the bottom, and cost nothing to find out" in {
    // Nothing is spent: the address is asked first and answers without attempting anything.
    //
    // The example has now moved twice in one day, and both moves are the machinery improving rather
    // than the test being wrong.
    //
    // It began as `!p:bool. p ==> p`. The negation-free propositional fragment got an address, so
    // that goal became a theorem costing no axiom. The obvious replacement `!p:bool. p = p` is not
    // it either and the reason is instructive: it comes back `Known`, because rewriting with the
    // held equations turns one side into the other in nought steps, and reflexivity is a corollary
    // of everything. So it became `!p:bool q:bool. p = q`.
    //
    // That one is now `False`. The model computes truth values exactly, `p = q` fails at
    // `p = true, q = false`, and a point among exact values is a refutation rather than evidence
    // about a model: `Abduce.Gap.decisive` is the distinction and `Cost` acts on it. Being told
    // that a false claim is false, with the pair that shows it, is better than being told nobody
    // could read it.
    //
    // What is unreadable now is a claim no procedure addresses **and** no point refutes. True,
    // about the naturals, and outside every fragment: `Linarith` decides the reals and there is no
    // counterpart for `num`, so nothing here has anything to say and the sampler finds no
    // counterexample because there is none.
    //
    // It was `!x:num. NUM_LE x (NUM_ADD x x)` until 2026-09-14, and this is the FOURTH time this
    // example has been eroded by the system getting stronger rather than by anything here changing.
    // `Peano.NUM_LE_ADD` landed that day, so the claim became an instance of a held lemma and came
    // back `Known`. Worth reading beside the three erosions above it: each was a different
    // mechanism, and what they have in common is that a test naming a claim the system cannot reach
    // has a shelf life, because reaching further is the work.
    val unreadable = reading("!x:num. NUM_LE x (NUM_MUL x x)")

    unreadable.standing shouldBe Novelty.Standing.Unreadable
    unreadable.inferences shouldBe 0
  }

  "A claim decided false" should "end the question rather than open one" in {
    val broken = reading("!x:real. 0 < x ==> 1 < x")

    broken.standing shouldBe Novelty.Standing.False
    Novelty.Standing.weight(broken.standing) should be <
      Novelty.Standing.weight(Novelty.Standing.Earned)
  }

  /* ------------------------------------------------- the part that earns its keep */

  "A claim the cheapest procedure cannot settle" should "rank above one it can" in {
    // The whole idea, as an assertion. `1 < x /\ 1 < y ==> 1 < x * y` is `(x-1)(y-1) > 0` and then
    // linear: RING cannot see it, the products of the hypotheses reach it, and it is not a lemma
    // this library holds.
    //
    // The example used to be `0 < x /\ 0 < y ==> 0 < x * y`, and the lookup half of the novelty
    // question moved it: that one is `LT_MUL`, an AXIOM of the theory, so `Known` is the right
    // answer and calling it earned was my mistake. The test found it rather than the reading.
    val earned = reading("!x:real y:real. 1 < x /\\ 1 < y ==> 1 < x * y")
    val immediate = reading("!x:real. x * 1 = x")

    earned.standing shouldBe Novelty.Standing.Earned
    Novelty.Standing.weight(earned.standing) should be >
      Novelty.Standing.weight(immediate.standing)
  }

  "A conditional identity" should "be earned, since a price is more than the minimum" in {
    reading("!x:real y:real. (x * y) / y = x").standing shouldBe Novelty.Standing.Earned
  }

  /* ------------------------------------------------- derivable from what is held */

  "A claim that falls out of the lemmas already held" should "be a corollary, not a result" in {
    // The second half of "how much more than the minimum", and the half that separates a new result
    // from a restatement of one. `Series.AtSuccessor` is in the library, so a claim that is that
    // equation with its quantifiers stripped collapses under rewriting and is not news.
    val known = reading("!n:num. !f:num->real. Sum f (SUC n) = Sum f n + f n")

    known.standing shouldBe Novelty.Standing.Known
    Novelty.Standing.weight(known.standing) should be <
      Novelty.Standing.weight(Novelty.Standing.Earned)
  }

  it should "not be searched for with a rule that matches everything it has just built" in {
    // The population interrogated is every entry of `Library.of(Chain.standard)`, which is the
    // library `Novelty.standard` reads, and the question put to each is whether it yields a rule
    // at all. A statement whose left side is a bare pattern variable matches every subterm of its
    // type, including the ones its own right-hand side has just created, so one step produces a
    // larger term with more redexes than it started with.
    //
    // **Two sessions found this on the same day in two files and repaired it at two layers.** One
    // made `Rewrite.Rule.of` refuse the shape outright; the other filtered such rules out inside
    // `Novelty`. The refusal is the layer that holds, because it reaches every caller rather than
    // this one, so the filter went and this test changed from naming what was filtered to naming
    // what is refused. `follows` drops a refused equation at `Rule.of(...).toOption`, so no rule
    // with that shape can reach the rewriting from here by any route.
    //
    // `MAT2_SURJECTIVE` is `|- !m. m = MAT2 (MAT_E11 m) (MAT_E12 m) (MAT_E21 m) (MAT_E22 m)` and
    // `PAIR_SURJECTIVE` is the same statement about a pair. They are named rather than described,
    // because the assertion is worthless if the shape it guards against has left the library: this
    // fails when the examples go, which is when somebody should be reading it.
    val chain = Chain.standard
    val refused = Library
      .of(chain)
      .entries
      .filter(entry => Rewrite.Rule.of(chain.logic, entry.theorem).isLeft)
      .map(_.name)
      .distinct

    refused should contain(Matrix.Surjective)
    refused should contain(Product.Surjective)

    // And a claim carrying that shape still gets an answer. Before the refusal it did not: with
    // `MAT2_SURJECTIVE` reaching the rule set, one thread inside `Sweep` spent 540 seconds of
    // processor time in `Rewrite` on a single claim and had not returned, and a thread dump is
    // what found it. What is asserted is that there is an answer, which is a returned standing and
    // not a time: this machine has read the same suite at 150 seconds and at 28 minutes.
    //
    // Read through the chain's widest signature rather than through `novelty.reals`, which is
    // `Series` and has no `prod`: the scale's reader is narrower than its library, which is a
    // separate narrowness this test does not repair and only has to work around. A claim only
    // reaches such a rule if it has a subterm of that rule's type, so a real-valued claim would
    // exercise nothing.
    val claim = force(Chain.standard.matrix.proposition(
      "!m:prod(prod(real,real),prod(real,real)). " +
        "MAT_DET (MAT_MUL m m) = MAT_DET m * MAT_DET m"
    ))

    novelty.of(claim).map(_.standing) shouldBe Right(Novelty.Standing.Known)
  }

  it should "be unreachable when the caller supplied no library, rather than defaulted to false" in {
    // "We did not look" and "we looked and it is new" are the two things this repository is most
    // careful never to merge. Without a library the scale says less and says so.
    val blind = Novelty(novelty.cost, garden.xeno.symbolum.theories.Ring.standard)
    val same = blind
      .of("!n:num. !f:num->real. Sum f (SUC n) = Sum f n + f n")
      .fold(error => fail(error.message), identity)

    same.standing should not be Novelty.Standing.Known
  }

  "A claim the library already holds outright" should "be Known, not Open" in {
    // Measured while correcting the benchmark row of `docs/evaluation.md`, and it is the same shape
    // as the curried implication the entry point could not read: `!x. 0 <= x * x` is
    // `Order.SQUARE_NONNEG`, a lemma this library HOLDS, and the decision procedures do not reach
    // it as a goal. Asking for it got a refusal from a system that had it written down.
    //
    // It is not an equation, so no rule set could ever rewrite one side into the other: the
    // rewriting half of this question cannot see it at all, and the lookup half is what does.
    reading("!x:real. 0 <= x * x").standing shouldBe Novelty.Standing.Known
  }

  it should "match up to the lemma's own quantifiers, and no further" in {
    // `!y. 0 <= y * y` is the same statement under another name for the bound variable and is held;
    // `!x. 0 <= x * 2` is not an instance of it and must not be claimed as one.
    reading("!y:real. 0 <= y * y").standing shouldBe Novelty.Standing.Known
    reading("!x:real. 0 <= x * 2").standing should not be Novelty.Standing.Known
  }

  /* ------------------------------------------------- the ordering */

  "The ranking" should "put what a procedure cannot settle above what one settles at once" in {
    // `Open` above `Earned` deliberately: a claim that survived the screen and was NOT certified is
    // the one thing a decision procedure cannot settle and a person might. That is what
    // `Discovery`'s `NotProvableHere` bucket means, and the loop's whole argument.
    val readings = Vector(
      reading("!x:real. x * 1 = x"),
      reading("!x:real y:real. 1 < x /\\ 1 < y ==> 1 < x * y"),
      reading("!x:num. NUM_LE x (NUM_MUL x x)")
    )

    val ranked = novelty.rank(readings)

    ranked.head.standing shouldBe Novelty.Standing.Earned
    ranked.last.standing shouldBe Novelty.Standing.Unreadable
  }

  it should "break a tie by what the proof cost, not by the order it was handed" in {
    val cheap = reading("!x:real. x * 1 = x")
    val dear = reading("!x:real y:real. (x + y) * (x + y) = x * x + 2 * (x * y) + y * y")

    cheap.standing shouldBe dear.standing
    dear.inferences should be > cheap.inferences
    novelty.rank(Vector(cheap, dear)).head.inferences shouldBe dear.inferences
  }

  /* --------------------------------------- the signal that was measured and not built */

  "The library" should "be too interconnected for an unused lemma to be a signal, which is why one is missing" in {
    // The third component the card asked for and called the strongest: whether a proof needed a
    // lemma no previous theorem had touched. It is not in the scale, and this is the measurement
    // that decided that rather than a paragraph saying it seemed unlikely.
    //
    // The shape is asserted and the counts are not, because the counts move every time somebody
    // proves a lemma and the shape is what the conclusion rests on. Two facts kill the signal
    // together: a proof here rests on a **great many** held lemmas, and the ones it rests on are
    // the common infrastructure that nearly every other proof rests on too. Either alone would
    // leave it usable.
    //
    // Measured on 2026-09-11: of 104 named lemmas, 30 were rested on by no other held theorem and
    // 59 by two or more; `NUM_REP_0` by 57 of them. Put to the 37 certified proposals `Propose`
    // makes, the signal fired once, on a proposal resting on the lemma it was made from.
    val chain = garden.xeno.symbolum.theories.Chain.standard
    val library = garden.xeno.symbolum.theories.Library.of(chain)

    val ordinary = force(novelty.cost.prove("!x:real y:real. 0 < x /\\ 0 < y ==> 0 < x + y"))
    val rested = library.restingOn(ordinary).map(_.name).distinct

    withClue(s"an ordinary proof rests on ${rested.size} held lemmas: ") {
      rested.size should be >= 8
    }

    // And they are the shared ones. Asserted through the most-rested-on lemma of the library rather
    // than by name, so that this survives the naturals being rebuilt on something else.
    //
    // The inverse relation is built in ONE pass over the entries, and the shape of that loop is the
    // whole cost of this test. `restingOn` walks a proof's entire DAG and hashes the conclusion at
    // every node, and a term's hash is not cached, so one call over a lemma of tens of thousands of
    // inferences is not cheap; asking it once per (name, entry) pair repeats the same walk
    // `rested.size` times over. Both forms measured in one process on 2026-09-13, over 278 entries
    // with `rested` holding 13 names: **611.32 s written the repeated way, 43.60 s in one pass**,
    // and the same 13 shared names out of both. The factor is `rested.size` and nothing else.
    //
    // What that repetition costs is **contention**, and the first reading of it was wrong. Written
    // the repeated way this test was measured at 41 seconds and at 11 minutes 45 on 2026-09-13, and
    // the obvious explanation, that the library had grown from 260 entries to 278 that day, is
    // refused by the log: at a fixed 277 it measured 1 minute 03 at 13:16 and 9 minutes 59 at
    // 15:32. The library is not what moved. Three sbt runs and several sessions sharing one machine
    // is, and a loop that repeats the most expensive call in the suite multiplies whatever share of
    // processor it is given. That is the argument for the single pass: not that it is faster on an
    // idle machine, but that it stops this test amplifying a busy one.
    //
    // The relation is asserted non-empty before it is used, because a one-pass construction is the
    // shape that can silently find nothing: a relation built with the wrong side as its key, or
    // over an empty library, would make `shared` empty. That case is already red rather than green
    // here, since `rested.size` is at least 8 above and no set of size zero is larger than four,
    // but the guard is written down instead of being left as arithmetic a reader has to redo.
    val restedOnBy = library.entries
      .flatMap { entry =>
        library.restingOn(entry.theorem).map(_.name).distinct.map(held => (held, entry.name))
      }
      .groupMap(_._1)(_._2)

    withClue(s"the inverse relation holds ${restedOnBy.size} names: ") {
      restedOnBy.keySet should contain allElementsOf rested
    }

    val shared =
      rested.filter(name => restedOnBy.getOrElse(name, Vector.empty).count(_ != name) > 1)

    withClue(s"of those, ${shared.size} are rested on by more than one other held theorem: ") {
      shared.size should be > rested.size / 2
    }
  }

  /* ------------------------------------------------- the honest limit */

  "The scale" should "keep the report it read, rather than replacing it with a number" in {
    // A caller that wants to know what a claim charges, or where it fails, reads the five answers
    // `Cost` gathered. This file ranks; it does not summarise away the thing that was measured.
    val priced = reading("!x:real y:real. (x * y) / y = x")

    priced.report.outcome shouldBe Cost.Outcome.Conditional
    priced.report.conditions should not be empty
    priced.axioms should be > 0
  }
}
