package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What `max`, `min` and `abs` are, and what having them costs.
 *
 * Two claims are being probed here and only the second is about the mathematics. The first is that
 * the choice axiom is the price of naming a greatest of two reals at all, and it is asserted the
 * only way it cannot go stale: by counting the axioms of the theory these facts are stated over
 * against the axioms of the one they are not, and by putting an order built over the axiom-free
 * logic to `Magnitude.construct` and reading the refusal.
 *
 * The second is that the characterisations are complete rather than merely true. `x <= max x y` and
 * `y <= max x y` are satisfied by anything large enough, so the assertions that matter are the two
 * that pin the term: that it is one of the pair, and that it is the least of the upper bounds.
 * `max x x = x` is derived here from those rather than asserted, because a derivation is what shows
 * the facts compose.
 */
class MagnitudeSpec extends AnyFlatSpec with Matchers {

  private def force[E <: LogicError, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got ${error.message}"), identity)

  private val magnitude = Magnitude.standard
  private val order = magnitude.order
  private val reals = magnitude.reals
  private val rules = magnitude.logic.rules

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val x: FVar = Term.variable("x", real)
  private val y: FVar = Term.variable("y", real)

  "The greater of two reals" should "be one of them, and above both" in {
    // The three facts that characterise it, printed rather than compared as terms: what a reader
    // checks against a textbook is the statement, and a bound stated about the wrong argument is
    // invisible in a comparison against a term this file built the same way.
    magnitude.show(force(magnitude.maxCases).conclusion) shouldBe
      "!x:real. !y:real. max x y = x \\/ max x y = y"
    magnitude.show(force(magnitude.maxAboveLeft).conclusion) shouldBe
      "!x:real. !y:real. x <= max x y"
    magnitude.show(force(magnitude.maxAboveRight).conclusion) shouldBe
      "!x:real. !y:real. y <= max x y"
    magnitude.show(force(magnitude.maxLeast).conclusion) shouldBe
      "!x:real. !y:real. !z:real. x <= z ==> y <= z ==> max x y <= z"
  }

  it should "be pinned by those facts and not merely bounded by them" in {
    // The invariant the two bounding facts do not carry on their own: they hold of anything large
    // enough, so what says `max x y` is *the* greater of the two is `MAX_CASES` together with
    // `MAX_LEAST`. This derives `max x x = x` from them, which no single one of them gives: the
    // upper bound comes from `MAX_LEAST` at `z := x`, the lower from `MAX_ABOVE_LEFT`, and the two
    // meet by antisymmetry. A `max` that returned something too large would satisfy both bounding
    // facts and fail this.
    val same = Kernel.refl(x)

    val theorem = force(
      for {
        reflexive <- order.leOfEq.flatMap(rules.specAll(_, List(x, x))).flatMap(rules.mp(_, same))
        least <- magnitude.maxLeast
        atSame <- rules
          .specAll(least, List(x, x, x))
          .flatMap(rules.mp(_, reflexive))
          .flatMap(rules.mp(_, reflexive))
        above <- magnitude.maxAboveLeft.flatMap(rules.specAll(_, List(x, x)))
        antisymmetric <- order.antisymmetric
        equal <- rules
          .specAll(antisymmetric, List(force(magnitude.term("max (x:real) x")), x))
          .flatMap(rules.mp(_, atSame))
          .flatMap(rules.mp(_, above))
      } yield equal
    )

    theorem.hypotheses shouldBe empty
    magnitude.show(theorem.conclusion) shouldBe "max x x = x"
  }

  "The lesser of two reals" should "be one of them, and below both" in {
    magnitude.show(force(magnitude.minCases).conclusion) shouldBe
      "!x:real. !y:real. min x y = x \\/ min x y = y"
    magnitude.show(force(magnitude.minBelowLeft).conclusion) shouldBe
      "!x:real. !y:real. min x y <= x"
    magnitude.show(force(magnitude.minBelowRight).conclusion) shouldBe
      "!x:real. !y:real. min x y <= y"
  }

  it should "be the other one of the pair, which is what defining it by subtraction buys" in {
    // The invariant behind the definition `min x y = x + y - max x y`: the two of them are the same
    // pair of numbers in the other order, so their sum does not depend on which is which. If this
    // held and the facts above did not, the definition would be an unrelated term that happened to
    // be below both; if the facts held and this did not, `min` and `max` would not be a pair.
    magnitude.show(force(magnitude.minPlusMax).conclusion) shouldBe
      "!x:real. !y:real. min x y + max x y = x + y"
  }

  it should "be a definition rather than a second appeal to choice" in {
    // `min` and `abs` are abbreviations for combinations of `max`, which is the claim being probed:
    // a second `select` for either would be a second existence proof to keep in agreement with the
    // first. What says so is that each of them unfolds into a term whose only unfamiliar name is
    // `max`, and the definitions are read back here rather than described.
    magnitude.definitions.keys.toVector.sorted shouldBe
      Vector(Magnitude.AbsName, Magnitude.MaxName, Magnitude.MinName, Magnitude.SignName).sorted

    magnitude.show(force(magnitude.definition(Magnitude.MinName)).conclusion) shouldBe
      "min = (\\x:real. \\y:real. x + y - max x y)"
    magnitude.show(force(magnitude.definition(Magnitude.AbsName)).conclusion) shouldBe
      "abs = (\\x:real. max x (-x))"
  }

  "The distance from zero" should "be one of the two reflections, and above both" in {
    magnitude.show(force(magnitude.absCases).conclusion) shouldBe
      "!x:real. abs x = x \\/ abs x = -x"
    magnitude.show(force(magnitude.absAbove).conclusion) shouldBe "!x:real. x <= abs x"
    magnitude.show(force(magnitude.absAboveNegation).conclusion) shouldBe "!x:real. -x <= abs x"
    magnitude.show(force(magnitude.absNonNegative).conclusion) shouldBe "!x:real. 0 <= abs x"
    magnitude.show(force(magnitude.absZero).conclusion) shouldBe "!x:real. abs x = 0 ==> x = 0"
  }

  it should "obey the triangle inequality" in {
    magnitude.show(force(magnitude.triangle).conclusion) shouldBe
      "!x:real. !y:real. abs (x + y) <= abs x + abs y"
  }

  it should "give the bound a limit argument actually asks for" in {
    // The triangle inequality used end to end rather than only stated: `abs x <= abs y + abs (x-y)`
    // is the form every estimate takes, and it is this fact at `y` and `x - y` with one ring
    // identity to see that the two add back to `x`. The invariant is that the inequality survives
    // an instantiation at a compound term, which is where a lemma stated about the wrong side of the
    // sum would show up.
    val theorem = force(
      for {
        triangle <- magnitude.triangle
        difference <- magnitude.term("x:real - y:real")
        instance <- rules.specAll(triangle, List(y, difference))
        // The rewrite has to reach inside `abs`, so it is the rewriter at depth rather than
        // congruence on the two sides of the inequality: what has to change is an argument.
        restores <- order.ring.prove("y:real + (x:real - y) = x")
        rule <- Rewrite.Rule.all(magnitude.logic, Vector(restores))
        result <- Rewrite.inTheorem(rule, instance)
      } yield result
    )

    theorem.hypotheses shouldBe empty
    magnitude.show(theorem.conclusion) shouldBe "abs x <= abs y + abs (x - y)"
  }

  it should "be the argument itself where the sign says so, which is what removes it from a term" in {
    // The two facts this file's own opening called "not reached rather than out of reach" until
    // 2026-09-20. What they are for is not the statement: it is that with the sign known, `abs`
    // stops being an opaque application and becomes a term the ring can normalise, which is the
    // only reason `ABS_MUL` below is four ring identities instead of four arguments about `abs`.
    magnitude.show(force(magnitude.fact(Magnitude.OfNonNegative)).conclusion) shouldBe
      "!x:real. 0 <= x ==> abs x = x"
    magnitude.show(force(magnitude.fact(Magnitude.OfNonPositive)).conclusion) shouldBe
      "!x:real. x <= 0 ==> abs x = -x"
  }

  it should "multiply, which is the half of the triangle inequality's question that was missing" in {
    magnitude.show(force(magnitude.fact(Magnitude.Multiplicative)).conclusion) shouldBe
      "!x:real. !y:real. abs (x * y) = abs x * abs y"
  }

  it should "be spent on a product with a sign, which is where a stated identity would hide a swap" in {
    // `ABS_MUL` at a negative factor, end to end: the statement is symmetric in a way that a
    // derivation with the two signs crossed would satisfy just as well, so what says the four
    // cases landed where they were meant to is an instance where the two sides are **different
    // terms** before the ring sees them. At `x := -y` the left is `abs (-y * y)` and the right is
    // `abs (-y) * abs y`, and the second fact above turns the first factor into `y` only because
    // the sign is known.
    val theorem = force(
      for {
        lemma <- magnitude.fact(Magnitude.Multiplicative)
        negated <- magnitude.term("-y:real")
        instance <- rules.specAll(lemma, List(negated, y))
      } yield instance
    )

    theorem.hypotheses shouldBe empty
    magnitude.show(theorem.conclusion) shouldBe "abs (-y * y) = abs (-y) * abs y"
  }

  it should "turn a vanishing distance into an equality" in {
    // `ABS_ZERO` at a difference, which is the only shape it is ever used at: two quantities whose
    // distance is nothing are the same quantity. The hypothesis is carried rather than discharged,
    // because a caller who has it has it as an assumption.
    val theorem = force(
      for {
        lemma <- magnitude.absZero
        difference <- magnitude.term("x:real - y:real")
        instance <- rules.spec(difference, lemma)
      } yield instance
    )

    magnitude.show(theorem.conclusion) shouldBe "abs (x - y) = 0 ==> x - y = 0"
  }

  "The sign of a real" should "be decided by where the real sits, and stated as three implications" in {
    magnitude.show(force(magnitude.signNegative).conclusion) shouldBe
      "!x:real. x < 0 ==> sgn x = -1"
    magnitude.show(force(magnitude.signZero).conclusion) shouldBe "!x:real. x = 0 ==> sgn x = 0"
    magnitude.show(force(magnitude.signPositive).conclusion) shouldBe
      "!x:real. 0 < x ==> sgn x = 1"
  }

  it should "cost a second existence proof and no second axiom" in {
    // The distinction the file turns on, and the one easiest to get wrong in a report: `sgn` is a
    // three-way split, so it cannot be assembled out of `max` and needs its own appeal to choice.
    // A second *use* of an axiom already believed adds nothing to what has to be believed, so the
    // theory here holds the axioms of `Real.Axioms` and `Classical.Axioms` and no more, as it did
    // before `sgn` existed. What is asserted is that the count did not move and that `sgn` is
    // nevertheless a constant of its own.
    magnitude.theory.axioms should have length (Real.Axioms.length + Classical.Axioms.length)
    magnitude.definitions.keySet should contain(Magnitude.SignName)
  }

  it should "answer at a numeral, which is the only place the value is a fact rather than a case" in {
    // Used end to end: `0 < 2` is a theorem of the numerals, so `sgn 2 = 1` follows with nothing
    // assumed. This is the shape a caller has, and it is why the three facts being implications
    // costs nothing in practice: the hypothesis is discharged by `Order.positive`.
    val theorem = force(
      for {
        lemma <- magnitude.signPositive
        two <- magnitude.term("2")
        instance <- rules.spec(two, lemma)
        positive <- order.positive(2)
        result <- rules.mp(instance, positive)
      } yield result
    )

    theorem.hypotheses shouldBe empty
    magnitude.show(theorem.conclusion) shouldBe "sgn 2 = 1"
  }

  it should "not answer where nothing decides it, which is now the development and not the language" in {
    // The limit, stated rather than left to be discovered: there is no unconditional theorem here
    // saying what `sgn x` is, because `sgn x` is one term and which numeral it equals depends on
    // `x`. Nothing in the development proves the three values at once, and `Linarith` cannot either:
    // it treats `sgn x` as an atom it knows nothing about.
    //
    // Until 2026-09-12 this was a limit of the logic, which had no case expression to put on the
    // right of such an equation. `Classical.COND` is one and this file has not been rewritten
    // around it, so what is measured here is a development that was not restated rather than a
    // language that cannot say it.
    val unconditional = force(magnitude.proposition("!x:real. sgn x = 1 \\/ sgn x = 0"))

    Linarith.standard.prove(unconditional).isLeft shouldBe true
    magnitude.facts.values.exists(_.conclusion == unconditional) shouldBe false
  }

  "Every fact here" should "have nothing assumed" in {
    magnitude.facts.foreach { case (name, theorem) =>
      withClue(s"$name: ") { theorem.hypotheses shouldBe empty }
    }
  }

  "The price of having a greatest of two reals at all" should "be choice, with eta beside it" in {
    // The claim the whole file exists to make, asserted by counting rather than by prose. The
    // numbers are the code's: `Real.Axioms` plus `Classical.Axioms` against `Real.Axioms` alone,
    // both spelled in the assertion below rather than written here. A `max` that had cost nothing
    // would make these equal and a `max` that had cost more would make the first larger.
    magnitude.theory.axioms should have length (Real.Axioms.length + Classical.Axioms.length)
    Real.standard.theory.axioms should have length Real.Axioms.length

    // And the choice axiom itself is among what the classical logic adds, which is the one naming a
    // greatest of two needs; eta arrives beside it with that logic.
    val choice = force(Classical.standard.axiom(Classical.Choice)).conclusion
    magnitude.theory.axioms should contain(choice)
  }

  it should "be refused rather than worked around when the order has no choice in it" in {
    // The other half of the same claim, and the one that would catch a future route that quietly
    // named `max` without choice: `Order.standard` is built over `Real.standard`, which sits over
    // the axiom-free logic on purpose, so its signature has no `select`. Asked for the magnitude
    // constants over that order, this refuses and says which operator is missing. It does not fall
    // back to a definition of its own, because there is none over **that** signature: `COND` is
    // defined in `Classical`, which `Order.standard` does not sit over, so it is as absent there as
    // `select` is, and `p \/ ~p` is not derivable there either. A definition by cases has nothing
    // to split on and no case expression to split into.
    val refused = Magnitude.construct(Classical.standard, Order.standard)

    refused.isLeft shouldBe true
    refused.left.map(_.message) match {
      case Left(message) =>
        message should include(Classical.Select)
        message should include(Magnitude.MaxName)
      case Right(built) => fail(s"expected a refusal, got a development with ${built.facts.size} facts")
    }
  }

  "The same facts over a chain that also carries the naturals" should "be the caller's signature and not a second one" in {
    // Why the order is a parameter rather than something this file builds: a development that has
    // already assembled `num` and `real` in one signature gets these facts over *that* theory. Two
    // chains from one root could not state a theorem mentioning both, which is the failure
    // `Chain`'s own note describes.
    //
    // The axiom count is the code's again, and it is the third of the three configurations: the
    // reals' alone, then the classical logic's added, then `Natural`'s infinity added as well.
    val chain = Chain.standard
    val overChain = force(Magnitude.construct(chain.classical, chain.order))

    overChain.theory.axioms should have length
      (Real.Axioms.length + Classical.Axioms.length + Natural.Axioms.length)

    // The facts are the same statements, not merely the same names, and they are stated in a theory
    // that can also read a claim about `num`.
    overChain.facts.keys.toVector.sorted shouldBe magnitude.facts.keys.toVector.sorted
    overChain.show(force(overChain.triangle).conclusion) shouldBe
      magnitude.show(force(magnitude.triangle).conclusion)
    Parser.proposition(overChain.theory, overChain.notation, "!n:num. ZERO <= abs (x:real)").isRight shouldBe false
    Parser.term(overChain.theory, overChain.notation, "abs (x:real)").isRight shouldBe true
  }

  "A fact this development does not have" should "be refused by name" in {
    magnitude.fact("ABS_MULTIPLIES").left.map(_.getClass) shouldBe Left(classOf[MissingDefinition])
    magnitude.definition("floor").left.map(_.getClass) shouldBe Left(classOf[MissingDefinition])
  }

  "Neither floor nor ceiling" should "be here, and the reason is the integers and not the budget" in {
    // Recorded as a test rather than only as a comment, because the absence is a decision. The
    // characterising fact for `floor x` is that it is an *integer* below `x` with `x` below
    // `floor x + 1`, and this signature has no integers in it: `Natural` builds `num` and nothing
    // embeds it in the reals, so the statement cannot be written down at all. A definition by
    // choice could be written today, over a predicate nothing can be proved to satisfy, and it
    // would look like progress while every theorem about it stayed out of reach.
    //
    // What is asserted is the premise of that reasoning: there is no function from `num` to `real`
    // in this signature, so `floor x <= x` with `floor x` an integer has no formalisation here.
    val chain = Chain.standard
    val embedding = Parser.term(chain.reals.theory, chain.reals.notation, "of_num (n:num)")

    embedding.isRight shouldBe false
    magnitude.definitions.keys.toVector should not contain "floor"
    magnitude.definitions.keys.toVector should not contain "ceiling"
  }

  "The identity joining the sign to the distance" should "not be here, and be recorded as absent" in {
    // `sgn x * abs x = x` is the fact that makes `sgn` worth having and it is not derived. It wants
    // `abs x = x` under `0 <= x` and `abs x = -x` under `x <= 0`, two more case analyses on
    // `ABS_CASES` against antisymmetry, and neither is in this development. Written down as a test
    // rather than as a comment so that the gap is read off the code: a later session that derives it
    // deletes this and adds the fact, and a document claiming it is here fails.
    val statement = force(magnitude.proposition("!x:real. sgn x * abs x = x"))

    magnitude.facts.values.exists(_.conclusion == statement) shouldBe false
    Linarith.standard.prove(statement).isLeft shouldBe true
  }
}
