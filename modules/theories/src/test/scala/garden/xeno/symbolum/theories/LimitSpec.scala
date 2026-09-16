package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The limit development says what it says, costs what it costs, and refuses what it should refuse.
 *
 * Three questions, and the third is the one that is easy to leave out. A development whose
 * predicate held of everything would pass every assertion of the first two kinds: each fact would
 * still be provable, each statement would still read back, and the axiom count would be unchanged.
 * So [[refuses]] below derives a **non**-convergence, which is the assertion that `converges`
 * discriminates, and it is the shape `LanguageSpec` uses for `NUM_TERM` and for the same reason.
 *
 * What it does not check is that the epsilon-N definition is the **right** definition of a limit.
 * Nothing here can: that is a translation from mathematics into this notation and what checks it is
 * a reader, which is what `docs/reading-register.md` is for and why `Limit.ConvergesBody` is
 * written as a sentence rather than assembled.
 */
class LimitSpec extends AnyFlatSpec with Matchers {

  private val chain: Chain = Chain.standard
  private val limit: Limit = chain.limit

  private def force[A](result: Either[LogicError, A]): A =
    result.fold(error => fail(error.message), identity)

  private def proposition(text: String): Term =
    force(Parser.proposition(limit.theory, limit.notation, text))

  "Every fact of the limit development" should "prove the statement it is published as" in {
    Limit.Statements.foreach { case (name, text) =>
      val proved = force(limit.fact(name))
      withClue(s"$name: ") { proved.conclusion shouldBe proposition(text) }
      proved.hypotheses shouldBe empty
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    limit.facts.keySet shouldBe Limit.Statements.map(_._1).toSet
  }

  "The development" should "declare exactly the two constants it is about" in {
    val before = chain.provability.theory.constants.keySet
    (limit.theory.constants.keySet -- before) shouldBe Set(Limit.Converges, Limit.Value)
  }

  it should "add no axiom at all, which is the whole of what a definition costs" in {
    limit.theory.axioms.length shouldBe chain.provability.theory.axioms.length
  }

  /**
   * The costs, pinned as equalities rather than as ceilings.
   *
   * A ceiling is what a reader assumes is being asserted and is not the same claim: it passes when
   * a derivation quietly stops spending something as much as when it starts. `CodingSpec` makes
   * this argument first and this is the same measurement one link up.
   *
   * The two numbers worth reading are the ends of the range. `CONVERGES_EVENTUALLY` costs the
   * naturals' two, choice and infinity, because it moves a proposition about a sequence around and
   * touches no arithmetic at all. `CONVERGES_UNIQUE` costs seventeen, and the two beyond the field
   * and the order are `MUL_INVERSE` and `ONE_NOT_ZERO`: they are what halving the tolerance spends,
   * which is the one step in that proof that leaves the linear fragment.
   */
  "What each fact rests on" should "be what it was measured to rest on" in {
    def axioms(name: String): Int = Derivation.axiomsOf(force(limit.fact(name))).size

    axioms(Limit.Eventually) shouldBe 2
    axioms(Limit.BelowEveryPositive) shouldBe 11
    axioms(Limit.Constant) shouldBe 13
    axioms(Limit.Unique) shouldBe 17
    axioms(Limit.ValueOfConverges) shouldBe 17

    // The monotone convergence theorem and the order fact under it. The second costs fewer than
    // the convergence facts above and the difference is the whole of what it is: no tolerance is
    // halved in it, so neither `MUL_INVERSE` nor `ONE_NOT_ZERO` appears.
    axioms(Limit.MonotoneBelow) shouldBe 11
    axioms(Limit.MonotoneConverges) shouldBe 15
  }

  it should "spend the choice axiom on the value and not on the epsilon principle" in {
    val choice = force(chain.classical.axiom(Classical.Choice)).conclusion

    Derivation.axiomsOf(force(limit.fact(Limit.ValueOfConverges))) should contain(choice)

    // And not here, which is the claim the file's own docstring makes about the route it takes:
    // the epsilon principle is a disjunction elimination over `LE_CASES` rather than a
    // contradiction, so nothing classical is reached.
    Derivation.axiomsOf(force(limit.fact(Limit.BelowEveryPositive))) should not contain choice
  }

  /**
   * The theorem spends `COMPLETENESS`, which is the claim its own docstring makes.
   *
   * Asserted by name rather than left to the count, because the count moving would not say which
   * axiom arrived and this is the one the theorem is about: an ordered field that is not complete
   * has bounded increasing sequences that converge to nothing, so a derivation of this that did
   * **not** reach the sixteenth axiom would be a derivation of something else.
   */
  "The monotone convergence theorem" should "be where the sixteenth axiom is spent" in {
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion
    val spent = Derivation.axiomsOf(force(limit.monotoneConverges))

    spent should contain(completeness)

    // And the order fact under it does not, which says the induction is about the order alone.
    Derivation.axiomsOf(force(limit.monotoneBelow)) should not contain completeness
  }

  /**
   * It applies to a sequence somebody can name, which is what says it is not vacuous.
   *
   * A theorem whose hypotheses nothing satisfies is provable and useless, and this one takes two.
   * The constant sequence satisfies both, so the theorem hands back a limit for it, and
   * `CONVERGES_UNIQUE` says that limit is the constant itself. The demonstration is worth more
   * than the statement: it is the first time in this repository that a limit is **obtained**
   * rather than assumed.
   */
  it should "apply to a sequence whose hypotheses can be discharged" in {
    val rules = limit.logic.rules
    val real = TyApp(Real.TypeName, Nil)
    val c = Term.variable("c", real)
    val n = Term.variable("n", TyApp(Natural.TypeName, Nil))

    val constant = force(
      limit.term("\\n:num. c:real", Type.fun(TyApp(Natural.TypeName, Nil), real)))
    val specialised = force(rules.spec(constant, force(limit.monotoneConverges)))
    val opened = force(
      Conv
        .betaNormalise(specialised.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, specialised))))

    // Both hypotheses, discharged: the constant sequence does not decrease, and it is its own
    // bound.
    val reflexive = force(
      rules
        .specAll(force(chain.order.leOfEq), List(c, c))
        .flatMap(rules.mp(_, Kernel.refl(c))))
    val everywhere = force(rules.gen(n, reflexive))

    val boundedStatement = proposition("?b:real. !n:num. c:real <= b")
    val boundedPredicate = force(
      limit.logic
        .destExistsPredicate(boundedStatement)
        .toRight(MissingDefinition("an existential")))
    val bounded = force(rules.existsIntro(boundedPredicate, c, everywhere))

    val obtained = force(rules.mp(opened, everywhere).flatMap(rules.mp(_, bounded)))
    obtained.conclusion shouldBe proposition("?l:real. converges (\\n:num. c:real) l")
    obtained.hypotheses shouldBe empty
  }

  "The definition" should "unfold to the epsilon-N statement a reader checks" in {
    val sequence =
      Term.variable("s", Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Real.TypeName, Nil)))
    val value = Term.variable("l", TyApp(Real.TypeName, Nil))
    val unfolded =
      force(Conv.unfold(force(limit.definition(Limit.Converges)), List(sequence, value)))
    val body = Term.destEq(unfolded.conclusion) match {
      case Some((_, right)) => right
      case None => fail(s"not an equation: ${limit.show(unfolded.conclusion)}")
    }

    // Against the parsed sentence rather than against a printed string: what is being checked is
    // the statement and not the printer's choice of bound names, and the two differ in nothing a
    // reader of this file should have to know about.
    body shouldBe proposition(
      "!e:real. 0 < e ==> ?N:num. !n:num. NUM_LE N n ==> abs ((s:num -> real) n - (l:real)) < e")
  }

  /**
   * `converges` refuses, which is what says it is a predicate rather than a true one.
   *
   * The constant sequence converges to its own value and to nothing else, and the second half is
   * the one worth deriving: it comes straight out of [[Limit.Unique]], so what this really asserts
   * is that uniqueness is not vacuous. A `converges` that held of every pair would make every fact
   * in this file provable and this one false.
   */
  "A constant sequence" should "converge to its value and refuse every other" in {
    val rules = limit.logic.rules
    val c = Term.variable("c", TyApp(Real.TypeName, Nil))
    val d = Term.variable("d", TyApp(Real.TypeName, Nil))

    val converges = force(rules.spec(c, force(limit.constantSequence)))
    limit.show(converges.conclusion) shouldBe "converges (\\x:num. c) c"

    // At the other value: assume it converges there too, and uniqueness closes it.
    val other = proposition("converges (\\n:num. c:real) (d:real)")
    val assumed = force(LogicError.lift(Kernel.assume(other)))
    val sequence = converges.conclusion match {
      case App(App(_, sequence), _) => sequence
      case other => fail(s"not a convergence: ${limit.show(other)}")
    }
    val equal = force(
      rules
        .specAll(force(limit.unique), List(sequence, c, d))
        .flatMap(rules.mp(_, converges))
        .flatMap(rules.mp(_, assumed))
    )
    limit.show(equal.conclusion) shouldBe "c = d"

    val refusal = force(
      limit.logic
        .mkNot(proposition("c:real = d:real"))
        .flatMap(negation => LogicError.lift(Kernel.assume(negation)))
        .flatMap(assumedDifferent => rules.notElim(assumedDifferent, equal))
        .flatMap(clash => rules.notIntro(other, clash))
    )
    limit.show(refusal.conclusion) shouldBe "~(converges (\\x:num. c) d)"
    refusal.hypotheses.map(limit.show).toList shouldBe List("~(c = d)")
  }

  "The value of a convergent sequence" should "be what it converges to" in {
    val rules = limit.logic.rules
    val c = Term.variable("c", TyApp(Real.TypeName, Nil))
    val converges = force(rules.spec(c, force(limit.constantSequence)))
    val sequence = converges.conclusion match {
      case App(App(_, sequence), _) => sequence
      case other => fail(s"not a convergence: ${limit.show(other)}")
    }

    val value = force(
      rules
        .specAll(force(limit.valueOfConverges), List(sequence, c))
        .flatMap(rules.mp(_, converges))
    )
    limit.show(value.conclusion) shouldBe "lim (\\x:num. c) = c"
  }

  /**
   * The additive algebra of limits, which is the half of it that needs no case split.
   *
   * Two assertions and they answer different questions. The first is that the sum fact costs
   * **exactly** what `CONVERGES_UNIQUE` costs, which is not a coincidence and is the reason to
   * write it as an equality between two measurements rather than as a number: both halve a
   * tolerance, both reach `abs`, and both put two indices together, so anything that moved one and
   * not the other would mean one of those three stopped happening. The second is that the negation
   * costs **strictly less**, and by name rather than by count: what it does not spend is
   * `MUL_INVERSE` and `ONE_NOT_ZERO`, which are what dividing by two spends, and it does not spend
   * them because it divides by nothing.
   *
   * Written as predictions before the suite was run, which is the discipline this file's figures
   * are under: a number copied out of a run is a transcription and not a check.
   */
  "The algebra of limits" should "cost the halving where it halves and not where it does not" in {
    def axioms(name: String): Int = Derivation.axiomsOf(force(limit.fact(name))).size

    axioms(Limit.Added) shouldBe axioms(Limit.Unique)

    val inverse = force(chain.reals.axiom("MUL_INVERSE")).conclusion
    val nonTrivial = force(chain.reals.axiom("ONE_NOT_ZERO")).conclusion

    Derivation.axiomsOf(force(limit.added)) should contain(inverse)
    Derivation.axiomsOf(force(limit.added)) should contain(nonTrivial)

    Derivation.axiomsOf(force(limit.negated)) should not contain inverse
    Derivation.axiomsOf(force(limit.negated)) should not contain nonTrivial
  }

  /**
   * Neither reaches `COMPLETENESS`, and that is the assertion this pair exists to survive.
   *
   * The algebra of limits is arithmetic of an ordered field: a sum of two sequences that each get
   * close gets close, and nothing about a supremum enters. A derivation of either of these that
   * went through `MONOTONE_CONVERGES` would reach the sixteenth axiom, would still prove the
   * statement, and would be a proof of the same sentence for a reason that is not the reason.
   * `LimitSpec` asserts the positive case for the monotone theorem three assertions above; this is
   * the same measurement pointed at where the axiom must **not** appear, which is the half that
   * catches a route changing under a refactoring nobody meant to be about the foundation.
   */
  it should "not reach the sixteenth axiom, because no supremum is involved" in {
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion

    Derivation.axiomsOf(force(limit.added)) should not contain completeness
    Derivation.axiomsOf(force(limit.negated)) should not contain completeness
  }

  /**
   * The two compose, and what comes out is a sequence that is identically zero.
   *
   * The assertion that matters here is not that the composite is provable, it is that the two
   * facts **fit together**: `CONVERGES_ADD` wants two convergent sequences and `CONVERGES_NEG`
   * produces one, so putting them in series is the first thing in this development that chains one
   * limit theorem into another. Before them there was nothing to chain, since every fact `Limit`
   * held took a sequence and said something about it alone.
   *
   * It is also the shape the Cauchy product will need and the reason this landed first: that
   * argument ends by adding and subtracting a quantity, which is these two facts and no others.
   */
  it should "compose, so that a sequence and its negation converge together" in {
    val rules = limit.logic.rules
    val real = TyApp(Real.TypeName, Nil)
    val s = Term.variable("s", Type.fun(TyApp(Natural.TypeName, Nil), real))
    val a = Term.variable("a", real)

    val assumed = force(LogicError.lift(Kernel.assume(proposition("converges (s:num -> real) (a:real)"))))

    // The negation of the sequence, from the fact under test.
    val negatedSequence = force(
      rules.specAll(force(limit.negated), List(s, a)).flatMap(rules.mp(_, assumed)))

    // And the two added, which is the second fact taking the first one's output as an input.
    val together = force(
      rules
        .specAll(
          force(limit.added),
          List(s, force(limit.term("\\n:num. -((s:num -> real) n)", Type.fun(TyApp(Natural.TypeName, Nil), real))), a, force(limit.term("-(a:real)", real)))
        )
        .flatMap(rules.mp(_, assumed))
        .flatMap(rules.mp(_, negatedSequence)))

    together.hypotheses shouldBe List(proposition("converges (s:num -> real) (a:real)"))

    // **Not beta-normal, and this assertion was written expecting it to be.** Specialising the
    // sum's `t` at the lambda leaves `(\\y. -(s y)) x` sitting under the binder rather than
    // `-(s x)`: substitution builds a redex and no rule reduces it on the way past. What came out
    // was a theorem about the sequence a reader means, printed in a form a reader does not write,
    // and the first version of this test compared it against the written form and went red. That
    // is `CLAUDE.md`'s sentence about `specToReduced` met from the other side -- the instance
    // carrying a redex is a **different term** -- and it is worth a red test rather than a silent
    // normalisation, because the reduction is a step the caller takes and not one it is given.
    val reduced = force(
      Conv
        .betaNormalise(together.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, together))))

    reduced.conclusion shouldBe
      proposition(
        "converges (\\n:num. (s:num -> real) n + -((s:num -> real) n)) ((a:real) + -(a:real))")
  }
}
