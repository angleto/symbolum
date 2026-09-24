package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Two-by-two matrices, the multiplicativity of the determinant, and the three refusals.
 *
 * **What it does.** `det (A * B) = det A * det B`, proved rather than computed, together with the
 * constructor, the four accessors, addition, scalar multiplication, multiplication, the identity,
 * the transpose and the laws that fall out of the same unfolding. Every fact is an entry of
 * `Matrix.Statements`; the ones `Matrix` names in `ByHand` are derived by hand and the rest by the
 * driver.
 *
 * **What it costs.** No axiom and no type. The theory's axiom list is asserted against the one
 * below it rather than against a number written here, and the type operator list is asserted to be
 * **unchanged**, which is the fourth `defineType` this development deliberately does not perform:
 * see `Matrix`'s own comment for why a 2x2 matrix has no predicate to be carved out by.
 *
 * **What it rests on.** The sixteen axioms of the reals, through `Ring`, and the choice operator,
 * through `FST` and `SND`. Not eta and not infinity. That is measured per fact by walking each
 * derivation rather than by reading the imports, and the split is the interesting part: the
 * accessor laws reach choice and no axiom of arithmetic at all, and the determinant reaches both.
 *
 * **What it does not do, asserted rather than described.** No 3x3, no general determinant, no
 * inverse, and no proof that multiplication fails to commute. The last of those is the one a reader
 * is most likely to assume away, so it is asserted against a named population: `Library.of` over the
 * standard chain, which is the library `Find` and `docs/lemmas.md` both read. "Absent from this
 * development" and "absent from the system" are two claims, and `WordSpec` made the wrong one of
 * them on 2026-09-11.
 */
class MatrixSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val matrices = Matrix.standard
  private val classical = matrices.product.classical

  private def fact(name: String): Kernel.Thm = force(matrices.fact(name))

  private val Derived: Vector[String] = Matrix.Statements.map(_._1)

  /* --------------------------------------------------------------- what it cost */

  "The eleven constants" should "be defined rather than assumed, and add no type" in {
    matrices.theory.axioms shouldBe chain.word.theory.axioms

    // The fourth `defineType` that is deliberately not here. A 2x2 matrix IS a pair of pairs, so
    // there is no subset to carve out and a new type operator would buy a name and cost a bijection
    // in every derivation below. `prod` and `word` are the two the base already had.
    matrices.theory.typeOperators.keySet shouldBe chain.word.theory.typeOperators.keySet

    (matrices.theory.definitions.keySet -- chain.word.theory.definitions.keySet) shouldBe
      Matrix.Definitions.map(_._1).toSet
  }

  it should "carry every fact without a hypothesis left standing" in {
    Derived.foreach(name => withClue(s"$name: ")(fact(name).hypotheses shouldBe empty))
  }

  it should "reach the reals and choice, and neither eta nor infinity" in {
    // The measurement worth having, and the reason it is per fact rather than per development: the
    // accessor laws are about the pair and reach only what the pair's projections cost, while
    // anything with an operation in it goes through `Ring` and reaches the field.
    val choice = force(classical.axiom(Classical.Choice)).conclusion
    val eta = force(classical.axiom(Classical.Eta)).conclusion
    val infinity = force(chain.naturals.axiom(Natural.Infinity)).conclusion

    Derived.foreach { name =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(fact(name)) should not contain eta
        Derivation.axiomsOf(fact(name)) should not contain infinity
      }
    }

    // The four accessor laws cost the projections and nothing else. `FST` is defined by choice, so
    // choice is what they reach, and no axiom of the reals appears in a statement that never adds
    // or multiplies anything.
    Derivation.axiomsOf(fact(Matrix.Entry11OfConstructor)) shouldBe Set(choice)

    // And the target reaches both halves: choice through the accessors, the field through `Ring`.
    val determinant = Derivation.axiomsOf(fact(Matrix.DeterminantMul))
    determinant should contain(choice)
    determinant.size should be > 1
  }

  it should "cost the number of inferences measured, and print the figure 3x3 would start from" in {
    // Counted rather than timed, which is this repository's standing rule: the machine has read one
    // suite at 41 seconds and at 6 minutes 39 in one afternoon, and an inference count is the same
    // on both runs.
    Derived.foreach { name =>
      withClue(s"$name: ") {
        Derivation.size(fact(name)) should be > 100
        Derivation.size(fact(name)) should be < 400000
      }
    }

    // The number anybody proposing 3x3 should start from, printed rather than asserted because it
    // is a reading of a derivation whose shared parts belong to `Ring` and `Product`. At 2x2 the
    // identity `Ring` settles is in 8 variables with 8 monomials a side; at 3x3 it is in 18
    // variables with 216 monomials on the left against 36 on the right, and `Polynomial`'s normal
    // form is sorted, so the cost is superlinear in that count rather than linear.
    // Read 8389 and 4938 on 2026-09-12. A band rather than an equality, because both counts
    // include the shared derivations of `Rules`, of `Product` and of `Polynomial` underneath them
    // and a cheaper `existsIntro` anywhere below would move every one of them.
    val cost = Derivation.size(fact(Matrix.DeterminantMul))
    val constructorForm = Derivation.size(fact(Matrix.MulOfConstructors))
    info(
      s"MAT_DET_MUL is $cost inferences and MAT_MUL_MAT2 is $constructorForm; " +
        "the 3x3 form of the first is an identity in 18 variables over 216 monomials"
    )
  }

  /* ------------------------------------------------------------------ the statements */

  "Every derived fact" should "read as the text this development is checked by" in {
    Matrix.Statements.foreach { case (name, text) =>
      withClue(s"$name: ")(fact(name).conclusion shouldBe force(matrices.proposition(text)))
    }
  }

  it should "name every fact the way the convention names one" in {
    val shape = "[A-Z][A-Z0-9]*(_[A-Z0-9]+)*".r

    Derived.foreach { name =>
      withClue(s"$name: ") {
        shape.matches(name) shouldBe true
        name should startWith("MAT")
      }
    }

    // One spelling per concept: the corpus spells surjective pairing `SURJECTIVE` and injectivity
    // `INJECTIVE`, in `Product`, so this development does not add a second spelling of either.
    Derived.filter(_.contains("_ONTO")) shouldBe empty
    Derived.filter(_.contains("_ONE_ONE")) shouldBe empty
  }

  it should "say what the determinant of a product is, in the notation a reader writes" in {
    // The printer spaces a type application's arguments and the parser does not require it, so the
    // text here is the printed form rather than `Matrix.MatrixText`. The two are the same type and
    // `NotationRoundTripSpec` is where that round trip is the subject; here the subject is the
    // statement.
    matrices.show(fact(Matrix.DeterminantMul).conclusion) shouldBe
      "!x:prod(prod(real, real), prod(real, real)). " +
        "!y:prod(prod(real, real), prod(real, real)). " +
        "MAT_DET (MAT_MUL x y) = MAT_DET x * MAT_DET y"
  }

  /* -------------------------------------------------- a matrix is a pair of pairs */

  "A matrix and a pair of pairs" should "be the same thing, which is the cost of no new type" in {
    // The decision read off the code rather than off the comment that argues for it. Nothing stops
    // a caller leaving this development's vocabulary, because there is no boundary to leave: the
    // two terms below are equal, and a development built on `defineType` would have refused the
    // second as a type error.
    val entry = force(matrices.term("MAT_E11 (m:prod(prod(real,real),prod(real,real)))"))
    val projection = force(matrices.term("FST (FST (m:prod(prod(real,real),prod(real,real))))"))

    val unfolded = force(
      Rewrite.rewrite(
        force(Rewrite.Rule.all(matrices.logic, Vector(force(matrices.definition(Matrix.Entry11))))),
        entry
      )
    )

    Term.destEq(unfolded.conclusion).map(_._2) shouldBe Some(projection)
  }

  /* ---------------------------------------------------------------------- using it */

  "The driver" should "prove an identity nobody wrote down here, end to end" in {
    // "Verify before recording as done": the development is built when it has proved something it
    // does not itself hold. Three matrices, and the determinant of the triple product.
    val goal = force(
      matrices.proposition(
        s"!x:${Matrix.MatrixText}. !y:${Matrix.MatrixText}. !z:${Matrix.MatrixText}. " +
          "MAT_DET (MAT_MUL (MAT_MUL x y) z) = MAT_DET x * MAT_DET y * MAT_DET z"
      )
    )

    val theorem = force(matrices.prove(goal))

    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe goal
  }

  it should "prove one about matrices rather than about reals, by components" in {
    // The other half of the driver: a matrix-valued equation is taken apart into four real ones and
    // rebuilt by congruence, because the ring has never heard of `prod` and would refuse the whole.
    val goal = force(
      matrices.proposition(
        s"!x:${Matrix.MatrixText}. MAT_TRANSPOSE (MAT_SMUL 2 x) = MAT_SMUL 2 (MAT_TRANSPOSE x)"
      )
    )

    force(matrices.prove(goal)).conclusion shouldBe goal
  }

  it should "read a statement written as text, which is what a consumer has" in {
    force(matrices.prove(s"!x:${Matrix.MatrixText}. MAT_ADD x x = MAT_SMUL 2 x")).hypotheses shouldBe
      empty
  }

  /* ------------------------------------------------------------------ the refusals */

  "A false identity" should "come back as the ring's refusal and not as an exhausted rewriter" in {
    // The two are different findings and call for opposite actions. This one is false, the rules
    // reach their fixed point, and what must come back is the ring saying the two normal forms
    // differ rather than `NotNormalised`.
    val goal = force(
      matrices.proposition(
        s"!x:${Matrix.MatrixText}. !y:${Matrix.MatrixText}. MAT_MUL x y = MAT_MUL y x"
      )
    )

    val refusal = matrices.prove(goal)

    refusal.isLeft shouldBe true
    refusal.left.map(_.getClass) should not be Left(classOf[NotNormalised])
  }

  it should "say which term it could not reduce when a side is not in constructor form" in {
    // A matrix written as the pair of pairs it is, which the rules have no reason to touch: they
    // reduce operations to `MAT2` and do not build a `MAT2` out of a `PAIR`. The refusal names the
    // term rather than reporting that something went wrong.
    val goal = force(
      matrices.proposition(
        "MAT_ADD MAT_ID MAT_ID = PAIR (PAIR 2 0) (PAIR 0 2)"
      )
    )

    matrices.prove(goal).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
  }

  it should "refuse a goal that is not an equation, by saying so" in {
    // A conjunction of two identities is the realistic case: each half is in range and the whole is
    // not, and a driver that took the first half and reported success would be the worse answer.
    val goal = force(
      matrices.proposition("MAT_DET MAT_ID = 1 /\\ MAT_DET (MAT_TRANSPOSE MAT_ID) = 1")
    )

    matrices.prove(goal).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
  }

  "An exhausted rewriter" should "be told from a false identity, which are the same Left otherwise" in {
    // The finding card 5f0cd494 is about, met in a third place. `Rewrite.rewrite` hands back the
    // theorem it had built when the step limit ran out, and that theorem is true: nothing in it
    // says whether the rewriting had finished, so a rule set that does not settle looks exactly
    // like an identity that is false.
    //
    // Two rules that undo each other, added to the real ones, so the rewriting alternates for ever
    // over any term mentioning `ff`. What must come back is `NotNormalised` and not the ring's
    // complaint. Built here rather than reachable from a statement, because every rule set this
    // development assembles terminates and the diagnostic would otherwise be untested code.
    val real = TyApp(Real.TypeName, Nil)
    val there = force(matrices.proposition("!i:real. (ff:real->real) i = (gg:real->real) i"))
    val back = force(matrices.proposition("!i:real. (gg:real->real) i = (ff:real->real) i"))
    val alternating = force(
      Rewrite.Rule.all(
        matrices.logic,
        Vector(
          force(LogicError.lift(Kernel.assume(there))),
          force(LogicError.lift(Kernel.assume(back)))
        )
      )
    )

    val goal = force(matrices.proposition("MAT_DET (MAT2 ((ff:real->real) 1) 0 0 0) = 1"))
    val confused = Matrix.Unfolding(
      matrices.logic,
      matrices.ring,
      matrices.theory,
      force(LogicError.lift(matrices.theory.constant(Matrix.Constructor, constructorType(real)))),
      force(
        Rewrite.Rule.all(
          matrices.logic,
          Vector(Matrix.Entry11, Matrix.Entry12, Matrix.Entry21, Matrix.Entry22)
            .map(name => fact(name + "_MAT2")) ++
            Vector(Matrix.Determinant).map(name => force(matrices.definition(name)))
        )
      ) ++ alternating,
      // The CONTRACTING direction, which is what the development itself builds its rule from.
      // `MAT2_SURJECTIVE` is stated the other way round to match `Product.Surjective`, and since
      // 2026-09-12 `Rewrite.Rule.of` refuses that shape outright: a left side that is one of the
      // rule's own variables matches every subterm of its type, including the four the right side
      // has just built. Turning it round here is not a workaround, it is asking for the rule the
      // production path uses.
      force(
        Rewrite.Rule.of(
          matrices.logic,
          force(
            for {
              instance <- matrices.logic.rules.spec(Term.variable("m", Matrix.Matrices), fact(Matrix.Surjective))
              turned <- Conv.sym(instance)
              law <- matrices.logic.rules.gen(Term.variable("m", Matrix.Matrices), turned)
            } yield law
          )
        )
      )
    )

    Matrix.establish(confused, goal).left.map(_.getClass) shouldBe Left(classOf[NotNormalised])
  }

  private def constructorType(real: Type): Type =
    Type.fun(real, Type.fun(real, Type.fun(real, Type.fun(real, Matrix.Matrices))))

  /* ------------------------------------------------- what is not here, by population */

  "Non-commutativity" should "be absent from the library a reader searches, and named as absent" in {
    // The population is named, which is the lesson of 2026-09-11: `WordSpec` asserted a lemma was
    // missing by asking a library that had never collected the development that held it, stayed
    // green, and the lemma had existed for an hour.
    //
    // This is the library `Find` reads and `docs/lemmas.md` is generated from. Matrix
    // multiplication does not commute; the counterexample is small and is a REFUTATION, which the
    // driver above cannot reach because it proves identities.
    val library = Library.of(chain)

    library.names.distinct.filter(name => name.startsWith("MAT_MUL") && name.endsWith("_SYM")) shouldBe
      empty
    library.from("Matrix").map(_.name) should contain(Matrix.DeterminantMul)

    // And the three that are not here either, read off the theory rather than off a comment.
    matrices.theory.constants.keySet should contain noneOf ("MAT_INV", "MAT3", "MAT_ADJUGATE")
  }

  "The chain" should "hold the matrices, so one claim can mention them and anything else" in {
    // The whole of what being in the chain buys, asserted as a caller doing it. `MAT_DET` and `Sum`
    // in one proposition is not a statement any development built beside the chain could make.
    // `chain.matrix` was `widest` until the rotation landed and is not any more. What this test is
    // about survives that unchanged and is asserted instead: the chain's widest signature can name
    // the matrix constants, which is the whole of what being in the chain buys and is a claim about
    // `Matrix` rather than about which development happens to be last.
    chain.widest.theory.constants.keySet should contain allElementsOf
      chain.matrix.theory.constants.keySet

    force(
      chain.widest.proposition(
        s"!f:num->real. !n:num. !x:${Matrix.MatrixText}. Sum f n + MAT_DET x = MAT_DET x + Sum f n"
      )
    )
  }
}
