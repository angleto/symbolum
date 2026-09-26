package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The predecessor and the truncated difference on `num`, and the one question they raise.
 *
 * The question is not whether they are derived — `PeanoSpec` asks that of the whole development at
 * once and the answer covers these — but whether a reader can be **misled** by them. `NUM_SUB` is
 * spelled like a subtraction, reads like a subtraction, and is not the one anybody learned:
 * `NUM_SUB ZERO (SUC ZERO)` is `ZERO` and not minus one, because `num` has no minus one. Every
 * consumer that forgets it writes a lemma that is false, and the two lemmas most likely to be
 * written that way are exactly the two this file states **with** a hypothesis.
 *
 * So the counterexamples are put to the kernel rather than left in a comment. `NUM_SUB_ADD` and
 * `NUM_REAL_SUB` are checked to fail at `m = ZERO, n = SUC ZERO`, which is the assertion that their
 * hypothesis is load-bearing: a test that only exercised them where they hold would pass just as
 * well against the unhypothesised statements, which are false.
 */
class SubtractionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val peano = Peano.standard
  private val ring = peano.ring
  private val logic = peano.logic
  private val rules = logic.rules

  private def fact(name: String): Kernel.Thm = force(peano.fact(name))

  private def rulesOf(names: String*): Vector[Rewrite.Rule] =
    force(Rewrite.Rule.all(logic, names.toVector.map(fact)))

  private val recurrences =
    rulesOf(Peano.SubAtZero, Peano.SubAtSuccessor, Peano.PreAtZero, Peano.PreAtSuccessor)

  private def term(text: String): Term = force(peano.term(text))

  private def applied(operator: => Term, arguments: List[Term]): Term =
    force(LogicError.lift(Term.appAll(operator, arguments)))

  private val zero = term("0:num")
  private val one = term("SUC 0")
  private val two = term("SUC (SUC 0)")
  private val three = term("SUC (SUC (SUC 0))")

  "The predecessor and the difference" should "be defined by recursion, and be total" in {
    // `PRE ZERO = ZERO` is the choice that makes `PRE` a function rather than a partial one, and it
    // is what `NUM_SUB` inherits at every step: the recursion bottoms out there and stays.
    peano.show(fact(Peano.PreAtZero).conclusion) shouldBe "PRE 0 = 0"
    peano.show(fact(Peano.PreAtSuccessor).conclusion) shouldBe "!n:num. PRE (SUC n) = n"

    peano.show(fact(Peano.SubAtZero).conclusion) shouldBe "!n:num. NUM_SUB n 0 = n"
    peano.show(fact(Peano.SubAtSuccessor).conclusion) shouldBe
      "!n:num. !m:num. NUM_SUB n (SUC m) = PRE (NUM_SUB n m)"

    peano.theory.definitions.keySet should contain allOf (Peano.Predecessor, Peano.Subtraction)
  }

  "A difference that would go below zero" should "stop at zero, computed rather than described" in {
    // One minus two, in the unary spelling `num` has. The four recurrences settle it by rewriting
    // with nothing assumed, and what they settle it to is `ZERO`.
    val proved = force(Rewrite.prove(recurrences, applied(minus, List(one, two)), zero))

    proved.hypotheses shouldBe empty
    peano.show(proved.conclusion) shouldBe "NUM_SUB (SUC 0) (SUC (SUC 0)) = 0"
  }

  it should "not be the successor of anything, which is the whole of what truncation costs" in {
    // The other half of the same computation. If `1 - 2` were the integers' answer it would be a
    // number whose successor is `ZERO`, and `NUM_SUC_NOT_ZERO` says there is no such number. Here
    // the refusal is the cheaper witness: the left side normalises to `ZERO` and the claim that it
    // is `SUC ZERO` is refused with both normal forms named.
    Rewrite.prove(recurrences, applied(minus, List(one, two)), one) should matchPattern {
      case Left(NotEqualTo(_, _)) =>
    }
  }

  "The law that has no hypothesis" should "be the one where nothing was truncated" in {
    // `NUM_ADD_SUB` holds everywhere because the sum is built first: whatever is taken away was
    // put there. Checked at a point as well as read off the statement, because the statement is
    // what a reader trusts and the point is what a consumer meets.
    peano.show(fact(Peano.SumMinus).conclusion) shouldBe
      "!n:num. !m:num. NUM_SUB (n + m) m = n"

    val instance = force(rules.specAll(fact(Peano.SumMinus), List(two, three)))
    instance.hypotheses shouldBe empty
    peano.show(instance.conclusion) shouldBe
      "NUM_SUB (SUC (SUC 0) + SUC (SUC (SUC 0))) (SUC (SUC (SUC 0))) = SUC (SUC 0)"
  }

  "The law that has one" should "be false at the point its hypothesis excludes" in {
    // `NUM_ADD (NUM_SUB m n) n = m` at `m = ZERO`, `n = SUC ZERO`. The left side computes to
    // `SUC ZERO` and the right is `ZERO`, so the unhypothesised statement is false and the
    // hypothesis on `NUM_SUB_ADD` is load-bearing rather than cautious.
    val restored = force(
      Rewrite.prove(
        recurrences ++ rulesOf(Peano.AddAtZero, Peano.AddAtSuccessor),
        applied(plus, List(applied(minus, List(zero, one)), one)),
        one
      )
    )

    restored.hypotheses shouldBe empty
    peano.show(restored.conclusion) shouldBe
      "NUM_SUB 0 (SUC 0) + SUC 0 = SUC 0"

    // And `SUC ZERO` is not `ZERO`, which is the Peano fact rather than an appeal to arithmetic.
    val never = force(rules.spec(zero, force(peano.naturals.fact(Natural.SuccessorNotZero))))
    peano.show(never.conclusion) shouldBe "~(SUC 0 = 0)"
  }

  it should "hold where the hypothesis does, end to end" in {
    // The same lemma used the way a consumer would: three is at least one, so `(3 - 1) + 1 = 3`,
    // and the difference computes to two. The bound is chained from `NUM_LE_SUC` rather than
    // witnessed by hand, because that is what a consumer has.
    val bounded = force(
      for {
        first <- rules.spec(one, fact(Peano.AtMostSuccessor))
        second <- rules.spec(two, fact(Peano.AtMostSuccessor))
        both <- rules.conjIntro(first, second)
        chained <- rules.specAll(fact(Peano.Transitive), List(one, two, three))
        result <- rules.mp(chained, both)
      } yield result
    )
    peano.show(bounded.conclusion) shouldBe "SUC 0 <= SUC (SUC (SUC 0))"

    val restored = force(
      rules.specAll(fact(Peano.MinusThenPlus), List(three, one)).flatMap(rules.mp(_, bounded))
    )
    restored.hypotheses shouldBe empty

    val computed = force(Rewrite.inTheorem(recurrences, restored))
    peano.show(computed.conclusion) shouldBe
      "SUC (SUC 0) + SUC 0 = SUC (SUC (SUC 0))"
  }

  "The embedding of a difference" should "be false at the point its hypothesis excludes" in {
    // `real_of_num (NUM_SUB m n) = real_of_num m - real_of_num n` at `m = ZERO`, `n = SUC ZERO`.
    // The left side is the image of `ZERO`, which is `0`; the right is `0 - 1`. `RING` refuses the
    // equation, and for two closed expressions that refusal is a decision: it normalises both and
    // compares, so there is nothing else it could have been waiting for.
    val goal = force(
      peano.proposition(
        "real_of_num (NUM_SUB 0 (SUC 0)) = real_of_num 0 - real_of_num (SUC 0)"
      )
    )
    val carried = force(
      Rewrite.rewrite(recurrences ++ rulesOf(Peano.EmbedsZero, Peano.EmbedsSuccessor), goal)
    )
    val residue = force(
      Term.destEq(carried.conclusion).map(_._2).toRight(NotOfForm("an equation", goal))
    )

    info(s"what the counterexample reduces to: ${peano.show(residue)}")
    ring.prove(residue) should matchPattern { case Left(_) => }
  }

  it should "hold where the hypothesis does, and land in the arithmetic the tactics decide" in {
    // The lemma the rest of the subtraction is for. `real_of_num (NUM_SUB 3 1)` is an atom to every
    // procedure over the reals until this says which real it is; after it, the goal is a ring
    // identity in numerals and `RING` closes it.
    val bounded = force(
      for {
        first <- rules.spec(one, fact(Peano.AtMostSuccessor))
        second <- rules.spec(two, fact(Peano.AtMostSuccessor))
        both <- rules.conjIntro(first, second)
        chained <- rules.specAll(fact(Peano.Transitive), List(one, two, three))
        result <- rules.mp(chained, both)
      } yield result
    )

    val crossed = force(
      rules.specAll(fact(Peano.EmbedsDifference), List(three, one)).flatMap(rules.mp(_, bounded))
    )
    crossed.hypotheses shouldBe empty

    val computed = force(
      Rewrite.inTheorem(recurrences ++ rulesOf(Peano.EmbedsZero, Peano.EmbedsSuccessor), crossed)
    )
    val sides = force(
      Term.destEq(computed.conclusion).toRight(NotOfForm("an equation", computed.conclusion))
    )

    info(s"the difference of two indices, over the reals: ${peano.show(computed.conclusion)}")
    force(ring.prove(force(LogicError.lift(Term.eq(sides._1, term("2:real")))))).hypotheses shouldBe empty
    force(ring.prove(force(LogicError.lift(Term.eq(sides._2, term("2:real")))))).hypotheses shouldBe empty
  }

  "The truncation" should "be stated as a theorem and not only as a warning in the docstring" in {
    // A reader who expects the integers' subtraction is wrong about this file, and the file says so
    // in prose. Prose is not checked; `NUM_SUB_EQ_ZERO` is.
    peano.show(fact(Peano.SubIsZero).conclusion) shouldBe
      "!n:num. !m:num. n <= m ==> NUM_SUB n m = 0"
    peano.show(fact(Peano.Truncates).conclusion) shouldBe
      "!n:num. !m:num. NUM_SUB n (n + m) = 0"
    peano.show(fact(Peano.SubBelow).conclusion) shouldBe
      "!n:num. !m:num. NUM_SUB n m <= n"
  }

  "Every fact about the difference" should "rest on nothing this development did not already cost" in {
    // The axiom count is `PeanoSpec`'s to assert and it does. What is asked here is the finer
    // question: a fact about `num` alone reaches the two the naturals cost, and only the one that
    // crosses into the reals reaches theirs.
    Vector(
      Peano.PreAtZero,
      Peano.PreAtSuccessor,
      Peano.SubAtZero,
      Peano.SubAtSuccessor,
      Peano.ZeroMinus,
      Peano.SubSuccessors,
      Peano.SubSelf,
      Peano.SumMinus,
      Peano.Truncates,
      Peano.SubIsZero,
      Peano.PredecessorBelow,
      Peano.SubBelow,
      Peano.MinusThenPlus
    ).foreach { name =>
      withClue(s"$name: ") {
        fact(name).hypotheses shouldBe empty
        Derivation.axiomsOf(fact(name)) should have size 2
      }
    }

    Derivation.axiomsOf(fact(Peano.EmbedsDifference)).size should be > 2
  }

  "The size of each proof" should "be reported, since the inductions are the expensive part" in {
    Vector(
      Peano.ZeroMinus,
      Peano.SubSuccessors,
      Peano.SubSelf,
      Peano.SumMinus,
      Peano.Truncates,
      Peano.SubIsZero,
      Peano.PredecessorBelow,
      Peano.SubBelow,
      Peano.MinusThenPlus,
      Peano.EmbedsDifference
    ).foreach { name =>
      val theorem = fact(name)
      info(
        s"$name: ${Derivation.size(theorem)} inferences over " +
          s"${Derivation.axiomsOf(theorem).size} axioms"
      )
      Derivation.size(theorem) should be > 10
    }
  }

  "What is still not on num" should "be absent from `Peano` by name, so the gap reads off the code" in {
    // The file's own list of what it does not cover, checked rather than believed. A development
    // that added one of these and forgot the docstring would fail here, which is the arrangement
    // `MagnitudeSpec` uses for the floor it refuses.
    //
    // **The population is `Peano`'s theory and that is now load-bearing.** `NUM_DIV` and `NUM_MOD`
    // are constants of `Modular` since 2026-09-12, which extends this theory, so "absent here" and
    // "absent from the system" stopped being the same claim on that day. This one is still true and
    // still worth asserting: the division `Peano` does not have is the one it would have needed a
    // remainder for, and it did not acquire one by somebody else defining it downstream. The other
    // reading is `ModularSpec`'s, which asserts the two constants are present there.
    val constants = peano.theory.constants.keySet

    constants should not contain "NUM_DIV"
    constants should not contain "NUM_MOD"

    Chain.standard.modular.theory.constants.keySet should contain allOf ("NUM_DIV", "NUM_MOD")

    // **`NUM_BIT0` was on this list until 2026-09-12 and has come off it**, together with the
    // assertion below it that `2` is a real. Both were true and both stopped being true on the day
    // `num` got numerals, and the pair is kept here rather than deleted because what they asserted
    // is now asserted in the other direction: the three constants are `Peano`'s own, and a digit
    // string is read at whichever of the two types its context forces.
    constants should contain allOf (Peano.NumeralOne, Peano.NumeralBit0, Peano.NumeralBit1)

    // `2` alone is now ambiguous rather than real, and the refusal is the point: this signature
    // reads numerals at two types and nothing here says which. Asserting the refusal and then the
    // two readings is what keeps this from passing on a parse that failed for some other reason.
    peano.term("2").isLeft shouldBe true
    Term.typeOf(term("2:real")) shouldBe TyApp(Real.TypeName, Nil)
    Term.typeOf(term("2:num")) shouldBe TyApp(Natural.TypeName, Nil)
  }

  private lazy val numbers = TyApp(Natural.TypeName, Nil)

  private lazy val minus: Term =
    force(
      LogicError.lift(
        peano.theory.constant(Peano.Subtraction, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
    )

  private lazy val plus: Term =
    force(
      LogicError.lift(
        peano.theory.constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
    )
}
