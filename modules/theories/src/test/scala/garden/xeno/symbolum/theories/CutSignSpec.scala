package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The product and the inverse of the cuts read at their definitions, at one and minus one.
 *
 * Written by the verification of card c72f04ee. `CutSpec` detaches the product's laws at the cut of
 * one only, which is on the cone, so every branch `CUT_MUL` and `CUT_INV` take off the cone is
 * reached there through the laws and never through the text of the definition. Here the definition
 * itself is unfolded at the four sign pairs of one and minus one and at the three signs of the
 * inverse, and each `COND` is settled by a sign fact derived with nothing assumed; what comes back
 * is compared with the branch the definition is meant to pick, and then evaluated to a cut:
 *
 *  - `1 * 1 = 1`, `1 * -1 = -1`, `-1 * 1 = -1` and `-1 * -1 = 1`, the last positive;
 *  - `inv 0 = 0`, `inv 1 = 1` and `inv (-1) = -1`.
 *
 * What would make this vacuous is one and minus one being the same cut, since then every sign
 * would be right; so their distinctness is derived here too.
 */
class CutSignSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)
  private def lift[T](result: Either[KernelError, T]): Either[LogicError, T] = LogicError.lift(result)

  private val chain = Chain.standard
  private val fractions = chain.fractions
  private val cuts = chain.cuts
  private val rules = cuts.logic.rules

  private def fact(name: String): Kernel.Thm = force(cuts.fact(name))
  private def rational(text: String): Term = force(cuts.term(text, Fraction.Classes))
  private def cut(text: String): Term = force(cuts.term(text, Cut.Classes))
  private def proposition(text: String): Term = force(cuts.proposition(text))

  private val zeroRat = rational("RAT_ZERO")
  private val oneRat = rational("RAT_ONE")
  private val zero = cut("CUT_OF_RAT RAT_ZERO")
  private val one = cut("CUT_OF_RAT RAT_ONE")
  private val minusOne = cut("CUT_NEG (CUT_OF_RAT RAT_ONE)")

  /** The head of a binary application, read from a proposition so the parser settles its type. */
  private def binary(text: String): Term = proposition(text) match {
    case App(App(head, _), _) => head
    case other => fail(s"not a binary application: $other")
  }
  private def unary(text: String): Term = cut(text) match {
    case App(head, _) => head
    case other => fail(s"not an application: $other")
  }
  private val atMost = binary("CUT_LE (CUT_OF_RAT RAT_ZERO) (CUT_OF_RAT RAT_ZERO)")
  private val less = binary("CUT_LT (CUT_OF_RAT RAT_ZERO) (CUT_OF_RAT RAT_ZERO)")
  private val posMul = unary("CUT_PMUL (CUT_OF_RAT RAT_ZERO) (CUT_OF_RAT RAT_ZERO)") match {
    case App(head, _) => head
    case other => fail(s"not a binary application: $other")
  }
  private val negation = unary("CUT_NEG (CUT_OF_RAT RAT_ZERO)")
  private val posInverse = unary("CUT_PINV (CUT_OF_RAT RAT_ZERO)")

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  /** `|- f a b = f c d` from `|- a = c` and `|- b = d`. */
  private def both(f: Term, left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv.apTerm(f, left).flatMap(partial => lift(Kernel.mkComb(partial, right)))

  /** `|- COND p a b = a` or `= b`, as the sign fact says `p` or `~p`: the reading `Cut` uses. */
  private def branch(term: Term, sign: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    term match {
      case App(App(App(_, test), yes), no) =>
        val holds = sign.conclusion == test
        cuts.classical.fact(if (holds) Classical.CondTrue else Classical.CondFalse)
          .map(Kernel.instType(Map(Classical.TypeVariable -> Cut.Classes), _))
          .flatMap(rules.specAll(_, List(test, yes, no)))
          .flatMap(rules.mp(_, sign))
      case other => Left(NotOfForm("a conditional", other))
    }

  /** The definition unfolded at `arguments`, with its two conditionals settled by the two sign facts. */
  private def evaluated(name: String, arguments: List[Term], first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm =
    force(
      for {
        definition <- cuts.definition(name)
        unfolded <- Conv.unfold(definition, arguments)
        outer <- rightOf(unfolded).flatMap(branch(_, first)).flatMap(Conv.trans(unfolded, _))
        inner <- rightOf(outer).flatMap(branch(_, second)).flatMap(Conv.trans(outer, _))
      } yield inner
    )

  /* ------------------------------------------------------------------ the sign facts */

  private val zeroAtMostOne: Kernel.Thm = force(
    rules.specAll(fact(Cut.OfRationalOrder), List(zeroRat, oneRat))
      .flatMap(Conv.sym)
      .flatMap(equation => fractions.fact(Fraction.ZeroAtMostOne).flatMap(t => lift(Kernel.eqMp(equation, t))))
  )

  private val oneNotAtMostZero: Kernel.Thm = force(
    for {
      backwardsTerm <- cuts.proposition("CUT_LE (CUT_OF_RAT RAT_ONE) (CUT_OF_RAT RAT_ZERO)")
      backwards <- lift(Kernel.assume(backwardsTerm))
      rats <- rules.specAll(fact(Cut.OfRationalOrder), List(oneRat, zeroRat)).flatMap(eq => lift(Kernel.eqMp(eq, backwards)))
      absurd <- fractions.fact(Fraction.OneNotAtMostZero).flatMap(rules.notElim(_, rats))
      result <- rules.notIntro(backwardsTerm, absurd)
    } yield result
  )

  /** `|- CUT_LT a b` from `|- ~(CUT_LE b a)`. */
  private def strictly(a: Term, b: Term, notBelow: Kernel.Thm): Kernel.Thm = force(
    cuts.definition(Cut.LessThan).flatMap(Conv.unfold(_, List(a, b))).flatMap(Conv.sym).flatMap(eq => lift(Kernel.eqMp(eq, notBelow)))
  )

  private val onePositive: Kernel.Thm = strictly(zero, one, oneNotAtMostZero)

  private val negZero: Kernel.Thm = fact(Cut.NegZero)
  private val negNegOne: Kernel.Thm = force(rules.spec(one, fact(Cut.NegNeg)))

  /** `|- CUT_LE (-1) 0`, from `0 <= 1` through the negation's order and `-0 = 0`. */
  private val minusOneAtMostZero: Kernel.Thm = force(
    for {
      flipped <- rules.specAll(fact(Cut.AtMostNeg), List(zero, one)).flatMap(rules.mp(_, zeroAtMostOne))
      rewrite <- both(atMost, Conv.refl(minusOne), negZero)
      result <- lift(Kernel.eqMp(rewrite, flipped))
    } yield result
  )

  /** `|- ~(CUT_LE 0 (-1))`: were it so, `--1 <= -0` would put one below zero. */
  private val minusOneNotNonNegative: Kernel.Thm = force(
    for {
      aboveTerm <- cuts.proposition("CUT_LE (CUT_OF_RAT RAT_ZERO) (CUT_NEG (CUT_OF_RAT RAT_ONE))")
      above <- lift(Kernel.assume(aboveTerm))
      flipped <- rules.specAll(fact(Cut.AtMostNeg), List(zero, minusOne)).flatMap(rules.mp(_, above))
      rewrite <- both(atMost, negNegOne, negZero)
      oneBelow <- lift(Kernel.eqMp(rewrite, flipped))
      absurd <- rules.notElim(oneNotAtMostZero, oneBelow)
      result <- rules.notIntro(aboveTerm, absurd)
    } yield result
  )

  private val minusOneNegative: Kernel.Thm = strictly(minusOne, zero, minusOneNotNonNegative)

  /** `|- ~(CUT_LT 0 (-1))`. */
  private val minusOneNotPositive: Kernel.Thm = force(
    for {
      lessTerm <- cuts.proposition("CUT_LT (CUT_OF_RAT RAT_ZERO) (CUT_NEG (CUT_OF_RAT RAT_ONE))")
      held <- lift(Kernel.assume(lessTerm))
      opened <- cuts.definition(Cut.LessThan).flatMap(Conv.unfold(_, List(zero, minusOne))).flatMap(eq => lift(Kernel.eqMp(eq, held)))
      absurd <- rules.notElim(opened, minusOneAtMostZero)
      result <- rules.notIntro(lessTerm, absurd)
    } yield result
  )

  /** `|- ~(CUT_LT 0 0)`. */
  private val zeroNotPositive: Kernel.Thm = force(
    for {
      lessTerm <- cuts.proposition("CUT_LT (CUT_OF_RAT RAT_ZERO) (CUT_OF_RAT RAT_ZERO)")
      held <- lift(Kernel.assume(lessTerm))
      opened <- cuts.definition(Cut.LessThan).flatMap(Conv.unfold(_, List(zero, zero))).flatMap(eq => lift(Kernel.eqMp(eq, held)))
      reflexive <- rules.spec(zero, fact(Cut.AtMostReflexive))
      absurd <- rules.notElim(opened, reflexive)
      result <- rules.notIntro(lessTerm, absurd)
    } yield result
  )

  /** `|- CUT_PMUL 1 1 = 1`. */
  private val coreOne: Kernel.Thm = force(rules.spec(one, fact(Cut.PosMulOne)).flatMap(rules.mp(_, zeroAtMostOne)))

  "One and minus one" should "be different cuts, or every sign below would be right by collapse" in {
    val distinct = force(
      for {
        sameTerm <- cuts.proposition("CUT_OF_RAT RAT_ONE = CUT_NEG (CUT_OF_RAT RAT_ONE)")
        same <- lift(Kernel.assume(sameTerm))
        moved <- both(atMost, Conv.refl(zero), same).flatMap(eq => lift(Kernel.eqMp(eq, zeroAtMostOne)))
        absurd <- rules.notElim(minusOneNotNonNegative, moved)
        result <- rules.notIntro(sameTerm, absurd)
      } yield result
    )
    distinct.hypotheses shouldBe empty
    distinct.conclusion shouldBe proposition("~(CUT_OF_RAT RAT_ONE = CUT_NEG (CUT_OF_RAT RAT_ONE))")
    minusOneNegative.hypotheses shouldBe empty
    minusOneNegative.conclusion shouldBe proposition("CUT_LT (CUT_NEG (CUT_OF_RAT RAT_ONE)) (CUT_OF_RAT RAT_ZERO)")
    onePositive.conclusion shouldBe proposition("CUT_LT (CUT_OF_RAT RAT_ZERO) (CUT_OF_RAT RAT_ONE)")
  }

  /* ------------------------------------------------------------------ the product by sign */

  "CUT_MUL" should "take the core at two non-negative factors, and give one at one times one" in {
    val picked = evaluated(Cut.Multiplication, List(one, one), zeroAtMostOne, zeroAtMostOne)
    picked.hypotheses shouldBe empty
    picked.conclusion shouldBe proposition(
      "CUT_MUL (CUT_OF_RAT RAT_ONE) (CUT_OF_RAT RAT_ONE) = CUT_PMUL (CUT_OF_RAT RAT_ONE) (CUT_OF_RAT RAT_ONE)")
    val value = force(Conv.trans(picked, coreOne))
    value.conclusion shouldBe proposition("CUT_MUL (CUT_OF_RAT RAT_ONE) (CUT_OF_RAT RAT_ONE) = CUT_OF_RAT RAT_ONE")
  }

  it should "negate the core at a non-negative times a negative, and give minus one at one times minus one" in {
    val picked = evaluated(Cut.Multiplication, List(one, minusOne), zeroAtMostOne, minusOneNotNonNegative)
    picked.hypotheses shouldBe empty
    picked.conclusion shouldBe proposition(
      "CUT_MUL (CUT_OF_RAT RAT_ONE) (CUT_NEG (CUT_OF_RAT RAT_ONE)) = " +
        "CUT_NEG (CUT_PMUL (CUT_OF_RAT RAT_ONE) (CUT_NEG (CUT_NEG (CUT_OF_RAT RAT_ONE))))")
    val value = force(
      both(posMul, Conv.refl(one), negNegOne).flatMap(Conv.trans(_, coreOne)).flatMap(Conv.apTerm(negation, _)).flatMap(Conv.trans(picked, _))
    )
    value.hypotheses shouldBe empty
    value.conclusion shouldBe proposition("CUT_MUL (CUT_OF_RAT RAT_ONE) (CUT_NEG (CUT_OF_RAT RAT_ONE)) = CUT_NEG (CUT_OF_RAT RAT_ONE)")
  }

  it should "negate the core at a negative times a non-negative, and give minus one at minus one times one" in {
    val picked = evaluated(Cut.Multiplication, List(minusOne, one), minusOneNotNonNegative, zeroAtMostOne)
    picked.hypotheses shouldBe empty
    picked.conclusion shouldBe proposition(
      "CUT_MUL (CUT_NEG (CUT_OF_RAT RAT_ONE)) (CUT_OF_RAT RAT_ONE) = " +
        "CUT_NEG (CUT_PMUL (CUT_NEG (CUT_NEG (CUT_OF_RAT RAT_ONE))) (CUT_OF_RAT RAT_ONE))")
    val value = force(
      both(posMul, negNegOne, Conv.refl(one)).flatMap(Conv.trans(_, coreOne)).flatMap(Conv.apTerm(negation, _)).flatMap(Conv.trans(picked, _))
    )
    value.conclusion shouldBe proposition("CUT_MUL (CUT_NEG (CUT_OF_RAT RAT_ONE)) (CUT_OF_RAT RAT_ONE) = CUT_NEG (CUT_OF_RAT RAT_ONE)")
  }

  it should "take the core of the negations at two negatives, so minus one times minus one is one and positive" in {
    val picked = evaluated(Cut.Multiplication, List(minusOne, minusOne), minusOneNotNonNegative, minusOneNotNonNegative)
    picked.hypotheses shouldBe empty
    picked.conclusion shouldBe proposition(
      "CUT_MUL (CUT_NEG (CUT_OF_RAT RAT_ONE)) (CUT_NEG (CUT_OF_RAT RAT_ONE)) = " +
        "CUT_PMUL (CUT_NEG (CUT_NEG (CUT_OF_RAT RAT_ONE))) (CUT_NEG (CUT_NEG (CUT_OF_RAT RAT_ONE)))")
    val value = force(both(posMul, negNegOne, negNegOne).flatMap(Conv.trans(_, coreOne)).flatMap(Conv.trans(picked, _)))
    value.hypotheses shouldBe empty
    value.conclusion shouldBe proposition("CUT_MUL (CUT_NEG (CUT_OF_RAT RAT_ONE)) (CUT_NEG (CUT_OF_RAT RAT_ONE)) = CUT_OF_RAT RAT_ONE")
    val positive = force(
      both(less, Conv.refl(zero), value).flatMap(Conv.sym).flatMap(eq => lift(Kernel.eqMp(eq, onePositive)))
    )
    positive.hypotheses shouldBe empty
    positive.conclusion shouldBe proposition(
      "CUT_LT (CUT_OF_RAT RAT_ZERO) (CUT_MUL (CUT_NEG (CUT_OF_RAT RAT_ONE)) (CUT_NEG (CUT_OF_RAT RAT_ONE)))")
  }

  /* ------------------------------------------------------------------ the inverse by sign */

  /** `|- CUT_PINV 1 = 1`: `1 * pinv 1 = 1` on the core, with the core's unit and commutativity. */
  private val pinvOne: Kernel.Thm = force(
    for {
      pinv <- lift(Term.app(posInverse, one))
      nonNegative <- rules.spec(one, fact(Cut.PosInverseNonNegative)).flatMap(rules.mp(_, onePositive))
      unitLaw <- rules.spec(pinv, fact(Cut.PosMulOne)).flatMap(rules.mp(_, nonNegative))
      swapped <- rules.specAll(fact(Cut.PosMulCommutative), List(pinv, one))
      inverse <- rules.spec(one, fact(Cut.PosMulInverse)).flatMap(rules.mp(_, onePositive))
      result <- Conv.sym(unitLaw).flatMap(Conv.trans(_, swapped)).flatMap(Conv.trans(_, inverse))
    } yield result
  )

  "CUT_INV" should "write zero at zero, where both of its tests fail" in {
    val picked = evaluated(Cut.Inverse, List(zero), zeroNotPositive, zeroNotPositive)
    picked.hypotheses shouldBe empty
    picked.conclusion shouldBe proposition("CUT_INV (CUT_OF_RAT RAT_ZERO) = CUT_OF_RAT RAT_ZERO")
    picked.conclusion shouldBe fact(Cut.InverseZero).conclusion
  }

  it should "take the positive inverse above zero, which is one at one" in {
    val definition = force(cuts.definition(Cut.Inverse))
    val picked = force(
      Conv.unfold(definition, List(one)).flatMap(unfolded => rightOf(unfolded).flatMap(branch(_, onePositive)).flatMap(Conv.trans(unfolded, _)))
    )
    picked.conclusion shouldBe proposition("CUT_INV (CUT_OF_RAT RAT_ONE) = CUT_PINV (CUT_OF_RAT RAT_ONE)")
    val value = force(Conv.trans(picked, pinvOne))
    value.hypotheses shouldBe empty
    value.conclusion shouldBe proposition("CUT_INV (CUT_OF_RAT RAT_ONE) = CUT_OF_RAT RAT_ONE")
  }

  it should "negate the inverse of the negation below zero, which is minus one at minus one" in {
    val picked = evaluated(Cut.Inverse, List(minusOne), minusOneNotPositive, minusOneNegative)
    picked.hypotheses shouldBe empty
    picked.conclusion shouldBe proposition(
      "CUT_INV (CUT_NEG (CUT_OF_RAT RAT_ONE)) = CUT_NEG (CUT_PINV (CUT_NEG (CUT_NEG (CUT_OF_RAT RAT_ONE))))")
    val value = force(
      Conv.apTerm(posInverse, negNegOne).flatMap(Conv.trans(_, pinvOne)).flatMap(Conv.apTerm(negation, _)).flatMap(Conv.trans(picked, _))
    )
    value.hypotheses shouldBe empty
    value.conclusion shouldBe proposition("CUT_INV (CUT_NEG (CUT_OF_RAT RAT_ONE)) = CUT_NEG (CUT_OF_RAT RAT_ONE)")
  }

  it should "meet the published inverse law at minus one, whose hypothesis a negative cut meets" in {
    val detached = force(
      for {
        zeroTerm <- cuts.proposition("CUT_NEG (CUT_OF_RAT RAT_ONE) = CUT_OF_RAT RAT_ZERO")
        isZero <- lift(Kernel.assume(zeroTerm))
        backwards <- Conv.sym(isZero)
        reflexive <- rules.spec(zero, fact(Cut.AtMostReflexive))
        rewrite <- both(atMost, Conv.refl(zero), backwards)
        nonNegative <- lift(Kernel.eqMp(rewrite, reflexive))
        absurd <- rules.notElim(minusOneNotNonNegative, nonNegative)
        nonZero <- rules.notIntro(zeroTerm, absurd)
        result <- rules.spec(minusOne, fact(Cut.MulInverse)).flatMap(rules.mp(_, nonZero))
      } yield result
    )
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe proposition(
      "CUT_MUL (CUT_NEG (CUT_OF_RAT RAT_ONE)) (CUT_INV (CUT_NEG (CUT_OF_RAT RAT_ONE))) = CUT_OF_RAT RAT_ONE")
  }
}
