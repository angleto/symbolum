package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What `IS_CUT` refuses, and what the theory of cuts holds beyond the one it is built on.
 *
 * Written by the verification of cards 709a37d4 and c71986c3. `CutSpec` shows that the sets the
 * development builds are cuts and that `cut` does not collapse; nothing there shows that the
 * predicate **refuses** anything, and a predicate weaker than the one written in `Cut` would pass
 * every assertion in that file, since each of them proves `IS_CUT` of a set rather than its
 * negation. So each clause is made to bite here, at a set that meets the other three and fails that
 * one, and the refutation is a kernel theorem with nothing assumed:
 *
 *  - the empty set fails the first clause, the set of every rational the second;
 *  - the open interval between zero and one is inhabited, bounded and has no greatest member, and is
 *    not closed downwards, which is the third;
 *  - the closed half-line `p <= 0` is closed downwards and fails the fourth, since zero is its
 *    greatest member. This is also the one that reads `RAT_LT` as strict: with a reflexive
 *    `RAT_LT` the closed half-line would be a cut.
 *
 * The control for the last is the same refutation put to the open half-line `p < 0`, which is a cut
 * by `CUT_BELOW`, and which it must fail to refute.
 *
 * `CUT_LE_ADD` is the one law of the sum carrying an antecedent, and `CutSpec` detaches none of
 * them, so it is detached here at `0 <= 1`.
 *
 * The cost is asserted per fact in `CutSpec`, through `Derivation.axiomsOf`. What that does not
 * read is the theory: an axiom asserted during the construction and spent by no published fact would
 * pass it. So the theory's own axioms are compared with those of the theory it extends here.
 */
class CutDefinitionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val fractions = force(Fraction.construct(chain.classical, chain.integers, chain.product, chain.peano))
  private val cuts = force(Cut.construct(fractions, chain.peano))
  private val rules = cuts.logic.rules
  private val rats = Fraction.Classes

  private def rational(text: String): Term = force(cuts.term(text, rats))
  private def lift[T](result: Either[KernelError, T]): Either[LogicError, T] = LogicError.lift(result)

  private val zero = rational("RAT_ZERO")

  /**
   * `IS_CUT S |- (clause 1) /\ (clause 2) /\ (clause 3) /\ (clause 4)`, beta-normal, with the
   * assumption returned beside it so that a refutation can discharge it.
   */
  private def assumedCut(set: String): Either[LogicError, (Term, Vector[Kernel.Thm])] =
    for {
      proposition <- cuts.proposition(s"IS_CUT ($set)")
      argument <- proposition match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("an application of IS_CUT", other))
      }
      definition <- cuts.definition(Cut.IsCut)
      unfolded <- Conv.unfold(definition, List(argument))
      body <- Term.destEq(unfolded.conclusion).map(_._2).toRight(NotOfForm("an equation", unfolded.conclusion))
      normal <- Conv.betaNormalise(body)
      equation <- Conv.trans(unfolded, normal)
      held <- lift(Kernel.assume(proposition))
      whole <- lift(Kernel.eqMp(equation, held))
      first <- rules.conjElim1(whole)
      rest <- rules.conjElim2(whole)
      second <- rules.conjElim1(rest)
      last <- rules.conjElim2(rest)
      third <- rules.conjElim1(last)
      fourth <- rules.conjElim2(last)
    } yield (proposition, Vector(first, second, third, fourth))

  /** `|- ~(RAT_LE b a)` from `|- RAT_LT a b`, through the definition of the strict order. */
  private def strict(less: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    less.conclusion match {
      case App(App(_, a), b) =>
        for {
          definition <- fractions.definition(Fraction.LessThan)
          unfolded <- Conv.unfold(definition, List(a, b))
          result <- lift(Kernel.eqMp(unfolded, less))
        } yield result
      case other => Left(NotOfForm("a strict comparison", other))
    }

  private def reflexive(at: Term): Either[LogicError, Kernel.Thm] =
    fractions.fact(Fraction.AtMostReflexive).flatMap(rules.spec(at, _))

  /** From an existential clause whose every instance is refuted by `refute`, falsity. */
  private def refuteEach(
    existential: Kernel.Thm,
    name: String,
    instance: FVar => Either[LogicError, Term],
    refute: Kernel.Thm => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val variable = Term.variable(name, rats)
    for {
      term <- instance(variable)
      held <- lift(Kernel.assume(term))
      absurd <- refute(held)
      result <- rules.existsElim(existential, variable, absurd)
    } yield result
  }

  private def refuted(proposition: Term, absurd: Kernel.Thm): Kernel.Thm = {
    val result = force(rules.notIntro(proposition, absurd))
    result.hypotheses shouldBe empty
    result.conclusion shouldBe force(cuts.logic.mkNot(proposition))
    result
  }

  /** The fourth clause refuted at a set holding zero whose members are all at most zero. */
  private def noGreatestFails(set: String): Either[LogicError, Kernel.Thm] =
    assumedCut(set).flatMap { case (proposition, clauses) => for {
      atZero <- rules.spec(zero, clauses(3))
      zeroIn <- reflexive(zero)
      above <- rules.mp(atZero, zeroIn)
      absurd <- refuteEach(
        above,
        "b",
        b => cuts.proposition(s"RAT_LE (${b.name}:rat) RAT_ZERO /\\ RAT_LT RAT_ZERO ${b.name}"),
        pair =>
          for {
            atMost <- rules.conjElim1(pair)
            notAtMost <- rules.conjElim2(pair).flatMap(strict)
            result <- rules.notElim(notAtMost, atMost)
          } yield result
      )
      result <- rules.notIntro(proposition, absurd)
    } yield result }

  /* ------------------------------------------------------------------ each clause bites */

  "IS_CUT" should "refuse the empty set, at its first clause" in {
    val set = "\\p:rat. ~(p = p)"
    val (proposition, clauses) = force(assumedCut(set))
    val absurd = force(
      refuteEach(
        clauses(0),
        "a",
        a => cuts.proposition(s"~((${a.name}:rat) = ${a.name})"),
        held => held.conclusion match {
          case App(_, App(App(_, a), _)) => rules.notElim(held, Conv.refl(a))
          case other => Left(NotOfForm("a negated equation", other))
        }
      )
    )
    refuted(proposition, absurd)
  }

  it should "refuse the set of every rational, at its second clause" in {
    val set = "\\p:rat. p = p"
    val (proposition, clauses) = force(assumedCut(set))
    val absurd = force(
      refuteEach(
        clauses(1),
        "b",
        b => cuts.proposition(s"~((${b.name}:rat) = ${b.name})"),
        held => held.conclusion match {
          case App(_, App(App(_, b), _)) => rules.notElim(held, Conv.refl(b))
          case other => Left(NotOfForm("a negated equation", other))
        }
      )
    )
    refuted(proposition, absurd)
  }

  it should "refuse the open interval from zero to one, which is not closed downwards" in {
    // Inhabited by density, bounded by one and without a greatest member, so only the third clause
    // can refuse it: a member `z` above zero puts zero in the set, and zero is not above itself.
    val set = "\\p:rat. RAT_LT RAT_ZERO p /\\ RAT_LT p RAT_ONE"
    val (proposition, clauses) = force(assumedCut(set))
    val one = rational("RAT_ONE")
    val zeroBelowOne = force(
      for {
        definition <- fractions.definition(Fraction.LessThan)
        unfolded <- Conv.unfold(definition, List(zero, one)).flatMap(Conv.sym)
        result <- fractions.fact(Fraction.OneNotAtMostZero).flatMap(t => lift(Kernel.eqMp(unfolded, t)))
      } yield result
    )
    val between = force(rules.specAll(force(fractions.fact(Fraction.Dense)), List(zero, one)).flatMap(rules.mp(_, zeroBelowOne)))
    val absurd = force(
      refuteEach(
        between,
        "z",
        z => cuts.proposition(s"RAT_LT RAT_ZERO (${z.name}:rat) /\\ RAT_LT ${z.name} RAT_ONE"),
        pair =>
          for {
            z <- Right(Term.variable("z", rats))
            closure <- rules.specAll(clauses(2), List(zero, z))
            zeroBelowZ <- rules.conjElim1(pair)
            premise <- rules.conjIntro(pair, zeroBelowZ)
            zeroIn <- rules.mp(closure, premise)
            notAtMost <- rules.conjElim1(zeroIn).flatMap(strict)
            atMost <- reflexive(zero)
            result <- rules.notElim(notAtMost, atMost)
          } yield result
      )
    )
    refuted(proposition, absurd)
  }

  it should "refuse the closed half-line at zero, whose greatest member is zero" in {
    val refutation = force(noGreatestFails("\\p:rat. RAT_LE p RAT_ZERO"))
    refutation.hypotheses shouldBe empty
    refutation.conclusion shouldBe force(cuts.proposition("~(IS_CUT (\\p:rat. RAT_LE p RAT_ZERO))"))
  }

  it should "not be refuted the same way at the open half-line, which is a cut" in {
    // The control for the line above: the refutation reads the set, and at a set that is a cut it
    // has nothing to stand on. `CUT_BELOW` at zero is the proof that this one is a cut.
    noGreatestFails("\\p:rat. RAT_LT p RAT_ZERO").isLeft shouldBe true
    val below = force(cuts.fact(Cut.BelowIsCut).flatMap(rules.spec(zero, _)))
    below.hypotheses shouldBe empty
    below.conclusion shouldBe force(cuts.proposition("IS_CUT (\\p:rat. RAT_LT p RAT_ZERO)"))
  }

  /* ------------------------------------------------------------------ the order with the sum */

  "The order with the sum" should "be detached at zero below one, so its antecedent is one two cuts meet" in {
    // `CUT_LE_ADD` is the one law of the sum with an antecedent. At `0 <= 1`, shifted by the cut of
    // one, what comes back is `0 + 1 <= 1 + 1` with nothing assumed.
    val one = rational("RAT_ONE")
    val zeroCut = force(cuts.term("CUT_OF_RAT RAT_ZERO", Cut.Classes))
    val oneCut = force(cuts.term("CUT_OF_RAT RAT_ONE", Cut.Classes))
    val shifted = force(
      for {
        order <- cuts.fact(Cut.OfRationalOrder).flatMap(rules.specAll(_, List(zero, one))).flatMap(Conv.sym)
        upwards <- fractions.fact(Fraction.ZeroAtMostOne).flatMap(t => lift(Kernel.eqMp(order, t)))
        law <- cuts.fact(Cut.AtMostAdd).flatMap(rules.specAll(_, List(zeroCut, oneCut, oneCut)))
        result <- rules.mp(law, upwards)
      } yield result
    )
    shifted.hypotheses shouldBe empty
    shifted.conclusion shouldBe force(cuts.proposition(
      "CUT_LE (CUT_ADD (CUT_OF_RAT RAT_ZERO) (CUT_OF_RAT RAT_ONE)) (CUT_ADD (CUT_OF_RAT RAT_ONE) (CUT_OF_RAT RAT_ONE))"
    ))
  }

  /* ------------------------------------------------------------------ what the theory holds */

  "The theory of cuts" should "hold the axioms of the theory it is built on and no other" in {
    // Per-fact cost is `CutSpec`'s; an axiom asserted during the construction and spent by nothing
    // published would pass that and fail this. The comparison is with the base and not with the
    // foundation, and that is measured rather than chosen: on 2026-09-26 the base `Fraction` is
    // built on here, `chain.integers`, holds all nineteen, the sixteen of the reals included,
    // because the chain's integers sit above its reals. So at the level of the theory the reals'
    // axioms are present and nothing can say from here that the cuts do without them; that each
    // published fact does is the per-fact count in `CutSpec`, and it is the only instrument that
    // can. Where the base holds only the foundation, this line still says the construction added
    // nothing.
    cuts.theory.axioms.toSet shouldBe fractions.theory.axioms.toSet
    val choice = force(chain.classical.axiom(Classical.Choice)).conclusion
    // The positive control: the instrument reads the base's axioms, which are not empty.
    fractions.theory.axioms should contain(choice)
    // And the comparison sees an axiom when one is added: the theory of cuts with `IS_CUT` of the
    // closed half-line asserted, which the lines above refute, no longer matches its base.
    val closed = force(cuts.proposition("IS_CUT (\\p:rat. RAT_LE p RAT_ZERO)"))
    val (extended, _) = force(lift(Kernel.assertAxiom(cuts.theory, closed)))
    extended.axioms.toSet should not be fractions.theory.axioms.toSet
  }
}
