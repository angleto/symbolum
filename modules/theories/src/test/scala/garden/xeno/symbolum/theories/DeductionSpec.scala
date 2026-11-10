package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Derivations of the embedded theory, and the one thing a reader has to be shown about them.
 *
 * The statements are checked below the way every development's are. What that does not say is that
 * they can be **used**, which is a different claim and the one this layer exists for: a scheme
 * proved over a variable formula is worth nothing until a caller can hand it a code, discharge the
 * `NUM_FORM` condition it carries, and get a provability fact back. So the last test builds a chain
 * of object-level implications out of three concrete axioms and reads the end off it.
 *
 * The three codes are deliberately **different** axioms. A syllogism wired to return one of its two
 * premises rather than their composition is a true theorem about the wrong pair, and with `A`, `B`
 * and `C` distinct the three candidate answers are three distinct terms.
 */
class DeductionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val deduction = chain.deduction
  private val logic = deduction.logic
  private val rules = logic.rules
  private val numbers = TyApp(Natural.TypeName, Nil)
  private val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))

  private def term(text: String): Term =
    force(Parser.term(deduction.theory, deduction.notation, text, numbers))

  private def proposition(text: String): Term =
    force(Parser.proposition(deduction.theory, deduction.notation, text))

  private def constant(name: String, ty: Type): Term =
    force(LogicError.lift(deduction.theory.constant(name, ty)))

  private def applied(head: Term, arguments: List[Term]): Term =
    force(LogicError.lift(Term.appAll(head, arguments)))

  private val pairing = constant(Numbering.PairName, arithmetic)
  private val coding = constant(Numbering.CodeName, arithmetic)

  private def imp(left: Term, right: Term): Term =
    applied(coding, List(term("7"), applied(pairing, List(left, right))))

  private def predicate(name: String)(subject: Term): Term =
    applied(constant(name, Type.fun(numbers, Type.Bool)), List(subject))

  private val isFormula = predicate(Language.FormulaName)
  private val isLogical = predicate(Language.LogicName)
  private val isProvable = predicate(Provability.ProvableName)

  private def imply(left: Term, right: Term): Term = force(logic.mkImp(left, right))

  "Deduction" should "be the statements this development publishes" in {
    Deduction.Statements.foreach { case (name, text) =>
      val theorem = force(deduction.fact(name))
      withClue(s"$name: ") {
        theorem.conclusion shouldBe proposition(text)
        theorem.hypotheses shouldBe empty
      }
    }
  }

  /**
   * PA proves its own arithmetic at a numeral, which is the first brick of Sigma-1 completeness.
   *
   * Every piece of this was in place except two, and both landed on 2026-09-15. The scheme's third
   * condition is `NUM_CLOSED t`, which nothing in the library could discharge, so
   * `NUM_LOGIC_SPECIALISE` was a theorem no caller could apply; `NUM_NUMERAL_CLOSED` is what
   * answers it, and at a numeral rather than at one term, which is what makes the claim here about
   * every `m`. And the conclusion carried `NUM_SUBST_FORM 0 (NUM_NUMERAL m) <body>` with the
   * substitution standing, which is a true statement about a number nobody can read as a formula;
   * `Language.substituteIn` computes it.
   *
   * What comes out is `NUM_PROV` of the code of `numeral m + 0 = numeral m`, for a **variable**
   * `m`, with nothing assumed and at the two axioms the naturals cost. It is the object theory
   * proving a fact about itself, which is what the whole construction is for, and it is the first
   * statement anywhere here of that shape.
   *
   * **It is not yet Sigma-1 completeness and the gap is worth naming**, since a reader meeting a
   * theorem about `+` and numerals will reach for that phrase. This is one axiom specialised. The
   * general `numeral m + numeral n = numeral (m + n)` goes by induction on `n`, and its step needs
   * the object theory's equality to be transitive and to respect the successor: `NUM_LOGIC` has
   * reflexivity and one replacement scheme, and nothing has yet derived symmetry, transitivity or
   * congruence out of them. That is the next development and it belongs in this file.
   */
  /**
   * The equality rules turned on something the object theory actually proved.
   *
   * A rule that has been derived and never applied is not built, and these three are easy to
   * derive in a way that no caller can use: every one of them asks `NUM_CLOSED` of BOTH sides, and
   * before today nothing could discharge such a condition at all. So this runs symmetry on the one
   * object theorem there is, `numeral m + 0 = numeral m`, and gets `numeral m = numeral m + 0`.
   *
   * The work is not the rule, it is the closure of the left side. `NUM_NUMERAL_CLOSED` closes a
   * numeral and nothing closes a SUM of one with zero, so it is derived here, one index at a time,
   * out of the freeness clause for a sum and the two closures underneath it. That is the first
   * compound closed term anywhere here, and it is the shape every further object derivation needs.
   */
  /**
   * The object theory's addition on numerals, and what it costs.
   *
   * `NUM_PROV_NUMERAL_ADD` is the first general statement here about what PA proves, as against a
   * statement about one instance of one axiom, and the two things worth asserting about it are
   * that it holds at a pair of concrete numbers and that it costs what everything else here costs.
   * The second is the one with teeth: an object-level theorem that had started spending an axiom
   * of the reals would be a defect in the construction rather than in the proof, and `docs/adr`
   * records that the whole point of building the arithmetic over `num` is that it does not.
   */
  it should "prove its own addition on numerals, at the naturals' cost" in {
    val theorem = force(deduction.fact(Deduction.NumeralAddition))
    theorem.hypotheses shouldBe empty
    Derivation.axiomsOf(theorem) should have size 2

    // At two concrete numbers, the statement is about the numerals of those numbers and of the
    // sum the META level computes. Nothing here evaluates `NUM_ADD`: that the two levels agree is
    // what the theorem says, not something the statement assumes.
    val instance = force(rules.specAll(theorem, List(term("SUC ZERO"), term("SUC (SUC ZERO)"))))
    instance.hypotheses shouldBe empty
    instance.conclusion shouldBe proposition(
      "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 3 (NUM_PAIR (NUM_NUMERAL (SUC ZERO)) (NUM_NUMERAL (SUC (SUC ZERO))))) " +
        "(NUM_NUMERAL (NUM_ADD (SUC ZERO) (SUC (SUC ZERO))))))")
  }

  /**
   * PA tells two numerals apart, in both orders, with the difference discharged rather than assumed.
   *
   * The two orders are not the same test twice: the induction on `m` meets `0` against a successor
   * at its base, which goes through `S x != 0` flipped by the denied symmetry, and a successor
   * against `0` in its step, which does not. `2` against `1` reaches the second through one use of
   * the hypothesis, and `0` against `3` the first directly, so between them every case of the proof
   * runs. And an implication whose antecedent nobody can discharge is a theorem about nothing, so
   * `~(m = n)` is derived here from the naturals' own `SUC n != 0` and injectivity.
   */
  it should "prove two different numerals different, in both orders, at the naturals' cost" in {
    val theorem = force(deduction.fact(Deduction.NumeralsDistinct))
    theorem.hypotheses shouldBe empty
    Derivation.axiomsOf(theorem) should have size 2

    val naturals = chain.naturals
    val notZero = force(naturals.fact(Natural.SuccessorNotZero))
    val injective = force(naturals.fact(Natural.SuccessorInjective))
    def apart(bigger: String, smaller: String, peeled: Int): Kernel.Thm = {
      // `SUC^peeled (x) = SUC^peeled (ZERO)` collapses to `x = ZERO` by injectivity, which the
      // successor axiom then refutes; `x` is `SUC something`.
      val equation = proposition(s"$bigger = $smaller")
      def peel(theorem: Kernel.Thm, left: Int): Kernel.Thm =
        if (left == 0) theorem
        else theorem.conclusion match {
          case App(App(_, App(_, l)), App(_, r)) =>
            peel(force(rules.specAll(injective, List(l, r)).flatMap(rules.mp(_, theorem))), left - 1)
          case other => fail(s"not an equation between successors: $other")
        }
      val bottom = peel(force(LogicError.lift(Kernel.assume(equation))), peeled)
      val residue = bottom.conclusion match {
        case App(App(_, App(_, inner)), _) => inner
        case other => fail(s"not a successor against zero: $other")
      }
      force(rules.spec(residue, notZero).flatMap(rules.notElim(_, bottom))
        .flatMap(rules.notIntro(equation, _)))
    }

    val two = "SUC (SUC ZERO)"
    val one = "SUC ZERO"
    val three = "SUC (SUC (SUC ZERO))"
    val twoOne = force(rules.specAll(theorem, List(term(two), term(one)))
      .flatMap(rules.mp(_, apart(two, one, 1))))
    twoOne.hypotheses shouldBe empty
    twoOne.conclusion shouldBe proposition(
      s"NUM_PROV (NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR (NUM_NUMERAL ($two)) (NUM_NUMERAL ($one)))))")

    val zeroIsNotThree = force(
      Conv.sym(force(LogicError.lift(Kernel.assume(proposition(s"ZERO = $three")))))
        .flatMap(reversed => rules.spec(term(s"SUC (SUC ZERO)"), notZero)
          .flatMap(rules.notElim(_, reversed)))
        .flatMap(rules.notIntro(proposition(s"ZERO = $three"), _)))
    val zeroThree = force(rules.specAll(theorem, List(term("ZERO"), term(three)))
      .flatMap(rules.mp(_, zeroIsNotThree)))
    zeroThree.hypotheses shouldBe empty
    zeroThree.conclusion shouldBe proposition(
      s"NUM_PROV (NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR (NUM_NUMERAL ZERO) (NUM_NUMERAL ($three)))))")
  }

  /**
   * The two facts an implication between closed formulas needs beyond `NUM_PROV_WEAKEN`, at the
   * smallest closed equations that tell them apart: `0 = 0` holds and `1 = 0` does not, so the
   * implication from the first to the second is refuted. Ex falso is taken from `1 = 0` to `0 = 1`,
   * whose consequent is false as well, because that fact already reaches every implication with a
   * provable consequent and an instance it reaches would not tell the new fact from it.
   */
  it should "decide an implication between closed equations, refuted by tollens and held by ex falso" in {
    val language = chain.language
    val notZero = force(chain.naturals.fact(Natural.SuccessorNotZero))
    val zero = term("NUM_NUMERAL ZERO")
    val one = term("NUM_NUMERAL (SUC ZERO)")
    def equation(a: Term, b: Term): Term =
      applied(coding, List(term("5"), applied(pairing, List(a, b))))
    def numeralIsTerm(n: String): Kernel.Thm =
      force(rules.spec(term(n), force(language.fact(Language.NumeralIsTerm))))
    def formulaOf(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
      force(rules.specAll(force(language.fact(Language.FormulaEquality)), List(a, b))
        .flatMap(rules.mp(_, left)).flatMap(rules.mp(_, right)))

    val same = equation(zero, zero)
    val apart = equation(one, zero)
    val flipped = equation(zero, one)
    val formulaSame = formulaOf(zero, zero, numeralIsTerm("ZERO"), numeralIsTerm("ZERO"))
    val formulaApart = formulaOf(one, zero, numeralIsTerm("SUC ZERO"), numeralIsTerm("ZERO"))
    val formulaFlipped = formulaOf(zero, one, numeralIsTerm("ZERO"), numeralIsTerm("SUC ZERO"))
    val holds = force(rules.spec(zero, force(deduction.fact(Deduction.Reflexivity)))
      .flatMap(rules.mp(_, numeralIsTerm("ZERO"))))
    val denied = force(rules.specAll(force(deduction.fact(Deduction.NumeralsDistinct)),
      List(term("SUC ZERO"), term("ZERO"))).flatMap(rules.mp(_, force(rules.spec(term("ZERO"), notZero)))))

    val refuted = force(rules.specAll(force(deduction.fact(Deduction.DeniedImplication)), List(same, apart))
      .flatMap(rules.mp(_, formulaSame)).flatMap(rules.mp(_, formulaApart))
      .flatMap(rules.mp(_, holds)).flatMap(rules.mp(_, denied)))
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(
      "NUM_PROV (NUM_CODE 6 (NUM_CODE 7 (NUM_PAIR " +
        "(NUM_CODE 5 (NUM_PAIR (NUM_NUMERAL ZERO) (NUM_NUMERAL ZERO))) " +
        "(NUM_CODE 5 (NUM_PAIR (NUM_NUMERAL (SUC ZERO)) (NUM_NUMERAL ZERO))))))")

    val held = force(rules.specAll(force(deduction.fact(Deduction.ImplicationOfDenial)), List(apart, flipped))
      .flatMap(rules.mp(_, formulaApart)).flatMap(rules.mp(_, formulaFlipped)).flatMap(rules.mp(_, denied)))
    held.hypotheses shouldBe empty
    held.conclusion shouldBe proposition(
      "NUM_PROV (NUM_CODE 7 (NUM_PAIR " +
        "(NUM_CODE 5 (NUM_PAIR (NUM_NUMERAL (SUC ZERO)) (NUM_NUMERAL ZERO))) " +
        "(NUM_CODE 5 (NUM_PAIR (NUM_NUMERAL ZERO) (NUM_NUMERAL (SUC ZERO))))))")

    Derivation.axiomsOf(refuted) should have size 2
    Derivation.axiomsOf(held) should have size 2
  }

  /**
   * PA proves `1 < 3` between numerals, and the code is the existential the order abbreviates.
   *
   * The strict order is a pair of numbers apart by two rather than by one, so the witness is
   * `numeral 1` and not zero, which is the case a witness wired to `0` would get right by accident.
   * The antecedent is derived from the naturals' own order rather than assumed, so the instance is
   * about something. The conclusion is compared twice: as `NUM_LESS`, which is what the fact
   * states, and opened by `NUM_LESS_CASES` into `~!5. ~(numeral 1 + S v5 = numeral 3)`, which is
   * what [[Deduction.ExistentialIntroduction]] put there.
   */
  it should "prove a true strict order between numerals by introducing its witness" in {
    val theorem = force(deduction.fact(Deduction.NumeralsOrdered))
    theorem.hypotheses shouldBe empty
    Derivation.axiomsOf(theorem) should have size 2
    Derivation.axiomsOf(force(deduction.fact(Deduction.ExistentialIntroduction))) should have size 2

    val peano = chain.peano
    val one = "SUC ZERO"
    val two = "SUC (SUC ZERO)"
    val three = "SUC (SUC (SUC ZERO))"
    val oneTwo = force(rules.spec(term(one), force(peano.fact(Peano.BelowSuccessor))))
    val twoThree = force(rules.spec(term(two), force(peano.fact(Peano.BelowSuccessor))))
    val oneThree = force(
      rules
        .specAll(force(peano.fact(Peano.StrictTransitive)), List(term(one), term(two), term(three)))
        .flatMap(implication => rules.conjIntro(oneTwo, twoThree).flatMap(rules.mp(implication, _))))
    val instance = force(rules.specAll(theorem, List(term("5"), term(one), term(three)))
      .flatMap(rules.mp(_, oneThree)))
    instance.hypotheses shouldBe empty
    instance.conclusion shouldBe proposition(
      s"NUM_PROV (NUM_LESS 5 (NUM_NUMERAL ($one)) (NUM_NUMERAL ($three)))")

    val opened = force(
      rules
        .specAll(force(chain.language.fact(Language.LessCases)),
          List(term("5"), term(s"NUM_NUMERAL ($one)"), term(s"NUM_NUMERAL ($three)")))
        .flatMap(Conv.apTerm(constant(Provability.ProvableName, Type.fun(numbers, Type.Bool)), _))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance))))
    opened.conclusion shouldBe proposition(
      s"NUM_PROV (NUM_EXISTS 5 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 3 (NUM_PAIR " +
        s"(NUM_NUMERAL ($one)) (NUM_CODE 2 (NUM_CODE 0 5)))) (NUM_NUMERAL ($three)))))")
  }

  /**
   * The object theory's multiplication on numerals, which stands on the addition above it.
   *
   * The same two assertions for the same two reasons, and one more that is about the ORDER rather
   * than about this theorem: the step of this induction turns `t * S u` into `t * u + t` and then
   * needs `numeral (m * k) + numeral m` to be a numeral, which is exactly what
   * `NUM_PROV_NUMERAL_ADD` says. So the second brick cannot be laid before the first, and the
   * `restingOn` assertion below is what says it really was laid on it rather than beside it.
   */
  it should "prove its own multiplication on numerals, at the naturals' cost" in {
    val theorem = force(deduction.fact(Deduction.NumeralMultiplication))
    theorem.hypotheses shouldBe empty
    Derivation.axiomsOf(theorem) should have size 2

    val instance = force(rules.specAll(theorem, List(term("SUC (SUC ZERO)"), term("SUC ZERO"))))
    instance.hypotheses shouldBe empty
    instance.conclusion shouldBe proposition(
      "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 4 (NUM_PAIR (NUM_NUMERAL (SUC (SUC ZERO))) (NUM_NUMERAL (SUC ZERO)))) " +
        "(NUM_NUMERAL (NUM_MUL (SUC (SUC ZERO)) (SUC ZERO)))))")

    // And it rests on the addition brick, which is the claim the file makes about the order. A
    // derivation that had reached the same statement without it would pass both assertions above.
    val addition = force(deduction.fact(Deduction.NumeralAddition))
    Derivation.restingOn(theorem, Set(addition.conclusion)) should contain(addition.conclusion)
  }

  /**
   * The two axioms of multiplication put to work, which is what the induction above is made of.
   *
   * They are asserted apart from it because they are the pieces a reader checks by eye: the second
   * is the one whose substitution descends through a sum AND a product, where addition's descends
   * through a sum alone, and an error there would show as a code that is not the axiom's.
   */
  it should "put both multiplication axioms to work at closed terms" in {
    val zero = force(deduction.fact(Deduction.MultiplicationAtZero))
    val successor = force(deduction.fact(Deduction.MultiplicationAtSuccessor))

    Derivation.axiomsOf(zero) should have size 2
    Derivation.axiomsOf(successor) should have size 2

    val numeral = term("NUM_NUMERAL (SUC ZERO)")
    val isTerm = force(rules.spec(term("SUC ZERO"), force(chain.language.fact(Language.NumeralIsTerm))))
    val isClosed =
      force(rules.spec(term("SUC ZERO"), force(chain.language.fact(Language.NumeralIsClosed))))

    val atZero = force(
      rules.specAll(zero, List(numeral)).flatMap(rules.mp(_, isTerm)).flatMap(rules.mp(_, isClosed)))
    atZero.conclusion shouldBe proposition(
      "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 4 (NUM_PAIR (NUM_NUMERAL (SUC ZERO)) (NUM_CODE 1 0))) (NUM_CODE 1 0)))")

    val atSuccessor = force(
      rules
        .specAll(successor, List(numeral, numeral))
        .flatMap(rules.mp(_, isTerm))
        .flatMap(rules.mp(_, isClosed))
        .flatMap(rules.mp(_, isTerm))
        .flatMap(rules.mp(_, isClosed)))
    atSuccessor.conclusion shouldBe proposition(
      "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 4 (NUM_PAIR (NUM_NUMERAL (SUC ZERO)) (NUM_CODE 2 (NUM_NUMERAL (SUC ZERO))))) " +
        "(NUM_CODE 3 (NUM_PAIR " +
        "(NUM_CODE 4 (NUM_PAIR (NUM_NUMERAL (SUC ZERO)) (NUM_NUMERAL (SUC ZERO)))) " +
        "(NUM_NUMERAL (SUC ZERO))))))")
  }

  it should "carry an object theorem across its own equality" in {
    val language = chain.language
    val numeral = term("NUM_NUMERAL m")
    val zeroCode = term("NUM_CODE 1 0")
    val sum = term("NUM_CODE 3 (NUM_PAIR (NUM_NUMERAL m) (NUM_CODE 1 0))")

    // `numeral m + 0` is a term.
    val sumIsTerm = force(
      rules
        .specAll(force(language.fact(Language.TermSum)), List(numeral, zeroCode))
        .flatMap(rules.mp(_, force(rules.spec(term("m"), force(language.fact(Language.NumeralIsTerm))))))
        .flatMap(rules.mp(_, force(language.fact(Language.TermZero))))
    )

    // And it is closed: at any index, neither half is free in it.
    val index = Term.variable("k", numbers)
    val closedNumeral = force(
      rules
        .spec(numeral, force(language.fact(Language.ClosedCases)))
        .flatMap(equation =>
          LogicError.lift(Kernel.eqMp(
            equation,
            force(rules.spec(term("m"), force(language.fact(Language.NumeralIsClosed)))))))
        .flatMap(rules.spec(index, _))
    )
    val notInZero = force(
      rules
        .spec(index, force(language.fact(Language.FreeZero)))
        .flatMap(equation =>
          LogicError
            .lift(Kernel.assume(Term.destEq(equation.conclusion).map(_._1).getOrElse(fail("an equation"))))
            .flatMap(assumedFree => LogicError.lift(Kernel.eqMp(equation, assumedFree)))
            .flatMap(rules.notIntro(
              Term.destEq(equation.conclusion).map(_._1).getOrElse(fail("an equation")), _)))
    )
    val neitherHalf = force(
      rules
        .conjIntro(closedNumeral, notInZero)
        .flatMap(both =>
          force(chain.classical.fact(Classical.DeMorganDisjunction)) match {
            case law =>
              rules
                .specAll(law, List(
                  force(logic.destNot(closedNumeral.conclusion).toRight(NotOfForm("a negation", closedNumeral.conclusion))),
                  force(logic.destNot(notInZero.conclusion).toRight(NotOfForm("a negation", notInZero.conclusion)))))
                .flatMap(Conv.sym)
                .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, both)))
          })
    )
    val sumIsClosed = force(
      rules
        .specAll(force(language.fact(Language.FreeSum)), List(index, numeral, zeroCode))
        .flatMap(clause =>
          LogicError
            .lift(language.theory.constant(Logic.Negation, Type.fun(Type.Bool, Type.Bool)))
            .flatMap(negation => Conv.apTerm(negation, clause))
            .flatMap(Conv.sym)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, neitherHalf))))
        .flatMap(rules.gen(index, _))
        .flatMap(nowhere =>
          rules
            .spec(sum, force(language.fact(Language.ClosedCases)))
            .flatMap(Conv.sym)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, nowhere))))
    )
    sumIsClosed.hypotheses shouldBe empty
    sumIsClosed.conclusion shouldBe proposition(
      "NUM_CLOSED (NUM_CODE 3 (NUM_PAIR (NUM_NUMERAL m) (NUM_CODE 1 0)))")

    // The object theorem this file already reaches, turned around.
    val forwards = provesNumeralAddition
    val backwards = force(
      rules
        .specAll(force(deduction.fact(Deduction.Symmetry)), List(sum, numeral))
        .flatMap(rules.mp(_, sumIsTerm))
        .flatMap(rules.mp(_, force(rules.spec(term("m"), force(language.fact(Language.NumeralIsTerm))))))
        .flatMap(rules.mp(_, sumIsClosed))
        .flatMap(rules.mp(_, force(rules.spec(term("m"), force(language.fact(Language.NumeralIsClosed))))))
        .flatMap(rules.mp(_, forwards))
    )

    backwards.hypotheses shouldBe empty
    backwards.conclusion shouldBe proposition(
      "NUM_PROV (NUM_CODE 5 (NUM_PAIR (NUM_NUMERAL m) " +
        "(NUM_CODE 3 (NUM_PAIR (NUM_NUMERAL m) (NUM_CODE 1 0)))))")
    Derivation.axiomsOf(backwards) should have size 2
  }

  /**
   * `|- NUM_PROV (code of numeral m + 0 = numeral m)`, derived once and asserted by two tests.
   *
   * Shared rather than repeated because the second test carries it across the object theory's own
   * equality, and a second copy of a derivation is the thing this repository deletes on sight.
   */
  private lazy val provesNumeralAddition: Kernel.Thm = {
    val language = chain.language
    val numeral = term("NUM_NUMERAL m")
    val index = term("0")
    val body = term(
      "NUM_CODE 5 (NUM_PAIR (NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0))) (NUM_CODE 0 0))")

    val axiom = force(language.fact("NUM_PA_ADD_ZERO"))
    val quantified = axiom.conclusion match {
      case App(_, argument) => argument
      case other => fail(s"not a membership: $other")
    }

    // PA proves its own axioms, by the derivation that is one line long.
    val provesTheAxiom = force(
      rules
        .spec(quantified, force(chain.provability.fact(Provability.ProvablePeano)))
        .flatMap(rules.mp(_, axiom))
    )

    // The three side conditions. The body is a formula by two introduction rules; the numeral is a
    // term and is closed, both from the library rather than by hand.
    val variableIsTerm = force(rules.spec(index, force(language.fact(Language.TermVariable))))
    val sumIsTerm = force(
      rules
        .specAll(force(language.fact(Language.TermSum)),
          List(term("NUM_CODE 0 0"), term("NUM_CODE 1 0")))
        .flatMap(rules.mp(_, variableIsTerm))
        .flatMap(rules.mp(_, force(language.fact(Language.TermZero))))
    )
    val bodyIsFormula = force(
      rules
        .specAll(force(language.fact(Language.FormulaEquality)),
          List(term("NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0))"), term("NUM_CODE 0 0")))
        .flatMap(rules.mp(_, sumIsTerm))
        .flatMap(rules.mp(_, variableIsTerm))
    )

    val specialised = force(
      rules
        .specAll(force(deduction.fact(Deduction.Specialisation)), List(index, numeral, body))
        .flatMap(rules.mp(_, bodyIsFormula))
        .flatMap(rules.mp(_, force(rules.spec(term("m"), force(language.fact(Language.NumeralIsTerm))))))
        .flatMap(rules.mp(_, force(rules.spec(term("m"), force(language.fact(Language.NumeralIsClosed))))))
        .flatMap(rules.mp(_, provesTheAxiom))
    )

    // Without this the conclusion is a number nobody can read as a formula.
    val computed = force(language.substituteIn(index, numeral, body))
    val provable = constant(Provability.ProvableName, Type.fun(numbers, Type.Bool))
    val reached = force(
      Conv
        .apTerm(provable, computed)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, specialised)))
    )


    reached
  }

  it should "prove its own arithmetic at a numeral, which nothing could state before" in {
    val reached = provesNumeralAddition
    reached.hypotheses shouldBe empty
    reached.conclusion shouldBe proposition(
      "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 3 (NUM_PAIR (NUM_NUMERAL m) (NUM_CODE 1 0))) (NUM_NUMERAL m)))")
    Derivation.axiomsOf(reached) should have size 2
  }



  /**
   * What a derivation of the embedded theory costs, which is what everything above it costs.
   *
   * An equality and not a ceiling, the way `CodingSpec` and `LanguageSpec` state theirs. Two is
   * what the naturals cost, choice and infinity, and a layer that started spending anything else
   * would be spending it on the embedded theory's behalf, which is the one number this whole
   * development is not allowed to move.
   */
  it should "cost what the naturals cost and nothing else" in {
    Deduction.Statements.foreach { case (name, _) =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(force(deduction.fact(name))) should have size 2
      }
    }
  }

  /**
   * It declares nothing, which is what makes it the first link that is not an extension.
   *
   * `docs/adr/0013` asks for a development whose product is object-level derivations, and the
   * measurable consequence is here: the theory it hands on is the one it was given, constant for
   * constant. If a definition ever lands in this file the assertion goes red, which is the moment
   * to decide whether it belongs here or one floor down.
   */
  it should "extend the theory it was built over by nothing at all" in {
    deduction.theory.constants shouldBe chain.provability.theory.constants
    deduction.theory.axioms shouldBe chain.provability.theory.axioms
  }

  /**
   * The deduction theorem at a concrete formula, with nothing left assumed.
   *
   * Both of its conditions are discharged here rather than carried: `NUM_FORM h` from
   * `NUM_PA_FORM`, and `!i. ~(NUM_FREE_FORM i h)` from `Language.notFreeIn`, which walks the code.
   * The second is why this test can exist at all. Until that walk landed, the theorem was proved
   * and applied to no formula anybody could name, and this file said so where this docstring now
   * says the opposite.
   *
   * The derivation it consumes is the smallest there is, the one line that **is** `h`, built from
   * `NUM_BETA_SEQUENCE` the way every inhabitation in `Provability` is. What comes out is
   * `NUM_PROV (h ==> h)` with **no hypotheses**, which is the whole point: a closed theorem about a
   * particular formula of the embedded theory, reached through the deduction theorem rather than
   * around it.
   *
   * `NUM_PROV_SELF` gives the same conclusion directly, and the agreement is the assertion rather
   * than a redundancy: this route exercises both definitions, the induction and the hypothesis
   * case, and the direct one touches none of them.
   */
  it should "apply at a concrete formula, with both of its conditions discharged" in {
    val axiom = force(chain.language.fact("NUM_PA_SUC_NOT_ZERO"))
    val h = axiom.conclusion match {
      case App(_, argument) => argument
      case other => fail(s"a claim about a code was expected, found $other")
    }

    val formulaH = force(
      rules
        .spec(h, force(chain.language.fact(Language.AxiomFormula)))
        .flatMap(rules.mp(_, axiom)))
    val notFree = force(chain.language.notFreeIn(h))

    val zero = term("ZERO")
    val one = term("SUC ZERO")

    // The sequence whose only entry is `h`, taken up to one.
    val constantSequence = force(LogicError.lift(Term.abs(Term.variable("j", numbers), h)))
    val taken = force(
      rules.specAll(force(chain.coding.fact(Coding.BetaSequence)), List(constantSequence, one)))
    val opened = force(
      Conv.betaNormalise(taken.conclusion)
        .flatMap(step => LogicError.lift(Kernel.eqMp(step, taken))))

    def openOne(existential: Kernel.Thm, name: String, avoid: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val inner = logic.destExistsPredicate(existential.conclusion)
        .getOrElse(fail("an existential was expected"))
      val fresh = Conv.freshVariable(
        name, numbers, avoid ++ Term.freeVariables(existential.conclusion))
      val body = Term
        .destEq(force(Conv.betaRoot(applied(inner, List(fresh)))).conclusion)
        .map(_._2)
        .getOrElse(fail("an equation was expected"))
      force(rules.existsElim(existential, fresh,
        reach(fresh, force(LogicError.lift(Kernel.assume(body))))))
    }

    val reached = openOne(opened, "a", Set.empty) { (a, atA) =>
      openOne(atA, "b", Set(a)) { (b, atB) =>
        // The entry at zero is `h`, since zero is below one.
        val here = force(
          rules
            .spec(zero, atB)
            .flatMap(rules.mp(_, force(
              rules.spec(zero, force(chain.peano.fact(Peano.SuccessorPositive)))))))

        // So the step at zero is justified by being the hypothesis, and it is a formula.
        val stepCases = force(
          rules.specAll(force(chain.provability.fact(Provability.StepFromCases)),
            List(h, a, b, zero)))
        val body = Term.destEq(stepCases.conclusion).map(_._2).getOrElse(fail("an equation"))
        val (_, choice) = logic.destConj(body).getOrElse(fail("a conjunction"))

        val formulaHere = force(
          Conv
            .apTerm(constant(Language.FormulaName, Type.fun(numbers, Type.Bool)), here)
            .flatMap(Conv.sym)
            .flatMap(step => LogicError.lift(Kernel.eqMp(step, formulaH))))
        val justified = force(
          rules
            .conjIntro(formulaHere, force(rules.disjIntro2(
              logic.destDisj(choice).map(_._1).getOrElse(fail("a disjunction")), here)))
            .flatMap(pair => Conv.sym(stepCases)
              .flatMap(step => LogicError.lift(Kernel.eqMp(step, pair)))))

        // Every index at most zero is zero, so that one step is the whole derivation.
        val marker = Term.variable("j", numbers)
        val boundTerm = proposition("NUM_LE j ZERO")
        val bounded = force(LogicError.lift(Kernel.assume(boundTerm)))
        val isZero = force(
          rules
            .spec(marker, force(chain.peano.fact(Peano.AtMostZero)))
            .flatMap(rules.mp(_, bounded)))
        val everyStep = force(
          Conv
            .apTerm(
              applied(
                constant(Provability.StepFromName,
                  Type.fun(numbers, Type.fun(numbers, Type.fun(numbers,
                    Type.fun(numbers, Type.Bool))))),
                List(h, a, b)),
              isZero)
            .flatMap(Conv.sym)
            .flatMap(step => LogicError.lift(Kernel.eqMp(step, justified)))
            .flatMap(rules.disch(boundTerm, _))
            .flatMap(rules.gen(marker, _)))

        val fromCases = force(
          rules.specAll(force(chain.provability.fact(Provability.ProvableFromCases)), List(h, h)))
        val fromBody = Term.destEq(fromCases.conclusion).map(_._2).getOrElse(fail("an equation"))

        def instantiate(existential: Term, argument: Term): Term = {
          val inner = logic.destExistsPredicate(existential).getOrElse(fail("an existential"))
          Term
            .destEq(force(Conv.betaRoot(applied(inner, List(argument)))).conclusion)
            .map(_._2)
            .getOrElse(fail("an equation"))
        }
        val atLength = instantiate(fromBody, zero)
        val atFirst = instantiate(atLength, a)

        def under(existential: Term, witness: Term, proof: Kernel.Thm): Kernel.Thm =
          force(rules.existsIntro(
            logic.destExistsPredicate(existential).getOrElse(fail("an existential")),
            witness, proof))

        val derivation = force(
          rules
            .conjIntro(here, everyStep)
            .map(pair => under(fromBody, zero, under(atLength, a, under(atFirst, b, pair))))
            .flatMap(packed => Conv.sym(fromCases)
              .flatMap(step => LogicError.lift(Kernel.eqMp(step, packed)))))

        force(
          rules
            .specTo(
              force(deduction.fact(Deduction.DeductionTheorem)),
              imply(isFormula(h), imply(notFree.conclusion,
                imply(applied(
                  constant(Provability.ProvableFromName,
                    Type.fun(numbers, Type.fun(numbers, Type.Bool))),
                  List(h, h)), isProvable(imp(h, h))))))
            .flatMap(rules.mp(_, formulaH))
            .flatMap(rules.mp(_, notFree))
            .flatMap(rules.mp(_, derivation)))
      }
    }

    reached.hypotheses shouldBe empty
    reached.conclusion shouldBe isProvable(imp(h, h))
    Derivation.axiomsOf(reached) should have size 2

    // The direct route agrees, which is what makes this a check of the long one.
    val direct = force(
      rules
        .specTo(force(deduction.fact(Deduction.SelfImplication)),
          imply(isFormula(h), isProvable(imp(h, h))))
        .flatMap(rules.mp(_, formulaH)))
    direct.conclusion shouldBe reached.conclusion
  }

  /**
   * The deduction theorem's rules, composed into something neither gives alone.
   *
   * `NUM_PROV_WEAKEN` and `NUM_PROV_IMP_MP` are checked against their statements above. What that
   * does not say is that they fit together, which is the only reason either exists: the deduction
   * theorem's induction applies the first at its axiom cases and the second at its modus ponens
   * case, and if the shapes did not meet the induction would not close.
   *
   * So this does one step of that induction by hand. `A ==> (C ==> A)` is weakening and therefore
   * provable; carried under `B` it is `B ==> (A ==> (C ==> A))`. `A` is an axiom, so `B ==> A` is
   * provable the same way. Modus ponens under the hypothesis `B` then detaches `A` and leaves
   * `B ==> (C ==> A)`, which is not an axiom of either set and is not reachable by weakening alone.
   *
   * The three codes are distinct axioms, so a rule that returned one of its arguments rather than
   * their composition has three wrong answers available and the assertion below rejects them.
   *
   * What is **not** asserted here, and it is the third rule: `NUM_PROV_IMP_GEN` is not exercised at
   * a concrete code, because its side condition is `~(NUM_FREE_FORM i h)` and discharging that for
   * a particular `h` means walking the code through the freeness clauses. The rule is checked
   * against its statement like the others; that its side condition is satisfiable at a real code is
   * work the deduction theorem itself will have to do.
   */
  it should "compose weakening with modus ponens under a hypothesis, which is one step of the induction" in {
    val axioms = Vector("NUM_PA_SUC_NOT_ZERO", "NUM_PA_ADD_ZERO", "NUM_PA_MUL_ZERO")
      .map(name => force(chain.language.fact(name)))

    def codeOf(member: Kernel.Thm): Term = member.conclusion match {
      case App(_, argument) => argument
      case other => fail(s"a claim about a code was expected, found $other")
    }

    val Vector(first, second, third) = axioms.map(codeOf)
    Vector(first, second, third).distinct should have size 3

    val areFormulas = force(chain.language.fact(Language.AxiomFormula))
    def formula(member: Kernel.Thm): Kernel.Thm =
      force(rules.spec(codeOf(member), areFormulas).flatMap(rules.mp(_, member)))

    def provableAxiom(member: Kernel.Thm): Kernel.Thm =
      force(
        rules
          .spec(codeOf(member), force(chain.provability.fact(Provability.ProvablePeano)))
          .flatMap(rules.mp(_, member))
      )

    def carriedUnder(hypothesis: Term, held: Kernel.Thm, subject: Term, form: Kernel.Thm)
      : Kernel.Thm =
      force(
        rules
          .specTo(
            force(deduction.fact(Deduction.Weaken)),
            imply(
              isFormula(hypothesis),
              imply(isFormula(subject), imply(isProvable(subject), isProvable(imp(hypothesis, subject))))))
          .flatMap(rules.mp(_, formula(axioms(1))))
          .flatMap(rules.mp(_, form))
          .flatMap(rules.mp(_, held))
      )

    // `A ==> (C ==> A)` is weakening, hence provable.
    val weakened = imp(first, imp(third, first))
    val weakeningIsLogical = force(
      rules
        .specTo(
          force(chain.language.fact("NUM_LOGIC_WEAKEN")),
          imply(isFormula(first), imply(isFormula(third), isLogical(weakened))))
        .flatMap(rules.mp(_, formula(axioms(0))))
        .flatMap(rules.mp(_, formula(axioms(2))))
    )
    val weakeningIsProvable = force(
      rules
        .spec(weakened, force(chain.provability.fact(Provability.ProvableLogic)))
        .flatMap(rules.mp(_, weakeningIsLogical))
    )

    val formulaOfWeakened = force(
      rules
        .specTo(
          force(chain.language.fact("NUM_FORM_IMP")),
          imply(
            isFormula(first),
            imply(isFormula(imp(third, first)), isFormula(weakened))))
        .flatMap(rules.mp(_, formula(axioms(0))))
        .flatMap(rules.mp(_, force(
          rules
            .specTo(
              force(chain.language.fact("NUM_FORM_IMP")),
              imply(isFormula(third), imply(isFormula(first), isFormula(imp(third, first)))))
            .flatMap(rules.mp(_, formula(axioms(2))))
            .flatMap(rules.mp(_, formula(axioms(0)))))))
    )

    val underB = carriedUnder(second, weakeningIsProvable, weakened, formulaOfWeakened)
    val antecedent = carriedUnder(second, provableAxiom(axioms(0)), first, formula(axioms(0)))

    val detached = force(
      rules
        .specTo(
          force(deduction.fact(Deduction.ImplicationModusPonens)),
          imply(
            isFormula(second),
            imply(
              isFormula(first),
              imply(
                isFormula(imp(third, first)),
                imply(
                  isProvable(imp(second, imp(first, imp(third, first)))),
                  imply(
                    isProvable(imp(second, first)),
                    isProvable(imp(second, imp(third, first)))))))))
        .flatMap(rules.mp(_, formula(axioms(1))))
        .flatMap(rules.mp(_, formula(axioms(0))))
        .flatMap(rules.mp(_, force(
          rules
            .specTo(
              force(chain.language.fact("NUM_FORM_IMP")),
              imply(isFormula(third), imply(isFormula(first), isFormula(imp(third, first)))))
            .flatMap(rules.mp(_, formula(axioms(2))))
            .flatMap(rules.mp(_, formula(axioms(0)))))))
        .flatMap(rules.mp(_, underB))
        .flatMap(rules.mp(_, antecedent))
    )

    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe isProvable(imp(second, imp(third, first)))
    detached.conclusion should not be isProvable(imp(second, first))
    detached.conclusion should not be isProvable(weakened)
    Derivation.axiomsOf(detached) should have size 2
  }

  /**
   * Three axioms chained into one implication, which is the assertion that the layer is usable.
   *
   * `B` is provable because it is an axiom, so weakening gives `NUM_PROV (A ==> B)`; the same for
   * `C` gives `NUM_PROV (B ==> C)`; and the syllogism composes them. Everything below has to hold
   * together for that to come out: the membership facts, `NUM_PA_FORM` for the side conditions,
   * `NUM_LOGIC_WEAKEN`, `NUM_PROV_LOGIC`, `NUM_PROV_MP` inside the syllogism, and the syllogism
   * itself.
   *
   * The identity is checked at the same `A`, and it is the one place a reader can see that a
   * scheme proved over a variable formula really does apply to a code.
   */
  it should "chain three concrete axioms into an implication none of them is" in {
    val axioms = Vector("NUM_PA_SUC_NOT_ZERO", "NUM_PA_ADD_ZERO", "NUM_PA_MUL_ZERO")
      .map(name => force(chain.language.fact(name)))

    def codeOf(member: Kernel.Thm): Term = member.conclusion match {
      case App(_, argument) => argument
      case other => fail(s"a claim about a code was expected, found $other")
    }

    val Vector(first, second, third) = axioms.map(codeOf)
    Vector(first, second, third).distinct should have size 3

    val areFormulas = force(chain.language.fact(Language.AxiomFormula))
    def formula(member: Kernel.Thm): Kernel.Thm =
      force(rules.spec(codeOf(member), areFormulas).flatMap(rules.mp(_, member)))

    def provableAxiom(member: Kernel.Thm): Kernel.Thm =
      force(
        rules
          .spec(codeOf(member), force(chain.provability.fact(Provability.ProvablePeano)))
          .flatMap(rules.mp(_, member))
      )

    /** `NUM_PROV (x ==> y)` whenever `y` is provable, by weakening it under `x`. */
    def weakenedTo(x: Term, member: Kernel.Thm): Kernel.Thm = {
      val y = codeOf(member)
      val code = imp(y, imp(x, y))
      val logical = force(
        rules
          .specTo(
            force(chain.language.fact("NUM_LOGIC_WEAKEN")),
            imply(isFormula(y), imply(isFormula(x), isLogical(code))))
          .flatMap(rules.mp(_, formula(member)))
          .flatMap(rules.mp(_, formula(axioms.find(other => codeOf(other) == x).getOrElse(
            fail("the antecedent has to be one of the three axioms")))))
      )
      val provable = force(
        rules
          .spec(code, force(chain.provability.fact(Provability.ProvableLogic)))
          .flatMap(rules.mp(_, logical))
      )
      force(
        rules
          .specTo(
            force(chain.provability.fact(Provability.ModusPonens)),
            imply(isProvable(code), imply(isProvable(y), isProvable(imp(x, y)))))
          .flatMap(rules.mp(_, provable))
          .flatMap(rules.mp(_, provableAxiom(member)))
      )
    }

    val firstStep = weakenedTo(first, axioms(1))
    val secondStep = weakenedTo(second, axioms(2))
    firstStep.conclusion shouldBe isProvable(imp(first, second))
    secondStep.conclusion shouldBe isProvable(imp(second, third))

    val chained = force(
      rules
        .specTo(
          force(deduction.fact(Deduction.Syllogism)),
          imply(
            isFormula(first),
            imply(
              isFormula(second),
              imply(
                isFormula(third),
                imply(
                  isProvable(imp(first, second)),
                  imply(isProvable(imp(second, third)), isProvable(imp(first, third)))))))
        )
        .flatMap(rules.mp(_, formula(axioms(0))))
        .flatMap(rules.mp(_, formula(axioms(1))))
        .flatMap(rules.mp(_, formula(axioms(2))))
        .flatMap(rules.mp(_, firstStep))
        .flatMap(rules.mp(_, secondStep))
    )

    chained.hypotheses shouldBe empty
    chained.conclusion shouldBe isProvable(imp(first, third))
    chained.conclusion should not be isProvable(imp(first, second))
    chained.conclusion should not be isProvable(imp(second, third))
    Derivation.axiomsOf(chained) should have size 2

    val identity = force(
      rules
        .specTo(
          force(deduction.fact(Deduction.SelfImplication)),
          imply(isFormula(first), isProvable(imp(first, first))))
        .flatMap(rules.mp(_, formula(axioms(0))))
    )
    identity.hypotheses shouldBe empty
    identity.conclusion shouldBe isProvable(imp(first, first))
    Derivation.axiomsOf(identity) should have size 2
  }
}
