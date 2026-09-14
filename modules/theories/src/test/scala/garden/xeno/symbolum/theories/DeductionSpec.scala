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
   * What a derivation of the embedded theory costs, which is what everything above it costs.
   *
   * An equality and not a ceiling, the way `CodingSpec` and `LanguageSpec` state theirs. Two is
   * what the naturals cost, choice and infinity, and a layer that started spending anything else
   * would be spending it on the embedded theory's behalf, which is the one number this whole
   * development is not allowed to move.
   */
  it should "cost the naturals' two axioms and nothing else" in {
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
    chain.widest.theory.constants shouldBe chain.provability.theory.constants
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
