package garden.xeno.symbolum.logic

import org.scalacheck.Gen
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks
import garden.xeno.symbolum.kernel.*

/**
 * The derived rules over arbitrary formulas rather than the two or three anyone would pick.
 *
 * A rule that unfolds a definition and matches a theorem against the result is sensitive to the
 * shape of what it is given: a nested connective, a negation where a variable was expected, a
 * formula deep enough that normalisation has somewhere to go. Example tests fix the shapes
 * someone imagined. These generate them.
 *
 * The last property is the one that pays for itself. Printing and parsing are separate pieces of
 * code with no shared representation of precedence, so asking that every generated formula
 * survives a round trip is a check on both at once: a precedence mistake in either shows up as a
 * formula that comes back different.
 */
class RulesPropertySpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {

  /**
   * ScalaTest's default is ten cases, which is a smoke test rather than a property check.
   *
   * The count below was measured, before 2026-09-14 where this repository's history begins: the
   * slowest property took about five seconds at it, because each case runs a real derivation
   * through the kernel, and the module's whole suite took sixteen. That is the budget these are
   * worth; a higher count belongs in a slower gate rather than in this one.
   */
  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 200)

  private val logic = Logic.standard
  private val rules = logic.rules

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val atoms: Vector[Term] = Vector("p", "q", "r").map(Term.variable(_, Type.Bool))

  private def propositionOf(depth: Int): Gen[Term] =
    if (depth <= 0) Gen.oneOf(atoms)
    else
      Gen.frequency(
        (3, Gen.oneOf(atoms)),
        (2, for {
          left <- propositionOf(depth - 1)
          right <- propositionOf(depth - 1)
        } yield force(logic.mkConj(left, right))),
        (2, for {
          left <- propositionOf(depth - 1)
          right <- propositionOf(depth - 1)
        } yield force(logic.mkImp(left, right))),
        (1, for {
          left <- propositionOf(depth - 1)
          right <- propositionOf(depth - 1)
        } yield force(logic.mkDisj(left, right))),
        (1, propositionOf(depth - 1).map(inner => force(logic.mkNot(inner))))
      )

  private val propositions: Gen[Term] = propositionOf(3)

  "Discharge and detachment" should "undo each other over any pair of formulas" in {
    forAll(propositions, propositions) { (antecedent, consequent) =>
      val theorem = for {
        implication <- rules.disch(antecedent, force(Kernel.assume(consequent)))
        detached <- rules.mp(implication, force(Kernel.assume(antecedent)))
      } yield detached

      force(theorem).conclusion shouldBe consequent
    }
  }

  "Conjunction" should "give back both of the formulas it was built from" in {
    forAll(propositions, propositions) { (left, right) =>
      val introduced =
        force(rules.conjIntro(force(Kernel.assume(left)), force(Kernel.assume(right))))

      force(rules.conjElim1(introduced)).conclusion shouldBe left
      force(rules.conjElim2(introduced)).conclusion shouldBe right
    }
  }

  "Generalisation" should "specialise back to the formula it generalised" in {
    forAll(propositions) { proposition =>
      val variable = Term.variable("w", Type.Bool)
      val general = force(rules.gen(variable, force(Kernel.assume(proposition))))

      force(rules.spec(variable, general)).conclusion shouldBe proposition
    }
  }

  "Negation" should "contradict the formula it denies, whatever that formula is" in {
    forAll(propositions) { proposition =>
      val negated = force(logic.mkNot(proposition))
      val contradiction =
        rules.notElim(force(Kernel.assume(negated)), force(Kernel.assume(proposition)))

      force(contradiction).conclusion shouldBe logic.falsity
    }
  }

  "A formula" should "survive being printed and read back" in {
    forAll(propositions) { proposition =>
      Parser.proposition(logic.theory, Show.show(proposition)) shouldBe Right(proposition)
    }
  }
}
