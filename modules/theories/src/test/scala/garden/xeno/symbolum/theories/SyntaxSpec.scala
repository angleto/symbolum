package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The terms of Peano arithmetic as a type, which is [[Datatype]]'s consumer.
 *
 * The acceptance criterion the builder was written against is this file: a type defined by the
 * builder and not by hand, a substitution defined by recursion on its structure, and a lemma about
 * that substitution proved. Each of the three is asserted below, and the last two are also
 * **spent**: `PSUBST` is computed on a concrete term through its equations, and the lemma is
 * detached at one. An equation nobody can use to compute and a lemma nobody detaches read exactly
 * like the ones that work.
 */
class SyntaxSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private lazy val syntax = force(Syntax.construct(chain))
  private lazy val rules = syntax.logic.rules

  private def fact(name: String): Kernel.Thm = force(syntax.fact(name))
  private def term(text: String): Term = force(syntax.term(text))

  "Every fact of the development" should "prove the statement it is published as" in {
    Syntax.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe force(syntax.proposition(text))
        fact(name).hypotheses shouldBe empty
      }
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    syntax.facts.keySet shouldBe Syntax.Statements.map(_._1).toSet
  }

  "The type" should "be the builder's, with the five constructors in Language's order" in {
    syntax.datatype.specification shouldBe Syntax.Specification
    force(syntax.fact(Datatype.induction(Syntax.TypeName))).conclusion shouldBe force(
      syntax.proposition(
        "!P:pterm -> bool. (!j:num. P (PVAR j)) /\\ P PZERO /\\ (!t:pterm. P t ==> P (PSUC t)) /\\ " +
          "(!t:pterm. !u:pterm. P t ==> P u ==> P (PADD t u)) /\\ " +
          "(!t:pterm. !u:pterm. P t ==> P u ==> P (PMUL t u)) ==> (!t:pterm. P t)"
      )
    )
  }

  "The substitution" should "compute on a concrete term through its equations" in {
    // PSUBST 0 PZERO (PADD (PVAR 0) (PVAR 1)) = PADD PZERO (PVAR 1): the variable that is `0` is
    // replaced and the one that is not is left, which is both branches of the conditional.
    val computed = force(
      for {
        zero <- syntax.term("0", TyApp(Natural.TypeName, Nil))
        one <- syntax.term("1", TyApp(Natural.TypeName, Nil))
        pzero = term("PZERO")
        pvar0 = term("PVAR 0")
        pvar1 = term("PVAR 1")
        sum <- rules.specAll(fact("PSUBST_PADD"), List(zero, pzero, pvar0, pvar1))
        atZero <- rules.specAll(fact("PSUBST_PVAR"), List(zero, pzero, zero))
        atOne <- rules.specAll(fact("PSUBST_PVAR"), List(zero, pzero, one))
        condTrue <- chain.classical.fact(Classical.CondTrue)
        condFalse <- chain.classical.fact(Classical.CondFalse)
        carrier = syntax.datatype.carrier
        same <- syntax.proposition("(0:num) = 0")
        other <- syntax.proposition("(1:num) = 0")
        chosen <- rules
          .specAll(Kernel.instType(Map(Classical.TypeVariable -> carrier), condTrue), List(same, pzero, pvar0))
          .flatMap(rules.mp(_, Conv.refl(zero)))
        apart <- chain.successor.distinct(one, zero)
        kept <- rules
          .specAll(Kernel.instType(Map(Classical.TypeVariable -> carrier), condFalse), List(other, pzero, pvar1))
          .flatMap(rules.mp(_, apart))
        left <- Conv.trans(atZero, chosen)
        right <- Conv.trans(atOne, kept)
        add <- syntax.datatype.constructor(Syntax.Addition)
        both <- Conv.apTerm(add, left).flatMap(partial => LogicError.lift(Kernel.mkComb(partial, right)))
        result <- Conv.trans(sum, both)
      } yield result
    )
    computed.hypotheses shouldBe empty
    computed.conclusion shouldBe force(
      syntax.proposition("PSUBST 0 PZERO (PADD (PVAR 0) (PVAR 1)) = PADD PZERO (PVAR 1)")
    )
  }

  "The lemma" should "detach at a concrete term and variable" in {
    val detached = force(
      for {
        one <- syntax.term("1", TyApp(Natural.TypeName, Nil))
        result <- rules.specAll(fact(Syntax.SubstitutionOfItself), List(term("PSUC (PVAR 1)"), one))
      } yield result
    )
    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe force(syntax.proposition("PSUBST 1 (PVAR 1) (PSUC (PVAR 1)) = PSUC (PVAR 1)"))
  }

  it should "cost exactly choice, eta and infinity, which is what the chain already holds" in {
    // Choice through the conditional in the variable clause and through the graph's witness, eta
    // through the node's extensionality, infinity through `num`. An equality and not a ceiling:
    // the induction principle under it spends none of the three, so a lemma that stopped using the
    // equations would show up here as a smaller set.
    val foundation = Set(
      force(chain.classical.axiom(Classical.Choice)).conclusion,
      force(chain.classical.axiom(Classical.Eta)).conclusion,
      force(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    Derivation.axiomsOf(fact(Syntax.SubstitutionOfItself)) shouldBe foundation
  }
}
