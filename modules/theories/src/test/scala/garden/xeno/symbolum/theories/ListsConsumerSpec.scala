package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * That an existing development writes with the lists, for the verification of Mycelium card
 * `7a761cf1` on 2026-09-26.
 *
 * The card closes on "an existing development rewritten with the lists, its lemma proved, and the
 * axioms held at nineteen". `CollatzSpec` measures the third through axiom counts, and a count can
 * move for a reason that is not the lists. What is asserted here is the first two read off the
 * objects rather than off a count: the constant's definition in the theory **is** a fold, and the
 * lemma the card names reaches the fold's facts in its derivation, not merely a third axiom.
 */
class ListsConsumerSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard

  private lazy val system: Collatz =
    Collatz
      .construct(
        chain.forward,
        chain.folding,
        chain.reaching,
        chain.numbering,
        chain.naturals,
        chain.peano,
        chain.successor,
        chain.folding.theory,
        chain.forward.notation)
      .fold(error => fail(s"the system does not build: ${error.message}"), identity)

  private def fold(name: String): Kernel.Thm =
    chain.folding.fact(name).fold(error => fail(error.message), identity)

  private def constantsOf(term: Term): Set[String] = term match {
    case Const(name, _) => Set(name)
    case App(f, a)      => constantsOf(f) ++ constantsOf(a)
    case Abs(_, body)   => constantsOf(body)
    case _              => Set.empty
  }

  "The two marker-free predicates" should "be defined in the theory as folds, not by position" in {
    for (name <- List(Collatz.TailFree, Collatz.HeadFree)) {
      val defined = system.theory.definitions.getOrElse(name, fail(s"$name has no definition"))
      withClue(s"$name is defined as ${Show.show(system.notation, defined)}: ") {
        constantsOf(defined) should contain(Folding.Fold)
        constantsOf(defined) should not contain "WORD_NTH"
      }
    }
    // The control: a predicate this development still writes by position reads as one.
    constantsOf(system.theory.definitions.getOrElse(Collatz.Marked, fail("no S2_MARKED"))) should not contain Folding.Fold
  }

  "The split over a concatenation" should "be proved through the fold's own lemma" in {
    val wanted = Set(fold(Folding.FoldOfEveryConcat).conclusion, fold(Folding.FoldOfEvery).conclusion)
    for (name <- List(Collatz.TailFreeConcat, Collatz.HeadFreeConcat)) {
      val theorem = system.fact(name).fold(error => fail(error.message), identity)
      withClue(s"$name: ") {
        Derivation.restingOn(theorem, wanted) should contain(fold(Folding.FoldOfEveryConcat).conclusion)
      }
    }
  }

  "Every fact of the development" should "rest on the chain's axioms and nothing else" in {
    // Three since `docs/adr/0053` proved the sixteen of the reals, nineteen until then.
    val believed = chain.widest.theory.axioms.toSet
    believed.size shouldBe 3
    Collatz.Statements.map(_._1).foreach { name =>
      val theorem = system.fact(name).fold(error => fail(error.message), identity)
      withClue(s"$name: ") { Derivation.axiomsOf(theorem).diff(believed) shouldBe empty }
    }
  }
}
