package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The system $S_2$: that the eleven rules are the source's eleven, and that they constrain.
 *
 * This development is `BesideTheChain`, so nothing else builds it and this file is the only thing
 * that does. That is the obligation the standing carries rather than an accident of where the test
 * went.
 *
 * == The assertion that matters is the refusal ==
 *
 * A relation that held of every pair would make `WORD_RFC S2` the set of all words, and every
 * statement downstream of it true and empty. [[Collatz.Refused]] is what says the eleven are a
 * constraint, and it is derived rather than observed: `Propositional` was tried first and refuses
 * with the right message, that the atoms are uninterpreted and the skeleton of eleven disjuncts is
 * satisfiable. Nothing about words is propositional, so the eleven are refuted on their lengths.
 */
class CollatzSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard

  private lazy val system: Collatz =
    Collatz
      .construct(chain.forward, chain.naturals, chain.peano, chain.forward.theory, chain.forward.notation)
      .fold(error => fail(s"the system does not build: ${error.message}"), identity)

  private def fact(name: String): Kernel.Thm =
    system.fact(name).fold(error => fail(error.message), identity)

  /** The body of a nest of lambdas: both definitions here are `\l. \r. <the disjunction>`. */
  private def under(term: Term): Term = term match {
    case Abs(_, body) => under(body)
    case other => other
  }

  "The system" should "declare the alphabet and the four relations, and no more" in {
    system.definitions.keySet shouldBe Set(
      Collatz.F, Collatz.T, Collatz.Head, Collatz.Tail,
      Collatz.Name, Collatz.Counted, Collatz.Potential, Collatz.Marked
    )
  }

  it should "hold exactly eleven rules, which is the number the source has" in {
    // Counted off the definition rather than off the table that generated it, so that a
    // generation which dropped or doubled a clause is caught here rather than believed.
    val definition = system
      .definition(Collatz.Name)
      .fold(error => fail(error.message), identity)

    def disjuncts(term: Term): Int = system.logic.destDisj(term) match {
      case Some((left, right)) => disjuncts(left) + disjuncts(right)
      case None => 1
    }

    val body = Term.destEq(definition.conclusion).map(_._2).getOrElse(fail("not an equation"))

    withClue(s"${system.show(definition.conclusion)}\n") {
      disjuncts(under(body)) shouldBe 11
    }
  }

  it should "say the same thing its published statements do" in {
    for ((name, text) <- Collatz.Statements) {
      val expected = Parser
        .proposition(system.theory, system.notation, text)
        .fold(error => fail(s"$name does not parse: ${error.message}"), identity)

      withClue(s"$name\n  text:    ${system.show(expected)}\n  theorem: ${system.show(fact(name).conclusion)}\n") {
        fact(name).conclusion shouldBe expected
      }
    }
  }

  "The relation" should "hold of something, so that nothing downstream of it is vacuous" in {
    // `WORD_RFC S2` of an empty relation is empty and every non-membership about it is trivially
    // true. This is the guard `InductiveSpec` puts on the even numbers, at this system.
    fact(Collatz.Inhabited).hypotheses shouldBe empty
  }

  it should "refuse a pair, which is what makes it a constraint rather than a relation" in {
    // The half that cannot be got by looking: a search over the rules answers a membership and
    // never a non-membership. Here the one-letter word is refuted against all eleven clauses on
    // the lengths, which is a derivation the kernel checked.
    val refused = fact(Collatz.Refused)
    refused.hypotheses shouldBe empty

    withClue(s"${system.show(refused.conclusion)}\n") {
      system.logic.destNot(refused.conclusion) shouldBe defined
    }
  }

  "The counted sub-relation" should "be six of the eleven, and every one of them a rule" in {
    val counted = system
      .definition(Collatz.Counted)
      .fold(error => fail(error.message), identity)

    def disjuncts(term: Term): Int = system.logic.destDisj(term) match {
      case Some((left, right)) => disjuncts(left) + disjuncts(right)
      case None => 1
    }

    val body = Term.destEq(counted.conclusion).map(_._2).getOrElse(fail("not an equation"))
    disjuncts(under(body)) shouldBe 6

    // And they really are rules of the system, which is the fact a potential argument needs
    // before it can call `A` a sub-relation of `R` at all.
    fact(Collatz.CountedIsRule).hypotheses shouldBe empty
  }

  "What the facts cost" should "be nothing for the two that are about the syntax, and the naturals' two for the refusal" in {
    // The split is the interesting half. The first two are equations between words and closed
    // under the definition, so they reach no foundational axiom at all. The refusal reasons about
    // LENGTHS, which are naturals, so it pays exactly what anything about `num` pays here and not
    // more: `SELECT` and `INFINITY`, and no third.
    Derivation.axiomsOf(fact(Collatz.CountedIsRule)) shouldBe empty
    Derivation.axiomsOf(fact(Collatz.Inhabited)) shouldBe empty

    val refusal = Derivation.axiomsOf(fact(Collatz.Refused))
    withClue(s"the refusal rests on: ${refusal.map(system.show).toVector.sorted.mkString(", ")}\n") {
      refusal.size shouldBe 2
    }
  }
}
