package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Definition by recursion, derived.
 *
 * The thing without which not even addition can be defined on the naturals, and the point at which
 * the axiom of infinity finally reaches the mathematics: the type, induction and the case split
 * reach no axiom at all, and this reaches both.
 */
class RecursionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val naturals = Natural.standard
  private val theorem = force(naturals.recursion)

  "The recursion theorem" should "be derived, and be the statement as it is written" in {
    theorem.hypotheses shouldBe empty
    naturals.show(theorem.conclusion) shouldBe
      "!x:'a. !y:'a -> num -> 'a. ?z:num -> 'a. z ZERO = x /\\ (!u:num. z (SUC u) = y (z u) u)"

    theorem.conclusion shouldBe force(naturals.proposition(Recursion.Statement))
  }

  it should "rest on axioms, which nothing below it did" in {
    // Where the axiom of infinity is finally spent. Uniqueness needs `SUC n` never to be `ZERO` and
    // `SUC` to be injective, and those are the two facts that reach it; the type, induction and the
    // case split reach nothing. Everything built by recursion inherits both from here.
    Derivation.axiomsOf(theorem) should have size 2

    Derivation.axiomsOf(force(naturals.fact(Natural.Induction))) shouldBe empty
    Derivation.axiomsOf(force(naturals.fact(Natural.ZeroOrSuccessor))) shouldBe empty
  }

  it should "be polymorphic, so a recursion into any type is one instance of it" in {
    // The value type is a type variable, which is what makes this one theorem rather than one per
    // codomain. A caller instantiates it where they use it.
    Term.typeVariables(theorem.conclusion) should contain("a")
  }

  "The function it produces" should "be usable, which a statement alone would not show" in {
    // A rule whose statement is right and which nothing can apply is one nobody finds out about
    // until later. This instantiates it at the naturals themselves and takes the two equations out,
    // which is exactly what defining a function by recursion looks like from a caller's side.
    val rules = naturals.logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    val atNumbers = Kernel.instType(Map("a" -> numbers), theorem)
    val zero = force(LogicError.lift(naturals.theory.constant(Natural.NumberZero, numbers)))
    val step = force(naturals.term("\\v:num. \\i:num. SUC v"))

    val instance = force(rules.specAll(atNumbers, List(zero, step)))

    naturals.show(instance.conclusion) shouldBe
      "?x:num -> num. x ZERO = ZERO /\\ (!y:num. x (SUC y) = (\\z:num. \\u:num. SUC z) (x y) y)"
    instance.hypotheses shouldBe empty
  }

  "The size of the derivation" should "be reported, since it is the largest one here" in {
    // Reported rather than asserted to a figure. Measured on 2026-09-10: about 6100 inferences, and
    // the second reading of it takes a few seconds, which is the first proof in this system large
    // enough for checking to be worth timing.
    val size = Derivation.size(theorem)

    info(s"the recursion theorem is $size inferences over ${Derivation.axiomsOf(theorem).size} axioms")
    size should be > 1000
  }
}
