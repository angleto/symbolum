package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Recursion along a measure, asked what it proves, what it costs, and whether its hypothesis
 * carries weight.
 *
 * The last is the guard that matters. A recursion theorem whose admissibility hypothesis could be
 * dropped would be a theorem that every step has a fixed point, which is false, and a statement
 * comparison would not notice a derivation that had quietly stopped needing the hypothesis. So the
 * conclusion without it is **refuted** at one step, `st f x = SUC (f x)`, where no function can
 * satisfy the equation. `EuclidAlgorithm` is where the theorem is spent, and `EuclidAlgorithmSpec` computes with it.
 */
class WellFoundedSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val base = chain.widest
  private lazy val theorem = force(WellFounded.theorem(Datatype.Ground.of(chain), base.theory, base.notation))
  private lazy val rules = force(chain.classical.logic.over(base.theory)).rules

  "The recursion theorem" should "prove the statement it is published as, and assume nothing" in {
    theorem.conclusion shouldBe force(Parser.proposition(base.theory, base.notation, WellFounded.Statement))
    theorem.hypotheses shouldBe empty
  }

  it should "cost choice and infinity, and not eta" in {
    // Choice names the function, infinity is what `num` and its strong induction rest on. Eta is
    // what `Datatype`'s recursion spends on its nodes' extensionality and there is no node here,
    // so its absence is a fact about this proof and is asserted as one.
    Derivation.axiomsOf(theorem) shouldBe Set(
      force(chain.classical.axiom(Classical.Choice)).conclusion,
      force(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
  }

  "Its conclusion without admissibility" should "be false at a step that reads the function at the point itself" in {
    // `st f x = SUC (f x)` reads `f` at `x`, which is not below `x` by any measure, and a function
    // with `f x = SUC (f x)` at even one point does not exist. So `?f. !x. f x = st f x` is refuted
    // here, which is what makes the hypothesis load-bearing rather than decorative.
    val refuted = force(
      for {
        claim <- Parser.proposition(base.theory, base.notation, "?f:num -> num. !x:num. f x = SUC (f x)")
        notSelf <- chain.peano.fact(Peano.SuccessorNotSelf)
        logic <- chain.classical.logic.over(base.theory)
        f = Term.variable("f", Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Natural.TypeName, Nil)))
        x = Term.variable("x", TyApp(Natural.TypeName, Nil))
        body <- Parser.proposition(base.theory, base.notation, "!x:num. (f:num -> num) x = SUC (f x)")
        assumedBody <- LogicError.lift(Kernel.assume(body))
        atX <- rules.spec(x, assumedBody)
        fx <- LogicError.lift(Term.app(f, x))
        refusal <- rules.spec(fx, notSelf)
        flipped <- Conv.sym(atX)
        absurd <- rules.notElim(refusal, flipped)
        assumedClaim <- LogicError.lift(Kernel.assume(claim))
        opened <- rules.existsElim(assumedClaim, f, absurd)
        result <- rules.notIntro(claim, opened)
      } yield result
    )
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe force(
      Parser.proposition(base.theory, base.notation, "~(?f:num -> num. !x:num. f x = SUC (f x))")
    )
  }
}
