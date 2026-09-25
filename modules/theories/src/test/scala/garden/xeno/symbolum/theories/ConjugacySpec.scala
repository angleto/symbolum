package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The conjugacy series of the Collatz investigation converges where its offsets grow slower than
 * `3^i`, and the statement is usable.
 *
 * Two assertions and the second is the one with content. The first says the theorem is the
 * statement written in `Conjugacy.GammaStatement`, which is the text a reader compares with
 * section 3.1.10 B of `collatz@8b991e5`. The second **detaches** it at the offsets of the word
 * `1^infinity`, where `E i = i`, with every hypothesis discharged: an implication with three
 * antecedents nobody can meet is a theorem that says nothing, and it would pass the first assertion
 * exactly as well.
 */
class ConjugacySpec extends AnyFlatSpec with Matchers {

  private val chain: Chain = Chain.standard
  private val rules: Rules = chain.logic.rules
  private val real: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  private def force[A](result: Either[LogicError, A]): A =
    result.fold(error => fail(error.message), identity)

  private lazy val gamma: Kernel.Thm = force(Conjugacy.prove(chain))

  "The conjugacy series" should "converge under the growth bound, as the statement a reader checks says" in {
    gamma.conclusion shouldBe force(chain.widest.proposition(Conjugacy.GammaStatement))
    gamma.hypotheses shouldBe empty
  }

  /**
   * The route, asserted rather than described: the comparison test against the scaled geometric
   * series. A theorem proved some other way would read the same word for word, which is why the
   * route is a separate question from the statement.
   */
  it should "rest on the comparison test and the geometric series with its scaling" in {
    val route = Set(Limit.Comparison, Limit.GeometricConverges, Limit.ScaleConverges)
      .map(name => force(chain.limit.fact(name)).conclusion)
    Derivation.restingOn(gamma, route) shouldBe route
  }

  /**
   * At `E i = i`, which is the all-ones word: `2^i <= 1 * 2^i` at `b = 2 < 3`, and the series is
   * `sum 2^i / 3^(i + 1)`, whose sum section 3.1.10 B measures as `gamma = 1`. The value is not
   * asserted here, since the theorem obtains a limit and does not name it.
   */
  it should "detach at the all-ones word with every hypothesis discharged" in {
    val linarith = force(Linarith.construct(chain.order))
    val offsets = force(chain.widest.term("\\i:num. (i:num)", Type.fun(numbers, numbers)))
    val instance = force(
      rules
        .specAll(gamma, List(offsets, force(chain.widest.term("2:real", real)), force(chain.widest.term("1:real", real))))
        .flatMap(Limit.normalised))
    val i = Term.variable("i", numbers)
    val growth = force(
      linarith
        .prove("!p:real. p <= 1 * p")
        .flatMap(rules.spec(force(chain.widest.term("Power (2:real) (i:num)", real)), _))
        .flatMap(rules.gen(i, _)))
    val converging = force(
      rules
        .mp(instance, force(linarith.prove("0 <= (2:real)")))
        .flatMap(rules.mp(_, force(linarith.prove("(2:real) < 3"))))
        .flatMap(rules.mp(_, growth)))

    converging.conclusion shouldBe force(
      chain.widest.proposition("?l:real. converges (Sum (\\i:num. Power (2:real) i / Power 3 (SUC i))) l"))
    converging.hypotheses shouldBe empty
  }
}
