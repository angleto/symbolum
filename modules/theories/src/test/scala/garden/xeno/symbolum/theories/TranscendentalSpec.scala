package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The four transcendental constants are definitions, they are four different things, and what is
 * proved about them is what is claimed.
 *
 * The assertion this file exists for is the third one. Six constants defined out of one limit
 * operator could all be the same function without any other test here noticing:
 * every value at zero would still come out, the axiom count would be unchanged, and the statements
 * would still read back. What says they are different is a derivation that two of them differ at a
 * point, and what that costs is one axiom of the reals, `ONE_NOT_ZERO`.
 *
 * **What this file cannot assert is the honest limitation.** That `exp 1` is above `2`, that
 * `sin x * sin x + cos x * cos x = 1`, that `ln` has any property at all: none of them is provable
 * here and a test cannot assert that something is **not** provable, only that a particular
 * derivation refuses. `docs/adr/0017` carries the list and the order the work wants it in, and the
 * row in `README.md` is where a reader meets it.
 */
class TranscendentalSpec extends AnyFlatSpec with Matchers {

  private val chain: Chain = Chain.standard
  private val transcendental: Transcendental = chain.transcendental

  private def force[A](result: Either[LogicError, A]): A =
    result.fold(error => fail(error.message), identity)

  private def proposition(text: String): Term =
    force(Parser.proposition(transcendental.theory, transcendental.notation, text))

  "Every fact of the development" should "prove the statement it is published as" in {
    Transcendental.Statements.foreach { case (name, text) =>
      val proved = force(transcendental.fact(name))
      withClue(s"$name: ") { proved.conclusion shouldBe proposition(text) }
      proved.hypotheses shouldBe empty
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    transcendental.facts.keySet shouldBe Transcendental.Statements.map(_._1).toSet
  }

  "The development" should "declare exactly the six constants it is about" in {
    val before = chain.limit.theory.constants.keySet
    (transcendental.theory.constants.keySet -- before) shouldBe
      Set(
        Transcendental.Exponential,
        Transcendental.Sine,
        Transcendental.Cosine,
        Transcendental.Logarithm,
        Transcendental.HyperbolicSine,
        Transcendental.HyperbolicCosine
      )
  }

  it should "add no axiom, which is what `docs/adr/0017` decided instead of four" in {
    transcendental.theory.axioms.length shouldBe chain.limit.theory.axioms.length
  }

  /**
   * Each definition is its series, read back as the text a person checks against the books.
   *
   * The printed form is what the assertion is against rather than the term, because what is being
   * checked is a translation: `Sum f n` is the first `n` terms indexed from zero, so the exponential
   * is `\sum_{i<n} x^i / i!` and the sine's exponent is `2k + 1`. A reader comparing these four
   * lines with a textbook is doing the only check that matters here, and a definition has to be
   * checkable that way by somebody who did not write it, which is why they are printed rather than
   * assembled.
   */
  "Each constant" should "be defined as the series it is published as" in {
    val expected = Map(
      Transcendental.Exponential ->
        "exp = (\\x:real. lim (\\y:num. Sum (\\z:num. Power x z / real_of_num (NUM_FACT z)) y))",
      Transcendental.Sine ->
        ("sin = (\\x:real. lim (\\y:num. Sum (\\z:num. Power (0 - 1) z * " +
          "(Power x (NUM_ADD (NUM_MUL 2 z) 1) / " +
          "real_of_num (NUM_FACT (NUM_ADD (NUM_MUL 2 z) 1)))) y))"),
      Transcendental.Cosine ->
        ("cos = (\\x:real. lim (\\y:num. Sum (\\z:num. Power (0 - 1) z * " +
          "(Power x (NUM_MUL 2 z) / real_of_num (NUM_FACT (NUM_MUL 2 z)))) y))"),
      Transcendental.Logarithm -> "ln = (\\x:real. select (\\y:real. exp y = x))",
      Transcendental.HyperbolicSine -> "sinh = (\\x:real. (exp x - exp (0 - x)) / 2)",
      Transcendental.HyperbolicCosine -> "cosh = (\\x:real. (exp x + exp (0 - x)) / 2)"
    )

    expected.foreach { case (name, text) =>
      withClue(s"$name: ") {
        transcendental.show(force(transcendental.definition(name)).conclusion) shouldBe text
      }
    }
  }

  /**
   * The exponential and the sine differ at zero, so the four are not one constant four times.
   *
   * `EXP_ZERO` and `SIN_ZERO` give `exp 0 = 1` and `sin 0 = 0`, and `ONE_NOT_ZERO` is what turns
   * that pair into a difference. It is the axiom of the reals that says the field is not trivial,
   * and this is the first thing in the repository to spend it on a claim about two functions.
   */
  "The constants" should "not all be the same function" in {
    val rules = transcendental.logic.rules
    val notZero = force(chain.reals.axiom("ONE_NOT_ZERO"))

    val atZero = force(transcendental.exponentialAtZero)
    val sineAtZero = force(transcendental.sineAtZero)

    // `exp 0 = sin 0` would make `1 = 0`, which the axiom denies.
    val same = proposition("exp 0 = sin 0")
    val assumed = force(LogicError.lift(Kernel.assume(same)))
    val oneIsZero = force(
      Conv
        .sym(atZero)
        .flatMap(Conv.trans(_, assumed))
        .flatMap(Conv.trans(_, sineAtZero))
    )
    transcendental.show(oneIsZero.conclusion) shouldBe "1 = 0"

    val refusal = force(
      rules.notElim(notZero, oneIsZero).flatMap(clash => rules.notIntro(same, clash))
    )
    transcendental.show(refusal.conclusion) shouldBe "~(exp 0 = sin 0)"
    refusal.hypotheses shouldBe empty
  }

  /**
   * The values at zero rest on the naturals and the field and nothing else, pinned as equalities.
   *
   * A ceiling would pass both when a derivation stops spending something and when it starts, which
   * is `CodingSpec`'s argument and is why these are equalities. What is worth reading is the
   * difference rather than the numbers: the sine and the cosine cost one axiom more than the
   * exponential, and the assertion below names it by **computing** it rather than by asserting a
   * name somebody guessed.
   *
   * **The axiom is eta**, and the guess written here first was the positivity of a product, which
   * the measurement refuted. It is the right answer in hindsight and would not have been found by
   * thinking harder: the sine and the cosine reach `SUM_CONGRUENCE`, whose derivation is the reason
   * eta was asserted at all (`docs/adr/0009`), and the exponential reaches a plain induction that
   * never needs a congruence under a binder. So the extra axiom is not about the trigonometric
   * functions, it is about which of the two routes to a partial sum the derivation took.
   */
  "What the values at zero rest on" should "be what they were measured to rest on" in {
    def axioms(name: String): Int =
      Derivation.axiomsOf(force(transcendental.fact(name))).size

    axioms(Transcendental.ExponentialAtZero) shouldBe 17
    axioms(Transcendental.SineAtZero) shouldBe 18
    axioms(Transcendental.CosineAtZero) shouldBe 18

    // The hyperbolic pair costs less, and the reason is the whole of why it is defined from `exp`
    // rather than from a series: nothing about a sum, a power or an index takes part in these.
    axioms(Transcendental.HyperbolicSineAtZero) shouldBe 15
    axioms(Transcendental.HyperbolicCosineAtZero) shouldBe 17
    axioms(Transcendental.CosinePlusSine) shouldBe 15
    axioms(Transcendental.CosineMinusSine) shouldBe 15
  }

  /**
   * The identity that pays for the divergence, checked as the statement rather than as a count.
   *
   * `docs/adr/0017` justifies defining the hyperbolic pair from `exp` by what it makes provable
   * today, so what that section claims is exactly this theorem. If it ever stops being derivable
   * the record's argument is gone, which is a different failure from a number moving.
   */
  it should "relate the hyperbolic pair to the exponential at every argument" in {
    transcendental.show(force(transcendental.cosinePlusSine).conclusion) shouldBe
      "!x:real. cosh x + sinh x = exp x"
    force(transcendental.cosinePlusSine).hypotheses shouldBe empty
  }

  it should "differ between the exponential and the other two by exactly one axiom" in {
    def axioms(name: String): Set[Term] =
      Derivation.axiomsOf(force(transcendental.fact(name))).toSet

    val extra = axioms(Transcendental.SineAtZero) -- axioms(Transcendental.ExponentialAtZero)
    extra.map(transcendental.show) shouldBe Set("!x:'a -> 'b. (\\y:'a. x y) = x")

    axioms(Transcendental.CosineAtZero) -- axioms(Transcendental.ExponentialAtZero) shouldBe extra
  }

  /**
   * A claim about these constants is a proposition now, which is the point of the whole file.
   *
   * Before they existed, `sin x * sin x + cos x * cos x = 1` was a parse error about an unknown
   * constant, which reads as the asker's mistake. It now reads, and the prover cannot settle it,
   * which reads as the system's limit. Those are different answers and this asserts the second.
   */
  "A claim the prover cannot settle" should "at least be statable" in {
    val pythagoras = Parser.proposition(
      chain.widest.theory,
      chain.widest.notation,
      "!x:real. sin x * sin x + cos x * cos x = 1"
    )
    pythagoras.isRight shouldBe true

    val logarithm =
      Parser.proposition(chain.widest.theory, chain.widest.notation, "ln 1 = 0")
    logarithm.isRight shouldBe true
  }
}
