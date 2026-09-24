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
        ("sin = (\\x:real. lim (\\y:num. Sum (\\z:num. Power (0 - 1) z * (Power x (2 * z + 1) / " +
          "real_of_num (NUM_FACT (2 * z + 1)))) y))"),
      Transcendental.Cosine ->
        ("cos = (\\x:real. lim (\\y:num. Sum (\\z:num. Power (0 - 1) z * (Power x (2 * z) / " +
          "real_of_num (NUM_FACT (2 * z)))) y))"),
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
  /**
   * The absolute convergence does what it was built for, which is to feed the Cauchy product.
   *
   * `Limit.SUM_CAUCHY_PRODUCT` asks four things of its two series and two of them are absolute
   * convergences. This asserts that [[Transcendental.AbsolutelyConvergent]] supplies one of
   * those at an arbitrary real, and that `Limit.CONVERGES_ABSOLUTE` turns it into the other, the
   * plain convergence of the signed series — which is the pair the addition theorem needs and
   * which `EXP_ONE_ABOVE_TWO` supplies at `x = 1` and nowhere else.
   *
   * Both come out with `hypotheses` empty and with `x` still a variable, and the second is the
   * half worth asserting: a theorem that held only at a particular real would satisfy every
   * reading of the statement above and would be useless to the product.
   */
  "The exponential's series" should "converge absolutely at an arbitrary real, and so converge" in {
    val rules = transcendental.logic.rules
    val real = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val x = Term.variable("x", real)
    val p = Term.variable("P", real)

    val absolute = force(transcendental.fact(Transcendental.AbsolutelyConvergent))
    val atAPoint = force(rules.spec(x, absolute))

    atAPoint.hypotheses shouldBe empty
    atAPoint.conclusion shouldBe proposition(
      "?P:real. converges (Sum (\\i:num. abs (Power (x:real) i / real_of_num (NUM_FACT i)))) P")

    // And the signed series converges, which is the second of the product's four antecedents.
    val terms = force(
      Parser.term(
        transcendental.theory,
        transcendental.notation,
        "\\i:num. Power (x:real) i / real_of_num (NUM_FACT i)",
        Type.fun(numbers, real)))
    val assumed = force(
      LogicError.lift(
        Kernel.assume(proposition(
          "converges (Sum (\\i:num. abs (Power (x:real) i / real_of_num (NUM_FACT i)))) (P:real)"))))
    val signed = force(
      rules
        .specAll(force(chain.limit.absolute), List(terms, p))
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))
            .flatMap(rules.mp(_, assumed))))

    val settled = force(rules.existsElim(atAPoint, p, signed))

    settled.hypotheses shouldBe empty
    settled.conclusion shouldBe proposition(
      "?m:real. converges (Sum (\\i:num. Power (x:real) i / real_of_num (NUM_FACT i))) m")
  }

  /**
   * It rests on the monotone convergence theorem and on the reindexing, and **not** on the
   * comparison test.
   *
   * That last one is the claim the docstring makes about itself and the only one a reader cannot
   * check from the statement: `SUM_COMPARISON` is the obvious instrument for a convergence of
   * this shape and it is deliberately not used, because it asks for domination at every index
   * and a uniform geometric dominator for an arbitrary `x` wants a fact about `num` this
   * repository does not have. What replaces it is a **split**, and `SUM_REINDEX` is what does
   * the splitting, so the pair of assertions below is the route rather than a remark about it.
   *
   * `EXP_ONE_ABOVE_TWO` is asserted on the other side of the same line: it **does** rest on the
   * comparison test, which is what makes the absence above a choice rather than an accident.
   */
  it should "rest on the monotone convergence and the reindexing, and not on the comparison test" in {
    val absolute = force(transcendental.fact(Transcendental.AbsolutelyConvergent))

    val route = Set(
      force(chain.limit.fact(Limit.MonotoneConverges)).conclusion,
      force(chain.series.fact(Series.Reindex)).conclusion,
      force(transcendental.fact(Transcendental.TailIsGeometric)).conclusion,
      force(transcendental.fact(Transcendental.TermsHalve)).conclusion)

    Derivation.restingOn(absolute, route) shouldBe route

    val comparison = force(chain.limit.fact(Limit.Comparison)).conclusion

    Derivation.restingOn(absolute, Set(comparison)) shouldBe empty
    Derivation.restingOn(
      force(transcendental.fact(Transcendental.ExponentialAboveTwo)),
      Set(comparison)) shouldBe Set(comparison)

    // And completeness is reached, through the monotone convergence and nowhere else.
    Derivation.axiomsOf(absolute) should contain(
      force(chain.reals.axiom("COMPLETENESS")).conclusion)
  }
  /**
   * The addition theorem, and what it does **not** say.
   *
   * `exp (x + y) = exp x * exp y` at two variables, with `hypotheses` empty. The assertion worth
   * having beside it is the second one: `exp 0 = 1` comes out of it by putting `y := 0` and
   * cancelling, which is a fact this file already proves another way, so agreeing with it is a
   * check that the addition theorem is about the same constant.
   *
   * What is asserted is the agreement and not a new derivation of `EXP_ZERO`: the cancellation
   * needs `~(exp 0 = 0)`, which this development has no way to reach — nothing here bounds `exp`
   * away from zero at a general point, and `EXP_ONE_ABOVE_TWO` is at one point only.
   */
  "The addition theorem" should "hold at two variables with nothing assumed" in {
    val addition = force(transcendental.fact(Transcendental.Addition))

    addition.hypotheses shouldBe empty
    addition.conclusion shouldBe proposition("!x:real. !y:real. exp (x + y) = exp x * exp y")

    // At `y := 0` it reads `exp x = exp x * exp 0`, and `EXP_ZERO` is what makes that an
    // identity rather than a constraint. The two facts agree, which is the check.
    val rules = transcendental.logic.rules
    val real = TyApp(Real.TypeName, Nil)
    val x = Term.variable("x", real)
    val zero = force(
      Parser.term(transcendental.theory, transcendental.notation, "0:real", real))

    val atZero = force(rules.specAll(addition, List(x, zero)))

    atZero.hypotheses shouldBe empty
    atZero.conclusion shouldBe proposition("exp ((x:real) + 0) = exp (x:real) * exp 0")

    force(transcendental.fact(Transcendental.ExponentialAtZero)).conclusion shouldBe
      proposition("exp 0 = 1")
  }

  /**
   * It rests on the Cauchy product, on the convolution and on the absolute convergence.
   *
   * The three are the route and none of them is visible in the statement, which is four symbols
   * long. `Limit.SUM_CAUCHY_PRODUCT` is what multiplies the two series;
   * [[Transcendental.Convolution]] is what says the result is the exponential's own series at
   * `x + y`, and it is where `Coding.NUM_CHOOSE_FACTORIAL` is spent; and
   * [[Transcendental.AbsolutelyConvergent]] is what lets the product be applied at all.
   *
   * `Series.POWER_BINOMIAL` is asserted under them because it is the fact that had been proved
   * and unspent: nothing consumed it until the convolution did.
   */
  it should "rest on the Cauchy product, the convolution and the binomial theorem" in {
    val addition = force(transcendental.fact(Transcendental.Addition))

    val route = Set(
      force(chain.limit.fact(Limit.Cauchy)).conclusion,
      force(transcendental.fact(Transcendental.Convolution)).conclusion,
      force(transcendental.fact(Transcendental.AbsolutelyConvergent)).conclusion,
      force(chain.series.fact(Series.Binomial)).conclusion,
      force(chain.coding.fact(Coding.ChooseTimesFactorials)).conclusion)

    Derivation.restingOn(addition, route) shouldBe route
  }
  /**
   * The hyperbolic pair, which is what `docs/adr/0017` chose the sum and the difference for.
   *
   * That record decided `sinh` and `cosh` would be `(exp x - exp (0 - x)) / 2` and the same sum
   * rather than two series of their own, and said what it bought was `cosh x + sinh x = exp x`
   * today. This is the rest of that purchase: those two facts landed on 2026-09-15 and had
   * nothing to spend until [[Transcendental.Addition]] arrived.
   *
   * Two assertions carry the claim that it is **bought** and not proved again: it rests on
   * `EXP_ADD`, and it spends exactly the axioms `EXP_ADD` spends and no others. A derivation
   * through the two series would reach the same statement and would cost the Cauchy product a
   * second time, and neither the statement nor an axiom count alone would show the difference.
   *
   * The trigonometric identity is out of reach and no test can say so; what says it is the
   * docstring on the name, and the reason is that `sin` and `cos` meet `exp` only through a
   * square root of minus one.
   */
  "The hyperbolic pair" should "be bought by the addition theorem rather than proved again" in {
    val reciprocal = force(transcendental.fact(Transcendental.Reciprocal))
    val pythagoras = force(transcendental.fact(Transcendental.HyperbolicPythagoras))

    reciprocal.hypotheses shouldBe empty
    pythagoras.hypotheses shouldBe empty
    reciprocal.conclusion shouldBe proposition("!x:real. exp x * exp (0 - x) = 1")
    pythagoras.conclusion shouldBe
      proposition("!x:real. cosh x * cosh x - sinh x * sinh x = 1")

    val route = Set(
      force(transcendental.fact(Transcendental.Addition)).conclusion,
      force(transcendental.fact(Transcendental.CosinePlusSine)).conclusion,
      force(transcendental.fact(Transcendental.CosineMinusSine)).conclusion)

    Derivation.restingOn(pythagoras, route) shouldBe route

    // And it adds **no** axiom to what the addition theorem already cost, which is the half that
    // says it is bought rather than proved again: a derivation through the two series would
    // reach the same statement and would spend the Cauchy product a second time.
    Derivation.axiomsOf(pythagoras) shouldBe
      Derivation.axiomsOf(force(transcendental.fact(Transcendental.Addition)))
  }

  /**
   * The trigonometric identity, which the two series owe and the hyperbolic one could not buy.
   *
   * What `Trigonometric` claims is a route, and a route is invisible in a statement four symbols
   * long, so the route is what is asserted: the two Cauchy products, the convolution at `(x, -x)`
   * read by parity, the sign law at a doubled exponent, and the shift that lines the cosine's
   * product up with the sine's one index along.
   *
   * **And what it does not rest on is half the claim.** `EXP_ADD` is the exponential's reading of
   * the same convolution fact, and a derivation of this from it would be the square root of minus
   * one this repository does not have. Asserting the absence is what separates "the same
   * convolution read twice" from "one identity read off the other", and it is not vacuous: the
   * same walk finds every fact of the route above.
   */
  "The trigonometric identity" should "hold at every real with nothing assumed" in {
    val squared = force(transcendental.fact(Transcendental.Pythagoras))

    squared.hypotheses shouldBe empty
    transcendental.show(squared.conclusion) shouldBe "!x:real. sin x * sin x + cos x * cos x = 1"
  }

  it should "rest on the two Cauchy products and the convolution read by parity" in {
    val squared = force(transcendental.fact(Transcendental.Pythagoras))

    val route = Set(
      force(chain.limit.fact(Limit.Cauchy)).conclusion,
      force(chain.limit.fact(Limit.Shifted)).conclusion,
      force(transcendental.fact(Transcendental.Convolution)).conclusion,
      force(transcendental.fact(Transcendental.CosineAbsolute)).conclusion,
      force(transcendental.fact(Transcendental.SineAbsolute)).conclusion,
      force(chain.series.fact(Series.EvenOdd)).conclusion,
      force(chain.series.fact(Series.NegatedDouble)).conclusion,
      force(chain.series.fact(Series.Binomial)).conclusion)

    Derivation.restingOn(squared, route) shouldBe route

    val addition = force(transcendental.fact(Transcendental.Addition)).conclusion
    Derivation.restingOn(squared, Set(addition)) shouldBe empty
  }

  it should "cost what the addition theorem costs, and the series' magnitudes what the exponential's do" in {
    // Equalities and not ceilings, for `CodingSpec`'s reason. The absolute convergence of the two
    // alternating series was predicted at nineteen before it was measured and came in at eighteen,
    // which is `EXP_ABSOLUTE`'s own figure: the bound it spends is the exponential's, and the sign
    // `(0 - 1)^k` costs nothing past the magnitude facts `EXP_ABSOLUTE` already reaches.
    def axioms(name: String): Set[Term] =
      Derivation.axiomsOf(force(transcendental.fact(name))).toSet

    axioms(Transcendental.Pythagoras) shouldBe axioms(Transcendental.Addition)
    axioms(Transcendental.CosineAbsolute) shouldBe axioms(Transcendental.AbsolutelyConvergent)
    axioms(Transcendental.SineAbsolute) shouldBe axioms(Transcendental.AbsolutelyConvergent)
  }

  it should "detach at zero into the two values the series have there" in {
    // Not a second proof of anything: the identity at zero, with `SIN_ZERO` and `COS_ZERO`
    // substituted, is `0 * 0 + 1 * 1 = 1`. What it checks is that the constants the identity is
    // about are the ones those two facts are about, which a statement parsed against another
    // signature would not be.
    val squared = force(transcendental.fact(Transcendental.Pythagoras))
    val zero = force(Parser.term(transcendental.theory, transcendental.notation, "0:real"))
    val atZero = force(transcendental.logic.rules.spec(zero, squared))
    val values = force(Rewrite.Rule.all(
      transcendental.logic,
      Vector(force(transcendental.sineAtZero), force(transcendental.cosineAtZero))))
    val moved = force(Rewrite.inTheorem(values, atZero))

    transcendental.show(moved.conclusion) shouldBe "0 * 0 + 1 * 1 = 1"
  }
}
