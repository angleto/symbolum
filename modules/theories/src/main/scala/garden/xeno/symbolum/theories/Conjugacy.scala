package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The one claim about a real series that the Collatz investigation holds and this repository can
 * now state: when the offsets of a word grow slower than `3^i`, its conjugacy series converges.
 *
 * Source: `collatz@8b991e5`, `documents/05-open-problems-and-research-log.md`, section 3.1.10 A
 * and B. With `E_i` the partial valuation sums of an infinite word,
 *
 * {{{
 *   gamma(W) = sum_{i >= 1} 2^(E_(i-1)) / 3^i
 * }}}
 *
 * is the series whose sum turns the Syracuse map into multiplication, `xi(Syr x) = (3 / 2^v) xi(x)`,
 * which is the Bernstein-Lagarias conjugacy. Section B records, as a numerical reading and not as a
 * theorem, that **the series converges exactly on the expanding words**, those whose density of
 * the letter two is below `log_2 (3/2)`.
 *
 * == What is formalised, and which of the two criteria it is ==
 *
 * [[Conjugacy.GammaConverges]] is the **sufficient** condition in multiplicative form: if
 * `2^(E i) <= c * b^i` at every index for some `b < 3`, the series converges. Reindexed from zero,
 * `2^(E_(i-1)) / 3^i` at `i >= 1` is `2^(E i) / 3^(i + 1)` at `i >= 0`, which is the summand below.
 * `E` is any function `num -> num`: that it is a sum of valuations is a fact about where it comes
 * from and nothing in the convergence uses it.
 *
 * Two things it is **not**, and both are the source's own claim rather than a weaker one:
 *
 *  - It is not the density statement. `limsup E_i / i < log_2 3` implies the hypothesis with any
 *    `b` strictly between `2^(limsup)` and `3`, and the converse direction needs neither; but saying
 *    so needs `ln` and a `limsup`, and the translation between the two is a note for a reader
 *    rather than a theorem here.
 *  - It is not the sharp criterion. "Exactly on the expanding words" is an equivalence, and the
 *    divergence half on the contracting words wants the root test, which wants `n`th roots and a
 *    `limsup`; neither is here. The ratio test would give a sufficient condition only.
 *
 * So a reader comparing this with section 3.1.10 B should read it as: one direction of the
 * section's claim, in the form the comparison test gives, with the threshold moved from a density
 * to a growth rate.
 *
 * == Why it is a development beside the chain and not a fact of `Limit` ==
 *
 * It is about one investigation's series, for the reason `Collatz` is beside the chain: a fact
 * about a Collatz encoding does not belong in the vocabulary a question about the reals is typed
 * in. It declares nothing, so it is a function of the chain rather than a link of it, and
 * `ConjugacySpec` is what builds it.
 */
object Conjugacy {

  /** `|- !E b c. 0 <= b ==> b < 3 ==> (!i. 2^(E i) <= c * b^i) ==> ?l. converges (Sum (\i. 2^(E i) / 3^(i + 1))) l` */
  val GammaConverges: String = "GAMMA_CONVERGES"

  /** The statement, as the text a person checks it by against section 3.1.10 B. */
  val GammaStatement: String =
    "!E:num -> num. !b:real. !c:real. 0 <= b ==> b < 3 ==> " +
      "(!i:num. Power 2 (E i) <= c * Power b i) ==> " +
      "?l:real. converges (Sum (\\i:num. Power 2 (E i) / Power 3 (SUC i))) l"

  private val values: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val sequences: Type = Type.fun(numbers, values)

  /**
   * [[GammaConverges]], by comparison with `c/3 * (b/3)^i`.
   *
   * The dominating series is geometric at `b / 3 < 1` and scaled by `c / 3`, so it converges by
   * `Limit.SUM_GEOMETRIC_CONVERGES` and `Limit.SUM_SCALE_CONVERGES`, and its partial sums sit under
   * its limit because its terms are not negative. Those terms are not negative because each is
   * above the corresponding term of `gamma`, which is a quotient of two powers of positive numbers:
   * that is why `c` needs no hypothesis of its own, although `c` is what could have made the
   * dominating terms negative.
   *
   * The termwise bound is the one step with arithmetic in it. `3^(i + 1)` is `3 * 3^i`, and
   * `(b/3)^i * 3^i` is `b^i` by `POWER_MULTIPLICATIVE` at the product `(b/3) * 3`, so
   * `(c * b^i) / (3 * 3^i)` is `c/3 * (b/3)^i` wherever `3^i` is not zero, which `Field` proves
   * with that condition attached and `POWER_POSITIVE` discharges.
   */
  def prove(chain: Chain): Either[LogicError, Kernel.Thm] = {
    val theory = chain.widest.theory
    val notation = chain.widest.notation
    val logic = chain.logic
    val rules = logic.rules
    val e = Term.variable("E", Type.fun(numbers, numbers))
    val b = Term.variable("b", values)
    val c = Term.variable("c", values)
    val i = Term.variable("i", numbers)

    def term(text: String, ty: Type): Either[LogicError, Term] = Parser.term(theory, notation, text, ty)
    def assume(text: String): Either[LogicError, (Term, Kernel.Thm)] =
      Parser.proposition(theory, notation, text).flatMap(p => LogicError.lift(Kernel.assume(p)).map(p -> _))

    for {
      linarith <- Linarith.construct(chain.order)
      field <- Field.construct(chain.arithmetic)
      geometric <- chain.limit.fact(Limit.GeometricConverges)
      scaling <- chain.limit.fact(Limit.ScaleConverges)
      belowLimit <- chain.limit.fact(Limit.BelowLimit)
      comparison <- chain.limit.fact(Limit.Comparison)
      powerPositive <- chain.series.fact(Series.PowerPositive)
      powerAtSuccessor <- chain.series.fact(Series.PowerAtSuccessor)
      powerOfProduct <- chain.series.fact(Series.Multiplicative)
      absOfNonNegative <- chain.magnitude.fact(Magnitude.OfNonNegative)
      leOfLt <- chain.order.fact(Order.LeOfLt)
      multiplyLe <- chain.order.fact(Order.MultiplyLe)
      inversePositive <- chain.order.fact(Order.InversePositive)
      nonZero <- chain.order.fact(Order.NonZero)
      productPositive <- chain.reals.law("LT_MUL")

      assumedNonNegative <- assume("0 <= b:real")
      (nonNegative, isNonNegative) = assumedNonNegative
      assumedBelow <- assume("b:real < 3")
      (below, isBelow) = assumedBelow
      assumedGrowth <- assume("!i:num. Power 2 ((E:num -> num) i) <= c:real * Power (b:real) i")
      (growth, grows) = assumedGrowth
      zero <- term("0:real", values)
      two <- term("2:real", values)
      three <- term("3:real", values)
      successor <- term("SUC (i:num)", numbers)
      bounding <- term("c:real * Power (b:real) (i:num)", values)
      ratioPower <- term("Power ((b:real) / 3) (i:num)", values)

      /* ---- the dominating series converges ---- */

      ratio <- term("(b:real) / 3", values)
      ratioNonNegative <- linarith
        .prove("!b:real. 0 <= b ==> 0 <= b / 3")
        .flatMap(rules.spec(b, _))
        .flatMap(rules.mp(_, isNonNegative))
      ratioBelow <- linarith
        .prove("!b:real. b < 3 ==> b / 3 < 1")
        .flatMap(rules.spec(b, _))
        .flatMap(rules.mp(_, isBelow))
      ratioSize <- rules.spec(ratio, absOfNonNegative).flatMap(rules.mp(_, ratioNonNegative)).flatMap(Conv.sym)
      ratioSmall <- Limit.rewriteInProposition(ratioSize, ratioBelow)
      powers <- rules.spec(ratio, geometric).flatMap(rules.mp(_, ratioSmall))
      powersParts <- Limit.convergenceOf(powers)
      summands <- powersParts._1 match {
        case App(_, summand) => Right(summand)
        case other           => Left(NotOfForm("the partial sums of a series", other))
      }
      factor <- term("(c:real) / 3", values)
      dominating <- rules
        .specAll(scaling, List(summands, factor, powersParts._2))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, powers))
      dominatingParts <- Limit.convergenceOf(dominating)

      /* ---- termwise: gamma's term is positive and under the dominating one ---- */

      exponent <- term("(E:num -> num) (i:num)", numbers)
      twoPositive <- linarith.prove("0 < (2:real)")
      threePositive <- linarith.prove("0 < (3:real)")
      top <- term("Power 2 ((E:num -> num) (i:num))", values)
      topPositive <- rules
        .spec(two, powerPositive)
        .flatMap(rules.mp(_, twoPositive))
        .flatMap(rules.spec(exponent, _))
      powerThreePositive <- rules
        .spec(three, powerPositive)
        .flatMap(rules.mp(_, threePositive))
      bottom <- term("Power 3 (SUC (i:num))", values)
      bottomPositive <- rules.spec(successor, powerThreePositive)
      reciprocalPositive <- rules.spec(bottom, inversePositive).flatMap(rules.mp(_, bottomPositive))
      reciprocal <- term("inv (Power 3 (SUC (i:num)))", values)
      quotientPositive <- rules
        .conjIntro(topPositive, reciprocalPositive)
        .flatMap(both => rules.specAll(productPositive, List(top, reciprocal)).flatMap(rules.mp(_, both)))
      asQuotient <- Parser
        .proposition(theory, notation,
          "Power 2 ((E:num -> num) (i:num)) * inv (Power 3 (SUC i)) = Power 2 (E i) / Power 3 (SUC i)")
        .flatMap(chain.ring.prove)
      gammaTerm <- term("Power 2 ((E:num -> num) (i:num)) / Power 3 (SUC i)", values)
      termPositive <- Limit.rewriteInProposition(asQuotient, quotientPositive)
      termNonNegative <- rules.specAll(leOfLt, List(zero, gammaTerm)).flatMap(rules.mp(_, termPositive))

      // `(b/3)^i * 3^i = b^i`
      splitProduct <- rules.specAll(powerOfProduct, List(ratio, three, i))
      rejoined <- field.prove("!b:real. b / 3 * 3 = b").flatMap(rules.spec(b, _))
      product <- Limit.rewriteInProposition(rejoined, splitProduct)

      // `(c * b^i) * inv (3^(i + 1))` under `c/3 * (b/3)^i`, as an equation where `3^i` is not zero
      lowerPower <- term("Power 3 (i:num)", values)
      lowerPositive <- rules.spec(i, powerThreePositive)
      lowerNonZero <- rules.spec(lowerPower, nonZero).flatMap(rules.mp(_, lowerPositive))
      // At the instance rather than quantified: `Field` charges `~(t = 0)` on the atom it cancels,
      // and a condition on a variable cannot be generalised over, so the atom is `3^i` itself.
      identityAt <- Parser
        .proposition(theory, notation,
          "(c:real * (Power ((b:real) / 3) (i:num) * Power 3 i)) * inv (3 * Power 3 i) = " +
            "c / 3 * Power (b / 3) i")
        .flatMap(field.prove)
      identityHeld <- identityAt.hypotheses match {
        case Nil => Right(identityAt)
        case List(condition) if condition == lowerNonZero.conclusion =>
          rules.disch(condition, identityAt).flatMap(rules.mp(_, lowerNonZero))
        case _ => Left(NotOfForm("an identity owing at most that 3^i is not zero", identityAt.conclusion))
      }

      atI <- rules.spec(i, grows)
      reciprocalNonNegative <- rules.specAll(leOfLt, List(zero, reciprocal)).flatMap(rules.mp(_, reciprocalPositive))
      scaledDown <- rules
        .specAll(multiplyLe, List(reciprocal, top, bounding))
        .flatMap(rules.mp(_, reciprocalNonNegative))
        .flatMap(rules.mp(_, atI))
      threeUp <- rules.specAll(powerAtSuccessor, List(three, i))
      spread <- Limit.rewriteInProposition(product, scaledDown)
      openedBottom <- Limit.rewriteInProposition(threeUp, spread)
      bounded <- Limit.rewriteInProposition(identityHeld, openedBottom)
      closedBottom <- Conv.sym(threeUp).flatMap(Limit.rewriteInProposition(_, bounded))
      termBound <- Limit.rewriteInProposition(asQuotient, closedBottom)

      /* ---- so the dominating terms are not negative either, and their partial sums are bounded ---- */

      dominatingTerm <- term("(c:real) / 3 * Power ((b:real) / 3) (i:num)", values)
      dominatingNonNegative <- linarith
        .prove("!x:real. !y:real. 0 <= x ==> x <= y ==> 0 <= y")
        .flatMap(rules.specAll(_, List(gammaTerm, dominatingTerm)))
        .flatMap(rules.mp(_, termNonNegative))
        .flatMap(rules.mp(_, termBound))
        .flatMap(rules.gen(i, _))
      dominatingSummands <- dominatingParts._1 match {
        case App(_, summand) => Right(summand)
        case other           => Left(NotOfForm("the partial sums of a series", other))
      }
      underLimit <- rules
        .specAll(belowLimit, List(dominatingSummands, dominatingParts._2))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, dominatingNonNegative))
        .flatMap(rules.mp(_, dominating))
      claim <- Parser.proposition(theory, notation,
        "?B:real. !n:num. Sum (\\i:num. (c:real) / 3 * Power ((b:real) / 3) i) n <= B")
      predicate <- logic.destExistsPredicate(claim).toRight(NotOfForm("an existential", claim))
      boundedSums <- rules.existsIntro(predicate, dominatingParts._2, underLimit)

      /* ---- and the comparison test closes it ---- */

      gammaSummands <- term("\\i:num. Power 2 ((E:num -> num) i) / Power 3 (SUC i)", sequences)
      termsNonNegative <- rules.gen(i, termNonNegative)
      dominated <- rules.gen(i, termBound)
      converging <- rules
        .specAll(comparison, List(gammaSummands, dominatingSummands))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, termsNonNegative))
        .flatMap(rules.mp(_, dominated))
        .flatMap(rules.mp(_, boundedSums))
      result <- rules
        .disch(growth, converging)
        .flatMap(rules.disch(below, _))
        .flatMap(rules.disch(nonNegative, _))
        .flatMap(rules.genAll(_, List(e, b, c)))
    } yield result
  }
}
