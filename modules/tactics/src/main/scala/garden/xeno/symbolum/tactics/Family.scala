package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.*

/**
 * A closed form for a finite sum, guessed from its first few values and then proved.
 *
 * The fourth source on the conjecture card's list, and the one with the shape the whole repository
 * is built around: **the proposal is arithmetic on numbers and the check is the kernel.** Nothing
 * here has to be right. It computes `Sum f n` for the first few `n`, fits the unique polynomial
 * through the points, states the claim that they agree for every `n`, and hands that to `Induct`. A
 * bad fit costs a refusal; it cannot produce a theorem about anything but the sum it was given.
 *
 * {{{
 *   Family.standard.of("\\i:num. real_of_num i")
 *   // Found(!n:num. Sum (\i:num. real_of_num i) n = real_of_num n * (real_of_num n - 1) / 2,
 *   //       degree 2, 13957 inferences on 2026-09-24)
 * }}}
 *
 * == Why it works at all, which is one lemma ==
 *
 * The claim is about `real_of_num n` and the induction step needs to get from `n` to `SUC n`
 * *inside* the polynomial. `Peano.EmbedsSuccessor` is what does it: `real_of_num (SUC n) =
 * real_of_num n + 1`, so the step is a ring identity in the single atom `real_of_num n` and `Ring`
 * closes it. Without the embedding there is no closed form to state, because `num` has no
 * arithmetic a polynomial could be written in; with it, the whole family is one induction.
 *
 * == The interpolation, and why it is the Newton form ==
 *
 * Finite differences rather than a matrix solve: `p(x) = Σ c_j * x(x-1)...(x-j+1) / j!` with `c_j`
 * the j-th forward difference of the sampled values at zero. It is exact over [[Rational]], it needs
 * no pivoting, and the **degree falls out of it**: the first `j` whose difference column is
 * identically zero is the degree, so the fit is not asked for in advance and a family that is not
 * polynomial says so instead of being fitted badly.
 *
 * A polynomial of degree `d` is determined by `d + 1` points and confirmed by one more. This
 * samples [[Family.Points]] of them and requires the difference column to vanish with at least one
 * point to spare, so the fit is never the last thing the data could have supported. That is a
 * screen and not a proof: the theorem at the end is the proof, and a family that agrees at ten
 * points and diverges at eleven comes back refused rather than certified.
 *
 * **What comes out is in the Newton basis and is not the form a textbook prints.** The sum of
 * squares arrives as `x(x-1)/2 + x(x-1)(x-2)/3` rather than as `x(x-1)(2x-1)/6`, and the two are
 * the same polynomial: the basis is what the interpolation is done in and nothing here rearranges
 * it afterwards. Rearranging would be the untrusted simplifier deciding what the claim says, which
 * is the one thing this border does not let it do. A reader who wants the familiar form asks `Ring`
 * whether the two are equal, and gets a theorem.
 *
 * == What it does not do ==
 *
 * **Only sums, and only polynomial ones.** `Sum (\i. Power 2 i) n` has the closed form
 * `Power 2 n - 1`, which is not a polynomial in `n` and no number of differences will find it. The
 * refusal says so by name. Products, and sums whose closed form is exponential or harmonic, want a
 * different fit and are a different source.
 *
 * **And it evaluates the samples itself**, in exact rational arithmetic, rather than through the
 * model: `Evaluate` has nothing to say about `Sum`, and what this needs is a number rather than a
 * theorem. The evaluation is untrusted like the fit, and for the same reason it can be.
 */
final class Family private (val chain: Chain, val rules: Vector[Rewrite.Rule]) {

  import Family.*

  private val signature: Signature = chain.widest
  private val logic: Logic = chain.logic
  private val real: Type = TyApp(Real.TypeName, Nil)
  private val natural: Type = TyApp(Natural.TypeName, Nil)

  /**
   * A closed form for the sum of a summand written in the theory's notation.
   *
   * Read at `num -> real`, which this knows and the writer of the text should not have to. Before
   * 2026-09-12 saying so bought nothing, since a term of any other shape was refused by the next
   * line anyway; with a digit string reading at either type it is the difference between
   * `\i:num. 1` being a summand and being an undetermined numeral, and the type is this
   * interface's fact rather than the text's.
   */
  def of(text: String): Outcome =
    signature.term(text, Type.fun(natural, real)) match {
      case Left(error) => Outcome.Unreadable(error.message)
      case Right(summand) => of(summand)
    }

  /**
   * A closed form for `Sum f n`, or which of the three things stopped it.
   *
   * The order is the order of what each step can say. A summand whose values cannot be computed is
   * not a failed fit; a family with no polynomial fit is not a failed proof; and a fit the prover
   * refuses is not a family without a closed form. Merging any two of them would turn "I could not
   * ask" into "I asked and it was not there", which is the failure this repository names most.
   */
  def of(summand: Term): Outcome =
    sampled(summand) match {
      case Left(why) => Outcome.Unreadable(why)

      case Right(values) =>
        coefficientsOf(values) match {
          case None => Outcome.NotPolynomial(values, Points)

          case Some(coefficients) =>
            claimFor(summand, coefficients) match {
              case Left(why) => Outcome.Unreadable(why)

              case Right(claim) =>
                chain.induct.prove(claim, held) match {
                  case Right(theorem) =>
                    Outcome.Found(claim, theorem, coefficients.length - 1, values)
                  case Left(refusal) => Outcome.NotCertified(claim, refusal.message)
                }
            }
        }
    }

  /* ------------------------------------------------------------------ the samples */

  /**
   * `Sum f k` for `k` from zero to [[Points]], as exact numbers.
   *
   * Each one is a closed term once the recurrences have unfolded it, so it is rewritten and then
   * evaluated rather than proved: what the fit needs is a value, and a theorem about the value
   * would cost a normalisation per point and say the same thing.
   */
  private def sampled(summand: Term): Either[String, Vector[Rational]] =
    (0 to Points).toVector.foldLeft(Right(Vector.empty): Either[String, Vector[Rational]]) {
      (acc, k) =>
        for {
          done <- acc
          length <- numeralOfNaturals(k)
          applied <- sumOf(summand, length)
          equation <- Rewrite.rewrite(rules, applied).left.map(_.message)
          reduced <- Term.destEq(equation.conclusion).map(_._2).toRight("the rewriting lost its shape")
          value <- valueOf(reduced).toRight(whyNotANumber(applied, reduced))
        } yield done :+ value
    }

  /**
   * Why a sample did not come out as a number, in the two ways that are not each other.
   *
   * `Rewrite.rewrite` hands back the theorem it had built when the step limit ran out, and that
   * theorem is true: nothing in it says whether the rewriting had finished. So a rule set that does
   * not settle looks exactly like a term that is genuinely irreducible, and the first version of
   * this file reported both as "the recurrences do not reduce it" — which is a statement about the
   * family, and is false in the first case.
   *
   * This is the defect `Rewrite.finished` exists for, reappearing in new code on the day the card
   * that reviewed its call sites predicted it would. Asked only here, after the value could not be
   * read, because on the path where it could the answer changes nothing.
   */
  private def whyNotANumber(applied: Term, reduced: Term): String =
    Rewrite.finished(rules, reduced) match {
      case Right(true) =>
        s"the recurrences have nothing left to do to ${signature.show(applied)} and it is not a " +
          s"number: it stops at ${signature.show(reduced)}"
      case Right(false) =>
        s"the rewriting of ${signature.show(applied)} stopped at the step limit rather than " +
          s"finishing, so ${signature.show(reduced)} is not what this family reduces to"
      case Left(error) =>
        s"${signature.show(applied)} did not reduce to a number, and whether the rewriting " +
          s"finished could not be asked: ${error.message}"
    }

  /** `SUC (SUC ... ZERO)`, which is the only way to write a particular natural here. */
  private def numeralOfNaturals(value: Int): Either[String, Term] =
    for {
      zero <- signature.theory.constant(Natural.NumberZero, natural).left.map(_.message)
      successor <- signature.theory
        .constant(Natural.NumberSuccessor, Type.fun(natural, natural))
        .left
        .map(_.message)
      built <- (1 to value).foldLeft(Right(zero): Either[String, Term]) { (acc, _) =>
        acc.flatMap(inner => Term.app(successor, inner).left.map(_.message))
      }
    } yield built

  private def sumOf(summand: Term, length: Term): Either[String, Term] =
    for {
      sum <- signature.theory
        .constant(Series.SumName, Type.fun(Type.fun(natural, real), Type.fun(natural, real)))
        .left
        .map(_.message)
      applied <- Term.appAll(sum, List(summand, length)).left.map(_.message)
    } yield applied

  /**
   * The number a closed arithmetic term denotes, or nothing when it is not one.
   *
   * Untrusted, exact, and deliberately small: the numerals, the four operators and a negation. A
   * term with a variable in it, or an unreduced `Sum`, is not a number and comes back as nothing,
   * which is what tells the caller the family did not reduce at that point rather than that it
   * reduced to something surprising.
   */
  private def valueOf(term: Term): Option[Rational] =
    Numeral.valueOf(signature, term).map(Rational.of).orElse(term match {
      case App(App(Const(Real.Addition, _), left), right) =>
        for { a <- valueOf(left); b <- valueOf(right) } yield a + b
      case App(App(Const(Real.Subtraction, _), left), right) =>
        for { a <- valueOf(left); b <- valueOf(right) } yield a - b
      case App(App(Const(Real.Multiplication, _), left), right) =>
        for { a <- valueOf(left); b <- valueOf(right) } yield a * b
      case App(App(Const(Real.Division, _), left), right) =>
        for { a <- valueOf(left); b <- valueOf(right) if !b.isZero } yield a / b
      case App(Const(Real.Negation, _), argument) => valueOf(argument).map(-_)
      case _ => None
    })

  /* ------------------------------------------------------------ the interpolation */

  /**
   * The Newton coefficients of the polynomial through the samples, or nothing when there is none.
   *
   * The difference columns are taken until one of them is identically zero, and what comes back is
   * the leading row: `c_j` is the j-th difference at zero. [[Slack]] points have to remain when the
   * column vanishes, so a family fitted here agreed at more points than the fit needed.
   */
  private def coefficientsOf(values: Vector[Rational]): Option[Vector[Rational]] = {
    def differences(column: Vector[Rational], taken: Vector[Rational]): Option[Vector[Rational]] =
      if (column.forall(_.isZero)) Some(taken)
      else if (column.length <= Slack + 1) None
      else
        differences(
          column.sliding(2).map(pair => pair(1) - pair(0)).toVector,
          taken :+ column.head
        )

    differences(values, Vector.empty)
  }

  /**
   * The claim, built as a term rather than as text that is parsed back.
   *
   * `Readback` exists because a term printed and re-read is a term somebody has to check, and a
   * generator that stated its claims by printing them would be proposing the statement its printer
   * produced rather than the one it fitted.
   */
  private def claimFor(summand: Term, coefficients: Vector[Rational]): Either[String, Term] = {
    val index = Term.variable("n", natural)

    for {
      embedding <- signature.theory
        .constant(Peano.EmbeddingName, Type.fun(natural, real))
        .left
        .map(_.message)
      embedded <- Term.app(embedding, index).left.map(_.message)
      polynomial <- polynomialOf(embedded, coefficients)
      left <- sumOf(summand, index)
      equation <- Term.eq(left, polynomial).left.map(_.message)
      closed <- logic.mkForall(index, equation).left.map(_.message)
    } yield closed
  }

  /** `Σ c_j * x(x-1)...(x-j+1) / j!`, with the zero coefficients left out. */
  private def polynomialOf(x: Term, coefficients: Vector[Rational]): Either[String, Term] = {
    val terms = coefficients.zipWithIndex.filterNot(_._1.isZero).map { case (coefficient, j) =>
      val scale = coefficient / Rational.of(factorial(j))
      fallingOf(x, j).flatMap(falling => scaled(scale, falling))
    }

    terms.foldLeft(Right(Vector.empty): Either[String, Vector[Term]]) { (acc, next) =>
      for { done <- acc; term <- next } yield done :+ term
    }.flatMap { parts =>
      parts.toList match {
        case Nil => numeralOfReals(Rational.zero)
        case first :: rest =>
          rest.foldLeft(Right(first): Either[String, Term]) { (acc, next) =>
            acc.flatMap(running => binary(Real.Addition, running, next))
          }
      }
    }
  }

  /** `x * (x - 1) * ... * (x - (j - 1))`, and `1` when `j` is zero. */
  private def fallingOf(x: Term, j: Int): Either[String, Term] =
    if (j == 0) numeralOfReals(Rational.one)
    else
      (1 until j).foldLeft(Right(x): Either[String, Term]) { (acc, step) =>
        for {
          running <- acc
          offset <- numeralOfReals(Rational.of(BigInt(step)))
          lowered <- binary(Real.Subtraction, x, offset)
          product <- binary(Real.Multiplication, running, lowered)
        } yield product
      }

  /** `a * body / b`, written so that a whole coefficient does not carry a denominator of one. */
  private def scaled(factor: Rational, body: Term): Either[String, Term] =
    for {
      numerator <- numeralOfReals(Rational(factor.numerator, 1))
      multiplied <-
        if (factor.numerator == 1) Right(body) else binary(Real.Multiplication, numerator, body)
      result <-
        if (factor.denominator == 1) Right(multiplied)
        else
          numeralOfReals(Rational(factor.denominator, 1))
            .flatMap(divisor => binary(Real.Division, multiplied, divisor))
    } yield result

  private def numeralOfReals(value: Rational): Either[String, Term] =
    if (value.denominator != 1) Left(s"$value is not a numeral of this theory")
    else if (value.numerator >= 0) Numeral.of(signature, value.numerator).left.map(_.message)
    else
      for {
        positive <- Numeral.of(signature, -value.numerator).left.map(_.message)
        negation <- signature.theory
          .constant(Real.Negation, Type.fun(real, real))
          .left
          .map(_.message)
        applied <- Term.app(negation, positive).left.map(_.message)
      } yield applied

  private def binary(name: String, left: Term, right: Term): Either[String, Term] =
    for {
      operator <- signature.theory
        .constant(name, Type.fun(real, Type.fun(real, real)))
        .left
        .map(_.message)
      applied <- Term.appAll(operator, List(left, right)).left.map(_.message)
    } yield applied

  private def factorial(n: Int): BigInt = (1 to n).foldLeft(BigInt(1))(_ * _)

  /**
   * The four equations the induction runs on, and there are no others.
   *
   * The same four `rules` was read from, held once in each form because the two halves want
   * different things: sampling rewrites with them and the induction is handed the theorems.
   */
  private val held: Vector[Kernel.Thm] = Family.equationsOf(chain)
}

object Family {

  /**
   * How many values are sampled, which bounds the degree this can find.
   *
   * Ten, and the number is a budget rather than a discovery about mathematics: a polynomial of
   * degree `d` needs `d + 1` points and this keeps [[Slack]] in hand, so the degrees reachable are
   * up to seven. Sampling further costs a rewriting per point of a sum with that many terms in it,
   * which grows quadratically, and nothing measured has wanted a degree past four.
   */
  val Points: Int = 10

  /**
   * How many points must remain unused when the difference column vanishes.
   *
   * Two, so a fit always agreed at two values it was not determined by. One would make every fit
   * exactly determined and the screen would pass everything; the theorem at the end is what
   * settles it either way, and this is only about not proposing claims that were never going to
   * stand.
   */
  val Slack: Int = 2

  /** What came of asking for a closed form, in four answers that are not each other. */
  enum Outcome:

    /** A theorem: the sum equals the polynomial at every `n`. */
    case Found(claim: Term, theorem: Kernel.Thm, degree: Int, samples: Vector[Rational])

    /**
     * The values are not a polynomial of any degree this sampled.
     *
     * Not a failure of the prover and not a claim that no closed form exists: `Sum (\i. Power 2 i)`
     * has one and it is exponential. The samples come back so that a reader can see what the
     * family actually does.
     */
    case NotPolynomial(samples: Vector[Rational], sampled: Int)

    /**
     * The fit was stated and the prover refused it.
     *
     * The interesting failure, and the reason the fit is a screen rather than an answer: a family
     * that agrees at ten points and diverges at eleven arrives here, with the claim that was put
     * so that a person can look at it.
     */
    case NotCertified(claim: Term, refusal: String)

    /** The summand, or one of its values, could not be read at all. Nothing was fitted. */
    case Unreadable(why: String)

  /**
   * The equations a closed form is sampled and proved from, which are always the same eight.
   *
   * The two that matter are `Peano`'s: `real_of_num ZERO = 0` and
   * `real_of_num (SUC n) = real_of_num n + 1` are what let a polynomial in `n` be stated at all and
   * what make the induction step a ring identity in one atom. The six recurrences are what unfold a
   * sum, a power and a product far enough for the sampling to reach a number.
   *
   * The power and the product are there so that a family that is **not** polynomial gets the
   * honest answer. Without them `Sum (\i. Power 2 i)` stopped at `0 + Power 2 ZERO` and came back
   * as unreadable, which says the reader failed; with them it reduces to 0, 1, 3, 7, 15 and comes
   * back as [[Outcome.NotPolynomial]], which says what is true about the family.
   */
  private[tactics] def equationsOf(chain: Chain): Vector[Kernel.Thm] =
    Vector(
      chain.series.fact(Series.AtZero),
      chain.series.fact(Series.AtSuccessor),
      chain.series.fact(Series.PowerAtZero),
      chain.series.fact(Series.PowerAtSuccessor),
      chain.series.fact(Series.ProdAtZero),
      chain.series.fact(Series.ProdAtSuccessor),
      chain.peano.fact(Peano.EmbedsZero),
      chain.peano.fact(Peano.EmbedsSuccessor)
    ).flatMap(_.toOption)

  /** Over the standard chain. */
  lazy val standard: Family = construct(Chain.standard).fold(
    error => throw new IllegalStateException(s"the family search does not build: ${error.message}"),
    identity
  )

  /** Over a chain of one's own. */
  def construct(chain: Chain): Either[LogicError, Family] =
    Rewrite.Rule.all(chain.logic, equationsOf(chain)).map(new Family(chain, _))
}
