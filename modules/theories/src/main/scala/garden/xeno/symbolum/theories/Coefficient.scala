package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Arithmetic on the coefficient of a monomial, which is a rational number written as one numeral
 * over another.
 *
 * [[Polynomial]] keeps a coefficient as a number rather than expanding it into that many copies of
 * a term, and until now the number had to be whole. A quotient by a numeral therefore had nowhere
 * to go: `x / 2` unfolds to `x * inv 2`, `inv 2` became one of the monomial's atoms, and
 * `x / 2 + x / 2` was a monomial of degree two rather than the coefficient `1` on `x`. That is why
 * `x / 2 + x / 2 = x` was refused with everything else in place to prove it.
 *
 * == The shape of a coefficient ==
 *
 * In lowest terms, with the denominator at least one and the sign on the numerator:
 *
 *   - `n` for a whole positive coefficient, `-n` for a whole negative one;
 *   - `n * inv d` and `-n * inv d` when the denominator is above one.
 *
 * The sign is on the numerator and never on the denominator, and the denominator is never zero and
 * never negative, so two coefficients denote the same number exactly when they are the same term.
 * That is what [[Polynomial]] relies on when it compares two normal forms.
 *
 * == Why the side condition costs nothing here ==
 *
 * Every step below needs `d * inv d = 1`, which is `MUL_INVERSE` under `~(d = 0)`. The denominator
 * is a numeral, so [[Positivity.numeralNonZero]] proves that outright and the condition is
 * discharged rather than assumed: nothing this file produces carries a hypothesis. [[Field]] meets
 * the same condition on a symbolic denominator, cannot settle it, and passes it to the caller in
 * the sequent, which is the right answer there and would be the wrong one here.
 *
 * == The lemmas that carry their side conditions, and why there are so few ==
 *
 * Each is stated over variables and takes its side conditions as the equations they will be used
 * as, `x * inv x = 1`, rather than as `~(x = 0)`. So the lemmas know nothing about numerals and the
 * call sites do the discharging once per denominator.
 *
 * The first design of this had a cancellation rule, `x * k = y * k ==> x = y`, and with it the fact
 * that a field has no zero divisors. Neither is here, because nothing below cancels: every step
 * multiplies by a disguised `1` and rearranges, which a ring identity settles, and the two
 * expensive lemmas were only ever needed to undo something this never does.
 *
 * What is left over after them is not rational arithmetic at all. `RAT_EQ`'s premise is
 * `n * f = e * m` between four numerals, and that is [[Arithmetic.multiply]]. The reduction to
 * lowest terms, the comparison of two fractions, and the sign rules all end there.
 *
 * == Its facts are private machinery, and a reader who counts them should know why ==
 *
 * On 2026-09-13 a census turned up two files holding a `facts` map that `Library.of` does not
 * collect. One was `Magnitude`, and that was a defect: seventeen lemmas nobody could name, with
 * its constants missing from the widest signature. This is the other one and it is **not** the
 * same case, which is worth writing down because the two look identical from a distance.
 *
 * This file declares no constant and defines none: it proves things about `+`, `*`, `inv` and
 * `neg`, which the reals already have. Its map is private and no caller can read it, so these are
 * steps of a procedure rather than lemmas anybody holds, which is the position `Bounded` documents
 * from the other side, having no map at all.
 *
 * The part that is a judgement rather than a fact: five of them would be lemmas a library would
 * want, `INVERSE_OF_UNIT`, `ADD_CANCEL_RIGHT`, `ADD_CANCEL_INTO`, `NEG_MUL_NEG` and
 * `NEG_ADD_GATHER`, and three others, `ADD_SYM`, `ADD_INVERSE` and `MUL_ONE`, are names the
 * library already holds from below and would duplicate. Publishing the five means putting `Field`
 * in the chain, and `Field` is built by the tactics rather than by the chain, so that is a
 * different move from the one `Magnitude` needed and not one this file should make on its own.
 */
final class Coefficient private (
  val arithmetic: Arithmetic,
  val positivity: Positivity,
  published: Map[String, Kernel.Thm],
  private val rules: Map[String, Rewrite.Rule],
  private val mulInverse: Kernel.Thm,
  private val syntax: Coefficient.Syntax
) {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  private val facts: Map[String, Kernel.Thm] = Published.cite(published)

  import Coefficient.*

  val reals: RealTheory = arithmetic.reals

  private val derived = reals.logic.rules

  /* ------------------------------------------------------------ reading and writing */

  /**
   * The number a coefficient denotes, as numerator over denominator, or nothing if the term is not
   * one.
   *
   * A denominator of one means the term carried no inverse at all, so a whole coefficient reads
   * back as itself over one and the two cases stay one case for every caller.
   */
  def valueOf(term: Term): Option[(BigInt, BigInt)] = term match {
    case Mul(numerator, Inv(denominator)) =>
      for {
        top <- signedValue(numerator)
        bottom <- Numeral.valueOf(reals, denominator) if bottom > 1
      } yield (top, bottom)

    case whole => signedValue(whole).map((_, BigInt(1)))
  }

  /** The canonical term for a number, which is the one every other use of it must reach. */
  def termOf(numerator: BigInt, denominator: BigInt): Either[LogicError, Term] =
    for {
      _ <-
        if (denominator > 0 && (numerator == 0 || numerator.gcd(denominator) == 1)) Right(())
        else Left(NotOfForm("a fraction in lowest terms with a positive denominator", syntax.zero))
      magnitude <- Numeral.of(reals, numerator.abs)
      signed <- if (numerator < 0) negated(magnitude) else Right(magnitude)
      result <-
        if (denominator == 1) Right(signed)
        else
          for {
            bottom <- Numeral.of(reals, denominator)
            inverse <- LogicError.lift(Term.app(syntax.inverse, bottom))
            whole <- product(signed, inverse)
          } yield whole
    } yield result

  /** The value a signed numeral denotes, which is a coefficient whose denominator is one. */
  def signedValue(term: Term): Option[BigInt] = term match {
    case Neg(inner) => Numeral.valueOf(reals, inner).map(-_)
    case _ => Numeral.valueOf(reals, term)
  }

  /* --------------------------------------------------------------- the two operations */

  /**
   * `|- a + b = c`, for two coefficients.
   *
   * Four cases, and the first is the one that was here before rational coefficients existed: two
   * whole numbers add by the numeral procedures and nothing else happens. The other three put the
   * sum over a common denominator and then reduce it.
   */
  def add(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    (valueOf(left), valueOf(right)) match {
      case (Some((_, leftBottom)), Some((_, rightBottom))) =>
        if (leftBottom == 1 && rightBottom == 1) addWhole(left, right)
        else if (rightBottom == 1)
          // `a + b` with only the second whole: commute and use the case below, rather than a
          // second lemma that says the same thing with the arguments the other way round.
          for {
            whole <- sum(left, right)
            swapped <- at(AddSym, whole)
            rest <- add(right, left)
            result <- Conv.trans(swapped, rest)
          } yield result
        else if (leftBottom == 1) addWholeToFraction(left, right)
        else addFractions(left, right)

      case _ => Left(NotOfForm("a coefficient", left))
    }

  /** `|- a * b = c`, for two coefficients. */
  def multiply(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    (valueOf(left), valueOf(right)) match {
      case (Some((leftTop, leftBottom)), Some((rightTop, rightBottom))) =>
        if (leftBottom == 1 && rightBottom == 1) multiplyWhole(left, right)
        else
          for {
            gathered <- gatherProduct(left, right, leftBottom, rightBottom)
            result <- settleNumerator(gathered, leftTop * rightTop, leftBottom * rightBottom)
          } yield result

      case _ => Left(NotOfForm("a coefficient", left))
    }

  /**
   * `|- -c = c'`, the coefficient of the other sign.
   *
   * The sign lives on the numerator, so negating a fraction moves the negation past the inverse
   * rather than around it. `-(n * inv d)` and `(-n) * inv d` denote the same number and only the
   * second is the shape everything else here reads, which is the whole reason this is a step and
   * not a construction.
   */
  def negate(term: Term): Either[LogicError, Kernel.Thm] =
    valueOf(term) match {
      case None => Left(NotOfForm("a coefficient", term))

      case Some((numerator, denominator)) =>
        for {
          negated <- negated(term)
          result <-
            if (denominator == 1)
              if (numerator == 0) at(NegZero, negated)
              else if (numerator > 0) Right(Conv.refl(negated))
              else at(NegNeg, negated)
            else
              for {
                gathered <- at(NegMulGather, negated)
                form <- rightOf(gathered)
                sides <- destBinary(form)
                joined <-
                  if (numerator > 0) Right(gathered)
                  else
                    for {
                      unwrapped <- at(NegNeg, sides._1)
                      lifted <- onFirst(syntax.times, unwrapped, sides._2)
                      chained <- Conv.trans(gathered, lifted)
                    } yield chained
              } yield joined
        } yield result
    }

  /**
   * `|- inv c = r`, for a coefficient `c` that is not zero: its reciprocal, as a coefficient.
   *
   * This is where a quotient becomes a coefficient, and until 2026-09-09 the `c` had to be a
   * numeral above zero. Any coefficient reaches it now, because [[Coefficient.inverseOfUnit]] asks
   * for a factor of one instead of asking for `~(c = 0)`, and the factor is the reciprocal this
   * file computes anyway. So `inv (-1)`, `inv (2 * inv 3)` and `inv 2` are one case rather than an
   * atom, an atom and a case.
   *
   * `inv 1` is the case worth stating on its own, because it is `1` and not a fraction: leaving it
   * as an atom would give the number one two normal forms, which is the one failure a normal form
   * cannot have. It falls out here rather than being written down, since the reciprocal of `1/1`
   * is `1/1`.
   *
   * Zero is refused, and that is the rule that keeps `inv 0` an atom: nothing multiplies it to
   * one, so nothing here has anything to say about it.
   */
  def ofInverse(numerator: BigInt, denominator: BigInt): Either[LogicError, Kernel.Thm] =
    for {
      _ <-
        if (numerator != 0) Right(())
        else Left(NotOfForm("a coefficient that is not zero", syntax.zero))

      value <- termOf(numerator, denominator)
      // The reciprocal, put back into the shape everything here reads: the sign is on the
      // numerator, so inverting a negative coefficient moves the sign rather than leaving it on a
      // denominator, which would be a second term for one number.
      sign = if (numerator < 0) BigInt(-1) else BigInt(1)
      reciprocal <- termOf(sign * denominator, sign * numerator)

      product <- multiply(value, reciprocal)
      lemma <- fact(InverseOfUnit)
      instance <- derived.specAll(lemma, List(value, reciprocal))
      result <- derived.mp(instance, product)
    } yield result

  /**
   * `|- d * inv d = 1`, for a numeral above zero, with nothing assumed.
   *
   * The whole file rests on this one line, and the line is short only because [[Positivity]] is
   * below the ring: `MUL_INVERSE` is stated with `~(d = 0)` in front of it, and for a numeral that
   * is a theorem rather than a hypothesis.
   */
  def inverseOf(denominator: BigInt): Either[LogicError, Kernel.Thm] =
    for {
      numeral <- Numeral.of(reals, denominator)
      notZero <- positivity.numeralNonZero(denominator)
      instance <- derived.spec(numeral, mulInverse)
      result <- derived.mp(instance, notZero)
    } yield result

  /**
   * `|- inv b * inv d = inv m`, with `m` the numeral `b * d`.
   *
   * The lemma proves it with the product left as `b * d`, so the last step replaces that by the
   * numeral it evaluates to. Doing the multiplication first and rewriting the theorem afterwards
   * would need the numeral to be rewritten in one occurrence and not the other, which is the kind
   * of step that goes wrong silently; here both occurrences move together and there is nothing to
   * get right.
   */
  def inverseOfProduct(left: BigInt, right: BigInt): Either[LogicError, Kernel.Thm] =
    for {
      evaluated <- numeralProduct(left, right)
      backwards <- Conv.sym(evaluated)
      wholeFact <- inverseOf(left * right)
      asProduct <- rewriteWith(backwards, wholeFact)

      leftFact <- inverseOf(left)
      rightFact <- inverseOf(right)
      leftTerm <- Numeral.of(reals, left)
      rightTerm <- Numeral.of(reals, right)

      lemma <- fact(InverseTimes)
      applied <- instantiate(lemma, List(leftTerm, rightTerm), List(leftFact, rightFact, asProduct))
      folded <- Conv.apTerm(syntax.inverse, evaluated)
      result <- Conv.trans(applied, folded)
    } yield result

  /* --------------------------------------------------------------- the four addition cases */

  /** `|- a + b = c`, both whole: the sign cases, each carried by one lemma. */
  private def addWhole(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    for {
      leftValue <- signedValue(left).toRight(NotOfForm("a signed numeral", left))
      rightValue <- signedValue(right).toRight(NotOfForm("a signed numeral", right))
      result <-
        if (leftValue > 0 && rightValue > 0) arithmetic.add(leftValue, rightValue)
        else if (leftValue < 0 && rightValue < 0)
          for {
            whole <- sum(left, right)
            gathered <- at(NegAddGather, whole)
            added <- arithmetic.add(-leftValue, -rightValue)
            lifted <- Conv.apTerm(syntax.negation, added)
            joined <- Conv.trans(gathered, lifted)
          } yield joined
        else if (leftValue < 0)
          for {
            whole <- sum(left, right)
            swapped <- at(AddSym, whole)
            rest <- addWhole(right, left)
            joined <- Conv.trans(swapped, rest)
          } yield joined
        else mixedSum(leftValue, -rightValue)
    } yield result

  /**
   * `|- a + -b = c`, with `a` and `b` positive: the three ways two signs can settle.
   *
   * Subtraction of numerals is not a procedure of its own and does not need to be. `a + -b` with
   * `a` the larger is `d` where `b + d = a`, and that equation is what [[Arithmetic.add]] proves;
   * the lemma `(x + y) + -x = y` carries it across. So one addition procedure answers all four
   * sign cases, and the difference is computed on this side and checked on the other.
   */
  private def mixedSum(positive: BigInt, negative: BigInt): Either[LogicError, Kernel.Thm] =
    if (positive == negative)
      for {
        term <- Numeral.of(reals, positive)
        negatedTerm <- negated(term)
        whole <- sum(term, negatedTerm)
        result <- at(AddInverse, whole)
      } yield result
    else if (positive > negative)
      // `(b + d) + -b = d` with `b + d` rewritten to `a`, which is the addition run backwards.
      for {
        difference <- Numeral.of(reals, positive - negative)
        smaller <- Numeral.of(reals, negative)
        negatedSmaller <- negated(smaller)
        split <- sum(smaller, difference)
        pattern <- sum(split, negatedSmaller)
        cancelled <- at(CancelRight, pattern)
        added <- arithmetic.add(negative, positive - negative)
        reversed <- Conv.sym(added)
        lifted <- onFirst(syntax.plus, reversed, negatedSmaller)
        result <- Conv.trans(lifted, cancelled)
      } yield result
    else
      // `x + -(x + y) = -y`, the same trick with the larger numeral inside the negation.
      for {
        difference <- Numeral.of(reals, negative - positive)
        smaller <- Numeral.of(reals, positive)
        split <- sum(smaller, difference)
        negatedSplit <- negated(split)
        pattern <- sum(smaller, negatedSplit)
        cancelled <- at(CancelInto, pattern)
        added <- arithmetic.add(positive, negative - positive)
        reversed <- Conv.sym(added)
        negatedStep <- Conv.apTerm(syntax.negation, reversed)
        lifted <- onSecond(syntax.plus, smaller, negatedStep)
        result <- Conv.trans(lifted, cancelled)
      } yield result

  /** `|- a + c * inv d = e * inv f`, with the first coefficient whole. */
  private def addWholeToFraction(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    for {
      leftValue <- signedValue(left).toRight(NotOfForm("a signed numeral", left))
      rightValue <- valueOf(right).toRight(NotOfForm("a coefficient", right))
      (top, bottom) = rightValue

      bottomTerm <- Numeral.of(reals, bottom)
      topTerm <- termOf(top, 1)
      bottomFact <- inverseOf(bottom)

      lemma <- fact(AddWhole)
      applied <- instantiate(lemma, List(left, topTerm, bottomTerm), List(bottomFact))
      result <- settleNumerator(applied, leftValue * bottom + top, bottom)
    } yield result

  /** `|- a * inv b + c * inv d = e * inv f`, with both coefficients fractional. */
  private def addFractions(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    for {
      leftValue <- valueOf(left).toRight(NotOfForm("a coefficient", left))
      rightValue <- valueOf(right).toRight(NotOfForm("a coefficient", right))
      (leftTop, leftBottom) = leftValue
      (rightTop, rightBottom) = rightValue

      leftTopTerm <- termOf(leftTop, 1)
      rightTopTerm <- termOf(rightTop, 1)
      leftBottomTerm <- Numeral.of(reals, leftBottom)
      rightBottomTerm <- Numeral.of(reals, rightBottom)

      leftFact <- inverseOf(leftBottom)
      rightFact <- inverseOf(rightBottom)
      together <- inverseOfProduct(leftBottom, rightBottom)
      commonTerm <- rightOf(together)

      lemma <- fact(AddFractions)
      applied <- instantiate(
        lemma,
        List(leftTopTerm, leftBottomTerm, rightTopTerm, rightBottomTerm, commonTerm),
        List(leftFact, rightFact, together)
      )
      result <- settleNumerator(
        applied,
        leftTop * rightBottom + rightTop * leftBottom,
        leftBottom * rightBottom
      )
    } yield result

  /* ------------------------------------------------------------------- multiplication */

  /** `|- a * b = c`, both whole: the sign is a lemma and the digits are a procedure. */
  private def multiplyWhole(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    for {
      leftValue <- signedValue(left).toRight(NotOfForm("a signed numeral", left))
      rightValue <- signedValue(right).toRight(NotOfForm("a signed numeral", right))
      whole <- product(left, right)
      magnitude <- numeralProduct(leftValue.abs, rightValue.abs)
      result <-
        if (leftValue > 0 && rightValue > 0) Right(magnitude)
        else if (leftValue < 0 && rightValue < 0)
          at(NegMulNeg, whole).flatMap(Conv.trans(_, magnitude))
        else
          for {
            gathered <- at(if (leftValue < 0) NegMulLeft else NegMulRight, whole)
            lifted <- Conv.apTerm(syntax.negation, magnitude)
            joined <- Conv.trans(gathered, lifted)
          } yield joined
    } yield result

  /**
   * `|- a * b = n * inv m`, with the numerator left as a product and the denominators merged.
   *
   * Three shapes rather than one, and none of the three needs a side condition: moving a numerator
   * past an inverse is an identity of a commutative ring, because `inv d` is an atom to it. The
   * only place a condition is paid is where the two inverses become one.
   */
  private def gatherProduct(
    left: Term,
    right: Term,
    leftBottom: BigInt,
    rightBottom: BigInt
  ): Either[LogicError, Kernel.Thm] =
    for {
      whole <- product(left, right)
      result <-
        if (leftBottom == 1) at(MulWholeLeft, whole)
        else if (rightBottom == 1) at(MulWholeRight, whole)
        else
          for {
            spread <- at(MulFractions, whole)
            together <- inverseOfProduct(leftBottom, rightBottom)
            form <- rightOf(spread)
            sides <- destBinary(form)
            merged <- onSecond(syntax.times, sides._1, together)
            joined <- Conv.trans(spread, merged)
          } yield joined
    } yield result

  /* ---------------------------------------------------------------------- reduction */

  /**
   * Given `|- x = <numerator> * inv m`, work the numerator out and reduce the fraction.
   *
   * The numerator arrives as an expression over numerals, `a * d + c * b` from the addition lemma
   * or `a * c` from the multiplication one, because the lemmas are about variables and cannot do
   * arithmetic. Evaluating it here is the same two procedures the whole coefficients use.
   */
  private def settleNumerator(
    step: Kernel.Thm,
    numerator: BigInt,
    denominator: BigInt
  ): Either[LogicError, Kernel.Thm] =
    for {
      form <- rightOf(step)
      sides <- destBinary(form)
      evaluated <- evaluate(sides._1)
      lifted <- onFirst(syntax.times, evaluated, sides._2)
      joined <- Conv.trans(step, lifted)
      result <- reduce(joined, numerator, denominator)
    } yield result

  /** `|- e = n`, for an expression built from signed numerals by `+` and `*`. */
  private def evaluate(term: Term): Either[LogicError, Kernel.Thm] = term match {
    case _ if signedValue(term).isDefined => Right(Conv.refl(term))

    case Add(left, right) =>
      for {
        leftStep <- evaluate(left)
        rightStep <- evaluate(right)
        lifted <- onBoth(syntax.plus, leftStep, rightStep)
        form <- rightOf(lifted)
        sides <- destBinary(form)
        added <- addWhole(sides._1, sides._2)
        result <- Conv.trans(lifted, added)
      } yield result

    case Mul(left, right) =>
      for {
        leftStep <- evaluate(left)
        rightStep <- evaluate(right)
        lifted <- onBoth(syntax.times, leftStep, rightStep)
        form <- rightOf(lifted)
        sides <- destBinary(form)
        multiplied <- multiplyWhole(sides._1, sides._2)
        result <- Conv.trans(lifted, multiplied)
      } yield result

    case other => Left(NotOfForm("an expression over numerals", other))
  }

  /**
   * Given `|- x = n * inv m` with `n` and `m` numerals, put the fraction in lowest terms.
   *
   * Three outcomes, and the first two are what stop a fraction from surviving where a whole number
   * would do: a numerator of zero is zero, and a denominator that divides the numerator leaves a
   * numeral with no inverse in it at all. Only the third stays a fraction, and it is a fraction in
   * lowest terms because the premise checked is a cross-multiplication between numerals.
   */
  private def reduce(
    step: Kernel.Thm,
    numerator: BigInt,
    denominator: BigInt
  ): Either[LogicError, Kernel.Thm] = {
    val divisor = if (numerator == 0) denominator else numerator.gcd(denominator)
    val top = numerator / divisor
    val bottom = denominator / divisor

    for {
      form <- rightOf(step)
      reduced <-
        if (numerator == 0) at(MulZeroLeft, form)
        else if (bottom == 1)
          for {
            numeratorTerm <- termOf(numerator, 1)
            denominatorTerm <- Numeral.of(reals, denominator)
            topTerm <- termOf(top, 1)
            bottomFact <- inverseOf(denominator)
            split <- multiplyWhole(topTerm, denominatorTerm).flatMap(Conv.sym)
            lemma <- fact(WholeFraction)
            applied <- instantiate(
              lemma,
              List(numeratorTerm, denominatorTerm, topTerm),
              List(bottomFact, split)
            )
          } yield applied
        else
          for {
            numeratorTerm <- termOf(numerator, 1)
            denominatorTerm <- Numeral.of(reals, denominator)
            topTerm <- termOf(top, 1)
            bottomTerm <- Numeral.of(reals, bottom)
            denominatorFact <- inverseOf(denominator)
            bottomFact <- inverseOf(bottom)
            crossed <- crossMultiplication(numeratorTerm, bottomTerm, topTerm, denominatorTerm)
            lemma <- fact(SameFraction)
            applied <- instantiate(
              lemma,
              List(numeratorTerm, denominatorTerm, topTerm, bottomTerm),
              List(denominatorFact, bottomFact, crossed)
            )
          } yield applied
      result <- Conv.trans(step, reduced)
    } yield result
  }

  /** `|- n * f = e * m`, which is the whole of what makes two fractions the same one. */
  private def crossMultiplication(
    numerator: Term,
    bottom: Term,
    top: Term,
    denominator: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      left <- multiplyWhole(numerator, bottom)
      right <- multiplyWhole(top, denominator)
      leftForm <- rightOf(left)
      rightForm <- rightOf(right)
      _ <-
        if (leftForm == rightForm) Right(())
        else Left(NotEqualTo(rightForm, leftForm))
      backwards <- Conv.sym(right)
      result <- Conv.trans(left, backwards)
    } yield result

  /* ------------------------------------------------------------------------ plumbing */

  /**
   * `|- a * b = c`, for two numerals, with the unit taken out of the numeral procedure's way.
   *
   * Not an optimisation looking for a place to happen. Counted on 2026-09-04, 154 of the 224
   * numeral operations that normalising `(x + 1)^12` performs are a multiplication by one, because
   * the coefficients of a binomial arrive as ones and are multiplied by the coefficients of the
   * factor. Each of those is a full run of the rewriter under a four-hundred pass budget where an
   * instance of `MUL_ONE` is a single kernel call.
   */
  private def numeralProduct(left: BigInt, right: BigInt): Either[LogicError, Kernel.Thm] =
    for {
      leftTerm <- Numeral.of(reals, left)
      rightTerm <- Numeral.of(reals, right)
      whole <- product(leftTerm, rightTerm)
      result <-
        if (right == 1) at(MulOne, whole)
        else if (left == 1) at(MulOneLeft, whole)
        else arithmetic.multiply(left, right)
    } yield result

  private def rewriteWith(
    equation: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      rule <- Rewrite.Rule.all(reals.logic, Vector(equation))
      result <- Rewrite.inTheorem(rule, theorem)
    } yield result

  private def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** A lemma at its arguments, with each of its premises discharged by a theorem. */
  private def instantiate(
    lemma: Kernel.Thm,
    arguments: List[Term],
    premises: List[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      specialised <- derived.specAll(lemma, arguments)
      result <- premises.foldLeft(Right(specialised): Either[LogicError, Kernel.Thm]) {
        (acc, premise) => acc.flatMap(derived.mp(_, premise))
      }
    } yield result

  /** Instantiate a rewrite rule at the root of a term, refusing when it does not apply. */
  private def at(name: String, term: Term): Either[LogicError, Kernel.Thm] =
    rules.get(name).toRight(MissingDefinition(name)).flatMap { rule =>
      Matching.matchTerm(rule.variables, rule.lhs, term) match {
        case None => Left(NotOfForm(s"a term ${reals.show(rule.lhs)} matches", term))
        case Some(found) => LogicError.lift(found.instance(rule.theorem))
      }
    }

  private def sum(left: Term, right: Term): Either[LogicError, Term] =
    apply2(syntax.plus, left, right)

  private def product(left: Term, right: Term): Either[LogicError, Term] =
    apply2(syntax.times, left, right)

  private def negated(term: Term): Either[LogicError, Term] =
    LogicError.lift(Term.app(syntax.negation, term))

  private def apply2(operator: Term, left: Term, right: Term): Either[LogicError, Term] =
    for {
      partial <- LogicError.lift(Term.app(operator, left))
      whole <- LogicError.lift(Term.app(partial, right))
    } yield whole

  private def onSecond(
    operator: Term,
    first: Term,
    step: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- LogicError.lift(Term.app(operator, first))
      result <- Conv.apTerm(partial, step)
    } yield result

  private def onFirst(
    operator: Term,
    step: Kernel.Thm,
    second: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      applied <- Conv.apTerm(operator, step)
      result <- Conv.apThm(applied, second)
    } yield result

  private def onBoth(
    operator: Term,
    left: Kernel.Thm,
    right: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      applied <- Conv.apTerm(operator, left)
      result <- LogicError.lift(Kernel.mkComb(applied, right))
    } yield result

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def destBinary(term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(_, left), right) => Right((left, right))
    case other => Left(NotOfForm("an application of a binary operator", other))
  }

  private object Add {
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(Real.Addition, _), left), right) => Some((left, right))
      case _ => None
    }
  }

  private object Mul {
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(Real.Multiplication, _), left), right) => Some((left, right))
      case _ => None
    }
  }

  private object Neg {
    def unapply(term: Term): Option[Term] = term match {
      case App(Const(Real.Negation, _), argument) => Some(argument)
      case _ => None
    }
  }

  private object Inv {
    def unapply(term: Term): Option[Term] = term match {
      case App(Const(Real.Inverse, _), argument) => Some(argument)
      case _ => None
    }
  }
}

object Coefficient {

  /** The terms this procedure builds with, read once rather than at every step. */
  private[theories] final case class Syntax(
    plus: Term,
    times: Term,
    negation: Term,
    inverse: Term,
    zero: Term,
    one: Term
  )

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val binary: Type = Type.fun(real, Type.fun(real, real))
  private val unary: Type = Type.fun(real, real)

  /* The lemmas about whole coefficients, which moved here with the code that uses them. */

  val AddSym: String = "ADD_SYM"
  val AddInverse: String = "ADD_INVERSE"
  val MulOne: String = "MUL_ONE"
  val MulOneLeft: String = Arithmetic.OneOnTheLeft
  val MulZeroLeft: String = Arithmetic.ZeroTimes
  val NegAdd: String = Arithmetic.NegAdd
  val NegMulLeft: String = Arithmetic.NegMulLeft
  val NegMulRight: String = Arithmetic.NegMulRight
  val NegNeg: String = Arithmetic.NegNeg
  val NegZero: String = Arithmetic.NegZero

  val InverseOfUnit: String = "INVERSE_OF_UNIT"
  val CancelRight: String = "ADD_CANCEL_RIGHT"
  val CancelInto: String = "ADD_CANCEL_INTO"
  val NegMulNeg: String = "NEG_MUL_NEG"

  /** The reversed forms, which a rewriter needs as their own theorems because it is directional. */
  val NegAddGather: String = "NEG_ADD_GATHER"
  val NegMulGather: String = "NEG_MUL_GATHER"

  /* The lemmas about fractions. The first four carry their side conditions as the equations they
   * are used as; the last three are identities of a commutative ring with `inv d` as an atom. */

  val InverseTimes: String = "INV_TIMES"
  val AddFractions: String = "RAT_ADD"
  val AddWhole: String = "RAT_ADD_WHOLE"
  val SameFraction: String = "RAT_EQ"
  val WholeFraction: String = "RAT_WHOLE"

  val MulFractions: String = "MUL_FRACTIONS"
  val MulWholeLeft: String = "MUL_WHOLE_LEFT"
  val MulWholeRight: String = "MUL_WHOLE_RIGHT"

  /**
   * The lemmas with no side condition, each an identity of a commutative ring over variables.
   *
   * `inv b` and `inv d` are atoms to the expanding normalisation, so moving a numerator past one
   * asks for nothing and these are proved the same way every other structural lemma is. That is
   * the dividing line this file is organised around: rearranging a fraction is free, and only
   * turning two inverses into one costs a discharged condition.
   */
  val Lemmas: Vector[(String, String)] = Vector(
    CancelRight -> "(x:real + y:real) + -x = y",
    CancelInto -> "x:real + -(x + y:real) = -y",
    NegMulNeg -> "-x:real * -y:real = x * y",
    MulFractions -> "(a:real * inv b:real) * (c:real * inv d:real) = (a * c) * (inv b * inv d)",
    MulWholeLeft -> "a:real * (c:real * inv d:real) = (a * c) * inv d",
    MulWholeRight -> "(a:real * inv b:real) * c:real = (a * c) * inv b"
  )

  /** Built once over the standard arithmetic. */
  lazy val standard: Coefficient =
    construct(Arithmetic.standard, Positivity.standard).fold(
      error =>
        throw new IllegalStateException(s"the coefficient arithmetic does not build: ${error.message}"),
      identity
    )

  /** Prove what this needs, then keep the rewrites ready to instantiate. */
  def construct(
    arithmetic: Arithmetic,
    positivity: Positivity
  ): Either[LogicError, Coefficient] = {
    val reals = arithmetic.reals
    val logic = reals.logic

    def named(name: String): Either[LogicError, Kernel.Thm] =
      reals.axiom(name).orElse(arithmetic.lemma(name))

    for {
      syntax <- readSyntax(reals)

      inherited <- collect(
        Vector(
          AddSym, AddInverse, MulOne, MulOneLeft, MulZeroLeft, NegAdd, NegMulLeft, NegMulRight,
          NegNeg, NegZero
        ).map(name => named(name).map(name -> _))
      )

      proved <- collect(
        Lemmas.map { case (name, text) => proveIdentity(arithmetic, text).map(name -> _) }
      )

      addGather <- reverse(logic, inherited(NegAdd)).map(NegAddGather -> _)
      mulGather <- reverse(logic, inherited(NegMulLeft)).map(NegMulGather -> _)

      inverseTimes <- inverseTimes(arithmetic)
      inverseOfUnit <- inverseOfUnit(arithmetic)
      addFractions <- addFractions(arithmetic)
      addWhole <- addWhole(arithmetic)
      sameFraction <- sameFraction(arithmetic)
      wholeFraction <- wholeFraction(arithmetic)

      conditional = Map(
        InverseTimes -> inverseTimes,
        InverseOfUnit -> inverseOfUnit,
        AddFractions -> addFractions,
        AddWhole -> addWhole,
        SameFraction -> sameFraction,
        WholeFraction -> wholeFraction
      )

      rewritable = inherited ++ proved + addGather + mulGather
      rules <- collect(rewritable.toVector.map { case (name, theorem) =>
        Rewrite.Rule.of(logic, theorem).map(name -> _)
      })

      mulInverse <- reals.axiom("MUL_INVERSE")
    } yield new Coefficient(
      arithmetic,
      positivity,
      rewritable ++ conditional,
      rules,
      mulInverse,
      syntax
    )
  }

  /* --------------------------------------- the lemmas that carry their side conditions */

  /**
   * `|- !x y. x * y = 1 ==> inv x = y`: a factor of one has an inverse, and it is the other factor.
   *
   * What this buys is every denominator that is a constant and not a numeral. `inv (-1)` and
   * `inv (2 * inv 3)` were atoms, because `MUL_INVERSE` is stated under `~(d = 0)` and
   * [[Positivity]] proves that for a numeral and for nothing else. Here the question turns round:
   * a term that multiplies to one cannot be zero, and the reciprocal is a number this file already
   * knows how to compute. So the side condition is discharged by the arithmetic rather than by the
   * order, and the alternative — that a field has no zero divisors, which would put
   * `0 < inv d` and therefore the order below the ring — is not needed and is not proved.
   *
   * Two halves, and the first is the one worth reading. Were `x` zero the product would be zero and
   * therefore one, against `ONE_NOT_ZERO`, which is the only axiom separating the two numerals and
   * the same one `Positivity.zeroLessOne` turns on. With `~(x = 0)` in hand the rest is this file's
   * ordinary shape: `inv x = inv x * 1 = inv x * (x * y) = (x * inv x) * y = 1 * y = y`, which is
   * multiplying by a disguised one and rearranging, with nothing cancelled.
   */
  def inverseOfUnit(arithmetic: Arithmetic): Either[LogicError, Kernel.Thm] =
    derivation(arithmetic) { context =>
      import context.*

      val derived = reals.logic.rules

      for {
        unit <- assume("x:real * y:real = 1")

        x <- term("x:real")
        y <- term("y:real")
        inverse <- term("inv (x:real)")

        // `~(x = 0)`. Assume it is zero, and the product the premise calls one is zero instead.
        isZero <- assume("x:real = 0")
        scaled <- onFirst(isZero, y)
        toOne <- Conv.sym(scaled).flatMap(Conv.trans(_, unit))
        vanishes <- context.arithmetic.lemma(Arithmetic.ZeroTimes).flatMap(derived.spec(y, _))
        zeroIsOne <- Conv.sym(vanishes).flatMap(Conv.trans(_, toOne))
        distinct <- reals.axiom("ONE_NOT_ZERO")
        absurd <- Conv.sym(zeroIsOne).flatMap(derived.notElim(distinct, _))
        notZero <- derived.notIntro(isZero.conclusion, absurd)

        cancels <- reals
          .axiom("MUL_INVERSE")
          .flatMap(derived.spec(x, _))
          .flatMap(derived.mp(_, notZero))

        s1 <- identity("inv (x:real) = inv x * 1")
        s2 <- Conv.sym(unit).flatMap(onSecond(inverse, _))
        s3 <- identity("inv (x:real) * (x * y:real) = (x * inv x) * y")
        s4 <- onFirst(cancels, y)
        s5 <- identity("1 * y:real = y")

        chained <- chain(List(s1, s2, s3, s4, s5))
        result <- close(chained, List(unit), List("x", "y"))
      } yield result
    }

  /**
   * `|- !a b p q. a * p = 1 ==> b * q = 1 ==> (a * b) * (p * q) = 1`
   *
   * The reciprocal of a product is the product of the reciprocals, and saying it this way rather
   * than about `inv` is what makes it compose: the caller carries a reciprocal alongside each
   * denominator and builds the next one from it, and [[inverseOfUnit]] turns the whole into a
   * statement about `inv` once, at the end.
   *
   * **It needs no fact about zero divisors, and that is why [[Field]] can take a denominator
   * apart at all.** The obvious route to `inv (a * b) = inv a * inv b` derives `~(a * b = 0)` from
   * `~(a = 0)` and `~(b = 0)`, which is a real theorem with a case analysis behind it. Here nothing
   * is derived about `a * b`: the product of the reciprocals multiplies it to one by rearranging,
   * and a factor of one is an inverse.
   */
  def unitOfProduct(arithmetic: Arithmetic): Either[LogicError, Kernel.Thm] =
    derivation(arithmetic) { context =>
      import context.*

      for {
        ha <- assume("a:real * p:real = 1")
        hb <- assume("b:real * q:real = 1")

        s1 <- identity("(a:real * b:real) * (p:real * q:real) = (a * p) * (b * q)")
        halves <- onBoth(ha, hb)
        s2 <- identity("1 * 1 = 1")

        chained <- chain(List(s1, halves, s2))
        result <- close(chained, List(hb, ha), List("a", "b", "p", "q"))
      } yield result
    }

  /**
   * `|- !a p. a * p = 1 ==> -a * -p = 1`
   *
   * The same idea for the other shape a denominator wears. Two negations cancel by ring reasoning,
   * so a negated denominator costs exactly what the thing under the negation costs and not a
   * condition of its own.
   */
  def unitOfNegation(arithmetic: Arithmetic): Either[LogicError, Kernel.Thm] =
    derivation(arithmetic) { context =>
      import context.*

      for {
        ha <- assume("a:real * p:real = 1")

        s1 <- identity("-a:real * -p:real = a * p")
        chained <- chain(List(s1, ha))
        result <- close(chained, List(ha), List("a", "p"))
      } yield result
    }

  /**
   * `|- !a p. a * p = 1 ==> p * a = 1`
   *
   * Which is the reciprocal of `inv a`, when `p` is `inv a`: a term and its reciprocal are each
   * other's, and a denominator written `inv a` has `a` as its reciprocal rather than `inv (inv a)`.
   * Commutativity, stated as its own lemma only so that the caller composing reciprocals has the
   * same shape available for all four cases.
   */
  def unitReversed(arithmetic: Arithmetic): Either[LogicError, Kernel.Thm] =
    derivation(arithmetic) { context =>
      import context.*

      for {
        ha <- assume("a:real * p:real = 1")

        s1 <- identity("p:real * a:real = a * p")
        chained <- chain(List(s1, ha))
        result <- close(chained, List(ha), List("a", "p"))
      } yield result
    }

  /**
   * `|- !b d. b * inv b = 1 ==> d * inv d = 1 ==> (b * d) * inv (b * d) = 1
   *           ==> inv b * inv d = inv (b * d)`
   *
   * Forwards, and that is the point. Multiply by `1` written as `(b * d) * inv (b * d)`, rearrange,
   * which is a ring identity because every inverse in it is an atom to the ring, then read the two
   * premises off. The version of this that went through the uniqueness of an inverse needed a
   * cancellation rule and, with it, that a field has no zero divisors; neither is here, because
   * nothing cancels.
   */
  def inverseTimes(arithmetic: Arithmetic): Either[LogicError, Kernel.Thm] =
    derivation(arithmetic) { context =>
      import context.*

      for {
        hb <- assume("b:real * inv b = 1")
        hd <- assume("d:real * inv d = 1")
        hm <- assume("(b:real * d:real) * inv (b * d) = 1")

        factor <- term("inv b:real * inv d:real")
        inverse <- term("inv (b:real * d:real)")

        s1 <- identity("inv b:real * inv d:real = (inv b * inv d) * 1")
        s2 <- Conv.sym(hm).flatMap(onSecond(factor, _))
        s3 <- identity(
          "(inv b:real * inv d:real) * ((b * d) * inv (b * d)) = " +
            "((b * inv b) * (d * inv d)) * inv (b * d)"
        )
        halves <- onBoth(hb, hd)
        s4 <- onFirst(halves, inverse)
        s5 <- identity("(1 * 1) * inv (b:real * d:real) = inv (b * d)")

        chained <- chain(List(s1, s2, s3, s4, s5))
        result <- close(chained, List(hm, hd, hb), List("b", "d"))
      } yield result
    }

  /**
   * `|- !a b c d p. b * inv b = 1 ==> d * inv d = 1 ==> inv b * inv d = p
   *                 ==> a * inv b + c * inv d = (a * d + c * b) * p`
   *
   * Each summand is multiplied by the other's denominator over itself, which is `1`, and then both
   * carry the same factor and distributivity collects them. `p` is a variable rather than
   * `inv (b * d)` so that the caller supplies the numeral it has already worked out, and the lemma
   * never has to be told what a numeral is.
   */
  def addFractions(arithmetic: Arithmetic): Either[LogicError, Kernel.Thm] =
    derivation(arithmetic) { context =>
      import context.*

      for {
        hb <- assume("b:real * inv b = 1")
        hd <- assume("d:real * inv d = 1")
        hp <- assume("inv b:real * inv d:real = p:real")

        leftFactor <- term("a:real * inv b:real")
        rightFactor <- term("c:real * inv d:real")
        leftNumerator <- term("a:real * d:real")
        rightNumerator <- term("c:real * b:real")

        l1 <- identity("a:real * inv b:real = (a * inv b) * 1")
        l2 <- Conv.sym(hd).flatMap(onSecond(leftFactor, _))
        l3 <- identity(
          "(a:real * inv b:real) * (d * inv d) = (a * d) * (inv b * inv d)"
        )
        l4 <- onSecond(leftNumerator, hp)
        left <- chain(List(l1, l2, l3, l4))

        r1 <- identity("c:real * inv d:real = (c * inv d) * 1")
        r2 <- Conv.sym(hb).flatMap(onSecond(rightFactor, _))
        r3 <- identity(
          "(c:real * inv d:real) * (b * inv b) = (c * b) * (inv b * inv d)"
        )
        r4 <- onSecond(rightNumerator, hp)
        right <- chain(List(r1, r2, r3, r4))

        summed <- onBothPlus(left, right)
        collected <- identity(
          "(a:real * d:real) * p:real + (c:real * b:real) * p = (a * d + c * b) * p"
        )

        chained <- chain(List(summed, collected))
        result <- close(chained, List(hp, hd, hb), List("a", "b", "c", "d", "p"))
      } yield result
    }

  /**
   * `|- !a c d. d * inv d = 1 ==> a + c * inv d = (a * d + c) * inv d`
   *
   * The mixed case. It is a lemma of its own rather than the one above with `b` set to `1`, because
   * that would need `inv 1 = 1` and a whole coefficient would stop being written the way it is
   * written everywhere else.
   */
  def addWhole(arithmetic: Arithmetic): Either[LogicError, Kernel.Thm] =
    derivation(arithmetic) { context =>
      import context.*

      for {
        hd <- assume("d:real * inv d = 1")

        whole <- term("a:real")
        fraction <- term("c:real * inv d:real")

        l1 <- identity("a:real = a * 1")
        l2 <- Conv.sym(hd).flatMap(onSecond(whole, _))
        l3 <- identity("a:real * (d:real * inv d) = (a * d) * inv d")
        left <- chain(List(l1, l2, l3))

        summed <- onBothPlus(left, Conv.refl(fraction))
        collected <- identity(
          "(a:real * d:real) * inv d + c:real * inv d = (a * d + c) * inv d"
        )

        chained <- chain(List(summed, collected))
        result <- close(chained, List(hd), List("a", "c", "d"))
      } yield result
    }

  /**
   * `|- !n m e f. m * inv m = 1 ==> f * inv f = 1 ==> n * f = e * m ==> n * inv m = e * inv f`
   *
   * Two fractions are the same one exactly when the cross-multiplication agrees, and this is what
   * makes that usable: the premise is an equation between products of numerals, which
   * [[Arithmetic.multiply]] settles. Reducing a fraction to lowest terms and comparing two of them
   * are the same step, so there is one lemma rather than two.
   */
  def sameFraction(arithmetic: Arithmetic): Either[LogicError, Kernel.Thm] =
    derivation(arithmetic) { context =>
      import context.*

      for {
        hm <- assume("m:real * inv m = 1")
        hf <- assume("f:real * inv f = 1")
        hc <- assume("n:real * f:real = e:real * m:real")

        factor <- term("n:real * inv m:real")
        inverse <- term("inv f:real")
        scaled <- term("e:real")

        q1 <- identity("n:real * inv m:real = (n * inv m) * 1")
        q2 <- Conv.sym(hf).flatMap(onSecond(factor, _))
        q3 <- identity(
          "(n:real * inv m:real) * (f * inv f) = ((n * f) * inv m) * inv f"
        )
        crossed <- onFirstTimes(hc, "inv m:real")
        q4 <- onFirst(crossed, inverse)
        q5 <- identity(
          "((e:real * m:real) * inv m) * inv f:real = (e * (m * inv m)) * inv f"
        )
        settled <- onSecond(scaled, hm)
        q6 <- onFirst(settled, inverse)
        q7 <- identity("(e:real * 1) * inv f:real = e * inv f")

        chained <- chain(List(q1, q2, q3, q4, q5, q6, q7))
        result <- close(chained, List(hc, hf, hm), List("n", "m", "e", "f"))
      } yield result
    }

  /**
   * `|- !n m e. m * inv m = 1 ==> n = e * m ==> n * inv m = e`
   *
   * The case where the fraction was not one: a denominator that divides its numerator leaves a
   * whole coefficient with no inverse anywhere in it. Without this, `x / 2 + x / 2` would reach
   * `1 * inv 1 * x` and every whole number would have two spellings.
   */
  def wholeFraction(arithmetic: Arithmetic): Either[LogicError, Kernel.Thm] =
    derivation(arithmetic) { context =>
      import context.*

      for {
        hm <- assume("m:real * inv m = 1")
        hc <- assume("n:real = e:real * m:real")

        inverse <- term("inv m:real")
        scaled <- term("e:real")

        w1 <- onFirst(hc, inverse)
        w2 <- identity("(e:real * m:real) * inv m = e * (m * inv m)")
        settled <- onSecond(scaled, hm)
        w4 <- identity("e:real * 1 = e")

        chained <- chain(List(w1, w2, settled, w4))
        result <- close(chained, List(hc, hm), List("n", "m", "e"))
      } yield result
    }

  /* ------------------------------------------------------------------------ plumbing */

  /**
   * What a derivation by hand needs, gathered once so that each lemma above reads as its chain.
   *
   * They are all the same shape: assume the side conditions as equations, walk from one side
   * to the other through ring identities and rewrites with those equations, then discharge and
   * generalise. Written out at each of them, the plumbing would be four times the mathematics.
   */
  private final class Context(val arithmetic: Arithmetic, val syntax: Syntax) {
    val reals: RealTheory = arithmetic.reals
    private val derived = reals.logic.rules

    def term(text: String): Either[LogicError, Term] = reals.term(text)

    def assume(text: String): Either[LogicError, Kernel.Thm] =
      reals.proposition(text).flatMap(statement => LogicError.lift(Kernel.assume(statement)))

    /** An identity of a commutative ring, settled by the expanding normalisation. */
    def identity(text: String): Either[LogicError, Kernel.Thm] =
      reals
        .proposition(text)
        .flatMap(Rewrite.proveEquation(reals.logic, arithmetic.normalisation, _))

    def onSecond(first: Term, step: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        partial <- LogicError.lift(Term.app(syntax.times, first))
        result <- Conv.apTerm(partial, step)
      } yield result

    def onFirst(step: Kernel.Thm, second: Term): Either[LogicError, Kernel.Thm] =
      for {
        applied <- Conv.apTerm(syntax.times, step)
        result <- Conv.apThm(applied, second)
      } yield result

    def onFirstTimes(step: Kernel.Thm, secondText: String): Either[LogicError, Kernel.Thm] =
      term(secondText).flatMap(onFirst(step, _))

    def onBoth(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        applied <- Conv.apTerm(syntax.times, left)
        result <- LogicError.lift(Kernel.mkComb(applied, right))
      } yield result

    def onBothPlus(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        applied <- Conv.apTerm(syntax.plus, left)
        result <- LogicError.lift(Kernel.mkComb(applied, right))
      } yield result

    def chain(steps: List[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      steps match {
        case Nil => Left(NotOfForm("at least one step", syntax.one))
        case head :: rest =>
          rest.foldLeft(Right(head): Either[LogicError, Kernel.Thm]) { (acc, step) =>
            acc.flatMap(Conv.trans(_, step))
          }
      }

    /** Discharge the assumptions, innermost first, then quantify the variables in order. */
    def close(
      theorem: Kernel.Thm,
      assumptions: List[Kernel.Thm],
      variables: List[String]
    ): Either[LogicError, Kernel.Thm] =
      for {
        discharged <- assumptions.foldLeft(Right(theorem): Either[LogicError, Kernel.Thm]) {
          (acc, assumption) => acc.flatMap(derived.disch(assumption.conclusion, _))
        }
        result <- derived.genAll(
          discharged,
          variables.map(name => Term.variable(name, real))
        )
      } yield result
  }

  private def derivation(arithmetic: Arithmetic)(
    body: Context => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    readSyntax(arithmetic.reals).flatMap(syntax => body(new Context(arithmetic, syntax)))

  /** `|- !x. l = r` from an identity written in the theory's notation, through the expanding form. */
  private def proveIdentity(
    arithmetic: Arithmetic,
    text: String
  ): Either[LogicError, Kernel.Thm] = {
    val reals = arithmetic.reals

    for {
      statement <- reals.proposition(text)
      proved <- Rewrite.proveEquation(reals.logic, arithmetic.normalisation, statement)
      general <- generaliseAll(reals, proved)
    } yield general
  }

  /** `|- !x. r = l` from `|- !x. l = r`: a rewriter reads an equation in one direction only. */
  private def reverse(logic: Logic, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Rewrite.specialiseAll(logic, theorem)
      flipped <- Conv.sym(stripped._2)
      general <- logic.rules.genAll(flipped, stripped._1.toList)
    } yield general

  private def generaliseAll(
    reals: Signature,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    reals.logic.rules.genAll(
      theorem,
      Term.freeVariables(theorem.conclusion).toList.sortBy(_.name)
    )

  private def readSyntax(reals: Signature): Either[LogicError, Syntax] =
    for {
      plus <- LogicError.lift(reals.theory.constant(Real.Addition, binary))
      times <- LogicError.lift(reals.theory.constant(Real.Multiplication, binary))
      negation <- LogicError.lift(reals.theory.constant(Real.Negation, unary))
      inverse <- LogicError.lift(reals.theory.constant(Real.Inverse, unary))
      zero <- reals.term("0")
      one <- reals.term("1")
    } yield Syntax(plus, times, negation, inverse, zero, one)

  private def collect[T](
    steps: Vector[Either[LogicError, (String, T)]]
  ): Either[LogicError, Map[String, T]] =
    steps.foldLeft(Right(Map.empty[String, T]): Either[LogicError, Map[String, T]]) {
      (acc, step) =>
        for {
          collected <- acc
          entry <- step
        } yield collected.updated(entry._1, entry._2)
    }
}
