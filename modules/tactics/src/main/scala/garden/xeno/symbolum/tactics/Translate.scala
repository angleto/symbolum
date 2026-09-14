package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.{Add, Div, Expr, Mul, Neg, Num, Pow, Rational, Sub, Var}
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Natural, Numeral, Peano, Real, RealTheory, Signature}

/**
 * The border between the computer algebra system and the logic: an `Expr` becomes a `Term`.
 *
 * This is the only place the two sides meet, and it is deliberately thin. A translation that
 * quietly changed the meaning of an expression would be a way to make the kernel certify something
 * other than what the oracle claimed, so what it does is rename constructors: nothing is reordered,
 * no identity is applied, and no term is simplified on the way across.
 *
 * == The one computation, and where it is confined ==
 *
 * An exponent is a number, not a spelling. `x ^ (2 + 2)` is `x ^ 4`, and accepting the second while
 * refusing the first would make the border a statement about how somebody wrote a number rather
 * than about what the theory can say. So an exponent with no variable in it is evaluated here, by
 * [[closedExponent]] below: a small total function over the arithmetic constructors, on `Rational`'s
 * exact fractions rather than on the doubles inside them.
 *
 * It is deliberately not `Expr.simplify`. The simplifier is the untrusted half of this repository
 * and carries rewrites that hold only under hypotheses it does not record; letting it decide what
 * exponent a term carries would move it inside the border this file exists to be. Thirty lines that
 * can be read in one sitting are what that costs, and the two are not interchangeable however
 * closely they agree today.
 *
 * == What `x ^ 0` becomes, and why that is not a side condition ==
 *
 * The numeral 1, for every base, and there is nothing conditional about it. Expanding `x ^ n` into
 * a product of `n` copies makes `x ^ 0` the empty product, and the empty product is the unit of the
 * ring whichever base was raised. `Pow` says the same, and so do HOL Light and Mathlib, which prove
 * it with no hypothesis. The convention that leaves `0 ^ 0` undefined is the analytic one, about a
 * limit, and this theory has no limits to take.
 *
 * An earlier version of this comment claimed the opposite, that `x ^ 0` was 1 only for a non-zero
 * base and that this border was quietly dropping a side condition. It was wrong: it read an
 * algebraic expansion as an analytic one.
 *
 * == The fragment ==
 *
 * The theory of the reals has `+`, `*`, unary and binary `-`, `/`, the order and the numerals.
 * Division is in that list because `x / y` abbreviates `x * inv y`, and unfolding an abbreviation
 * asks for nothing: the hypothesis `~(y = 0)` belongs to cancelling `y` against `inv y`, which is a
 * tactic's step and not this border's. The `Div` case below records when the two stopped being
 * treated as one thing.
 *
 * Outside the fragment are a constant the theory does not have, a cosine or a logarithm or an
 * exponential or a derivative or an integral; a literal that is not one of the numerals, which are
 * the integers, whether it is fractional or inexact; and an exponent this reader will not expand.
 * Such an expression is refused with [[OutsideFragment]], which is not a defect report but the
 * truthful answer, and the refusal says which of them it was rather than only that something was
 * outside.
 *
 * A power with a whole non-negative exponent is expanded into a product, because the theory has no
 * exponentiation constant. That is exact, and it is bounded, and an exponent fails in four ways
 * that are kept apart: a symbolic one, a fractional one, which is a root, a negative one, which is
 * an inverse this reader does not expand although the same claim written as a quotient is read, and
 * one above [[MaximumExponent]], which would expand into a term nobody can hold.
 *
 * == The second target, which is the naturals ==
 *
 * An expression does not say what type it is about; the development it came from does. Until
 * 2026-09-11 this reader had one answer, the reals, so a claim about whole numbers could be stated
 * here only by forgetting that they were whole. [[Target]] is the caller saying which, and the
 * naturals are read **through the embedding**: a variable becomes `real_of_num v` with `v` of type
 * `num`, and the claim that comes out is a claim about the image of the naturals in the reals.
 *
 * That is the arrangement `Peano` was built for and the one HOL Light writes `&n` for. It is
 * faithful because `real_of_num` is an injective homomorphism of the ordered semiring: a sum goes
 * to a sum ([[Peano.EmbedsSum]]), a product to a product ([[Peano.EmbedsProduct]]), zero to zero
 * and a successor to a successor, so `P(n)` over the naturals and `P(real_of_num n)` over the
 * reals are the same claim about the same numbers. Nothing about that reading is a coercion taken
 * in silence: the embedding is written into the term and a reader sees it.
 *
 * What it buys is that the arithmetic the tactics decide is the arithmetic the statement is in.
 * There is no decision procedure for `num` and `Peano` says so; `real_of_num n` is an atom the
 * procedures for the reals already handle, so a statement about naturals is put to them rather
 * than refused for the type it is about.
 *
 * == What the naturals refuse, and why refusing is the whole point ==
 *
 * `-` and `/` are **not** the reals' operators at that type, and reading them as such is the
 * silent semantic step this file exists not to take. Subtraction on the naturals is truncated, so
 * `3 - 5` is zero and not minus two; division is the floor, so `1 / 4` is zero and not a quarter.
 * Both are refused by name under [[Target.Naturals]], and so is a negation, which the naturals do
 * not have at all.
 *
 * The corpus supplies the witness rather than the argument supplying it. miniF2F's
 * `mathd_algebra_314` is `(n : ℕ) (h₀ : n = 11) : (1 / 4)^(n + 1) * 2^(2 * n) = 1 / 4`, and every
 * literal in it is a natural: `1 / 4` is zero, both sides are zero, and the statement Lean holds is
 * `0 = 0`. Reading those quotients as the reals' would hand the kernel a statement about fourths
 * that nobody wrote, and it would very likely go on to certify it. Refusing loses one statement;
 * translating loses the guarantee that a proof is a proof of what was asked.
 */
object Translate {

  /** Above this, expanding a power into a product costs more than it is worth. */
  val MaximumExponent: Int = 16

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val natural: Type = TyApp(Natural.TypeName, Nil)
  private val binary: Type = Type.fun(real, Type.fun(real, real))

  /**
   * Which type the variables of an expression stand at.
   *
   * The expression itself does not say, and neither does the algebra system, which has one sort of
   * unknown. Whoever hands an expression over knows: a corpus reader knows because the source
   * declared the binders, and a caller building a goal knows because it chose the variables. So it
   * is a parameter rather than something inferred, and there is no third answer that means "work
   * it out": an expression whose variables are of two different types is two expressions with a
   * coercion between them, and that is a thing to refuse rather than to guess at.
   */
  enum Target:

    /** The variables are reals, and every operator is the reals' own. */
    case Reals

    /**
     * The variables are naturals, read through `real_of_num` into the reals.
     *
     * The statement that comes out is about the image of the naturals, which is the same claim
     * about the same numbers, and it is in the arithmetic the tactics decide. What this target
     * refuses is the part of the reals' arithmetic that the naturals do not share: subtraction,
     * division and negation. See the note at the top of the file, which carries the corpus
     * statement that shows what reading them anyway would produce.
     */
    case Naturals

  /** An expression of the computer algebra system as a term of the theory of the reals. */
  def toTerm(reals: Signature, expression: Expr): Either[TacticError, Term] =
    toTerm(reals, expression, Target.Reals)

  /**
   * The same, at a stated target type.
   *
   * The term is of type `real` whichever target is asked for: [[Target.Naturals]] does not produce
   * a term of type `num`, it produces the image of one. A caller that wants to quantify over the
   * naturals binds a variable of type `num`, which is what the variables inside the term already
   * are.
   */
  def toTerm(reals: Signature, expression: Expr, target: Target): Either[TacticError, Term] = {

    def constant(name: String, ty: Type): Either[TacticError, Term] =
      TacticError.lift(LogicError.lift(reals.theory.constant(name, ty)))

    /** `real_of_num v` for a variable of type `num`, which is how a natural enters the reals. */
    def embedded(name: String): Either[TacticError, Term] =
      for {
        operator <- constant(Peano.Embedding, Type.fun(natural, real))
        result <- TacticError.lift(LogicError.lift(
          Term.app(operator, Term.variable(name, natural))
        ))
      } yield result

    /** The refusal for an operator of the reals that is not the naturals' operator of that name. */
    def notTheSameOperator(current: Expr, what: String, at: String): Either[TacticError, Term] =
      Left(OutsideFragment(
        current,
        s"$what on the naturals is $at, and is not the reals' $what: reading it as the reals' " +
          "would state something other than what was written"
      ))

    def binaryApplication(name: String, left: Term, right: Term): Either[TacticError, Term] =
      for {
        operator <- constant(name, binary)
        result <- TacticError.lift(LogicError.lift(Term.appAll(operator, List(left, right))))
      } yield result

    def negated(argument: Term): Either[TacticError, Term] =
      for {
        operator <- constant(Real.Negation, Type.fun(real, real))
        result <- TacticError.lift(LogicError.lift(Term.app(operator, argument)))
      } yield result

    def numeral(value: BigInt): Either[TacticError, Term] =
      if (value >= 0) TacticError.lift(Numeral.of(reals, value))
      else TacticError.lift(Numeral.of(reals, -value)).flatMap(negated)

    def foldLeftWith(name: String, parts: Vector[Expr]): Either[TacticError, Term] =
      parts.toList match {
        case Nil => Left(OutsideFragment(expression, "an operator with no operands"))
        case first :: rest =>
          rest.foldLeft(go(first)) { (acc, part) =>
            for {
              running <- acc
              next <- go(part)
              combined <- binaryApplication(name, running, next)
            } yield combined
          }
      }

    def power(base: Expr, exponent: Int): Either[TacticError, Term] =
      // The empty product, which is one whatever the base was. See the note at the top of the file.
      if (exponent == 0) numeral(BigInt(1))
      else
        go(base).flatMap { translated =>
          (2 to exponent).foldLeft(Right(translated): Either[TacticError, Term]) { (acc, _) =>
            acc.flatMap(running => binaryApplication(Real.Multiplication, running, translated))
          }
        }

    def go(current: Expr): Either[TacticError, Term] = current match {
      case n: Num =>
        if (n.denominator != 1.0)
          // Representable since `div` became readable, and still refused: the numerals of this
          // theory are integers, and a literal that is not one would translate to a quotient
          // whose value RING cannot recover, since a numeral is a monomial's coefficient here
          // and never one of its atoms. Refusing names the fragment; translating would produce
          // a goal that parses and then fails for a reason the caller cannot act on.
          Left(OutsideFragment(current, "a fractional literal is not a numeral of this theory, whose numerals are integers"))
        else if (!Rational.isWhole(n.numerator))
          Left(OutsideFragment(current, "an inexact literal is not a numeral"))
        else if (n.numerator < 0 && target == Target.Naturals)
          Left(OutsideFragment(current, "a negative literal is not a natural number"))
        else numeral(BigInt(n.numerator.toLong))

      case Var(name) =>
        target match {
          case Target.Reals => Right(Term.variable(name, real))
          case Target.Naturals => embedded(name)
        }

      case Add(terms) => foldLeftWith(Real.Addition, terms)
      case Mul(factors) => foldLeftWith(Real.Multiplication, factors)

      case Sub(operands) =>
        target match {
          case Target.Reals => foldLeftWith(Real.Subtraction, operands)
          case Target.Naturals => notTheSameOperator(current, "subtraction", "truncated at zero")
        }

      case Neg(argument) =>
        target match {
          case Target.Reals => go(argument).flatMap(negated)
          case Target.Naturals =>
            Left(OutsideFragment(current, "the naturals have no negation"))
        }

      // Each refusal names which of the four things went wrong, because "outside the fragment"
      // covers a symbolic exponent, a root, an inverse and a term too large to hold, and those
      // suggest different next steps to whoever is reading the failure.
      case Pow(base, exponent) =>
        closedExponent(exponent) match {
          case None =>
            Left(OutsideFragment(
              current,
              "an exponent that is not closed arithmetic is not a numeral, and the theory has no " +
                "exponentiation constant"
            ))

          case Some(fraction) =>
            wholeValue(fraction) match {
              case None =>
                Left(OutsideFragment(
                  current,
                  "a fractional exponent is a root, which the theory has no constant for"
                ))

              case Some(value) if value < 0 =>
                Left(OutsideFragment(
                  current,
                  "a negative exponent is an inverse, which this reader does not expand: " +
                    "write it as a quotient if the identity holds without cancelling it"
                ))

              case Some(value) if value > MaximumExponent =>
                Left(OutsideFragment(
                  current,
                  s"an exponent above $MaximumExponent expands into a product nobody can hold"
                ))

              case Some(value) => power(base, value)
            }
        }

      // Read, and it used to be refused. `x / y` abbreviates `x * inv y`, and unfolding an
      // abbreviation asks for nothing: what asks for `~(y = 0)` is cancelling `y` against
      // `inv y`, which is a different step and belongs to the tactic, not to the reader. The
      // sentence that kept quotients out named the cancellation and was applied to the
      // unfolding, so seven of the ten refusals in the RING corpus were quotients held out by
      // a reason that was never about them. Folded left, so `a / b / c` is `(a / b) / c`.
      case Div(operands) =>
        target match {
          case Target.Reals => foldLeftWith(Real.Division, operands)
          case Target.Naturals => notTheSameOperator(current, "division", "the floor of the quotient")
        }

      case other =>
        Left(OutsideFragment(other, "the theory of the reals has no constant for this"))
    }

    go(expression)
  }

  /**
   * The value of an exponent with no variable in it, or `None` when it has one.
   *
   * Total, and deliberately small: a literal, a negation, the four arithmetic operators, and a
   * power of any of those. Anything else, a variable or a cosine or an integral, is not something
   * this has an answer for, and the caller refuses it by name. The arithmetic is `Rational`'s, on
   * the fraction rather than on the double inside it, so `2 + 2` is 4 and not a value near 4; a
   * result that leaves `Rational`'s exact regime comes back as a fraction [[wholeValue]] then
   * declines, rather than as a rounded exponent nobody asked for.
   *
   * See the note at the top of this file for why it is not `Expr.simplify`.
   */
  private def closedExponent(expression: Expr): Option[Rational.Fraction] = {

    def negated(fraction: Rational.Fraction): Rational.Fraction =
      Rational.multiply(fraction, (-1.0, 1.0))

    def combine(
      parts: Vector[Expr],
      operation: (Rational.Fraction, Rational.Fraction) => Option[Rational.Fraction]
    ): Option[Rational.Fraction] =
      parts
        .map(closedExponent)
        .reduceOption((left, right) =>
          for {
            first <- left
            second <- right
            combined <- operation(first, second)
          } yield combined
        )
        .flatten

    expression match {
      case n: Num => Some(n.fraction)
      case Neg(argument) => closedExponent(argument).map(negated)
      case Add(parts) => combine(parts, (a, b) => Some(Rational.add(a, b)))
      case Sub(parts) => combine(parts, (a, b) => Some(Rational.add(a, negated(b))))
      case Mul(parts) => combine(parts, (a, b) => Some(Rational.multiply(a, b)))

      // The two guards are here rather than left to `Rational`, which throws on both: an exponent
      // written `1 / 0` or `0 ^ -1` is a refusal like any other and must not take the process down.
      case Div(parts) =>
        combine(parts, (a, b) => if (b._1 == 0.0) None else Some(Rational.divide(a, b)))

      case Pow(base, exponent) =>
        for {
          value <- closedExponent(base)
          raise <- closedExponent(exponent).flatMap(wholeValue)
          if !(value._1 == 0.0 && raise < 0)
          result <- Rational.power(value, raise)
        } yield result

      case _ => None
    }
  }

  /** A fraction as a whole number, or `None` if it is not one, or is too large to be an `Int`. */
  private def wholeValue(fraction: Rational.Fraction): Option[Int] = {
    val (numerator, denominator) = fraction
    if (denominator == 1.0 && Rational.isWhole(numerator) &&
      math.abs(numerator) <= Int.MaxValue.toDouble) Some(numerator.toInt)
    else None
  }

  /** Whether an expression can be stated at all, without building the term. */
  def isTranslatable(reals: Signature, expression: Expr): Boolean =
    isTranslatable(reals, expression, Target.Reals)

  /** The same, at a stated target type. */
  def isTranslatable(reals: Signature, expression: Expr, target: Target): Boolean =
    toTerm(reals, expression, target).isRight
}
