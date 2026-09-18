package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A defined constant of `num` at concrete arguments, as an equation the kernel built.
 *
 * `NUM_DIV`, `NUM_MOD`, `NUM_GCD`, `NUM_FLOOR` and `NUM_CEIL` denote and are characterised by
 * lemmas, and nothing computed one: until 2026-09-18 `NUM_DIV 17 5 = 3` was not a theorem anything
 * here produced, and a caller wanting the value derived it by hand through
 * `NUM_DIV_MOD_UNIQUE`, one number at a time.
 *
 * == What a value is here, and why it is an equation rather than a number ==
 *
 * Every method below returns a theorem. A procedure that returned `3` would be a second
 * arithmetic, believed because it is written in Scala, and the whole arrangement this repository
 * describes is that the fast side proposes and the kernel checks. So the answer to "what is
 * `NUM_DIV 17 5`" is `|- NUM_DIV 17 5 = 3`, and the value is read off it.
 *
 * == The table, and why it is a table ==
 *
 * [[Value.Routes]] is one entry per constant: the characterisation it is read off, how many
 * arguments it takes, and what proves it. A constant is added by adding a row, which is the
 * property the card that asked for this made a condition: a procedure that named its constants in
 * its own control flow would be rewritten by every addition.
 *
 * `NUM_DIV` and `NUM_MOD` are one route because they are one lemma. `NUM_DIV_MOD_UNIQUE` says that
 * `m = n * q + r` with `r < n` determines **both**, so the two rows differ by which half of the
 * conclusion they keep.
 *
 * == What it costs, and why that was the whole design question ==
 *
 * Two axioms: choice and infinity, which is what the naturals cost and what every characterisation
 * lemma spent here already costs. The route that suggests itself — embed into the reals, compute
 * there, come back — was measured on the day this was written and produces the same equations at
 * **sixteen**, because `NUM_REAL_INJECTIVE` rests on the reals. `Digits` exists so that this one
 * does not have to. `ValueSpec` asserts the two rather than describing them.
 *
 * == What it refuses ==
 *
 * A constant with no row, by name, and an argument that is not a numeral of `num`, by value. It is
 * not a decision procedure for anything: handed `NUM_GCD` today it says it has no route, which is
 * a statement about this table and not about the constant.
 */
final class Value private (val digits: Digits, val modular: Modular) {

  /** The constants this can evaluate, which is what a caller should ask before asking for one. */
  def reachable: Vector[String] = Value.Routes.keys.toVector.sorted

  /**
   * `|- <constant> <arguments> = <value>`, or a refusal naming what stopped it.
   *
   * The arguments are values rather than terms, which is the same decision `Arithmetic.add` makes
   * one floor down: a caller holding a term holds a numeral it read from somewhere, and reading it
   * back is `Notation.valueOfNumeral`. What this takes is what it can compute with.
   */
  def of(constant: String, arguments: Vector[BigInt]): Either[LogicError, Kernel.Thm] =
    Value.Routes.get(constant) match {
      // `TypeError` and not `MissingDefinition`, which is what this said first and which reads
      // "no definition of NUM_GCD in this theory": there is one, and saying otherwise sends a
      // caller to look for a constant that is right where they left it. What is missing is a row
      // in this table, and the message says which rows there are.
      case None =>
        Left(
          TypeError(
            s"$constant has no row in this table; what it evaluates is ${reachable.mkString(", ")}"
          )
        )

      case Some(route) =>
        if (route.arity != arguments.size)
          Left(
            TypeError(
              s"$constant takes ${route.arity} argument(s) and was given ${arguments.size}"
            )
          )
        else route.prove(this, arguments)
    }

  /**
   * `|- NUM_GCD a b = <their greatest common divisor>`, for numerals that are not both zero.
   *
   * The card that asked for this left a decision here and it is taken: **the characterisation and
   * Bezout, not Euclid's algorithm**. Euclid is a definition by well-founded recursion, which this
   * system does not have, so that route waits on a piece of work that is not this one; the
   * characterisation asks for nothing new and costs more per value, which is a trade that only
   * matters to a caller computing many.
   *
   * Two divisibilities meet at `NUM_DIVIDES_ANTISYM`. That the answer divides the gcd is
   * `NUM_GCD_DIVIDES`, which is the greatest-common-divisor property: it divides both, so it
   * divides the gcd. The other direction is where Bezout is spent, and it is spent as a **witness**
   * rather than as a theorem: for `a` and `b` not both zero there are `x` and `y` with
   * `a * x = b * y + c`, [[Value.combination]] finds them by searching, and what the kernel then
   * checks is one equation between numerals. The gcd divides `a`, hence `a * x`, hence
   * `b * y + c`; it divides `b`, hence `b * y`; and `NUM_DIVIDES_SUMMAND` takes the second from the
   * first.
   *
   * `NUM_GCD ZERO ZERO` is refused rather than answered, and the refusal is the one `Modular`
   * already argues for: with both arguments zero there is no greatest common divisor to choose, so
   * every fact about the constant carries "not both zero" and nothing is provable about that term.
   *
   * A zero on **one** side is not that case and is not a special one either, except in the Bezout
   * half: `a * x = b * y + c` has no solution at `a = ZERO`, because `c` is then `b`. It does not
   * need one — the gcd divides the other argument, which **is** the answer, so the side that would
   * have been reached through the combination is reached directly.
   */
  private[theories] def greatestCommonDivisor(
    left: BigInt,
    right: BigInt
  ): Either[LogicError, Kernel.Thm] = {
    val rules = modular.logic.rules
    val answer = left.gcd(right)

    for {
      leftTerm <- digits.numeral(left)
      rightTerm <- digits.numeral(right)
      answerTerm <- digits.numeral(answer)
      _ <-
        if (left != 0 || right != 0) Right(())
        else
          // One literal and not two joined, which is a shape `NotationBoundarySpec` asks about: a
          // description assembled from pieces is one nobody can read off the source at the site.
          // What is missing from it, that there is no greatest common divisor of nothing and
          // nothing to have been chosen, is in this method's docstring.
          Left(
            NotOfForm(
              "a pair that is not two zeros, since nothing is provable about NUM_GCD ZERO ZERO",
              leftTerm
            )
          )

      gcdOf <- LogicError.lift(modular.theory.constant(Modular.GcdName, Value.Binary))
      gcdTerm <- LogicError.lift(Term.appAll(gcdOf, List(leftTerm, rightTerm)))
      notBothZero <- either(left != 0, leftTerm, rightTerm, left, right)

      dividesLeft <- divides(answer, left)
      dividesRight <- divides(answer, right)
      greatest <- modular.fact(Modular.GcdDivides)
      answerDividesGcd <- rules
        .specAll(greatest, List(leftTerm, rightTerm, answerTerm))
        .flatMap(rules.mp(_, notBothZero))
        .flatMap(step => rules.conjIntro(dividesLeft, dividesRight).flatMap(rules.mp(step, _)))

      gcdDividesLeft <- modular
        .fact(Modular.GcdDividesLeft)
        .flatMap(rules.specAll(_, List(leftTerm, rightTerm)))
        .flatMap(rules.mp(_, notBothZero))
      gcdDividesRight <- modular
        .fact(Modular.GcdDividesRight)
        .flatMap(rules.specAll(_, List(leftTerm, rightTerm)))
        .flatMap(rules.mp(_, notBothZero))

      gcdDividesAnswer <-
        if (left == 0) Right(gcdDividesRight)
        else if (right == 0) Right(gcdDividesLeft)
        else throughCombination(left, right, answer, gcdTerm, gcdDividesLeft, gcdDividesRight)

      antisymmetric <- modular.fact(Modular.DividesAntisym)
      same <- rules
        .specAll(antisymmetric, List(answerTerm, gcdTerm))
        .flatMap(step => rules.conjIntro(answerDividesGcd, gcdDividesAnswer).flatMap(rules.mp(step, _)))
      result <- Conv.sym(same)
    } yield result
  }

  /**
   * `|- NUM_DIVIDES g c` from the gcd dividing both arguments, through one Bezout combination.
   *
   * The combination is found by searching and checked by the kernel, which is this repository's
   * arrangement at its smallest: what is believed is the equation `a * x = b * y + c` between four
   * numerals, and how `x` and `y` were come by is nobody's business.
   */
  private def throughCombination(
    left: BigInt,
    right: BigInt,
    answer: BigInt,
    gcdTerm: Term,
    gcdDividesLeft: Kernel.Thm,
    gcdDividesRight: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = modular.logic.rules

    for {
      pair <- Value.combination(left, right, answer)
      (multiplier, counter) = pair

      leftTerm <- digits.numeral(left)
      rightTerm <- digits.numeral(right)
      answerTerm <- digits.numeral(answer)
      multiplierTerm <- digits.numeral(multiplier)
      counterTerm <- digits.numeral(counter)

      dividesProduct <- modular.fact(Modular.DividesMul)
      timesMultiplier <- rules
        .specAll(dividesProduct, List(gcdTerm, leftTerm, multiplierTerm))
        .flatMap(rules.mp(_, gcdDividesLeft))
      timesCounter <- rules
        .specAll(dividesProduct, List(gcdTerm, rightTerm, counterTerm))
        .flatMap(rules.mp(_, gcdDividesRight))

      identity <- combined(left, multiplier, right, counter, answer)
      divisibility <- LogicError.lift(
        modular.theory.constant(Modular.DividesName, Type.fun(Value.Numbers, Type.fun(Value.Numbers, Type.Bool)))
      )
      partial <- LogicError.lift(Term.app(divisibility, gcdTerm))
      moved <- Conv.apTerm(partial, identity).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, timesMultiplier)))

      summand <- modular.fact(Modular.DividesSummand)
      product <- LogicError.lift(
        modular.theory.constant(Peano.Multiplication, Value.Binary)
      )
      rightProduct <- LogicError.lift(Term.appAll(product, List(rightTerm, counterTerm)))
      result <- rules
        .specAll(summand, List(gcdTerm, rightProduct, answerTerm))
        .flatMap(rules.mp(_, timesCounter))
        .flatMap(rules.mp(_, moved))
    } yield result
  }

  /** `|- a * x = b * y + c`, which is the combination with its three numeral computations in it. */
  private def combined(
    left: BigInt,
    multiplier: BigInt,
    right: BigInt,
    counter: BigInt,
    answer: BigInt
  ): Either[LogicError, Kernel.Thm] =
    for {
      leftSide <- digits.multiply(left, multiplier)
      rightSide <- digits.multiply(right, counter)
      answerTerm <- digits.numeral(answer)
      sum <- digits.add(right * counter, answer)
      addition <- LogicError.lift(modular.theory.constant(Peano.Addition, Value.Binary))
      shifted <- Conv.apTerm(addition, rightSide).flatMap(Conv.apThm(_, answerTerm))
      settled <- Conv.trans(shifted, sum).flatMap(Conv.sym)
      result <- Conv.trans(leftSide, settled)
    } yield result

  /** `|- NUM_DIVIDES d m`, for numerals where the first divides the second. */
  private def divides(divisor: BigInt, multiple: BigInt): Either[LogicError, Kernel.Thm] = {
    val rules = modular.logic.rules

    for {
      divisorTerm <- digits.numeral(divisor)
      multipleTerm <- digits.numeral(multiple)
      _ <-
        if (divisor != 0 && multiple % divisor == 0) Right(())
        else if (divisor == 0 && multiple == 0) Right(())
        else Left(NotOfForm(s"a multiple of $divisor, and $multiple is not one", multipleTerm))

      factor = if (divisor == 0) BigInt(0) else multiple / divisor
      factorTerm <- digits.numeral(factor)
      product <- digits.multiply(divisor, factor)
      equation <- Conv.sym(product)
      introduction <- modular.fact(Modular.DividesIntro)
      result <- rules
        .specAll(introduction, List(divisorTerm, multipleTerm, factorTerm))
        .flatMap(rules.mp(_, equation))
    } yield result
  }

  /** `|- ~(a = ZERO) \/ ~(b = ZERO)`, from whichever of the two is not zero. */
  private def either(
    onTheLeft: Boolean,
    leftTerm: Term,
    rightTerm: Term,
    left: BigInt,
    right: BigInt
  ): Either[LogicError, Kernel.Thm] = {
    val logic = modular.logic
    val rules = logic.rules

    for {
      zero <- LogicError.lift(modular.theory.constant(Natural.NumberZero, Value.Numbers))
      leftEquation <- LogicError.lift(Term.eq(leftTerm, zero))
      rightEquation <- LogicError.lift(Term.eq(rightTerm, zero))
      leftDenial <- LogicError.lift(Term.app(logic.negation, leftEquation))
      rightDenial <- LogicError.lift(Term.app(logic.negation, rightEquation))
      held <- if (onTheLeft) notZero(left) else notZero(right)
      result <-
        if (onTheLeft) rules.disjIntro1(rightDenial, held)
        else rules.disjIntro2(leftDenial, held)
    } yield result
  }

  /**
   * `|- ~(v = ZERO)` for a positive numeral, which is `0 < v` read as a refusal.
   *
   * `Digits.below` is what says the number is positive, and nothing is below zero, so a number that
   * were zero would be below itself. The same two lines are in `Collatz`, about the empty word, and
   * they are here rather than shared because what they are about is a different constant.
   */
  private def notZero(value: BigInt): Either[LogicError, Kernel.Thm] = {
    val logic = modular.logic
    val rules = logic.rules

    for {
      term <- digits.numeral(value)
      zero <- LogicError.lift(modular.theory.constant(Natural.NumberZero, Value.Numbers))
      order <- LogicError.lift(
        modular.theory.constant(Peano.StrictOrder, Type.fun(Value.Numbers, Type.fun(Value.Numbers, Type.Bool)))
      )
      positive <- digits.below(0, value)
      equation <- LogicError.lift(Term.eq(term, zero))
      assumed <- LogicError.lift(Kernel.assume(equation))
      partial <- LogicError.lift(Term.app(order, zero))
      absurd <- Conv
        .apTerm(partial, assumed)
        .flatMap(congruent => LogicError.lift(Kernel.eqMp(congruent, positive)))
      refused <- digits.peano.fact(Peano.NotBelowZero).flatMap(rules.spec(zero, _))
      falsity <- rules.notElim(refused, absurd)
      result <- rules.notIntro(equation, falsity)
    } yield result
  }

  /** `|- NUM_DIV m n = m/n`, and `|- NUM_MOD m n = m%n`, which are one derivation. */
  private[theories] def division(
    numerator: BigInt,
    divisor: BigInt,
    wantQuotient: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val logic = modular.logic
    val rules = logic.rules

    // Division by zero is not a hole in the table: both constants are total and `Modular` publishes
    // what they are there, so the case is a specialisation rather than a refusal. It is also the
    // one case the uniqueness lemma cannot cover, since `r < n` is unmeetable at `n = ZERO`.
    if (divisor == 0)
      for {
        term <- digits.numeral(numerator)
        fact <- modular.fact(if (wantQuotient) Modular.DivAtZero else Modular.ModAtZero)
        result <- rules.spec(term, fact)
      } yield result
    else {
      val quotient = numerator / divisor
      val remainder = numerator % divisor

      for {
        numeratorTerm <- digits.numeral(numerator)
        divisorTerm <- digits.numeral(divisor)
        quotientTerm <- digits.numeral(quotient)
        remainderTerm <- digits.numeral(remainder)

        product <- digits.multiply(divisor, quotient)
        sum <- digits.add(divisor * quotient, remainder)
        addition <- LogicError.lift(
          modular.theory.constant(Peano.Addition, Value.Binary)
        )
        shifted <- Conv.apTerm(addition, product).flatMap(Conv.apThm(_, remainderTerm))
        identity <- Conv.trans(shifted, sum).flatMap(Conv.sym)

        smaller <- digits.below(remainder, divisor)
        determined <- modular.fact(Modular.DivisionDetermined)
        instance <- rules.specAll(
          determined,
          List(numeratorTerm, divisorTerm, quotientTerm, remainderTerm)
        )
        both <- rules.conjIntro(identity, smaller).flatMap(rules.mp(instance, _))
        half <- if (wantQuotient) rules.conjElim1(both) else rules.conjElim2(both)
        result <- Conv.sym(half)
      } yield result
    }
  }
}

object Value {

  /**
   * One constant, with what it is read off and what proves it.
   *
   * `note` is what a reader wants before trusting a row: which lemma the value rests on, and what
   * about the constant made that lemma the one to spend. It is carried here rather than written in
   * a comment beside the row so that a row cannot be added without one.
   */
  final case class Route(
    arity: Int,
    characterisation: String,
    note: String,
    prove: (Value, Vector[BigInt]) => Either[LogicError, Kernel.Thm]
  )

  /**
   * What this evaluates, which is two of the five the card that asked for it names.
   *
   * The other three are rows nobody has written rather than constants this refuses on principle,
   * and the difference is what [[Value.of]]'s refusal says. `NUM_FLOOR` and `NUM_CEIL` carry
   * `0 <= x` as a written hypothesis and their arguments are reals, so their row needs an
   * obligation this table has no shape for yet; `NUM_GCD` is characterised rather than computed,
   * and its row spends Bezout rather than a uniqueness.
   */
  val Routes: Map[String, Route] = Map(
    Modular.DivName -> Route(
      2,
      Modular.DivisionDetermined,
      "the quotient is determined by `m = n * q + r` with `r < n`, and at a zero divisor by " +
        "`NUM_DIV_ZERO`, which is where the uniqueness cannot reach because `r < ZERO` is unmeetable",
      (value, arguments) => value.division(arguments(0), arguments(1), wantQuotient = true)
    ),
    Modular.ModName -> Route(
      2,
      Modular.DivisionDetermined,
      "the remainder of the same division, which is the other half of the same conclusion",
      (value, arguments) => value.division(arguments(0), arguments(1), wantQuotient = false)
    ),
    Modular.GcdName -> Route(
      2,
      Modular.GcdDivides,
      "the answer divides the gcd because it divides both, and the gcd divides the answer through " +
        "one Bezout combination found by searching and checked as an equation between numerals; " +
        "the two meet at `NUM_DIVIDES_ANTISYM`, and two zeros are refused because nothing is " +
        "provable about `NUM_GCD ZERO ZERO`",
      (value, arguments) => value.greatestCommonDivisor(arguments(0), arguments(1))
    )
  )

  /**
   * `x` and `y` with `a * x = b * y + c`, found by searching rather than by an algorithm.
   *
   * Bezout says the pair exists for `c` the greatest common divisor, and the classical route to it
   * is the extended Euclidean algorithm, which produces a coefficient that may be negative and then
   * needs its sign argued about over a type with no negative numbers. Searching `x` upwards avoids
   * that entirely: the solutions are a residue class modulo `b / c`, so one is found within that
   * many steps, and what leaves this function is a pair of numbers the derivation proves an
   * equation about. Nothing downstream trusts the search.
   */
  private[theories] def combination(
    left: BigInt,
    right: BigInt,
    answer: BigInt
  ): Either[LogicError, (BigInt, BigInt)] = {
    val bound = if (answer == 0) BigInt(1) else right / answer + 1

    val found = (BigInt(0) to bound).view
      .map(multiplier => (multiplier, left * multiplier - answer))
      .collectFirst {
        case (multiplier, remainder) if remainder >= 0 && right != 0 && remainder % right == 0 =>
          (multiplier, remainder / right)
      }

    found.toRight(
      TypeError(
        s"no combination a * x = b * y + c for a = $left, b = $right and c = $answer within $bound steps"
      )
    )
  }

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)

  private val Binary: Type = Type.fun(Numbers, Type.fun(Numbers, Numbers))

  /** Over a chain, which is where both halves it needs are built. */
  def construct(chain: Chain): Either[LogicError, Value] =
    for {
      semiring <- Semiring.construct(chain.peano)
      digits <- Digits.construct(semiring)
    } yield new Value(digits, chain.modular)

  /** The same, for a caller that has already built the arithmetic. */
  def over(digits: Digits, modular: Modular): Value = new Value(digits, modular)
}
