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
    )
  )

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
