package garden.xeno.symbolum

/**
 * An expression evaluated to as many digits as you ask for, and nothing where it cannot be.
 *
 * [[Expr.eval]] answers in `Double` and throws where the question has no answer: an unbound
 * variable, a zero divisor, a logarithm of a negative number. This answers in `BigDecimal` at the
 * precision [[Arbitrary]] was built to, and returns nothing in those places instead of throwing.
 * The difference in the return type is the point rather than a convenience: a screening loop asks
 * this question of thousands of points and wants "no answer here" to be a value it can skip, not a
 * control transfer it has to catch.
 *
 * == What it does not evaluate ==
 *
 * `Derivative` and `Integral`, which the `Double` evaluator answers by numerical differentiation
 * and quadrature. Those are approximations whose error is a property of the step size and not of
 * the arithmetic, so computing them to fifty digits would produce fifty digits of which six mean
 * anything. Refusing says so; answering would not. [[Precise.Declined]] names them and a test
 * checks that list against the node types this module actually defines, so a new one cannot be
 * quietly dropped into the catch-all.
 *
 * == What a literal costs ==
 *
 * `Num` holds a fraction of two `Double`s. A fraction of whole numbers is exact and this evaluates
 * it exactly, which is why `1/3` is worth a hundred digits here and `0.3333333333333333` is worth
 * sixteen wherever it came from. A literal that entered as a `Double` carries sixteen digits and no
 * arithmetic can recover a seventeenth, so `Dsl.e`, which is `Num(math.E)`, is a sixteen-digit
 * number in an expression however precisely the rest of it is evaluated. [[Arbitrary.e]] is the
 * constant to use instead, supplied through the point.
 *
 * == The constants are supplied and not assumed ==
 *
 * `Dsl.pi` is `Var("pi")` and this module gives that name no special meaning anywhere else, so
 * neither does this: a point that does not bind `pi` gets no answer, rather than an answer about a
 * number the caller did not mean. [[named]] is the map to merge in when the caller does mean it.
 *
 * == How much of the precision survives a deep expression ==
 *
 * Each step rounds to the precision asked for, so an expression of `n` steps carries an error of
 * about `n` units in the last place. That is the honest reading and it is why the comparison this
 * feeds, `Arbitrary.agree`, takes a slack: at fifty digits a tree of a thousand nodes is still
 * right to forty-six, and a caller comparing two such trees should not be asking about the
 * fiftieth.
 */
final class Precise private (val arithmetic: Arbitrary) {

  /** The digits this instance answers to. */
  def digits: Int = arithmetic.digits

  /**
   * The named constants, for a caller that means them.
   *
   * `pi` because `Dsl.pi` is a variable of that name, and `e` because `Dsl.e` is a sixteen-digit
   * literal and a caller who wants the constant has to say so.
   */
  def named: Map[String, BigDecimal] = Map("pi" -> arithmetic.pi, "e" -> arithmetic.e)

  /** The value of the expression at the point, or nothing where there is no value. */
  def at(expression: Expr, point: Map[String, BigDecimal]): Option[BigDecimal] = {
    def all(parts: Vector[Expr]): Option[Vector[BigDecimal]] =
      parts.foldLeft[Option[Vector[BigDecimal]]](Some(Vector.empty)) { (done, part) =>
        for {
          values <- done
          value <- at(part, point)
        } yield values :+ value
      }

    expression match {
      case literal: Num => arithmetic.fraction(literal.numerator, literal.denominator)
      case Var(name) => point.get(name)

      case Add(terms) => all(terms).map(arithmetic.sum)
      case Mul(factors) => all(factors).map(arithmetic.product)
      case Sub(parts) => all(parts).map(arithmetic.less)
      case Div(operands) => all(operands).flatMap(arithmetic.over)
      case Neg(argument) => at(argument, point).map(arithmetic.negated)

      case Pow(base, exponent) =>
        for {
          b <- at(base, point)
          e <- at(exponent, point)
          value <- arithmetic.power(b, e)
        } yield value

      case Exp(argument) => at(argument, point).flatMap(arithmetic.exp)
      case Log(argument) => at(argument, point).flatMap(arithmetic.log)
      case Sin(argument) => at(argument, point).flatMap(arithmetic.sin)
      case Cos(argument) => at(argument, point).flatMap(arithmetic.cos)
      case Tan(argument) => at(argument, point).flatMap(arithmetic.tan)

      // Everything else, which today is `Derivative` and `Integral` and tomorrow is whatever
      // somebody adds. The list in the companion is what keeps that from being silent.
      case _ => None
    }
  }

  /**
   * How many significant digits the two sides agree to at this point, and `None` when it is all of
   * them or when either side has no value.
   *
   * The number a screening report is about. A pair that agrees to nine digits and a pair that
   * agrees to forty-nine are both "agreed" to a `Double` screen and are not the same lead.
   */
  def agreement(left: Expr, right: Expr, point: Map[String, BigDecimal]): Option[Int] =
    for {
      a <- at(left, point)
      b <- at(right, point)
      digits <- arithmetic.agreeingDigits(a, b)
    } yield digits
}

object Precise {

  /** The node types this evaluates. */
  val Handled: Vector[String] =
    Vector("Num", "Var", "Add", "Mul", "Sub", "Div", "Neg", "Pow", "Exp", "Log", "Sin", "Cos",
      "Tan")

  /**
   * The node types this deliberately does not evaluate, and why.
   *
   * Both are approximations in the `Double` evaluator too, and their error comes from a step size
   * rather than from the arithmetic. Asking for fifty digits of a five-point finite difference
   * produces fifty digits, six of which are about the derivative and forty-four about the step.
   */
  val Declined: Vector[String] = Vector("Derivative", "Integral")

  /** To `digits` decimal digits. */
  def to(digits: Int): Precise = new Precise(Arbitrary.to(digits))

  /** Over a given arithmetic, for a caller that has one already. */
  def over(arithmetic: Arbitrary): Precise = new Precise(arithmetic)

  /** At the precision the discovery loop screens at. See `Arbitrary.standard`. */
  lazy val standard: Precise = new Precise(Arbitrary.standard)
}
