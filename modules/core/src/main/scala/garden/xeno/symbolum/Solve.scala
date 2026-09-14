package garden.xeno.symbolum

/**
 * Solver for `expression = 0`.
 *
 * Handles polynomials of degree one and two in the requested variable, and falls back to solving
 * each factor of a product separately.
 *
 * @example {{{
 * Solve.solve(Add(Vector(Var("x"), Num(2))), "x")   // List(-2)
 * Solve.solve(Sub(Vector(Pow(Var("x"), Num(2)), Num(4))), "x")  // List(2, -2)
 * }}}
 */
object Solve {

  /**
   * Solve `equation = 0` for `variable`.
   *
   * Returns an empty list both when there is no solution and when every value is one: the return
   * type cannot express an infinite solution set, and inventing a sentinel for it would put the
   * burden on every caller.
   */
  def solve(equation: Expr, variable: String)
           (implicit config: SimplificationConfig = SimplificationConfig.Default): List[Expr] = {
    val simplified = equation.simplify(config)

    coefficientsByDegree(simplified, variable) match {
      case Some(coefficients) =>
        def at(degree: Int): Expr = coefficients.getOrElse(degree, Num(0))
        coefficients.keys.max match {
          case 0 => List.empty
          case 1 => linear(at(1), at(0))
          case 2 => quadratic(at(2), at(1), at(0))
          case _ => factored(simplified, variable)
        }
      case None => factored(simplified, variable)
    }
  }

  /**
   * The coefficients of `expr` as a polynomial in `variable`, keyed by degree.
   *
   * `None` when `expr` is not a polynomial in that variable, for instance because the variable
   * appears under a function or in a denominator.
   *
   * Deciding the degree up front is what the previous implementation lacked. It extracted a
   * linear coefficient by pattern, treated any term it did not recognise as a constant, and so
   * answered `x^2 - 5x + 6 = 0` with `x = 6/5`: the squared term had been read as a constant with
   * coefficient zero and the equation solved as if it were linear.
   */
  private def coefficientsByDegree(expr: Expr, variable: String)
                                  (implicit config: SimplificationConfig): Option[Map[Int, Expr]] = {
    def ofTerm(term: Expr): Option[Map[Int, Expr]] = {
      val (numericCoefficient, base) = Canonical.splitCoefficient(term)
      val factors = base match {
        case Mul(fs) => fs
        case n: Num if n.value == 1.0 => Vector.empty
        case other => Vector(other)
      }

      // `None` as soon as one factor mentions the variable in a way no degree describes: the
      // fold carries the refusal rather than a flag read after the loop, so a later factor cannot
      // go on contributing to a degree that will be thrown away.
      val collected = factors.foldLeft(Option((0, Vector.empty[Expr]))) {
        case (None, _) => None
        case (Some((degree, symbolic)), factor) =>
          factor match {
            case Var(name) if name == variable =>
              Some((degree + 1, symbolic))
            case Pow(Var(name), exponent: Num)
              if name == variable && exponent.denominator == 1.0 && exponent.numerator >= 0.0 =>
              Some((degree + exponent.numerator.toInt, symbolic))
            case other if Symbols.contains(other, variable) =>
              None
            case other =>
              Some((degree, symbolic :+ other))
          }
      }

      collected.map { case (degree, symbolic) =>
        Map(degree -> Canonical.product(numericCoefficient +: symbolic))
      }
    }

    def merge(a: Map[Int, Expr], b: Map[Int, Expr]): Map[Int, Expr] =
      b.foldLeft(a) { case (acc, (degree, coefficient)) =>
        acc.updatedWith(degree) {
          case Some(existing) => Some(Canonical.sum(Vector(existing, coefficient)))
          case None => Some(coefficient)
        }
      }

    // A sum of terms over a common denominator is the canonical form of a polynomial with
    // fractional coefficients, so the quotient has to be looked through rather than treated as an
    // opaque term.
    def of(e: Expr): Option[Map[Int, Expr]] = e match {
      case Add(terms) =>
        val perTerm = terms.map(of)
        if (perTerm.forall(_.isDefined)) Some(perTerm.map(_.get).reduce(merge)) else None

      case Div(Vector(numerator, denominator)) if !Symbols.contains(denominator, variable) =>
        of(numerator).map(_.map { case (degree, coefficient) =>
          degree -> Canonical.quotient(coefficient, denominator)
        })

      case other => ofTerm(other)
    }

    of(expr)
  }

  /** Solve `a*x + b = 0`. */
  private def linear(a: Expr, b: Expr)(implicit config: SimplificationConfig): List[Expr] =
    if (a == Num(0)) List.empty
    else List(Canonical.quotient(Canonical.negate(b), a))

  /**
   * Solve `a*x^2 + b*x + c = 0` by the quadratic formula.
   *
   * A numeric discriminant decides the number of real roots. A symbolic one cannot, so both roots
   * are returned in symbolic form and the caller decides what they mean.
   */
  private def quadratic(a: Expr, b: Expr, c: Expr)
                       (implicit config: SimplificationConfig): List[Expr] = {
    val discriminant = Canonical.sum(Vector(
      Canonical.power(b, Num(2)),
      Canonical.negate(Canonical.product(Vector(Num(4), a, c)))
    ))
    val twiceA = Canonical.product(Vector(Num(2), a))

    def root(offset: Expr): Expr =
      Canonical.quotient(Canonical.sum(Vector(Canonical.negate(b), offset)), twiceA)

    discriminant match {
      case d: Num if d.value < 0.0 => List.empty
      case d: Num if d.value == 0.0 => List(root(Num(0)))
      case d =>
        val squareRoot = Canonical.power(d, Num(1, 2))
        List(root(squareRoot), root(Canonical.negate(squareRoot)))
    }
  }

  /**
   * Solve each factor of a product separately.
   *
   * Only reachable when distribution is disabled; with it enabled a factored polynomial has
   * already been multiplied out and solved by degree.
   */
  private def factored(expr: Expr, variable: String)
                      (implicit config: SimplificationConfig): List[Expr] =
    expr match {
      case Mul(factors) => factors.flatMap(factor => solve(factor, variable)(config)).toList
      case _ => List.empty
    }
}
