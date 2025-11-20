package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/**
 * Equation solver for symbolic expressions.
 *
 * Solves equations of the form: equation = 0 for a given variable.
 * Supports linear, quadratic, and some special forms.
 *
 * @example {{{
 *   // Solve x + 2 = 0 for x
 *   Solve.solve(Add(Vector(Var("x"), Num(2))), "x")  // List(Num(-2))
 *
 *   // Solve x^2 - 5x + 6 = 0 for x
 *   val expr = Add(Vector(Pow(Var("x"), Num(2)), Mul(Vector(Num(-5), Var("x"))), Num(6)))
 *   Solve.solve(expr, "x")  // List(Num(2), Num(3))
 * }}}
 */
object Solve {

  /**
   * Solve an equation for a variable.
   *
   * @param equation Expression that equals zero
   * @param variable Variable to solve for
   * @param config Simplification configuration
   * @return List of solutions
   */
  def solve(equation: Expr, variable: String)
           (implicit config: SimplificationConfig = SimplificationConfig.Default): List[Expr] = {
    val simplified = equation.simplify(config)

    // Try different solving strategies
    solveLinear(simplified, variable)(config)
      .orElse(solveQuadratic(simplified, variable)(config))
      .orElse(solveFactored(simplified, variable)(config))
      .getOrElse(List())  // Cannot solve
  }

  /**
   * Solve linear equation: ax + b = 0.
   *
   * @param expr Expression
   * @param variable Variable to solve for
   * @param config Simplification configuration
   * @return Some(List(solution)) if linear, None otherwise
   */
  private def solveLinear(expr: Expr, variable: String)
                         (implicit config: SimplificationConfig): Option[List[Expr]] = {
    // Extract coefficients: expr = a*x + b
    val (a, b) = extractLinearCoefficients(expr, variable)(config)

    (a, b) match {
      case (Some(coeff), Some(const)) if coeff != Num(0) =>
        // ax + b = 0  =>  x = -b/a
        val solution = Div(Vector(Neg(const).simplify(config), coeff)).simplify(config)
        Some(List(solution))

      case (Some(Num(0)), Some(Num(0))) =>
        // 0 = 0: infinite solutions (special case)
        None  // Cannot represent infinite solutions

      case (Some(Num(0)), Some(_)) =>
        // b = 0 where b ≠ 0: no solution
        Some(List())

      case _ =>
        None  // Not linear
    }
  }

  /**
   * Extract linear coefficients from expression.
   *
   * Tries to express expr as a*x + b.
   *
   * @param expr Expression
   * @param variable Variable
   * @param config Simplification configuration
   * @return (Some(a), Some(b)) if linear, None otherwise
   */
  private def extractLinearCoefficients(expr: Expr, variable: String)
                                       (implicit config: SimplificationConfig): (Option[Expr], Option[Expr]) = {
    expr match {
      // Just the variable: x => 1*x + 0
      case Var(v) if v == variable =>
        (Some(Num(1)), Some(Num(0)))

      // Constant: c => 0*x + c
      case Num(_) | Var(v) if v != variable =>
        (Some(Num(0)), Some(expr))

      // ax where a is constant
      case Mul(Vector(a, Var(v))) if v == variable && !containsVariable(a, variable) =>
        (Some(a), Some(Num(0)))

      case Mul(Vector(Var(v), a)) if v == variable && !containsVariable(a, variable) =>
        (Some(a), Some(Num(0)))

      // ax + b
      case Add(Vector(Mul(Vector(a, Var(v))), b)) if v == variable && !containsVariable(a, variable) && !containsVariable(b, variable) =>
        (Some(a), Some(b))

      case Add(Vector(Var(v), b)) if v == variable && !containsVariable(b, variable) =>
        (Some(Num(1)), Some(b))

      case Add(Vector(b, Var(v))) if v == variable && !containsVariable(b, variable) =>
        (Some(Num(1)), Some(b))

      case Add(Vector(b, Mul(Vector(a, Var(v))))) if v == variable && !containsVariable(a, variable) && !containsVariable(b, variable) =>
        (Some(a), Some(b))

      // Try general form by collecting terms
      case Add(terms) =>
        val (varTerms, constTerms) = terms.partition(containsVariable(_, variable))
        val a = varTerms.map(extractCoefficient(_, variable)(config)).reduceOption((x, y) => Add(Vector(x, y)).simplify(config))
        val b = if (constTerms.isEmpty) Some(Num(0)) else Some(Add(constTerms).simplify(config))
        (a, b)

      case _ =>
        (None, None)
    }
  }

  /**
   * Extract coefficient of variable from a term.
   *
   * @param term Expression term
   * @param variable Variable
   * @param config Simplification configuration
   * @return Coefficient
   */
  private def extractCoefficient(term: Expr, variable: String)
                                 (implicit config: SimplificationConfig): Expr = {
    term match {
      case Var(v) if v == variable => Num(1)
      case Mul(Vector(coeff, Var(v))) if v == variable => coeff
      case Mul(Vector(Var(v), coeff)) if v == variable => coeff
      case _ => Num(0)
    }
  }

  /**
   * Solve quadratic equation: ax^2 + bx + c = 0.
   *
   * Uses quadratic formula: x = (-b ± √(b² - 4ac)) / (2a)
   *
   * @param expr Expression
   * @param variable Variable to solve for
   * @param config Simplification configuration
   * @return Some(List(solutions)) if quadratic, None otherwise
   */
  private def solveQuadratic(expr: Expr, variable: String)
                            (implicit config: SimplificationConfig): Option[List[Expr]] = {
    extractQuadraticCoefficients(expr, variable)(config) match {
      case Some((a, b, c)) if a != Num(0) =>
        Some(quadraticFormula(a, b, c)(config))
      case _ =>
        None
    }
  }

  /**
   * Extract quadratic coefficients from expression.
   *
   * Tries to express expr as a*x^2 + b*x + c.
   *
   * @param expr Expression
   * @param variable Variable
   * @param config Simplification configuration
   * @return Some((a, b, c)) if quadratic, None otherwise
   */
  private def extractQuadraticCoefficients(expr: Expr, variable: String)
                                          (implicit config: SimplificationConfig): Option[(Expr, Expr, Expr)] = {
    val simplified = expr.simplify(config).expand(config).simplify(config)

    // Collect terms by degree
    val terms = simplified match {
      case Add(ts) => ts
      case other => Vector(other)
    }

    var a: Expr = Num(0)  // coefficient of x^2
    var b: Expr = Num(0)  // coefficient of x
    var c: Expr = Num(0)  // constant term

    for (term <- terms) {
      term match {
        // x^2 term
        case Pow(Var(v), Num(2)) if v == variable =>
          a = Add(Vector(a, Num(1))).simplify(config)

        case Mul(factors) if factors.exists {
          case Pow(Var(v), Num(2)) if v == variable => true
          case _ => false
        } =>
          val coeff = factors.filterNot {
            case Pow(Var(v), Num(2)) if v == variable => true
            case _ => false
          }
          val coeffExpr = if (coeff.isEmpty) Num(1) else if (coeff.length == 1) coeff.head else Mul(coeff).simplify(config)
          a = Add(Vector(a, coeffExpr)).simplify(config)

        // x term
        case Var(v) if v == variable =>
          b = Add(Vector(b, Num(1))).simplify(config)

        case Mul(Vector(coeff, Var(v))) if v == variable =>
          b = Add(Vector(b, coeff)).simplify(config)

        case Mul(Vector(Var(v), coeff)) if v == variable =>
          b = Add(Vector(b, coeff)).simplify(config)

        // Constant term
        case _ if !containsVariable(term, variable) =>
          c = Add(Vector(c, term)).simplify(config)

        case _ =>
          return None  // Term has degree > 2 or unsupported form
      }
    }

    Some((a, b, c))
  }

  /**
   * Apply quadratic formula.
   *
   * @param a Coefficient of x^2
   * @param b Coefficient of x
   * @param c Constant term
   * @param config Simplification configuration
   * @return List of solutions (0, 1, or 2 solutions)
   */
  private def quadraticFormula(a: Expr, b: Expr, c: Expr)
                               (implicit config: SimplificationConfig): List[Expr] = {
    // Discriminant: b^2 - 4ac
    val discriminant = Sub(Vector(
      Pow(b, Num(2)),
      Mul(Vector(Num(4), a, c))
    )).simplify(config)

    discriminant match {
      case Num(d) if d < 0 =>
        // No real solutions
        List()

      case Num(0) =>
        // One solution: -b / (2a)
        val solution = Div(Vector(
          Neg(b).simplify(config),
          Mul(Vector(Num(2), a)).simplify(config)
        )).simplify(config)
        List(solution)

      case Num(d) if d > 0 =>
        // Two solutions: (-b ± √d) / (2a)
        val sqrtD = Pow(Num(d), Num(0.5)).simplify(config)
        val twoA = Mul(Vector(Num(2), a)).simplify(config)

        val sol1 = Div(Vector(
          Add(Vector(Neg(b).simplify(config), sqrtD)).simplify(config),
          twoA
        )).simplify(config)

        val sol2 = Div(Vector(
          Sub(Vector(Neg(b).simplify(config), sqrtD)).simplify(config),
          twoA
        )).simplify(config)

        List(sol1, sol2)

      case _ =>
        // Symbolic discriminant: return symbolic solutions
        val sqrtDiscriminant = Pow(discriminant, Num(0.5)).simplify(config)
        val twoA = Mul(Vector(Num(2), a)).simplify(config)

        val sol1 = Div(Vector(
          Add(Vector(Neg(b).simplify(config), sqrtDiscriminant)).simplify(config),
          twoA
        )).simplify(config)

        val sol2 = Div(Vector(
          Sub(Vector(Neg(b).simplify(config), sqrtDiscriminant)).simplify(config),
          twoA
        )).simplify(config)

        List(sol1, sol2)
    }
  }

  /**
   * Solve factored equations: (x-a)(x-b) = 0.
   *
   * @param expr Expression
   * @param variable Variable to solve for
   * @param config Simplification configuration
   * @return Some(List(solutions)) if factored form detected, None otherwise
   */
  private def solveFactored(expr: Expr, variable: String)
                           (implicit config: SimplificationConfig): Option[List[Expr]] = {
    expr match {
      case Mul(factors) =>
        // Each factor must equal zero
        val solutions = factors.flatMap { factor =>
          solve(factor, variable)(config)
        }
        Some(solutions.toList)

      case _ =>
        None
    }
  }

  /**
   * Check if an expression contains a variable.
   *
   * @param expr Expression
   * @param variable Variable name
   * @return true if expression contains the variable
   */
  private def containsVariable(expr: Expr, variable: String): Boolean = {
    expr match {
      case Var(v) => v == variable
      case Num(_) => false
      case Add(terms) => terms.exists(containsVariable(_, variable))
      case Sub(terms) => terms.exists(containsVariable(_, variable))
      case Mul(factors) => factors.exists(containsVariable(_, variable))
      case Div(operands) => operands.exists(containsVariable(_, variable))
      case Pow(base, exp) => containsVariable(base, variable) || containsVariable(exp, variable)
      case Neg(inner) => containsVariable(inner, variable)
      case Cos(arg) => containsVariable(arg, variable)
      case Sin(arg) => containsVariable(arg, variable)
      case Tan(arg) => containsVariable(arg, variable)
      case Exp(arg) => containsVariable(arg, variable)
      case Log(arg) => containsVariable(arg, variable)
      case Derivative(e, _) => containsVariable(e, variable)
      case Integral(e, _, lb, ub) =>
        containsVariable(e, variable) || lb.exists(containsVariable(_, variable)) || ub.exists(containsVariable(_, variable))
    }
  }
}
