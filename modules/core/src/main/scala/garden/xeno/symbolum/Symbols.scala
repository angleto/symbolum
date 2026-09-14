package garden.xeno.symbolum

/**
 * Structural queries over an expression tree.
 *
 * `Derivative` and `Solve` both need to know whether a subexpression mentions a variable. Each
 * used to carry its own copy of the answer, written as a case per node type, so adding a node
 * meant remembering to extend two matches and one of them silently returned the wrong answer for
 * the node it had not been taught about. Here the recursion is driven by [[children]] and a new
 * node needs one line.
 */
object Symbols {

  /** The immediate subexpressions of `e`, in no particular order. */
  def children(e: Expr): Vector[Expr] = e match {
    case Add(terms) => terms
    case Sub(expressions) => expressions
    case Mul(factors) => factors
    case Div(operands) => operands
    case Pow(base, exponent) => Vector(base, exponent)
    case Neg(argument) => Vector(argument)
    case Sin(argument) => Vector(argument)
    case Cos(argument) => Vector(argument)
    case Tan(argument) => Vector(argument)
    case Exp(argument) => Vector(argument)
    case Log(argument) => Vector(argument)
    case Derivative(expression, _) => Vector(expression)
    case Integral(expression, _, lowerBound, upperBound) =>
      Vector(expression) ++ lowerBound ++ upperBound
    case _ => Vector.empty
  }

  /** Every variable occurring in `e`, without repeats. */
  def of(e: Expr): Vector[String] = e match {
    case Var(name) => Vector(name)
    case other => children(other).flatMap(of).distinct
  }

  /** True if `variable` occurs anywhere in `e`. */
  def contains(e: Expr, variable: String): Boolean = e match {
    case Var(name) => name == variable
    case other => children(other).exists(contains(_, variable))
  }
}
