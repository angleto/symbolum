package garden.xeno.symbolum

/**
 * A total order on expressions.
 *
 * Addition and multiplication are commutative, so `x + y` and `y + x` are the same expression
 * written two ways. Sorting the operands of every commutative node by this order collapses those
 * spellings into one, which buys three things the simplifier depends on:
 *
 *  - like-term collection groups by structural equality and cannot miss a match because the
 *    factors happened to arrive in a different order;
 *  - `fullSimplify` detects its fixpoint with `==`, exactly, with no tolerance fallback;
 *  - output is reproducible run to run. The previous implementation grouped through a hash map
 *    and emitted terms in whatever order the map iterated, so the same input could print two
 *    ways in one session.
 *
 * The order itself carries no mathematical meaning: it exists to be consistent. Its one
 * concession to legibility is the rank table, which puts simple nodes before compound ones so a
 * printed sum reads `3 * n + 1` rather than the reverse.
 *
 * What this does not cover: it is not an order by magnitude, and comparing two `Num`s by value
 * is an implementation detail of the tie-break, not a promise about numeric ordering.
 */
object ExprOrder extends Ordering[Expr] {

  /**
   * Ordering used for the terms of a sum.
   *
   * Numeric literals sort last so that a polynomial prints with its constant at the end, the
   * convention every reader of `3 * n + 1` expects.
   */
  val forSum: Ordering[Expr] = (a: Expr, b: Expr) => (a, b) match {
    case (_: Num, _: Num) => compare(a, b)
    case (_: Num, _) => 1
    case (_, _: Num) => -1
    case _ => compare(a, b)
  }

  /** Ordering used for the non-numeric factors of a product. */
  val forProduct: Ordering[Expr] = this

  private def rank(e: Expr): Int = e match {
    case _: Num => 0
    case _: Var => 1
    case _: Pow => 2
    case _: Mul => 3
    case _: Div => 4
    case _: Add => 5
    case _: Sub => 6
    case _: Neg => 7
    case _: Sin => 8
    case _: Cos => 9
    case _: Tan => 10
    case _: Exp => 11
    case _: Log => 12
    case _: Derivative => 13
    case _: Integral => 14
    case _ => 15
  }

  def compare(a: Expr, b: Expr): Int = {
    val rankDifference = rank(a) - rank(b)
    if (rankDifference != 0) rankDifference
    else (a, b) match {
      case (Num(an, ad), Num(bn, bd)) =>
        java.lang.Double.compare(an / ad, bn / bd)

      case (Var(x), Var(y)) => x.compareTo(y)

      case (Pow(baseA, expA), Pow(baseB, expB)) =>
        val byBase = compare(baseA, baseB)
        if (byBase != 0) byBase else compare(expA, expB)

      case (Mul(x), Mul(y)) => compareAll(x, y)
      case (Div(x), Div(y)) => compareAll(x, y)
      case (Add(x), Add(y)) => compareAll(x, y)
      case (Sub(x), Sub(y)) => compareAll(x, y)

      case (Neg(x), Neg(y)) => compare(x, y)
      case (Sin(x), Sin(y)) => compare(x, y)
      case (Cos(x), Cos(y)) => compare(x, y)
      case (Tan(x), Tan(y)) => compare(x, y)
      case (Exp(x), Exp(y)) => compare(x, y)
      case (Log(x), Log(y)) => compare(x, y)

      case (Derivative(exprA, varA), Derivative(exprB, varB)) =>
        val byVar = varA.compareTo(varB)
        if (byVar != 0) byVar else compare(exprA, exprB)

      case (Integral(exprA, varA, lowA, highA), Integral(exprB, varB, lowB, highB)) =>
        val byVar = varA.compareTo(varB)
        if (byVar != 0) byVar
        else {
          val byExpr = compare(exprA, exprB)
          if (byExpr != 0) byExpr
          else {
            val byLow = compareBound(lowA, lowB)
            if (byLow != 0) byLow else compareBound(highA, highB)
          }
        }

      // Unreachable while every expression type is listed above; kept total rather than
      // returning 0, because a zero here would let two distinct expressions sort either way and
      // silently break the canonical arrangement this object exists to provide.
      case _ => a.toString.compareTo(b.toString)
    }
  }

  private def compareBound(a: Option[Expr], b: Option[Expr]): Int = (a, b) match {
    case (None, None) => 0
    case (None, Some(_)) => -1
    case (Some(_), None) => 1
    case (Some(x), Some(y)) => compare(x, y)
  }

  // Iterators rather than `lazyZip`, which is strict in its `map` and would compare every pair
  // even after the first difference has decided the answer. This runs under every sort of every
  // commutative node, so the short circuit is the whole point.
  private def compareAll(a: Vector[Expr], b: Vector[Expr]): Int =
    a.iterator
      .zip(b.iterator)
      .map { case (x, y) => compare(x, y) }
      .find(_ != 0)
      .getOrElse(a.length - b.length)
}
