package collatz ;

import scala.annotation.tailrec ;

/* ============================================================================
 * n-ary composites
 * ========================================================================== */
final case class Add(exprs: Array[Expr]) extends Expr {
  override val precedence: Int = 1

  /* -------------------------------------------------------------------------
   * Try to merge a sum of “fractions” into a single common denominator
   * ----------------------------------------------------------------------- */
  private def mergeFractions(terms: Seq[Expr]): Option[Expr] = {

    /* helpers -------------------------------------------------------------- */
    def isWhole(d: Double): Boolean = (d % 1.0) == 0.0

    @tailrec
    def gcd(a: Int, b: Int): Int = if (b == 0) a.abs else gcd(b, a % b)

    def lcm(a: Int, b: Int): Int = (a / gcd(a, b)) * b

    /* Attempt to peel “numerator / integerDenominator” out of a term        */
    def asFraction(e: Expr): Option[(Expr, Int)] = e match {
      case Num(num, den) if isWhole(den) =>
        Some((Num(num).simplify, den.toInt))

      case Div(Array(numExpr, Num(denNum, denDen)))
        if denDen == 1.0 && isWhole(denNum) =>
        Some((numExpr, denNum.toInt))

      case _ => None
    }

    val extracted = terms.map(asFraction)

    /* Only proceed if we succeeded for every single term and we really
       *have* at least two fractions                                    */
    if (extracted.forall(_.isDefined) && terms.length > 1) {
      val fracs = extracted.map(_.get)
      val denominators = fracs.map(_._2)
      val commonDenominator = denominators.reduce(lcm)

      if (commonDenominator == 1) {
        None // nothing to do
      } else {
        /* scale every numerator so that it matches the common denominator    */
        val scaledNumerators = fracs.map { case (numExpr, den) =>
          val factor = commonDenominator / den
          if (factor == 1) numExpr
          else Mul(Array(numExpr, Num(factor))).simplify
        }

        val combinedNumerator = Add(scaledNumerators.toArray).simplify
        Some(Div(Array(combinedNumerator, Num(commonDenominator))).simplify)
      }
    } else None
  }

  /* ---------------- public part ------------------------------------------ */
  def eval(vars: Map[String, Double]): Double =
    exprs.map(_.eval(vars)).sum

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Add(exprs.map(_.replaceSymbol(sym, repl)))

  def simplify: Expr = {
    val simplified = exprs.map(_.simplify)
    val zero = Num(0)
    val noZeros = simplified.filterNot(_ == zero)

    /* first of all: does it look like a pure sum of fractions that can be
       merged into ONE fraction?                                          */
    mergeFractions(noZeros) match {
      case Some(merged) => merged // great!
      case None => // fallback
        /* collect all numeric literals (might have different denominators)
           and everything else                                              */
        val (nums, others) = noZeros.partition(_.isInstanceOf[Num])

        /* sum up numeric literals with identical denominators ------------ */
        val numericSum: Array[Expr] =
          nums
            .collect { case Num(n, d) => (n, d) }
            .groupBy(_._2) // group by denominator
            .map { case (den, pairs) =>
              val sumNum = pairs.map(_._1).sum
              Num(sumNum, den).simplify
            }
            .toArray

        val combined: Array[Expr] = numericSum ++ others

        combined.length match {
          case 0 => Num(0)
          case 1 => combined(0)
          case _ => Add(combined)
        }
    }
  }

  override def toString: String =
    exprs.map(e => showWithParens(e, this)).mkString(" + ")
}
