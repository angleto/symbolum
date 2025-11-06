package symbolicas

import symbolicas.{SimplificationConfig, SimplificationRule}
import SimplificationRule._

/* ------------------------------------------------------------------------- */
final case class Div(exprs: Array[Expr]) extends Expr {
  override val precedence: Int = 2

  def eval(vars: Map[String, Double]): Double =
    exprs.map(_.eval(vars)).reduce(_ / _)

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Div(exprs.map(_.replaceSymbol(sym, repl)))

  override def expand(implicit config: SimplificationConfig): Expr = {
    // Expand children and simplify
    val expandedChildren = exprs.map(_.expand(config))
    Div(expandedChildren).simplify(config)
  }

  /* helper – build a simplified product --------------------------------- */
  private def prod(xs: Seq[Expr])(implicit config: SimplificationConfig): Expr = xs.length match {
    case 0 => Num(1)
    case 1 => xs.head
    case _ => Mul(xs.toArray).simplify(config)
  }

  def simplify(implicit config: SimplificationConfig): Expr = {
    /* simplify every child first ---------------------------------------- */
    val children = exprs.map(_.simplify(config))

    /* 1)   a / b / c / d   ->   a / (b * c * d) ------------------------- */
    if (config.isEnabled(FlattenOperations) && children.length > 2)
      return Div(Array(children.head, prod(children.tail)(config))).simplify(config)

    /* now at most two operands ------------------------------------------ */
    children match {
      /* 2) (a / b) / c  ->  a / (b * c) --------------------------------- */
      case Array(Div(Array(num, den1)), den2) if config.isEnabled(FlattenOperations) =>
        Div(Array(num, prod(Seq(den1, den2))(config))).simplify(config)

      /* 3) a / (b / c) -> (a * c) / b ----------------------------------- */
      case Array(num, Div(Array(den1, den2))) if config.isEnabled(FlattenOperations) =>
        Div(Array(prod(Seq(num, den2))(config), den1)).simplify(config)

      /* 4) fully numeric -> calculate immediately ----------------------- */
      case Array(Num(an, ad), Num(bn, bd)) if config.isEnabled(CombineNumericLiterals) =>
        Num(an * bd, ad * bn).simplify(config)

      /* 5) divide by one ------------------------------------------------- */
      case Array(a, Num(1, 1)) if config.isEnabled(RemoveIdentity) =>
        a

      /* 6) If numerator is Add with all Divs of same denom, simplify --- */
      case Array(Add(addTerms), den) if config.isEnabled(MergeFractionsCommonDenom) =>
        // Check if all terms in the Add are Divs with the same denominator
        val allDivs = addTerms.forall(_.isInstanceOf[Div])
        if (allDivs && addTerms.length > 1) {
          val divTerms = addTerms.collect { case Div(Array(n, d)) => (n, d) }
          val denominators = divTerms.map(_._2.toString).toSet

          if (denominators.size == 1) {
            // All have same denominator, so (a/d + b/d + ...) / den = (a + b + ...) / (d * den)
            val commonDenom = divTerms.head._2
            val numerators = divTerms.map(_._1)
            val sumNumerators = Add(numerators).simplify(config)
            Div(Array(sumNumerators, prod(Seq(commonDenom, den))(config))).simplify(config)
          } else {
            Div(Array(Add(addTerms), den))
          }
        } else {
          Div(Array(Add(addTerms), den))
        }

      /* default ---------------------------------------------------------- */
      case Array(a, b) =>
        Div(Array(a, b))

      case _ =>
        Div(children)
    }
  }

  override def toString: String = {
    if (exprs.length == 2) {
      val num = exprs(0)
      val den = exprs(1)

      // For cleaner output, add parentheses to denominators when needed
      val numStr = if (num.precedence < this.precedence) s"($num)" else num.toString
      val denStr = if (den.precedence <= this.precedence) s"($den)" else den.toString

      s"$numStr/$denStr"
    } else {
      exprs.map(e => showWithParens(e, this)).mkString(" / ")
    }
  }
}

