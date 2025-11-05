package collatz

/* ------------------------------------------------------------------------- */
final case class Div(exprs: Array[Expr]) extends Expr {
  override val precedence: Int = 2

  def eval(vars: Map[String, Double]): Double =
    exprs.map(_.eval(vars)).reduce(_ / _)

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Div(exprs.map(_.replaceSymbol(sym, repl)))

  /* helper – build a simplified product --------------------------------- */
  private def prod(xs: Seq[Expr]): Expr = xs.length match {
    case 0 => Num(1)
    case 1 => xs.head
    case _ => Mul(xs.toArray).simplify
  }

  def simplify: Expr = {
    /* simplify every child first ---------------------------------------- */
    val children = exprs.map(_.simplify)

    /* 1)   a / b / c / d   ->   a / (b * c * d) ------------------------- */
    if (children.length > 2)
      Div(Array(children.head, prod(children.tail))).simplify

    /* now at most two operands ------------------------------------------ */
    children match {
      /* 2) (a / b) / c  ->  a / (b * c) --------------------------------- */
      case Array(Div(Array(num, den1)), den2) =>
        Div(Array(num, prod(Seq(den1, den2)))).simplify

      /* 3) fully numeric -> calculate immediately ----------------------- */
      case Array(Num(an, ad), Num(bn, bd)) =>
        Num(an * bd, ad * bn).simplify

      /* 4) divide by one ------------------------------------------------- */
      case Array(a, Num(1, 1)) =>
        a

      /* default ---------------------------------------------------------- */
      case Array(a, b) =>
        Div(Array(a, b))
    }
  }

  override def toString: String =
    exprs.map(e => showWithParens(e, this)).mkString(" / ")
}

