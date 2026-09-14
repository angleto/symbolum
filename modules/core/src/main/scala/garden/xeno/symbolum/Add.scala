package garden.xeno.symbolum

/**
 * An n-ary sum.
 *
 * @param terms the addends; at least one
 *
 * @example {{{
 * Add(Vector(Var("x"), Num(1)))            // x + 1
 * Add(Vector(Num(1, 2), Num(1, 3))).simplify  // 5/6
 * }}}
 */
final case class Add(terms: Vector[Expr]) extends Expr {
  require(terms.nonEmpty, "Addition requires at least one term")

  override val precedence: Int = 1

  def eval(variables: Map[String, Double]): Double =
    terms.foldLeft(0.0)((acc, t) => acc + t.eval(variables))

  def replaceSymbol(sym: String, repl: Expr): Expr =
    Add(terms.map(_.replaceSymbol(sym, repl)))

  /**
   * Print with each negative term carried by a minus sign rather than by `+ -`.
   *
   * The sign is a printing concern, not a structural one: the canonical form of `-(a + b)/d` is a
   * quotient with a negative numerator, and rendering it as a subtraction here is what keeps that
   * form readable without a second representation for the simplifier to maintain.
   */
  override def toString: String = {
    val head = showWithParens(terms.head, this)
    val tail = terms.tail.map { term =>
      Add.withoutSign(term) match {
        case Some(positive) => s"- ${showWithParens(positive, this)}"
        case None => s"+ ${showWithParens(term, this)}"
      }
    }
    (head +: tail).mkString(" ")
  }
}

object Add {

  /**
   * The magnitude of a term whose sign is negative, or `None` if the term is not negative.
   *
   * A sum whose terms are all negative counts as negative, so `(-7 - 9*n)/32` appearing inside a
   * larger sum prints as `- (7 + 9*n)/32`.
   */
  private[symbolum] def withoutSign(e: Expr): Option[Expr] = e match {
    case Neg(inner) => Some(inner)

    case Num(numerator, denominator) if numerator < 0.0 => Some(Num(-numerator, denominator))

    case Mul(factors) =>
      factors.head match {
        case Num(numerator, denominator) if numerator < 0.0 =>
          val head = Num(-numerator, denominator)
          val rest = factors.tail
          Some(
            if (head != Num(1)) Mul(head +: rest)
            else if (rest.length == 1) rest.head
            else Mul(rest)
          )
        case _ => None
      }

    case Div(Vector(numerator, denominator)) =>
      withoutSign(numerator).map(positive => Div(Vector(positive, denominator)))

    case Add(terms) =>
      val positives = terms.map(withoutSign)
      if (positives.forall(_.isDefined)) Some(Add(positives.map(_.get))) else None

    case _ => None
  }
}
