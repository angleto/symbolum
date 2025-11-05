package collatz;

/* ------------------------------------------------------------------------- */

import scala.Array;

final case class Sub(exprs: Array[Expr]) extends Expr {
    override val precedence: Int = 1

    def eval(vars: Map[String, Double]): Double =
            exprs.map(_.eval(vars)).reduce(_ - _)

    def replaceSymbol(sym: String, repl:Expr): Expr =
    Sub(exprs.map(_.replaceSymbol(sym, repl)))

    def simplify: Expr =
        if (exprs.isEmpty) Num(0)
        else {
            val head = exprs.head
            val tail = exprs.tail
            Add(Array(head) ++ tail.map(e => Neg(e))).simplify
        }

    override def toString: String =
            exprs.map(_.toString).mkString(" - ")
}
