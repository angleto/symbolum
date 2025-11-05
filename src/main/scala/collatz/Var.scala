package collatz;

/* ----------------------------------------------------------------------------
 * Atomic expressions
 * ------------------------------------------------------------------------- */
final case class Var(name: String) extends Expr {
    override val precedence: Int = 4

    def eval(vars: Map[String, Double]): Double =
            vars.getOrElse(name,
            throw new Exception(s"Variable $name not defined")
    )

    def replaceSymbol(sym: String, repl:Expr): Expr =
            if (name == sym) repl else this

    def simplify: Var = this

    override def toString: String = name
}

