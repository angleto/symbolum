package garden.xeno.symbolum.kernel

/**
 * How types, terms and theorems are shown.
 *
 * This exists earlier than a printer usually would, and the reason is the representation: a term
 * holds indices where a reader expects names, so an unprinted term is close to unreadable and
 * every kernel error message would be too. It is display only. Nothing here can build a theorem,
 * and nothing in the inference rules consults it.
 *
 * The names it invents for bound variables are not part of any term. Two terms that print the
 * same are equal, and two equal terms print the same, but a name in the output corresponds to
 * nothing in the value.
 */
object Printer {

  private val BoundNames: Vector[String] = Vector("x", "y", "z", "u", "v", "w")

  /** A type, with `->` right-associated as usual. */
  def show(ty: Type): String = ty match {
    case TyVar(name) => name

    case TyApp("fun", List(domain, codomain)) =>
      val left = domain match {
        case TyApp("fun", List(_, _)) => s"(${show(domain)})"
        case _ => show(domain)
      }
      s"$left -> ${show(codomain)}"

    case TyApp(operator, Nil) => operator
    case TyApp(operator, arguments) => s"$operator(${arguments.map(show).mkString(", ")})"
  }

  /** A term. Bound variables are given names here and have none in the term itself. */
  def show(term: Term): String = showTerm(term, Nil)

  /** A theorem, as `hypotheses |- conclusion`. */
  def show(hypotheses: List[Term], conclusion: Term): String = {
    val left = if (hypotheses.isEmpty) "" else hypotheses.map(show).mkString(", ") + " "
    s"$left|- ${show(conclusion)}"
  }

  private def showTerm(term: Term, bound: List[String]): String = term match {
    case BVar(index) =>
      // Only reachable for a term taken apart below a binder, which this function does not do,
      // or for a malformed term. Printing something is better than failing inside an error path.
      if (index < bound.length) bound(index) else s"?$index"

    case FVar(name, _) => name
    case Const(name, _) => name

    case _ if Term.destEq(term).isDefined =>
      val (lhs, rhs) = Term.destEq(term).get
      s"(${showTerm(lhs, bound)} = ${showTerm(rhs, bound)})"

    case App(fn, arg) => s"(${showTerm(fn, bound)} ${showTerm(arg, bound)})"

    case Abs(binderType, body) =>
      val name = freshName(bound)
      s"(\\$name:${show(binderType)}. ${showTerm(body, name :: bound)})"
  }

  private def freshName(bound: List[String]): String = {
    val depth = bound.length
    val base = BoundNames(depth % BoundNames.length)
    val round = depth / BoundNames.length
    if (round == 0) base else s"$base$round"
  }
}
