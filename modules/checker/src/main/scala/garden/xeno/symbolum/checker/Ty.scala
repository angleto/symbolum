package garden.xeno.symbolum.checker

/** A type, as this checker holds one. */
sealed trait Ty

object Ty {

  final case class Variable(name: String) extends Ty
  final case class Operator(name: String, arguments: List[Ty]) extends Ty

  val Bool: Ty = Operator("bool", Nil)

  def fun(domain: Ty, codomain: Ty): Ty = Operator("fun", List(domain, codomain))

  def destFun(ty: Ty): Option[(Ty, Ty)] = ty match {
    case Operator("fun", List(domain, codomain)) => Some((domain, codomain))
    case _ => None
  }

  /** The type variables a type mentions, which is what an escaping one is measured against. */
  def variables(ty: Ty): Set[String] = ty match {
    case Variable(name) => Set(name)
    case Operator(_, arguments) => arguments.foldLeft(Set.empty[String])(_ ++ variables(_))
  }

  def substitute(substitution: Map[String, Ty], ty: Ty): Ty = ty match {
    case Variable(name) => substitution.getOrElse(name, ty)
    case Operator(name, arguments) => Operator(name, arguments.map(substitute(substitution, _)))
  }
}
