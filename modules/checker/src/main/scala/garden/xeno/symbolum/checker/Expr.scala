package garden.xeno.symbolum.checker

/**
 * A term, as this checker holds one, which is not how the kernel holds one.
 *
 * The point of a second checker is that it disagrees where the first is wrong, and it cannot do
 * that with the first one's code. So the shape of a term is read off the kernel's public
 * extractors and everything done to a term from there on is written again here: the typing, the
 * closedness, the substitution, the opening of a binder, the beta step.
 *
 * **What is still shared, said plainly.** The *shape*: that a term is an index, a name, a constant,
 * an application or an abstraction, and that the kernel's extractors report it faithfully. A data
 * type is not an algorithm, and the defects a kernel has are in the algorithms; the 2026-09-03 hole
 * in this one was in what substitution and beta assumed about an index, which is exactly the kind
 * of thing this file re-decides for itself.
 *
 * What is not covered on the in-process route, and it is the honest limit: if the kernel's
 * extractors lied about the shape, this would be told the same lie. `Parse` is the route that does
 * not have that limit, since what reaches it is characters; there the shape is decided here too,
 * and what is shared is the writer alone.
 */
sealed trait Expr

object Expr {

  /** A variable bound by the `index`-th enclosing binder, innermost first. */
  final case class Bound(index: Int) extends Expr

  /** A free variable: a name and a type together. */
  final case class Free(name: String, ty: Ty) extends Expr

  /**
   * A constant at a type, carrying whatever gave it its identity.
   *
   * Its hash, like [[Apply]]'s and [[Lambda]]'s, is computed once and kept, which the kernel's `App`
   * and `Abs` do for the same reason. Since `docs/adr/0053` the primitives of the reals are defined
   * as operations on cuts, so an origin is a definition whose own constants carry origins down
   * through the rationals and the integers; `Read` shares each origin it reads, and a hash computed
   * afresh would walk that shared graph as a tree at every asking.
   */
  final case class Constant(name: String, ty: Ty, origin: Option[Expr]) extends Expr {
    private val hash = scala.util.hashing.MurmurHash3.productHash(this)
    override def hashCode(): Int = hash
  }

  /** An application, not assumed to be well-typed: [[typeOf]] is where that is found out. */
  final case class Apply(fn: Expr, argument: Expr) extends Expr {
    private val hash = scala.util.hashing.MurmurHash3.productHash(this)
    override def hashCode(): Int = hash
  }

  /** An abstraction. The bound name does not exist. */
  final case class Lambda(binder: Ty, body: Expr) extends Expr {
    private val hash = scala.util.hashing.MurmurHash3.productHash(this)
    override def hashCode(): Int = hash
  }

  /** The name equality goes by, which this checker knows for the same reason the kernel does. */
  val EqualityName: String = "="

  /** The two sides of an equation, if it is one. */
  def sidesOf(expression: Expr): Option[(Expr, Expr)] = expression match {
    case Apply(Apply(Constant(EqualityName, _, _), left), right) => Some((left, right))
    case _ => None
  }

  /**
   * The type of a term, or nothing when it has none.
   *
   * Partial where the kernel's is total, and deliberately: the kernel may assume its terms are
   * well-typed because it built them, and a checker may assume nothing about what it is handed.
   */
  def typeOf(expression: Expr): Option[Ty] = typeIn(expression, Nil)

  private def typeIn(expression: Expr, context: List[Ty]): Option[Ty] = expression match {
    case Bound(index) => if (index < context.length) Some(context(index)) else None
    case Free(_, ty) => Some(ty)
    case Constant(_, ty, _) => Some(ty)
    case Lambda(binder, body) => typeIn(body, binder :: context).map(Ty.fun(binder, _))
    case Apply(fn, argument) =>
      for {
        function <- typeIn(fn, context)
        (domain, codomain) <- Ty.destFun(function)
        actual <- typeIn(argument, context)
        if domain == actual
      } yield codomain
  }

  /** Whether the term is a proposition, which is what an assumption and an axiom have to be. */
  def isProposition(expression: Expr): Boolean = typeOf(expression).contains(Ty.Bool)

  /** Whether every index has a binder above it inside the term. */
  def isClosed(expression: Expr): Boolean = {
    def go(current: Expr, depth: Int): Boolean = current match {
      case Bound(index) => index < depth
      case Apply(fn, argument) => go(fn, depth) && go(argument, depth)
      case Lambda(_, body) => go(body, depth + 1)
      case _ => true
    }

    go(expression, 0)
  }

  /** The free variables of a term. */
  def freeVariables(expression: Expr): Set[Free] = expression match {
    case free: Free => Set(free)
    case Apply(fn, argument) => freeVariables(fn) ++ freeVariables(argument)
    case Lambda(_, body) => freeVariables(body)
    case _ => Set.empty
  }

  /** Replace the variable the outermost binder binds. */
  def open(body: Expr, replacement: Expr): Expr = {
    def go(current: Expr, depth: Int): Expr = current match {
      case Bound(index) if index == depth => replacement
      case Apply(fn, argument) => Apply(go(fn, depth), go(argument, depth))
      case Lambda(binder, inner) => Lambda(binder, go(inner, depth + 1))
      case other => other
    }

    go(body, 0)
  }

  /** Turn every free occurrence of `variable` into an index, giving a binder's body. */
  def close(variable: Free, expression: Expr): Expr = {
    def go(current: Expr, depth: Int): Expr = current match {
      case free: Free if free == variable => Bound(depth)
      case Apply(fn, argument) => Apply(go(fn, depth), go(argument, depth))
      case Lambda(binder, inner) => Lambda(binder, go(inner, depth + 1))
      case other => other
    }

    go(expression, 0)
  }

  /**
   * Every type variable anywhere in a term, binders and constants included.
   *
   * Walks the type of every subterm rather than only the term's own type: a term can carry a type
   * variable its type does not mention, which is exactly the case the escaping-variable condition
   * on a definition exists to refuse.
   */
  def typeVariables(expression: Expr): Set[String] = expression match {
    case Bound(_) => Set.empty
    case Free(_, ty) => Ty.variables(ty)
    case Constant(_, ty, _) => Ty.variables(ty)
    case Apply(fn, argument) => typeVariables(fn) ++ typeVariables(argument)
    case Lambda(binder, body) => Ty.variables(binder) ++ typeVariables(body)
  }

  /** Replace free variables. No renaming, for the reason the representation gives. */
  def substitute(substitution: Map[Free, Expr], expression: Expr): Expr = expression match {
    case free: Free => substitution.getOrElse(free, free)
    case Apply(fn, argument) =>
      Apply(substitute(substitution, fn), substitute(substitution, argument))
    case Lambda(binder, body) => Lambda(binder, substitute(substitution, body))
    case other => other
  }

  /** Replace type variables, leaving a constant's origin alone, as the kernel does. */
  def substituteTypes(substitution: Map[String, Ty], expression: Expr): Expr = expression match {
    case Bound(index) => Bound(index)
    case Free(name, ty) => Free(name, Ty.substitute(substitution, ty))
    case Constant(name, ty, origin) => Constant(name, Ty.substitute(substitution, ty), origin)
    case Apply(fn, argument) =>
      Apply(substituteTypes(substitution, fn), substituteTypes(substitution, argument))
    case Lambda(binder, body) =>
      Lambda(Ty.substitute(substitution, binder), substituteTypes(substitution, body))
  }

  /** One beta step at the root, if there is one. */
  def betaReduce(expression: Expr): Option[Expr] = expression match {
    case Apply(Lambda(_, body), argument) => Some(open(body, argument))
    case _ => None
  }
}
