package garden.xeno.symbolum.kernel

/**
 * A simple type: a type variable, or a type operator applied to arguments.
 *
 * There are no dependent types and no polymorphism inside a type: `list(A)` is a type, `∀A. A ->
 * A` is not. Polymorphism lives in the schema of a theorem instead, and is used by instantiating
 * the type variables of a theorem that has already been proved.
 *
 * Two type operators are known to the kernel by name: `bool`, the type of propositions, and
 * `fun`, the type of functions. Everything else is declared in a [[Theory]].
 */
sealed trait Type {
  override def toString: String = Printer.show(this)
}

/** A type variable, standing for any type. */
final case class TyVar(name: String) extends Type

/**
 * A type operator applied to its arguments.
 *
 * The arity is not checked here. It is checked where a type enters the system from outside, by
 * [[Theory.checkType]], because that is where a name is being trusted; a type produced by
 * instantiating a type that was already checked cannot become ill-formed.
 *
 * Built only by [[TyApp.apply]], which hands back one instance per value. Equality is still the
 * structural one, so nothing is decided by which instance a caller holds: `docs/adr/0058`.
 */
final case class TyApp private (operator: String, arguments: List[Type]) extends Type {
  private val hash = scala.util.hashing.MurmurHash3.productHash(this)
  override def hashCode(): Int = hash
}

/** The table grows with the distinct types a process spells, which a whole chain puts at 808. */
object TyApp {
  private val interned = new java.util.concurrent.ConcurrentHashMap[TyApp, TyApp]

  def apply(operator: String, arguments: List[Type]): TyApp = {
    val fresh = new TyApp(operator, arguments)
    Option(interned.putIfAbsent(fresh, fresh)).getOrElse(fresh)
  }
}

object Type {

  /** The type of propositions. */
  val Bool: Type = TyApp("bool", Nil)

  /** The type of functions from `domain` to `codomain`. */
  def fun(domain: Type, codomain: Type): Type = TyApp("fun", List(domain, codomain))

  /** The domain and codomain of a function type. */
  def destFun(ty: Type): Option[(Type, Type)] = ty match {
    case TyApp("fun", List(domain, codomain)) => Some((domain, codomain))
    case _ => None
  }

  /** The type variables occurring in `ty`. */
  def variables(ty: Type): Set[String] = ty match {
    case TyVar(name) => Set(name)
    case TyApp(_, arguments) => arguments.foldLeft(Set.empty[String])(_ ++ variables(_))
  }

  /** Replace type variables according to `substitution`. Variables not in it are left alone. */
  def substitute(substitution: Map[String, Type], ty: Type): Type = ty match {
    case TyVar(name) => substitution.getOrElse(name, ty)
    case TyApp(operator, arguments) => TyApp(operator, arguments.map(substitute(substitution, _)))
  }

  /**
   * One-way matching: the substitution that turns `pattern` into `instance`, if there is one.
   *
   * One-way rather than unification because the two sides are not symmetric anywhere the kernel
   * uses this. A constant's declared type is a schema and the type at the use site is an
   * instance of it, never the other way round, and a matcher that also instantiated the use site
   * would let a caller widen a constant's type by naming a type variable.
   */
  def matchType(pattern: Type, instance: Type): Option[Map[String, Type]] = {
    def go(pattern: Type, instance: Type, acc: Map[String, Type]): Option[Map[String, Type]] =
      (pattern, instance) match {
        case (TyVar(name), _) =>
          acc.get(name) match {
            case Some(bound) => if (bound == instance) Some(acc) else None
            case None => Some(acc.updated(name, instance))
          }
        case (TyApp(op1, args1), TyApp(op2, args2))
          if op1 == op2 && args1.length == args2.length =>
          args1.zip(args2).foldLeft(Option(acc)) {
            case (Some(current), (p, i)) => go(p, i, current)
            case (None, _) => None
          }
        case _ => None
      }

    go(pattern, instance, Map.empty)
  }

  /** A total order on types, so that a set of hypotheses has one spelling. */
  given ordering: Ordering[Type] = new Ordering[Type] {
    def compare(a: Type, b: Type): Int = (a, b) match {
      case (TyVar(x), TyVar(y)) => x.compare(y)
      case (TyVar(_), TyApp(_, _)) => -1
      case (TyApp(_, _), TyVar(_)) => 1
      case (TyApp(op1, args1), TyApp(op2, args2)) =>
        val byOperator = op1.compare(op2)
        if (byOperator != 0) byOperator else compareAll(args1, args2)
    }

    private def compareAll(a: List[Type], b: List[Type]): Int = (a, b) match {
      case (Nil, Nil) => 0
      case (Nil, _) => -1
      case (_, Nil) => 1
      case (x :: xs, y :: ys) =>
        val byHead = compare(x, y)
        if (byHead != 0) byHead else compareAll(xs, ys)
    }
  }
}
