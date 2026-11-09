package garden.xeno.symbolum.kernel

/**
 * The signature a term is built against: which type operators exist, which constants exist and at
 * what type, which constants have a definition, and which propositions are asserted without
 * proof.
 *
 * A theory is an immutable value and every extension returns a new one. The alternative, a global
 * mutable signature that every rule consults, is what the tradition does and it makes the theory
 * an ambient input to every inference: two theorems then carry no record of whether they were
 * proved against the same signature. Here they are values, and a caller that wants one signature
 * for the session holds one value.
 *
 * == What is safe to add and what is not ==
 *
 * Declaring a type operator or a constant is conservative. An uninterpreted name says nothing, so
 * nothing that was underivable becomes derivable, and a theory full of undefined constants proves
 * exactly what the empty one proves.
 *
 * Defining a constant is conservative too, under the conditions [[Kernel.defineConstant]]
 * enforces: the new name is an abbreviation, and every theorem mentioning it has a counterpart
 * that does not.
 *
 * Asserting an axiom is not conservative, and it is the only operation here that is not. It is
 * the reason [[axioms]] is a field a test can read: the size of the trusted base is a number, not
 * a matter of opinion, and it should change only when someone means it to.
 */
final case class Theory private[kernel] (
  typeOperators: Map[String, Int],
  constants: Map[String, Type],
  definitions: Map[String, Term],
  axioms: List[Term],
  origins: Map[String, Term] = Map.empty
) {

  /** Check that every type operator in `ty` exists and has the arity used. */
  def checkType(ty: Type): Either[KernelError, Unit] = ty match {
    case TyVar(_) => Right(())

    case TyApp(operator, arguments) =>
      typeOperators.get(operator) match {
        case None => Left(UnknownTypeOperator(operator))
        case Some(arity) if arity != arguments.length =>
          Left(ArityMismatch(operator, arity, arguments.length))
        case Some(_) =>
          arguments.foldLeft(Right(()): Either[KernelError, Unit]) { (acc, argument) =>
            acc.flatMap(_ => checkType(argument))
          }
      }
  }

  /** This theory extended with a type operator of the given arity. */
  def declareTypeOperator(name: String, arity: Int): Either[KernelError, Theory] =
    if (typeOperators.contains(name)) Left(AlreadyDeclared(name))
    else Right(copy(typeOperators = typeOperators.updated(name, arity)))

  /**
   * This theory extended with a constant, at the given type schema.
   *
   * The schema's type variables are the ones a use site may instantiate. A constant declared at
   * `A -> A` may be used at `real -> real`; one declared at `real -> real` may not be used at
   * `bool -> bool`.
   *
   * What it costs is the other instantiation: `Kernel.inst` substitutes free variables, so a
   * constant is a position nothing will ever specialise. Declare what a development is about and
   * leave what it is parameterised by a variable. `docs/proving.md` has the case that measured it.
   */
  def declareConstant(name: String, schema: Type): Either[KernelError, Theory] =
    if (name == Term.EqualityName || constants.contains(name)) Left(AlreadyDeclared(name))
    else checkType(schema).map(_ => copy(constants = constants.updated(name, schema)))

  /**
   * The constant `name` at type `instance`, if the theory declares it and the type is an instance
   * of the declared schema.
   */
  def constant(name: String, instance: Type): Either[KernelError, Term] =
    constants.get(name) match {
      case None => Left(UnknownConstant(name))
      case Some(schema) =>
        checkType(instance).flatMap { _ =>
          Type.matchType(schema, instance) match {
            // The origin travels with the constant, so a term built against this theory carries
            // which definition introduced each of its constants without any call site saying so.
            case Some(_) => Right(Const(name, instance, origins.get(name)))
            case None => Left(NotAnInstance(name, schema, instance))
          }
        }
    }

  /**
   * Check that every constant in `term` is declared here, at an instance of its declared type,
   * and that every type mentioned is well-formed.
   *
   * Terms are well-typed by construction, but nothing ties a term to a particular signature: it
   * can be built against one theory and handed to another. The three operations that extend a
   * theory call this: two of them would record such a term, and [[Kernel.defineType]] would build
   * its two theorems out of one.
   */
  def checkTerm(term: Term): Either[KernelError, Unit] =
    if (!Term.isLocallyClosed(term)) Left(NotLocallyClosed(term))
    else checkNames(term)

  private def checkNames(term: Term): Either[KernelError, Unit] = term match {
    case BVar(_) => Right(())
    case FVar(_, ty) => checkType(ty)
    // Not `map(_ => ())`: what this theory would build has to be the constant that is here, origin
    // and all. A name and a type that agree while the origins do not is a constant from another
    // chain, which is the case `docs/adr/0008` is about, and the three operations that extend a
    // theory are where such a term would otherwise be recorded.
    case found: Const =>
      constant(found.name, found.ty).flatMap { expected =>
        if (expected == found) Right(())
        else Left(NotAnInstance(found.name, found.ty, found.ty))
      }
    case App(fn, arg) => checkNames(fn).flatMap(_ => checkNames(arg))
    case Abs(binderType, body) => checkType(binderType).flatMap(_ => checkNames(body))
  }

  /** The constants that have no definition, equality among them. */
  def undefinedConstants: Set[String] = constants.keySet -- definitions.keySet
}

object Theory {

  /**
   * The theory the kernel starts from: the two type operators it knows by name, equality, and no
   * axioms at all.
   *
   * Equality is here rather than declared by a caller because the inference rules mention it: a
   * theory without it could not state the conclusion of reflexivity.
   */
  val primitive: Theory = {
    val alpha = TyVar("A")
    Theory(
      typeOperators = Map("bool" -> 0, "fun" -> 2),
      constants = Map(Term.EqualityName -> Type.fun(alpha, Type.fun(alpha, Type.Bool))),
      definitions = Map.empty,
      axioms = Nil,
      origins = Map.empty
    )
  }
}
