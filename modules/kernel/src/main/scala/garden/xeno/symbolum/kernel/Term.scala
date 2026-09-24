package garden.xeno.symbolum.kernel

/**
 * A term of the simply typed lambda calculus, in locally nameless form.
 *
 * A variable bound by a lambda is an index counting the enclosing binders; a free variable is a
 * name carrying its type. The two are different constructors, so they cannot be confused, and the
 * name of a bound variable does not exist at all.
 *
 * Two consequences, and they are the reason for the representation:
 *
 *  - alpha-equivalence is `==`. `λx. x` and `λy. y` are the same value, not two values a
 *    comparison has to reconcile.
 *  - substitution cannot capture. Replacing a free variable, or instantiating a type variable,
 *    can only touch [[FVar]] and [[Const]] nodes, and what is put in their place is a locally
 *    closed term, so no occurrence can fall under a binder that binds it. The renaming that a
 *    name-carrying representation needs here does not exist, and neither do its mistakes.
 *
 * Terms are well-typed by construction: every value built through the operations in [[Term]] and
 * [[Theory]] is, and the rest of the kernel relies on that rather than re-checking. Locally closed
 * is different. The extractor on [[Abs]] hands out a body whose outermost index has no binder
 * above it, so every operation here that accepts a term checks [[Term.isLocallyClosed]] and refuses
 * with [[NotLocallyClosed]] otherwise. Before it did, that body could be put back under a binder
 * of another type and made `|- 0 = 1`; the check is the fix, and the attack is a test.
 *
 * @see [[Kernel]] for the inference rules, which are the only way to obtain a theorem
 */
sealed trait Term {
  override def toString: String = Printer.show(this)
}

/** A variable bound by the `index`-th enclosing binder, counting from zero, innermost first. */
final case class BVar private[kernel] (index: Int) extends Term

/** A free variable. Its name and its type together are its identity. */
final case class FVar private[kernel] (name: String, ty: Type) extends Term

/**
 * A constant at a particular type, carrying the term that gave it its identity.
 *
 * The type is the instance being used, not the schema the theory declares: a theory declaring
 * `=` at `A -> A -> bool` admits a constant `=` at `real -> real -> bool`. [[Theory.constant]] is
 * what checks the instance against the schema, and is the only way to build one, with the single
 * exception of equality, which the kernel knows by name.
 *
 * == The origin, and what it is for ==
 *
 * Two constants are the same constant when the name, the type **and the origin** agree.
 * `docs/adr/0008` is the record: two theories defining one name differently used to produce
 * theorems that combined into `|- T = F`, and they no longer combine at all, because the two
 * constants are different terms and the rules already compare terms.
 *
 * The origin is the definition body for a defined constant and the predicate for the two constants
 * a type definition introduces. A **declared** constant has none, which is right: an uninterpreted
 * name says nothing, so two theories declaring one are talking about the same thing.
 *
 * It is a token and not content. Nothing substitutes into it, nothing reads variables out of it,
 * and the two-field extractor below is what keeps every pattern match in the system reading the
 * name and the type as it always did.
 */
final class Const private[kernel] (val name: String, val ty: Type, val origin: Option[Term])
    extends Term {

  override def equals(other: Any): Boolean = other match {
    case that: Const =>
      name == that.name && ty == that.ty && Const.sameOrigin(origin, that.origin)
    case _ => false
  }

  override def hashCode(): Int = 31 * (31 * name.hashCode + ty.hashCode)
}

object Const {

  /** The name and the type, so that every existing pattern match goes on working unchanged. */
  def unapply(constant: Const): Some[(String, Type)] = Some((constant.name, constant.ty))

  /**
   * Whether two origins are the same, by reference first.
   *
   * Inside one chain of extensions the two are the same object, so the comparison costs nothing
   * there; the structural fallback runs when two chains actually meet, which is the case this
   * exists for.
   */
  private[kernel] def sameOrigin(left: Option[Term], right: Option[Term]): Boolean =
    (left, right) match {
      case (None, None) => true
      case (Some(a), Some(b)) => (a eq b) || a == b
      case _ => false
    }
}

/** An application. Well-typed by construction: see [[Term.app]]. */
final case class App private[kernel] (fn: Term, arg: Term) extends Term

/**
 * A lambda abstraction. The bound variable has no name, only the type recorded here.
 */
final case class Abs private[kernel] (binderType: Type, body: Term) extends Term

object Term {

  /** The name equality is known by. Reserved: a theory cannot declare another constant with it. */
  val EqualityName: String = "="

  /* ----------------------------------------------------------------- building */

  /**
   * A free variable.
   *
   * Returns the narrow type rather than [[Term]] because [[abs]] and [[Kernel.abs]] take a free
   * variable specifically: widening here would make the two rules that need one unreachable from
   * outside this package.
   */
  def variable(name: String, ty: Type): FVar = FVar(name, ty)

  /** Equality at type `ty`, as a constant. */
  def equalityAt(ty: Type): Term =
    new Const(EqualityName, Type.fun(ty, Type.fun(ty, Type.Bool)), None)

  /** Apply `fn` to `arg`, checking that the types agree. */
  def app(fn: Term, arg: Term): Either[KernelError, Term] =
    if (!isLocallyClosed(fn)) Left(NotLocallyClosed(fn))
    else if (!isLocallyClosed(arg)) Left(NotLocallyClosed(arg))
    else Type.destFun(typeOf(fn)) match {
      case None => Left(NotAFunction(typeOf(fn)))
      case Some((domain, _)) =>
        val argumentType = typeOf(arg)
        if (domain == argumentType) Right(App(fn, arg))
        else Left(TypeMismatch(domain, argumentType, "application"))
    }

  /** Apply `fn` to each argument in turn. */
  def appAll(fn: Term, arguments: List[Term]): Either[KernelError, Term] =
    arguments.foldLeft(Right(fn): Either[KernelError, Term]) { (acc, argument) =>
      acc.flatMap(app(_, argument))
    }

  /**
   * Abstract `variable` out of `body`, giving `λ variable. body`.
   *
   * Every free occurrence of the variable becomes an index. Occurrences of a variable with the
   * same name at a different type are left alone: name and type together are the identity.
   *
   * **The check was missing until 2026-09-10**, and this is the operation the paragraph at the top
   * of this file described while being false of it. `close` is correct given a locally closed body,
   * since then every index it meets has a binder inside the term; a **loose** index it leaves
   * alone, and the new binder captures it at whatever type that binder has. Abstract the
   * destructured body of `\z:real. z = z` under a `bool` variable and the result applies equality
   * at `real` to two booleans, which [[typeOf]] answers for rather than refusing, because it is
   * entitled to assume what this was failing to establish. `SoundnessAttackSpec` carries it beside
   * the six operations that were already on that list.
   */
  def abs(variable: FVar, body: Term): Either[KernelError, Term] =
    requireClosed(body).map(_ => Abs(variable.ty, close(variable, 0, body)))

  /**
   * Abstract each variable in turn, outermost first: `absAll(List(p, q), t)` is `\p. \q. t`.
   *
   * The counterpart of [[appAll]]. The connectives are defined two binders at a time, and threading
   * the refusal by hand at each of those sites is the same line written twice with a chance of
   * writing it backwards once.
   */
  def absAll(variables: List[FVar], body: Term): Either[KernelError, Term] =
    variables.foldRight(Right(body): Either[KernelError, Term]) { (variable, acc) =>
      acc.flatMap(abs(variable, _))
    }

  /** The equation `lhs = rhs`, if the two sides have the same type. */
  def eq(lhs: Term, rhs: Term): Either[KernelError, Term] =
    if (!isLocallyClosed(lhs)) Left(NotLocallyClosed(lhs))
    else if (!isLocallyClosed(rhs)) Left(NotLocallyClosed(rhs))
    else {
      val leftType = typeOf(lhs)
      val rightType = typeOf(rhs)
      if (leftType != rightType) Left(TypeMismatch(leftType, rightType, "equation"))
      else appAll(equalityAt(leftType), List(lhs, rhs))
    }

  /** The two sides of an equation. */
  def destEq(term: Term): Option[(Term, Term)] = term match {
    case App(App(Const(EqualityName, _), lhs), rhs) => Some((lhs, rhs))
    case _ => None
  }

  /* ------------------------------------------------------------------ typing */

  /**
   * The type of a well-formed term.
   *
   * Total, because every term built through this object is well-typed: the checking happens once,
   * where the term is built, instead of on every inspection.
   *
   * **Where that premise is established:** [[app]] checks the argument against the domain, [[eq]]
   * checks the two sides agree, [[substitute]] checks each replacement, and [[abs]] checks the body
   * is locally closed. `TermSpec` enumerates those four so that a fifth builder cannot be added
   * without joining the list, which is how [[abs]] came to be the one that did not check.
   *
   * The `App` case below reads the codomain without computing the argument's type, so it answers
   * for an ill-typed application rather than refusing. The asymmetry with the `BVar` case, which
   * throws, is deliberate: a loose index is free to detect and a type mismatch would turn the
   * hottest primitive here from a walk down the spine into a walk over the whole term, on every
   * call, to defend what those four already establish.
   *
   * @throws KernelInvariantViolation if the term was not built through these constructors
   */
  def typeOf(term: Term): Type = typeIn(term, Nil)

  private def typeIn(term: Term, context: List[Type]): Type = term match {
    case BVar(index) =>
      if (index < context.length) context(index)
      // The count is written after its noun and not in front of it, which is a decision rather
      // than a style: this message used to read `${context.length} binders` and said "1 binders"
      // under exactly one binder. Everywhere else in the repository that defect is repaired with a
      // counter -- `Prose.count` in `modules/theories`, and a copy of it in each module that
      // cannot see it -- and the trusted base takes neither. How many those are is not written
      // here: it was four when this sentence was, `logic` became the fifth on 2026-09-20, and a
      // figure that moves whenever a module grows a message is a figure a comment cannot hold.
      // The trusted base is counted, in files and in lines against a bound `DocumentationSpec`
      // holds, and a line that exists to render English is a line somebody has to read and
      // believe. `Argument` set the precedent
      // one module over by changing the sentence rather than the last letter, and `ArityMismatch`
      // in `KernelError` is the same move at the one other site of this shape in here.
      else throw new KernelInvariantViolation(s"index $index, binders in scope: ${context.length}")

    case FVar(_, ty) => ty
    case Const(_, ty) => ty
    case Abs(binderType, body) => Type.fun(binderType, typeIn(body, binderType :: context))

    case App(fn, _) =>
      Type.destFun(typeIn(fn, context)) match {
        case Some((_, codomain)) => codomain
        case None => throw new KernelInvariantViolation(s"application of a non-function in $term")
      }
  }

  /** True if the term is a proposition. */
  def isProposition(term: Term): Boolean = typeOf(term) == Type.Bool

  /**
   * True if every index in `term` is bound by a binder inside it.
   *
   * The invariant every rule below relies on, and until an audit of this session it was assumed
   * rather than checked. It is not maintained by construction, because a case class hands out its
   * fields: `lambda match { case Abs(_, body) => body }` returns a term whose index has lost the
   * binder that gave it meaning, and pattern matching cannot be taken away because the printer,
   * the matcher and the rewriter all need it.
   *
   * An open term is not merely meaningless. Substitution and beta move a term across a binder
   * without shifting, exactly because they are entitled to assume this, so an index that arrives
   * from outside is captured by whatever binder it lands under. That turns `(\x. h) v = h` into
   * `(\x. f x) v = f ?0`, and two more steps turn it into a proof that two different functions are
   * equal. Every operation that admits a term from outside a theorem checks this now.
   */
  def isLocallyClosed(term: Term): Boolean = {
    def go(current: Term, depth: Int): Boolean = current match {
      case BVar(index) => index < depth
      case App(fn, argument) => go(fn, depth) && go(argument, depth)
      case Abs(_, body) => go(body, depth + 1)
      case _ => true
    }

    go(term, 0)
  }

  /** `Right` if the term is locally closed, and the refusal if it is not. */
  private[kernel] def requireClosed(term: Term): Either[KernelError, Unit] =
    if (isLocallyClosed(term)) Right(()) else Left(NotLocallyClosed(term))

  /* ------------------------------------------------- locally nameless plumbing */

  /**
   * Replace the variable bound by the outermost binder with `replacement`.
   *
   * `replacement` must be locally closed, which is to say it has no index of its own without an
   * enclosing binder. That is what makes this a plain traversal: nothing has to be shifted,
   * because nothing being moved inwards can be captured.
   *
   * The precondition is checked by every operation that admits a term from outside a theorem; see
   * [[isLocallyClosed]] for what happens when it does not hold, which is not a crash but a proof
   * that two different functions are equal.
   */
  private[kernel] def open(body: Term, replacement: Term): Term = openAt(body, 0, replacement)

  private def openAt(term: Term, depth: Int, replacement: Term): Term = term match {
    case BVar(index) if index == depth => replacement
    case App(fn, arg) => App(openAt(fn, depth, replacement), openAt(arg, depth, replacement))
    case Abs(binderType, body) => Abs(binderType, openAt(body, depth + 1, replacement))
    case other => other
  }

  private def close(variable: FVar, depth: Int, term: Term): Term = term match {
    case free: FVar if free == variable => BVar(depth)
    case App(fn, arg) => App(close(variable, depth, fn), close(variable, depth, arg))
    case Abs(binderType, body) => Abs(binderType, close(variable, depth + 1, body))
    case other => other
  }

  /* ------------------------------------------------------------ substitution */

  /** The free variables of a term. */
  def freeVariables(term: Term): Set[FVar] = term match {
    case free: FVar => Set(free)
    case App(fn, arg) => freeVariables(fn) ++ freeVariables(arg)
    case Abs(_, body) => freeVariables(body)
    case _ => Set.empty
  }

  /** True if `variable` occurs free in `term`. */
  def occursFree(variable: FVar, term: Term): Boolean = freeVariables(term).contains(variable)

  /**
   * Replace free variables according to `substitution`.
   *
   * Each replacement must have the type of the variable it replaces. No renaming happens and none
   * is needed: a bound variable is an index, so a replacement carried under a binder cannot be
   * captured by it.
   */
  def substitute(substitution: Map[FVar, Term], term: Term): Either[KernelError, Term] = {
    val open = substitution.collectFirst {
      case (_, replacement) if !isLocallyClosed(replacement) => NotLocallyClosed(replacement)
    }

    val illTyped = open.orElse(substitution.collectFirst {
      case (variable, replacement) if typeOf(replacement) != variable.ty =>
        TypeMismatch(variable.ty, typeOf(replacement), s"substitution for ${variable.name}")
    })

    illTyped match {
      case Some(error) => Left(error)
      case None => Right(go(substitution, term))
    }
  }

  private def go(substitution: Map[FVar, Term], term: Term): Term = term match {
    case free: FVar => substitution.getOrElse(free, free)
    case App(fn, arg) => App(go(substitution, fn), go(substitution, arg))
    case Abs(binderType, body) => Abs(binderType, go(substitution, body))
    case other => other
  }

  /**
   * Instantiate the type variables of a term.
   *
   * Two free variables with the same name at different types can become one variable here, which
   * is sound: a theorem holds for every value of each of its free variables, so the instance in
   * which two of them are equal is one of the cases it already covers. What would not be sound is
   * a free variable falling under a binder that now binds it, and that cannot happen, because a
   * binder binds an index and this rewrites neither indices nor the shape of the term.
   */
  def substituteTypes(substitution: Map[String, Type], term: Term): Term = term match {
    case BVar(index) => BVar(index)
    case FVar(name, ty) => FVar(name, Type.substitute(substitution, ty))
    // The origin travels unchanged. It says which definition introduced the constant, so
    // substituting into it would give two instances of one constant two identities and they would
    // stop being the same constant.
    case constant: Const =>
      new Const(constant.name, Type.substitute(substitution, constant.ty), constant.origin)
    case App(fn, arg) =>
      App(substituteTypes(substitution, fn), substituteTypes(substitution, arg))
    case Abs(binderType, body) =>
      Abs(Type.substitute(substitution, binderType), substituteTypes(substitution, body))
  }

  /** The type variables occurring anywhere in a term. */
  def typeVariables(term: Term): Set[String] = term match {
    case BVar(_) => Set.empty
    case FVar(_, ty) => Type.variables(ty)
    case Const(_, ty) => Type.variables(ty)
    case App(fn, arg) => typeVariables(fn) ++ typeVariables(arg)
    case Abs(binderType, body) => Type.variables(binderType) ++ typeVariables(body)
  }

  /** The result of one beta step at the root, if the term is a redex. */
  def betaReduce(term: Term): Option[Term] = term match {
    case App(Abs(_, body), argument) => Some(open(body, argument))
    case _ => None
  }

  /** A total order on terms, so that a set of hypotheses has one spelling. */
  given ordering: Ordering[Term] = new Ordering[Term] {
    def compare(a: Term, b: Term): Int = (rank(a), rank(b)) match {
      case (x, y) if x != y => x.compare(y)
      case _ => (a, b) match {
        case (BVar(i), BVar(j)) => i.compare(j)

        case (FVar(n1, t1), FVar(n2, t2)) => byNameThenType(n1, t1, n2, t2)

        // The origin is part of a constant's identity, so it is part of the order: an order that
        // called two constants equal where `==` does not would break the property that the two
        // agree, which `TermPropertySpec` asserts.
        case (c1: Const, c2: Const) =>
          val byNameAndType = byNameThenType(c1.name, c1.ty, c2.name, c2.ty)
          if (byNameAndType != 0) byNameAndType else compareOrigins(c1.origin, c2.origin)

        case (App(f1, a1), App(f2, a2)) =>
          val byFunction = compare(f1, f2)
          if (byFunction != 0) byFunction else compare(a1, a2)

        case (Abs(t1, b1), Abs(t2, b2)) =>
          val byBinder = Type.ordering.compare(t1, t2)
          if (byBinder != 0) byBinder else compare(b1, b2)

        case _ => 0
      }
    }

    private def compareOrigins(left: Option[Term], right: Option[Term]): Int = (left, right) match {
      case (None, None) => 0
      case (None, Some(_)) => -1
      case (Some(_), None) => 1
      case (Some(a), Some(b)) => if (a eq b) 0 else compare(a, b)
    }

    private def byNameThenType(n1: String, t1: Type, n2: String, t2: Type): Int = {
      val byName = n1.compare(n2)
      if (byName != 0) byName else Type.ordering.compare(t1, t2)
    }

    private def rank(term: Term): Int = term match {
      case BVar(_) => 0
      case FVar(_, _) => 1
      case Const(_, _) => 2
      case App(_, _) => 3
      case Abs(_, _) => 4
    }
  }
}
