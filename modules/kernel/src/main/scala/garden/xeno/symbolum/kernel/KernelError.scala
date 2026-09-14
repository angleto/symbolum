package garden.xeno.symbolum.kernel

/**
 * Why a construction or an inference was refused.
 *
 * Every operation that can fail returns one of these rather than throwing, and returns it rather
 * than a boolean, because a caller that cannot see which rule refused it and why has to guess.
 * Refusal is the normal case here: a tactic proposes steps and most of them do not apply.
 *
 * There is one exception, [[KernelInvariantViolation]], which is thrown. It is not a refusal.
 */
sealed trait KernelError {
  def message: String
}

/** A term was applied to an argument of the wrong type. */
final case class TypeMismatch(expected: Type, found: Type, context: String) extends KernelError {
  def message: String = s"$context: expected $expected, found $found"
}

/** Something in a function position was not of function type. */
final case class NotAFunction(found: Type) extends KernelError {
  def message: String = s"expected a function type, found $found"
}

/**
 * A term carries an index with no binder above it inside the term.
 *
 * Such a term can be obtained from outside this package, because a case class hands out its
 * fields and the printer and the rewriter need to pattern match on a binder. It cannot be allowed
 * into a theorem: substitution and beta move terms across binders without shifting, so the index
 * would be captured by whatever binder it landed under, and a proof that two different functions
 * are equal follows in two steps.
 */
final case class NotLocallyClosed(found: Term) extends KernelError {
  def message: String = s"$found has an index with no binder above it"
}

/** A rule needed an equation and was given something else. */
final case class NotAnEquation(found: Term) extends KernelError {
  def message: String = s"expected an equation, found $found"
}

/** Beta conversion was asked for on a term that is not an application of a lambda. */
final case class NotABetaRedex(found: Term) extends KernelError {
  def message: String = s"not a beta redex: $found"
}

/** A rule needed a proposition and was given a term of another type. */
final case class NotAProposition(found: Term, ty: Type) extends KernelError {
  def message: String = s"expected a term of type bool, found $found of type $ty"
}

/**
 * Two terms had to be equal and were not.
 *
 * **When the two print alike, the message says why anyway.** A constant carries the term that
 * defined it (`docs/adr/0008`), so two chains that define one name differently give two constants
 * that are different terms and print the same, and a refusal reading `c is not c` tells a caller
 * nothing at all. It is the one difference the spelling cannot show, so it is the one the message
 * has to name.
 */
final case class TermsDiffer(left: Term, right: Term, context: String) extends KernelError {
  def message: String = {
    val shown = s"$context: $left is not $right"
    if (Printer.show(left) != Printer.show(right)) shown
    else
      TermsDiffer.differingConstant(left, right) match {
        case Some(name) =>
          s"$shown; they print alike because the two are the constant $name from different " +
            "definitions, which are different constants"
        case None => s"$shown; the two print alike and are not the same term"
      }
  }
}

object TermsDiffer {

  /** The name of the first constant the two terms disagree about, when they disagree about one. */
  private def differingConstant(left: Term, right: Term): Option[String] = (left, right) match {
    case (a: Const, b: Const) if a.name == b.name && a.ty == b.ty && a != b => Some(a.name)
    case (App(f1, a1), App(f2, a2)) =>
      differingConstant(f1, f2).orElse(differingConstant(a1, a2))
    case (Abs(_, b1), Abs(_, b2)) => differingConstant(b1, b2)
    case _ => None
  }
}

/** A name was used that the theory does not declare. */
final case class UnknownConstant(name: String) extends KernelError {
  def message: String = s"no constant named $name in this theory"
}

/** A type operator was used that the theory does not declare. */
final case class UnknownTypeOperator(name: String) extends KernelError {
  def message: String = s"no type operator named $name in this theory"
}

/** A type operator was applied to the wrong number of arguments. */
final case class ArityMismatch(name: String, expected: Int, found: Int) extends KernelError {
  def message: String = s"type operator $name takes $expected arguments, found $found"
}

/** A use of a constant at a type that is not an instance of its declared type. */
final case class NotAnInstance(name: String, declared: Type, requested: Type) extends KernelError {
  def message: String = s"$requested is not an instance of the declared type $declared of $name"
}

/** A name was introduced that the theory already has. */
final case class AlreadyDeclared(name: String) extends KernelError {
  def message: String = s"$name is already declared in this theory"
}

/**
 * The variable an abstraction is over occurs free in the hypotheses of the theorem.
 *
 * **The blocking hypotheses are carried, not just the variable**, and that is the whole of what
 * this refusal is for. The rule already has them: the side condition is an `exists` over the
 * hypothesis list, so the ones that match are a `filter` away and were being thrown out at the
 * moment they were computed. A caller told only that `t` occurs free somewhere among four
 * hypotheses has to work out which, and the repair depends entirely on the answer: a hypothesis
 * that mentions the variable because it is a recursion stated at one length wants restating
 * universally, and one that mentions it because the caller assumed something about that particular
 * value wants discharging instead.
 *
 * Found on 2026-09-12 from the consumer, about to generalise a step whose four hypotheses are all
 * definitions. Reporting the variable alone is the same shape as a refusal naming its cause and not
 * its remedy, which this repository spent that day repairing one layer up.
 */
final case class VariableIsFreeInHypotheses(variable: Term, blocking: List[Term])
  extends KernelError {
  def message: String =
    s"$variable occurs free in ${blocking.size} of the hypotheses: ${blocking.mkString("; ")}"
}

/** A definition mentioned a free variable, so it does not define a single value. */
final case class DefinitionIsNotClosed(free: Set[Term]) extends KernelError {
  def message: String = s"the definition has free variables: ${free.mkString(", ")}"
}

/**
 * A definition whose body carries a type variable that its type does not.
 *
 * Refused because the constant would then have one definition per instantiation of that variable
 * while presenting a single type, which is the standard route to a contradiction from an
 * apparently harmless definitional extension.
 */
final case class TypeVariablesEscape(names: Set[String]) extends KernelError {
  def message: String =
    s"the type variables ${names.mkString(", ")} occur in the definition but not in its type"
}

/**
 * A theorem offered as a witness carried hypotheses of its own.
 *
 * Refused where a rule needs something to hold outright. [[Kernel.defineType]] is the one, and the
 * reason is that neither theorem it returns carries a hypothesis: a witness that held only under an
 * assumption would have that assumption discharged into silence, and the new type would be asserted
 * inhabited on a condition nobody records.
 */
final case class TheoremHasHypotheses(hypotheses: List[Term]) extends KernelError {
  def message: String =
    s"the theorem assumes ${hypotheses.mkString(", ")}, where it has to hold outright"
}

/** A term was needed in the form `f x` and was not an application. */
final case class NotAnApplication(found: Term) extends KernelError {
  def message: String = s"$found is not an application"
}

/**
 * A term was reached that could not have been built through the constructors in this package.
 *
 * Thrown rather than returned, and deliberately not a [[KernelError]]: a caller cannot do
 * anything sensible with it, because it means the invariant every other operation relies on is
 * already broken. It is reachable only through a defect in this package.
 */
final class KernelInvariantViolation(description: String)
  extends RuntimeException(s"kernel invariant violated: $description")
