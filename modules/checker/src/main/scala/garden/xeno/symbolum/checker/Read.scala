package garden.xeno.symbolum.checker

import garden.xeno.symbolum.kernel.*

/**
 * The kernel's data, read into this checker's own.
 *
 * The one place the two touch. It uses the public extractors and nothing else: no rule, no
 * substitution, no typing. What comes out is a value this checker owns, and everything done to it
 * afterwards is this checker's code.
 */
object Read {

  /** A type. */
  def ty(source: Type): Ty = source match {
    case TyVar(name) => Ty.Variable(name)
    case TyApp(operator, arguments) => Ty.Operator(operator, arguments.map(ty))
  }

  /**
   * A term.
   *
   * A constant's origin is read too, because it is part of what makes two constants the same and a
   * checker that dropped it would accept a chaining the kernel refuses. It is read to a fixed depth
   * of one: an origin's own constants keep theirs, since the traversal is the same function.
   */
  def expr(source: Term): Expr = source match {
    case BVar(index) => Expr.Bound(index)
    case FVar(name, kind) => Expr.Free(name, ty(kind))
    case constant: Const => Expr.Constant(constant.name, ty(constant.ty), constant.origin.map(expr))
    case App(fn, argument) => Expr.Apply(expr(fn), expr(argument))
    case Abs(binder, body) => Expr.Lambda(ty(binder), expr(body))
  }

  /** A sequent: what a theorem claims, with no view on whether it holds. */
  def claim(theorem: Kernel.Thm): Claim =
    Claim(theorem.hypotheses.map(expr).toVector, expr(theorem.conclusion))

  /**
   * An inference, in this checker's own terms.
   *
   * The premises are dropped here and not lost: they are reachable from the derivation and the
   * caller passes them beside the step, which is what lets a proof read from text reach the same
   * checking code as one walked in this process.
   */
  def step(derivation: Derivation): Step = derivation match {
    case Derivation.Reflexivity(term) => Step.Reflexivity(expr(term))
    case Derivation.Transitivity(_, _) => Step.Transitivity
    case Derivation.Congruence(_, _) => Step.Congruence
    case Derivation.Abstraction(variable, _) =>
      Step.Abstraction(Expr.Free(variable.name, ty(variable.ty)))
    case Derivation.BetaStep(term) => Step.BetaStep(expr(term))
    case Derivation.Assumption(proposition) => Step.Assumption(expr(proposition))
    case Derivation.EqualityElimination(_, _) => Step.EqualityElimination
    case Derivation.Antisymmetry(_, _) => Step.Antisymmetry
    case Derivation.Instantiation(substitution, _) =>
      Step.Instantiation(substitution.map { case (variable, replacement) =>
        Expr.Free(variable.name, ty(variable.ty)) -> expr(replacement)
      })
    case Derivation.TypeInstantiation(substitution, _) =>
      Step.TypeInstantiation(substitution.map { case (name, replacement) => name -> ty(replacement) })
    case Derivation.Definition(name, body) => Step.Definition(name, expr(body))
    case Derivation.Axiom(proposition) => Step.Axiom(expr(proposition))
    case Derivation.TypeDefinition(typeName, absName, repName, _, half) =>
      Step.TypeDefinition(typeName, absName, repName, half match {
        case Derivation.Half.AbstractionOfRepresentation => Step.Half.AbstractionOfRepresentation
        case Derivation.Half.Characterisation => Step.Half.Characterisation
      })
  }
}

/** What a theorem says, in this checker's terms. */
final case class Claim(hypotheses: Vector[Expr], conclusion: Expr) {

  /** The hypotheses as a set, since a sequent's left side is one however the kernel stores it. */
  def assumptions: Set[Expr] = hypotheses.toSet
}
