package garden.xeno.symbolum.checker

/**
 * An inference, as this checker holds one, which is not how the kernel holds one.
 *
 * `Expr` exists because the point of a second checker is that it disagrees where the first is
 * wrong, and it cannot do that with the first one's terms. This file is the same argument one level
 * up: a step used to arrive as a `Derivation`, a kernel value, and the checker read the terms out
 * of it with the kernel's extractors. So the *terms* were this checker's own and the *proof* was
 * still the kernel's object, held in memory, reachable only in this process.
 *
 * With a step of its own the checker takes a proof from anywhere. `Read.step` builds one from a
 * derivation, which is the in-process route and the fast one; `Parse.proof` builds a whole table of
 * them from text, and that route touches no kernel type at all. `Check` works on this, so both
 * routes reach the same code and there is one implementation of each rule rather than two.
 *
 * The premises are not here. A step names what rule it is and what that rule needs *besides* its
 * premises: which term was reflected on, which variable was abstracted, what was substituted. The
 * premises arrive beside it, as claims, because a table read from text has them by number and an
 * in-process walk has them by reference, and the checking is the same either way.
 */
sealed trait Step

object Step {

  /** Which of the two theorems a type definition returns. */
  enum Half {
    case AbstractionOfRepresentation, Characterisation
  }

  /** `|- t = t` */
  final case class Reflexivity(term: Expr) extends Step

  /** `G |- a = b` and `D |- b = c` give `G, D |- a = c` */
  case object Transitivity extends Step

  /** `G |- f = g` and `D |- x = y` give `G, D |- f x = g y` */
  case object Congruence extends Step

  /** `G |- s = t` gives `G |- (\x. s) = (\x. t)` */
  final case class Abstraction(variable: Expr.Free) extends Step

  /** `|- (\x. t) u = t[u/x]` */
  final case class BetaStep(term: Expr) extends Step

  /** `p |- p` */
  final case class Assumption(proposition: Expr) extends Step

  /** `G |- p = q` and `D |- p` give `G, D |- q` */
  case object EqualityElimination extends Step

  /** `G |- p` and `D |- q` give `(G - q), (D - p) |- p = q` */
  case object Antisymmetry extends Step

  /** Free variables replaced throughout. */
  final case class Instantiation(substitution: Map[Expr.Free, Expr]) extends Step

  /** Type variables replaced throughout. */
  final case class TypeInstantiation(substitution: Map[String, Ty]) extends Step

  /** A constant, and the body it was defined as. */
  final case class Definition(name: String, body: Expr) extends Step

  /** Asserted, and the only step in any proof that is believed rather than checked. */
  final case class Axiom(proposition: Expr) extends Step

  /** A type definition, and which half of the bijection this theorem is. */
  final case class TypeDefinition(
    typeName: String,
    absName: String,
    repName: String,
    half: Half
  ) extends Step

  /** How many premises the rule takes, which is what a table read from text has to agree with. */
  def arity(step: Step): Int = step match {
    case Transitivity | Congruence | EqualityElimination | Antisymmetry => 2
    case Abstraction(_) | Instantiation(_) | TypeInstantiation(_) | TypeDefinition(_, _, _, _) => 1
    case _ => 0
  }
}

/** One node of a proof: what it claims, the rule it claims it by, and where its premises are. */
final case class Node(claim: Claim, step: Step, premises: Vector[Int])
