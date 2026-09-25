package garden.xeno.symbolum.checker

import scala.annotation.tailrec

import garden.xeno.symbolum.kernel.{Derivation, Kernel, Theory}

/**
 * A second reading of a proof, by something that is not the kernel.
 *
 * The kernel says a theorem holds because it produced it. This says so, or does not, because it
 * walked the derivation and found every step to be an instance of a rule it implements itself. Two
 * implementations agreeing is evidence of a different kind from one implementation being careful,
 * and it is the kind `docs/evaluation.md` calls differential rather than adversarial.
 *
 * == What it catches ==
 *
 *  - a theorem that was not derived at all, however it was obtained;
 *  - a step that is not an instance of the rule it claims to be;
 *  - a rule the kernel implements differently from the way this file does, which is the case a
 *    second implementation exists for and the only one where the two disagree about mathematics
 *    rather than about a mistake.
 *
 * == Two routes in, one implementation of each rule ==
 *
 * [[proof]] takes a `Kernel.Thm` and walks it, reading each step through `Read`, which uses the
 * kernel's public extractors and nothing else. [[table]] takes a proof that has already been parsed
 * from text and touches no kernel type at all. Both end at [[node]], so there is one reading of
 * each rule rather than two that could drift apart.
 *
 * == What it does not catch, and this is the honest limit ==
 *
 * On the in-process route it reads the kernel's terms through the kernel's extractors, so a defect
 * in **those** would tell it the same story they tell everyone. Everything past the shape is
 * re-decided here: the typing, the closedness, the substitution, the opening of a binder and the
 * beta step are this file's own, which is where the 2026-09-03 hole lived and where a checker earns
 * its keep. The serialised route narrows that to the writer: what arrives is text, and a `Proof`
 * that writes down something other than what the kernel derived is caught by this refusing it.
 *
 * It also cannot check an axiom **is true**. Nothing can: that is what a trusted base is, and a
 * report names them rather than pretending to have verified them.
 *
 * It can check an axiom is one the theory **asserts**, and those are two different questions that
 * this file ran together until 2026-09-11. A step may claim any closed proposition as an axiom and
 * the arms below accept it, because accepting it is what an axiom step is; whether the theory ever
 * asserted that proposition is a question with an answer, and nobody was asking it. A proof of
 * `|- F` whose derivation says `Axiom(F)` came back `Holds` with `F` in the report, and every test
 * in this repository read the count and not the contents. [[proof]] and [[table]] now take the
 * theory, and an axiom outside it is [[RestsOnUnvouched]].
 *
 * That is not a defence against a forged theorem in general, and the limit is worth the sentence:
 * a theorem is a JVM object whose constructor is public in bytecode however `private` reads in the
 * source, so a caller willing to use reflection makes one. What this refuses is the forgery whose
 * derivation does not add up, and now also the one that adds up by naming an axiom nobody asserted.
 * `TrustBoundaryTwinSpec` measures which of those two the kernel stops on its own, which is
 * neither.
 *
 * == What each node is checked for, which is written down because it was not ==
 *
 * A checker whose coverage is not stated reads as though it covered everything, and on 2026-09-10
 * two arms were found accepting claims on their bracketing alone. Per node, then:
 *
 *  - **reflexivity, assumption, axiom**: fully. The claim is compared with the term the step
 *    carries, and the side conditions (no hypotheses, a closed proposition) are all of them.
 *  - **transitivity, congruence, antisymmetry, equality elimination**: fully. Each premise's
 *    conclusion is taken apart and the hypothesis arithmetic is recomputed rather than trusted.
 *  - **abstraction**: fully, including the side condition that is the whole content of the rule,
 *    the variable not being free in a hypothesis.
 *  - **beta**: fully. The redex is reduced here and the result compared.
 *  - **instantiation, type instantiation**: fully. The substitution is applied here, to the
 *    hypotheses as well as the conclusion, and each replacement is typed and closed.
 *  - **definition**: the name, the origin, the body's closedness and its escaping type variables.
 *    What is NOT checked is that the theory could have been extended by it, which is not in the
 *    node and would need the signature.
 *  - **type definition**: the two halves against the constants the step names, and the witness
 *    holding outright. What the halves MEAN is the rule's, and re-deriving it here would be
 *    re-implementing a theory extension rather than an inference. The predicate is read off the
 *    claim and not constrained, which is the rule's own arrangement.
 */
object Check {

  /** What a check found. */
  sealed trait Verdict

  /** Every step is an instance of the rule it claims, resting on these axioms and nothing else. */
  final case class Holds(steps: Int, axioms: Set[Expr]) extends Verdict

  /** A step that is not, with what was expected of it. */
  final case class Fails(step: Claim, rule: String, why: String) extends Verdict

  /**
   * A theorem keyed by which object it is, rather than by what it says.
   *
   * Two theorems are equal when they are the same sequent, whatever derived them, which is what
   * the rules need: they compare theorems to drop a duplicate hypothesis and to discharge one. A
   * walk over a proof that deduplicated on that would treat `trans(refl p, refl p)` and `refl p`
   * as one node, stop there, and report a proof of one step. It did, and `Derivation`'s own
   * comment is where that is recorded.
   *
   * `Derivation.walk` in the kernel answers the same requirement with a mutable identity set.
   * This puts the identity in the key instead, which is the same question asked of an immutable
   * `Set`. Shared with the test that counts what a writer would emit, because a second copy of
   * this class is a defect while the two agree.
   */
  private[checker] final class ByIdentity(val theorem: Kernel.Thm) {
    override def equals(other: Any): Boolean = other match {
      case that: ByIdentity => this.theorem eq that.theorem
      case _ => false
    }

    override def hashCode: Int = System.identityHashCode(theorem)
  }

  private[checker] object ByIdentity {
    def apply(theorem: Kernel.Thm): ByIdentity = new ByIdentity(theorem)
  }

  /**
   * Every step is an instance of its rule, and one of the axioms is not one the theory asserts.
   *
   * A third verdict rather than a [[Fails]], because it is a different finding and the two send a
   * reader to different places: a failed step says the proof is not a proof, and this says the
   * proof is a proof **of something else's theory**. The step it came from is a well-formed axiom
   * step; what is wrong is the axiom.
   */
  final case class RestsOnUnvouched(axiom: Expr, asserted: Set[Expr]) extends Verdict

  /**
   * Walk the proof and check every step.
   *
   * Iterative and by identity, for the reasons `Derivation` gives: a proof is as deep as the
   * derivation that built it, and two nodes that are the same sequent are not the same step.
   */
  def proof(theorem: Kernel.Thm, theory: Theory): Verdict =
    vouched(proof(theorem), theory)

  /**
   * The same without the theory, which checks the steps and **not** where the axioms came from.
   *
   * Kept because the two questions are separable and a caller replaying a proof it has no theory
   * for still wants the steps checked. It is the weaker call and the name does not say so, which is
   * why the one above exists and is what the suite uses.
   */
  def proof(theorem: Kernel.Thm): Verdict = {
    @tailrec
    def walk(pending: List[Kernel.Thm], seen: Set[ByIdentity], steps: Int, axioms: Set[Expr]): Verdict =
      pending match {
        case Nil => Holds(steps, axioms)
        case current :: rest =>
          val key = ByIdentity(current)
          if (seen.contains(key)) walk(rest, seen, steps, axioms)
          else
            node(
              Read.claim(current),
              Read.step(current.derivation),
              Derivation.premises(current.derivation).map(Read.claim).toVector
            ) match {
              // The first refusal is the answer and the walk stops: a reader shown the second
              // problem in a proof whose first step is already wrong is being told about the
              // wrong one.
              case Left(problem) => problem
              case Right(found) =>
                walk(
                  Derivation.premises(current.derivation) ++ rest,
                  seen + key,
                  steps + 1,
                  axioms ++ found
                )
            }
      }

    walk(List(theorem), Set.empty, 0, Set.empty)
  }

  /**
   * A verdict with every axiom it rests on checked against the ones a theory asserts.
   *
   * Set membership and nothing cleverer: an axiom step carries a proposition and a theory holds a
   * list of them, and what this asks is whether the first is among the second. It cannot ask
   * anything about the axiom itself, which is the sentence at the top of this file and is still
   * true.
   */
  private def vouched(verdict: Verdict, theory: Theory): Verdict = verdict match {
    case holds: Holds =>
      val asserted = theory.axioms.map(Read.expr).toSet
      holds.axioms.find(!asserted.contains(_)) match {
        case Some(stranger) => RestsOnUnvouched(stranger, asserted)
        case None => holds
      }
    case other => other
  }

  /**
   * Check a proof that arrived as a table rather than as a theorem.
   *
   * The route that shares no type with the kernel. A node's premises are numbers into the table,
   * and `Parse` has already refused a number that points forward or past the end, so the walk here
   * is a fold and not a search.
   *
   * **Every node is checked, including one nothing refers to.** A table can carry a step the
   * theorem does not rest on, and skipping it would let a writer hide a bad step where a reader
   * counts steps. What the verdict counts is the whole table, which is also what a size measurement
   * is about.
   */
  def table(proof: Parse.Proof, theory: Theory): Verdict =
    vouched(table(proof), theory)

  /** The same without the theory. See [[proof]] for what that leaves unasked. */
  def table(proof: Parse.Proof): Verdict = {
    @tailrec
    def walk(at: Int, axioms: Set[Expr]): Verdict =
      if (at == proof.nodes.length) Holds(proof.nodes.length, axioms)
      else {
        val current = proof.nodes(at)
        node(current.claim, current.step, current.premises.map(proof.nodes).map(_.claim)) match {
          case Left(problem) => problem
          case Right(found) => walk(at + 1, axioms ++ found)
        }
      }

    // By index rather than over a list, because a premise is a back reference by position and the
    // table is read the way it was written.
    walk(0, Set.empty)
  }

  /** The same, for text that has not been read yet. A text that is not a proof is a refusal. */
  def text(source: String): Either[String, Verdict] = Parse.proof(source).map(table)

  /** The same, with every axiom checked against the ones a theory asserts. See [[proof]]. */
  def text(source: String, theory: Theory): Either[String, Verdict] =
    Parse.proof(source).map(table(_, theory))

  /**
   * One node: the claim it makes, against the rule it says produced it and what it was given.
   *
   * Public and taking data rather than a theorem, so that a test can put a wrong claim to it. A
   * checker whose refusals are never exercised is a checker nobody has tested, and there is no way
   * to obtain a wrongly derived theorem from the kernel in order to try one.
   */
  def node(
    claim: Claim,
    step: Step,
    premises: Vector[Claim]
  ): Either[Verdict, Set[Expr]] = {

    def refuse(rule: String, why: String): Either[Verdict, Set[Expr]] =
      Left(Fails(claim, rule, why))

    def require(rule: String, why: String)(condition: Boolean): Either[Verdict, Set[Expr]] =
      if (condition) Right(Set.empty) else refuse(rule, why)

    step match {
      case Step.Reflexivity(subject) =>
        Expr.sidesOf(claim.conclusion) match {
          case Some((left, right)) =>
            require("reflexivity", "both sides are the term, under no hypothesis")(
              left == subject && right == subject && claim.hypotheses.isEmpty
            )
          case None => refuse("reflexivity", "the conclusion is an equation")
        }

      case Step.Transitivity =>
        (premises, Expr.sidesOf(claim.conclusion)) match {
          case (Vector(left, right), Some((a, c))) =>
            (Expr.sidesOf(left.conclusion), Expr.sidesOf(right.conclusion)) match {
              case (Some((a1, b1)), Some((b2, c1))) =>
                require("transitivity", "the middles meet and the ends are carried")(
                  b1 == b2 && a == a1 && c == c1 &&
                    claim.assumptions == left.assumptions ++ right.assumptions
                )
              case _ => refuse("transitivity", "two equations")
            }
          case _ => refuse("transitivity", "two premises and an equation")
        }

      case Step.Congruence =>
        (premises, Expr.sidesOf(claim.conclusion)) match {
          case (Vector(function, argument), Some((left, right))) =>
            (Expr.sidesOf(function.conclusion), Expr.sidesOf(argument.conclusion)) match {
              case (Some((f, g)), Some((x, y))) =>
                require("congruence", "each side is one function applied to one argument")(
                  left == Expr.Apply(f, x) && right == Expr.Apply(g, y) &&
                    Expr.typeOf(left).isDefined && Expr.typeOf(right).isDefined &&
                    claim.assumptions == function.assumptions ++ argument.assumptions
                )
              case _ => refuse("congruence", "two equations")
            }
          case _ => refuse("congruence", "two premises and an equation")
        }

      case Step.Abstraction(bound) =>
        (premises, Expr.sidesOf(claim.conclusion)) match {
          case (Vector(from), Some((left, right))) =>
            Expr.sidesOf(from.conclusion) match {
              case Some((s, t)) =>
                val binder = bound.ty
                require("abstraction", "the variable is bound on both sides and free in no hypothesis")(
                  left == Expr.Lambda(binder, Expr.close(bound, s)) &&
                    right == Expr.Lambda(binder, Expr.close(bound, t)) &&
                    !from.hypotheses.exists(Expr.freeVariables(_).contains(bound)) &&
                    claim.assumptions == from.assumptions
                )
              case None => refuse("abstraction", "an equation")
            }
          case _ => refuse("abstraction", "one premise and an equation")
        }

      case Step.BetaStep(redex) =>
        (Expr.betaReduce(redex), Expr.sidesOf(claim.conclusion)) match {
          case (Some(reduced), Some((left, right))) =>
            require("beta", "the redex equals what it reduces to, closed and under nothing")(
              left == redex && right == reduced && Expr.isClosed(redex) && claim.hypotheses.isEmpty
            )
          case _ => refuse("beta", "a redex and an equation")
        }

      case Step.Assumption(assumed) =>
        require("assumption", "a proposition standing as its own hypothesis")(
          claim.conclusion == assumed && claim.assumptions == Set(assumed) &&
            Expr.isProposition(assumed) && Expr.isClosed(assumed)
        )

      case Step.EqualityElimination =>
        premises match {
          case Vector(equivalence, antecedent) =>
            Expr.sidesOf(equivalence.conclusion) match {
              case Some((p, q)) =>
                require("equality elimination", "the antecedent is the left side, the conclusion the right")(
                  p == antecedent.conclusion && claim.conclusion == q &&
                    claim.assumptions == equivalence.assumptions ++ antecedent.assumptions
                )
              case None => refuse("equality elimination", "an equation")
            }
          case _ => refuse("equality elimination", "two premises")
        }

      case Step.Antisymmetry =>
        (premises, Expr.sidesOf(claim.conclusion)) match {
          case (Vector(left, right), Some((p, q))) =>
            val discharged =
              (left.assumptions - right.conclusion) ++ (right.assumptions - left.conclusion)
            require("antisymmetry", "each conclusion discharged from the other's hypotheses")(
              p == left.conclusion && q == right.conclusion && claim.assumptions == discharged
            )
          case _ => refuse("antisymmetry", "two premises and an equation")
        }

      case Step.Instantiation(mapping) =>
        premises match {
          case Vector(from) =>
            val typed = mapping.forall { case (variable, replacement) =>
              Expr.typeOf(replacement).contains(variable.ty) && Expr.isClosed(replacement)
            }
            require("instantiation", "every occurrence replaced, hypotheses included")(
              typed &&
                claim.conclusion == Expr.substitute(mapping, from.conclusion) &&
                claim.assumptions == from.assumptions.map(Expr.substitute(mapping, _))
            )
          case _ => refuse("instantiation", "one premise")
        }

      case Step.TypeInstantiation(mapping) =>
        premises match {
          case Vector(from) =>
            require("type instantiation", "every occurrence replaced, hypotheses included")(
              claim.conclusion == Expr.substituteTypes(mapping, from.conclusion) &&
                claim.assumptions == from.assumptions.map(Expr.substituteTypes(mapping, _))
            )
          case _ => refuse("type instantiation", "one premise")
        }

      // Four things were checked here until 2026-09-10 and none of them tied the node to a
      // definition: the right side equalled the declared body, the body was closed, there were no
      // hypotheses, and the left side was SOME constant. So `|- T = F`, presented as a definition
      // of anything at all, came back accepted on no axioms, which `CheckSpec` demonstrated by
      // construction before this was written. A checker that says yes to `|- T = F` is worth
      // nothing, whether or not anybody can go on to reach `|- F`.
      //
      // What ties it now is what `docs/adr/0008` made a constant's identity: the name the step
      // declares, and the **origin**, which for a defined constant is the body it was defined as.
      // A forged pairing fails on the origin, because the constant in the claim carries whatever
      // really defined it and the checker reads that across rather than trusting the pairing.
      //
      // The last condition is the one that makes `defineConstant` conservative rather than merely
      // well-formed: a type variable in the body that does not occur in the constant's type would
      // let two instantiations of one name be two different values.
      case Step.Definition(name, definition) =>
        Expr.sidesOf(claim.conclusion) match {
          case Some((constant: Expr.Constant, right)) =>
            val escaping = Expr.typeVariables(definition).diff(Ty.variables(constant.ty))

            require(
              "definition",
              "the named constant, carrying this body as its origin, closed and with no type variable escaping"
            )(
              constant.name == name && constant.origin.contains(definition) &&
                right == definition && Expr.freeVariables(definition).isEmpty &&
                escaping.isEmpty && claim.hypotheses.isEmpty
            )

          case Some(_) => refuse("definition", "a constant on the left")
          case None => refuse("definition", "an equation")
        }

      case Step.Citation(_) =>
        premises match {
          case Vector(fact) =>
            require("citation", "the sequent of the fact it cites")(
              claim.conclusion == fact.conclusion && claim.assumptions == fact.assumptions
            )
          case _ => refuse("citation", "one premise")
        }

      case Step.Axiom(asserted) =>
        if (
          claim.conclusion == asserted && claim.hypotheses.isEmpty &&
          Expr.isProposition(asserted) && Expr.freeVariables(asserted).isEmpty
        ) Right(Set(asserted))
        else refuse("axiom", "a closed proposition standing alone")

      // What a type definition MEANS is the rule's, and a checker that re-derived it would be
      // re-implementing a theory extension rather than an inference. What the claim must LOOK like
      // is checkable, and until 2026-09-10 it was checked far too loosely: the first half asked
      // only that the left side be a nested application, so `|- (f (g h)) = anything` passed. The
      // shapes are pinned to the names the step declares now, which is the same repair as the
      // definition arm above and for the same reason.
      case Step.TypeDefinition(_, absName, repName, half) =>
        premises match {
          case Vector(witness) =>
            require(
              "type definition",
              "a witness holding outright, and the declared abstraction and representation in the half returned"
            )(
              witness.hypotheses.isEmpty && claim.hypotheses.isEmpty &&
                shapeOf(claim, absName, repName, half)
            )
          case _ => refuse("type definition", "one witness")
        }
    }
  }

  /**
   * Whether the claim is the half of the bijection it says it is, over the two named constants.
   *
   * `abs (rep a) = a` and `P r = (rep (abs r) = r)`. Both are pinned to `absName` and `repName`
   * rather than to "some application", so a claim that merely has the right bracketing does not
   * pass. The predicate `P` is deliberately not constrained: the rule reads it off the witness, and
   * `SoundnessAttackSpec` pins that it is structural rather than checked.
   */
  private def shapeOf(claim: Claim, absName: String, repName: String, half: Step.Half): Boolean = {
    def named(expression: Expr, expected: String): Option[Expr] = expression match {
      case Expr.Apply(Expr.Constant(name, _, _), argument) if name == expected => Some(argument)
      case _ => None
    }

    (Expr.sidesOf(claim.conclusion), half) match {
      case (Some((left, right)), Step.Half.AbstractionOfRepresentation) =>
        named(left, absName).flatMap(named(_, repName)).contains(right)

      case (Some((left, right)), Step.Half.Characterisation) =>
        val applied = left match {
          case Expr.Apply(_, argument) => Some(argument)
          case _ => None
        }

        (applied, Expr.sidesOf(right)) match {
          case (Some(subject), Some((inner, back))) =>
            named(inner, repName).flatMap(named(_, absName)).contains(subject) && back == subject
          case _ => false
        }

      case _ => false
    }
  }
}
