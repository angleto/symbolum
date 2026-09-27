package garden.xeno.symbolum.kernel

import scala.annotation.tailrec

/**
 * How a theorem was obtained: one node per inference, holding the theorems it was built from.
 *
 * A theorem has recorded nothing since this kernel was written, and `docs/evaluation.md` names what
 * that costs in the row it cannot fill: "a kernel benchmark here must be adversarial rather than
 * differential", because there is nothing for a second checker to replay. Everything anyone is
 * asked to believe has to be believed by reading it. A derivation is what turns that into an
 * artifact: a theorem carries its own proof, and something that is not this kernel can check it.
 *
 * == It is not part of the trusted base, and that is the point ==
 *
 * Recording is not checking. If the kernel wrote down a derivation that does not replay, a checker
 * reports it and refuses; a wrong record is a false alarm and never a false theorem. So these lines
 * are in the kernel because that is where the inferences happen, and nothing here has to be right
 * for a theorem to be sound. What has to be right for the **checker** to be worth anything is the
 * checker, which is somewhere else and by someone else.
 *
 * == The shape, and why it holds theorems rather than derivations ==
 *
 * Each node holds the `Thm` values it was built from, and each of those holds its own derivation,
 * so a proof is a directed acyclic graph shared by reference rather than a tree copied out. A step
 * used twice is one object. What it costs is one node per inference and the retention of every
 * intermediate theorem for as long as the final one is held, which is the real change in
 * behaviour: before this, an intermediate was garbage the moment a rule consumed it.
 */
sealed trait Derivation

object Derivation {

  /** `|- t = t` */
  final case class Reflexivity(term: Term) extends Derivation

  /** `G |- a = b` and `D |- b = c` give `G, D |- a = c` */
  final case class Transitivity(left: Kernel.Thm, right: Kernel.Thm) extends Derivation

  /** `G |- f = g` and `D |- x = y` give `G, D |- f x = g y` */
  final case class Congruence(function: Kernel.Thm, argument: Kernel.Thm) extends Derivation

  /** `G |- s = t` gives `G |- (\x. s) = (\x. t)` */
  final case class Abstraction(variable: FVar, from: Kernel.Thm) extends Derivation

  /** `|- (\x. t) u = t[u/x]` */
  final case class BetaStep(term: Term) extends Derivation

  /** `p |- p` */
  final case class Assumption(proposition: Term) extends Derivation

  /** `G |- p = q` and `D |- p` give `G, D |- q` */
  final case class EqualityElimination(equivalence: Kernel.Thm, antecedent: Kernel.Thm)
      extends Derivation

  /** `G |- p` and `D |- q` give `(G - q), (D - p) |- p = q` */
  final case class Antisymmetry(left: Kernel.Thm, right: Kernel.Thm) extends Derivation

  /** Free variables replaced throughout. */
  final case class Instantiation(substitution: Map[FVar, Term], from: Kernel.Thm) extends Derivation

  /** Type variables replaced throughout. */
  final case class TypeInstantiation(substitution: Map[String, Type], from: Kernel.Thm)
      extends Derivation

  /**
   * A definition, an axiom, or one of the two theorems a type definition returns.
   *
   * These have no premises: what they rest on is the extension itself, which is why each records
   * what was extended with rather than which theorem it came from. An axiom is the one node a
   * checker cannot verify and can only report, and that is the whole of what a trusted base is.
   */
  final case class Definition(name: String, body: Term) extends Derivation

  /** Asserted, and the only node in any proof that is believed rather than checked. */
  final case class Axiom(proposition: Term) extends Derivation

  /** Which of the two theorems a type definition returns. */
  enum Half {
    case AbstractionOfRepresentation, Characterisation
  }

  /** A type definition, with the witness it was given and which half this theorem is. */
  final case class TypeDefinition(
    typeName: String,
    absName: String,
    repName: String,
    witness: Kernel.Thm,
    half: Half
  ) extends Derivation

  /**
   * A fact a development published under `name`, used by a proof that did not derive it.
   *
   * The same sequent as `fact`, so a checker replays through it as through an identity. What it is
   * for is the walks below, which stop here: a report on a proof reads that proof's own inferences
   * and one node per fact it cites, where it used to read every inference of every fact beneath,
   * and those grow with every development stacked under the one asking. `docs/adr/0047` has the
   * measurement.
   *
   * The axioms the fact rests on are worked out once, on first asking, and kept here, which is
   * what lets [[axiomsOf]] stop at the boundary and still answer for the whole proof. Lazily,
   * because most citations are never asked about and the walk under one is the cost being avoided.
   */
  final case class Citation(name: String, fact: Kernel.Thm) extends Derivation {
    lazy val axioms: Set[Term] = axiomsOf(fact)

    /** What the fact spends under each interface it has been read against, known after the first asking. */
    private[kernel] val readings: scala.collection.concurrent.TrieMap[Set[Term], Set[Term]] =
      scala.collection.concurrent.TrieMap.empty
  }

  /**
   * The theorems a node was built from, in order, which is what a walk over a proof needs.
   *
   * A citation's premise is the fact it cites, so a checker and the written proof both reach the
   * whole derivation; it is [[own]] that declines to follow it.
   */
  def premises(derivation: Derivation): List[Kernel.Thm] = derivation match {
    case Citation(_, fact) => List(fact)
    case Transitivity(left, right) => List(left, right)
    case Congruence(function, argument) => List(function, argument)
    case Abstraction(_, from) => List(from)
    case EqualityElimination(equivalence, antecedent) => List(equivalence, antecedent)
    case Antisymmetry(left, right) => List(left, right)
    case Instantiation(_, from) => List(from)
    case TypeInstantiation(_, from) => List(from)
    case TypeDefinition(_, _, _, witness, _) => List(witness)
    case _ => Nil
  }

  /**
   * Every axiom a theorem rests on, without duplicates.
   *
   * The question a reader of a proof actually asks, and one nothing could answer before: not how
   * long the derivation is but what it is believed on. A theorem whose walk turns up no axiom rests
   * on the inference rules alone.
   *
   * == It is not `Theory.axioms`, and the two get swapped ==
   *
   * `Theory.axioms` is what you must **accept** to build in a theory. This is what one proof
   * **spent**. They are different numbers about different populations and they are close enough to
   * read as the same one: on 2026-09-14 two sessions swapped them within an hour, in opposite
   * directions, while agreeing with each other.
   *
   * The measurement that separates them, taken that day: the naturals as a theory ask for three,
   * `SELECT`, `INFINITY` and `ETA`. Of the library's 322 entries, **five** reach `ETA` at all:
   * `FUNCTION_EXTENSIONALITY`, `SUM_CONGRUENCE`, `PROD_CONGRUENCE`, `WORD_EXTENSIONALITY` and
   * `WORD_ROTATE_ZERO`. So a development can sit above an axiom for months without a single one of
   * its theorems spending it, and saying "this costs the three of the naturals" of such a theorem
   * is false while saying it of the theory is true.
   *
   * Which one a document wants depends on what it is for. A front page telling a reader what they
   * are asked to believe wants `Theory.axioms`, because they accept all three whether anything
   * spends them or not. A spec pinning what a derivation cost wants this one.
   *
   * It answers for the whole proof, citations included, and walks only the proof's own part: what
   * a cited fact rests on is the [[Citation]]'s to know, and it knows it after the first asking.
   */
  def axiomsOf(theorem: Kernel.Thm): Set[Term] =
    own(theorem).foldLeft(Set.empty[Term]) { (found, node) =>
      node.derivation match {
        case Axiom(proposition) => found + proposition
        case citation: Citation => found ++ citation.axioms
        case _ => found
      }
    }

  /**
   * [[axiomsOf]] with some published facts read as premises in their own right: a node citing one
   * of `interface` counts as that fact, and the walk goes no further into it.
   *
   * What it is for is a construction under an interface. The sixteen statements of a complete
   * ordered field were axioms until `docs/adr/0053` proved them about the cuts on the rationals,
   * and since then every theorem about the reals rests on choice, eta and infinity and on nothing
   * that says which laws of the field it used. That was the informative half of the answer: a fact
   * about limits that reaches completeness and one that does not are different facts. Read with
   * the sixteen as the interface, it is the same answer it was while they were asserted.
   *
   * Every other citation is entered, since a cited fact about limits rests on the sixteen too and
   * its own summary has already walked past them; each is entered once per interface and the answer
   * kept on the citation, as [[Citation.axioms]] is. A theorem that
   * is itself a citation of one of `interface` answers with its own conclusion.
   */
  def axiomsOf(theorem: Kernel.Thm, interface: Set[Term]): Set[Term] = {
    def spent(current: Kernel.Thm): Set[Term] =
      own(current).foldLeft(Set.empty[Term]) { (found, node) =>
        node.derivation match {
          case Axiom(proposition) => found + proposition
          case Citation(_, _) if interface.contains(node.conclusion) => found + node.conclusion
          case citation @ Citation(_, fact) => found ++ citation.readings.getOrElseUpdate(interface, spent(fact))
          case _ => found
        }
      }
    theorem.derivation match {
      case Citation(_, _) if interface.contains(theorem.conclusion) => Set(theorem.conclusion)
      case _ => spent(theorem)
    }
  }

  /**
   * Which of a named collection of facts this proof actually rests on.
   *
   * The other half of [[axiomsOf]], and the half a discovery loop needs. "What is this believed on"
   * has an answer already; "**which of the things I know did it use**" did not, and it is the
   * stronger of the two signals about whether a result is new: a proof that reaches a lemma no
   * earlier proof reached went somewhere earlier proofs did not.
   *
   * By the sequent and not by identity, deliberately, and it is the opposite choice from [[walk]]'s
   * own. `walk` must not deduplicate on equality or it would report a proof of one step where there
   * are three. Here the question is which *fact* took part, and a fact re-derived by another route
   * is the same fact: a caller asking whether their proof used the triangle inequality does not mean
   * "the object in the library" and would be misled by an answer that said no because the lemma had
   * been proved again on the way.
   *
   * Only a node with no hypotheses counts. An assumed proposition that happens to read like a lemma
   * is an assumption, and counting it would say a proof rested on something it had asked for.
   *
   * **The one walk here that goes through a [[Citation]]**, and it pays the whole graph for it. A
   * fact used inside a cited fact is used by the proof, and the facts a caller asks about are any
   * named collection rather than the published ones, so no summary kept on the citation could
   * answer for them. Its callers are documents and a discovery loop, not the report on every proof.
   */
  def restingOn(theorem: Kernel.Thm, wanted: Set[Term]): Set[Term] =
    walk(theorem).foldLeft(Set.empty[Term]) { (found, node) =>
      if (node.hypotheses.isEmpty && wanted.contains(node.conclusion)) found + node.conclusion
      else found
    }

  /**
   * [[restingOn]] with the walk stopped at the cited facts of `interface`: such a fact is reached
   * and counted when it is wanted, and what it was proved from is not entered.
   *
   * The other half of [[axiomsOf]] with an interface, for the same construction: once the sixteen
   * statements of the reals were proved from the cuts, a walk through every citation found the
   * rationals, the integers and the classical axioms under every fact about the reals, and a report
   * over it said that `0 < 12` rests on choice. That is true of the construction and says nothing
   * about the claim.
   */
  def restingOn(theorem: Kernel.Thm, wanted: Set[Term], interface: Set[Term]): Set[Term] =
    reach(
      theorem,
      derivation => derivation match {
        case Citation(_, fact) if interface.contains(fact.conclusion) => Nil
        case other => premises(other)
      }
    ).foldLeft(Set.empty[Term]) { (found, node) =>
      if (node.hypotheses.isEmpty && wanted.contains(node.conclusion)) found + node.conclusion
      else found
    }

  /**
   * What a theorem carries that a theory does not hold, which is how a foreign theorem is spotted.
   *
   * `docs/adr/0008` made two theories that **define** one name differently produce terms that do
   * not combine, and `Term`'s own comment says why the other case is deliberately left open: a
   * declared constant has no origin, because "an uninterpreted name says nothing, so two theories
   * declaring one are talking about the same thing". That is right, and it is right only while the
   * name stays uninterpreted. What gives a declared constant content is an **axiom**, and an axiom
   * is held by the theory rather than by the constant, so no field on the term could carry it.
   *
   * That is the whole argument for putting the check here. The question "is this theorem one of
   * mine" is about a derivation and a theory together, and neither of them alone can answer it.
   * Fifteen constants of the standard chain are declared rather than defined, measured on
   * 2026-09-13 and listed in `DerivationSpec`: the six field primitives of the reals, the two
   * numerals, the order, equality, choice, and the three pairs a type definition introduces.
   *
   * == Two answers, kept apart ==
   *
   * [[Foreign.axioms]] is the one that matters for soundness. A theorem of a sibling theory that
   * axiomatises `utility` one way, carried into a theory that axiomatises it another, rests on an
   * axiom this theory does not hold, and that is visible here whatever the terms look like.
   *
   * [[Foreign.constants]] is diagnostic. A name this theory does not have, or has with another
   * definition, already fails to combine, because `docs/adr/0008` made those different terms and
   * the rules compare terms. What this adds is that the failure is **named** at the boundary rather
   * than met several inferences later as a complaint about something else.
   *
   * Merging the two would lose exactly the distinction this repository keeps everywhere: one says
   * the theorem is believed on something this theory does not believe, the other says it is written
   * in a vocabulary this theory does not share, and a caller's next move differs.
   *
   * == What it does not do ==
   *
   * It is a check at a boundary and not an invariant. Nothing forces a caller to ask, and
   * `Term.variable` is public and unchecked, so a theorem can still be assembled without anyone
   * consulting this. Closing that would mean carrying the theory on every theorem, which
   * `docs/adr/0008` priced and declined; this is what makes the risk **detectable** in the
   * meantime, which it was not before.
   *
   * It also says nothing about a theorem whose conclusion happens to be true in both theories. A
   * proof of `|- utility x = utility x` rests on no axiom and names a constant both hold, so it is
   * certified by both, and it is true in both.
   */
  def foreignTo(theory: Theory, theorem: Kernel.Thm): Foreign =
    Foreign(
      axioms = axiomsOf(theorem) -- theory.axioms.toSet,
      constants = (theorem.conclusion :: theorem.hypotheses)
        .flatMap(constantsIn)
        .toSet
        .filterNot(known(theory, _))
    )

  /**
   * A constant this theory would build: the same name, at a type its schema admits, same origin.
   *
   * **The type used not to be compared, and the reason given for that does not hold here.** It was
   * that comparing it properly is `Theory.constant`'s job and that reimplementing it would be a
   * second thing to keep in step, with a name held at a schema the instance does not fit reported
   * as known and refused later by the first rule that tries to use it. The first half is right and
   * the answer to it is to **call** that method rather than to reimplement it, which is what
   * happens below. The second half is what was wrong: this is a report at a boundary, and a
   * boundary is exactly where no later rule runs. A caller reading `clean` acts on it, and
   * `Session` and `DomainTheorySpec` both do.
   *
   * Measured on 2026-09-16 before the change, with two theories declaring one name at two types
   * neither of which is an instance of the other: the narrower theory refuses to build the
   * constant and `Theory.checkTerm` refuses the term, while this reported the theorem clean with
   * zero foreign constants. A control, a name that theory never declared, was reported foreign, so
   * the instrument was discriminating and still gave that answer.
   *
   * Equality is excluded by name because the kernel knows it by name: `Theory.declareConstant`
   * refuses it and every theory carries it from [[Theory.primitive]].
   */
  private def known(theory: Theory, constant: Term): Boolean = constant match {
    case found: Const =>
      found.name == Term.EqualityName ||
      theory.constant(found.name, found.ty).exists(_ == found)
    case _ => false
  }

  private def constantsIn(term: Term): Set[Term] = term match {
    case constant: Const => Set(constant)
    case App(fn, argument) => constantsIn(fn) ++ constantsIn(argument)
    case Abs(_, body) => constantsIn(body)
    case _ => Set.empty
  }

  /**
   * How many inferences a proof holds, counting a step used twice once and a cited fact as one.
   *
   * **A cited fact is one inference here and not the length of its own proof**, since 2026-09-25
   * and `docs/adr/0047`. The count is still a function of the proof and two machines still agree
   * on it; what it counts is the proof's own work, which is what a report on it is about, where it
   * used to count the work of every development underneath as well. A fact asked about directly is
   * not cited by anything, so its own proof is what is counted.
   */
  def size(theorem: Kernel.Thm): Int = own(theorem).size

  /**
   * How many inferences of each rule a proof holds, which is [[size]] taken apart.
   *
   * A proof's **shape** rather than its length, and the two answer different questions about the
   * same object. A cost measured in milliseconds is a measurement of the afternoon it was taken
   * in — the documents here record the same scale differing by a factor of two in one afternoon —
   * and this one is a function of the proof, so two runs on two machines agree and a change that
   * claims to have removed work has to show the count moving.
   *
   * What it was written for is the one claim about cost that can be checked this way: most of a
   * proof's nodes are reflexivity, built by a rewriting pass to say that nothing happened. Whether
   * that is worth repairing is a question about the rewriter; whether it is **true** is this.
   *
   * Keyed by the rule's simple name, because that is what a reader of the report wants and because
   * a key that is the class itself would make the report depend on a package name. A cited fact
   * is a `Citation` here, for the reason [[size]] gives.
   */
  def census(theorem: Kernel.Thm): Map[String, Int] =
    own(theorem)
      .groupBy(_.derivation.getClass.getSimpleName.stripSuffix("$"))
      .map { case (rule, nodes) => (rule, nodes.size) }

  /**
   * What [[foreignTo]] found, with the two answers separate.
   *
   * `clean` rather than `isEmpty`, because a caller reading `foreign.isEmpty` is one negation away
   * from reading it backwards, and the two fields are what a caller reports when it is not.
   */
  final case class Foreign(axioms: Set[Term], constants: Set[Term]) {
    def clean: Boolean = axioms.isEmpty && constants.isEmpty
  }

  /** Every node of a proof, each reached once, through every citation. */
  private def walk(theorem: Kernel.Thm): Vector[Kernel.Thm] = reach(theorem, premises)

  /**
   * Every node of a proof's own part: each reached once, and a cited fact reached as its citation.
   *
   * The root is the exception. A theorem that is itself a citation is a published fact asked about
   * by name, and what is being asked about is its proof, so the walk starts at what it cites; the
   * alternative answers "one" for every fact in the library.
   */
  private def own(theorem: Kernel.Thm): Vector[Kernel.Thm] = {
    @tailrec
    def uncited(current: Kernel.Thm): Kernel.Thm = current.derivation match {
      case Citation(_, fact) => uncited(fact)
      case _ => current
    }
    reach(
      uncited(theorem),
      derivation => derivation match {
        case Citation(_, _) => Nil
        case _ => premises(derivation)
      }
    )
  }

  /**
   * Every node reachable through `below`, each reached once.
   *
   * **By identity and not by equality**, which is the whole of why this is written out rather than
   * folded into a `Set`. Two theorems are equal when they are the same sequent, whatever derived
   * them, which is what the rules need; a walk over a proof that deduplicated on that would treat
   * `trans(refl p, refl p)` and `refl p` as one node, stop there, and report a proof of one step.
   * It did, and the test that says so is the reason this comment exists.
   *
   * Iterative, because a proof is as deep as the derivation that built it: the numeral procedures
   * chain hundreds of steps and a recursive walk would meet the stack before it met a long one.
   * `@tailrec` is what keeps that property visible: the compiler rejects the definition if the
   * recursion is ever moved out of tail position, where the previous `while` could only be read.
   */
  private def reach(
    theorem: Kernel.Thm,
    below: Derivation => List[Kernel.Thm]
  ): Vector[Kernel.Thm] = {
    val seen = java.util.Collections.newSetFromMap(
      new java.util.IdentityHashMap[Kernel.Thm, java.lang.Boolean]
    )

    @tailrec
    def step(pending: List[Kernel.Thm], order: Vector[Kernel.Thm]): Vector[Kernel.Thm] =
      pending match {
        case Nil => order
        case current :: rest =>
          if (seen.add(current)) step(below(current.derivation) ++ rest, order :+ current)
          else step(rest, order)
      }

    step(List(theorem), Vector.empty)
  }
}
