package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A theory of a domain that is not mathematics, as a value that can be built and composed.
 *
 * The declared purpose of this repository is not only mathematics: it is to state axioms and rules
 * from domains that are neither logical nor mathematical, and to settle claims about them. The
 * mechanism for one theory has always been there — `Theory` is a value, and `declareTypeOperator`,
 * `declareConstant` and `Kernel.assertAxiom` are all it takes — and `DomainTheorySpec` has been the
 * demonstration of it since 2026-09-15. What did not exist is anything that **packages** that, and
 * in particular anything that puts two domains together.
 *
 * == Why this is a description and not a finished `Theory` ==
 *
 * The obvious composition takes two `Theory` values and merges them. It cannot be written, and the
 * reason is worth stating because it is the first thing a reader will try.
 *
 * A `Theory` carries its type operators, constants, definitions and axioms as **maps and a list**,
 * with no record of the order they arrived in. Replaying one onto another therefore has to guess an
 * order, and a definitional extension does not admit one: a definition whose body mentions another
 * constant only typechecks after that constant exists. Worse, replaying a **defined** constant
 * through `declareConstant` would strip its origin, and `docs/adr/0008` makes a constant with a
 * different origin a different constant — so the merge would produce a theory in which the
 * theorems of neither half typecheck, and it would do it silently.
 *
 * So a domain is described rather than reverse-engineered. [[Domain]] is the list of what to
 * declare and what to assert, composition is a check and a concatenation of two such lists, and
 * [[build]] runs it once against a base. `Real.Declarations` and `Natural.Statements` already have
 * this shape; this makes it a value a caller can hold.
 *
 * == Why composition refuses on a shared name ==
 *
 * `docs/adr/0019` measured the identity of a declared constant and left `docs/adr/0008`'s rule
 * standing: a declared constant has **no origin**, so two domains that each declare `Cost` produce
 * constants that are equal, whatever either of them meant by it. Composing them silently would
 * merge two vocabularies into one and say nothing.
 *
 * [[compose]] therefore refuses, naming the constant. That is the whole of what this file does
 * about `0019`'s residual risk: it does not remove it, it makes the one place a caller could walk
 * into it say so. A caller who really does mean one constant says so with [[composeSharing]], and
 * then the sharing is a line in their source rather than an accident of two files agreeing on a
 * word.
 *
 * **Contradictory axioms are not what this guards against, and conflating the two is easy.** Two
 * domains whose axioms contradict each other compose into one inconsistent theory, and that is
 * honest: an inconsistent set of axioms is the author's to answer for and the kernel never claimed
 * otherwise. What `SoundnessAttackSpec` derives is a different thing — theorems from **two
 * separate** theories combining because their constants compare equal — and composing is the
 * repair for it rather than the cause. A caller who wants to reason across two domains composes
 * them first, and then the kernel's ordinary checks apply to one theory.
 *
 * == What this does not give ==
 *
 * **No automation.** `Ring` and `Linarith` decide fragments of the reals and have nothing to say
 * about an arbitrary axiom. What reaches a domain is the propositional skeleton, which
 * `DomainTheorySpec` measures in both directions: the same claim settled by hand costs no
 * foundational axiom, and settled by `Propositional` costs one, because that procedure decides
 * classical validity and closes with double negation. The promise here is accounting, not search,
 * and [[Built.spends]] is the accounting.
 */
final case class Domain(
  name: String,
  typeOperators: Vector[(String, Int)],
  constants: Vector[(String, Type)],
  axioms: Vector[(String, String)]
) {

  /** The names this domain introduces, which is what a composition may collide on. */
  def introduced: Set[String] = constants.map(_._1).toSet

  /** The type operators this domain introduces. */
  def introducedTypes: Set[String] = typeOperators.map(_._1).toSet
}

object Domain {

  /**
   * Two domains as one, refused when both introduce a name.
   *
   * The refusal is the point and not a safety rail: by `docs/adr/0008` two declared constants of
   * one name and one type **are** one constant, so a silent merge would have the composed theory
   * mean something neither domain said. Naming the collision turns that into a decision.
   *
   * A shared **type operator** is refused on the same ground and for a sharper reason: two domains
   * that each carve out `agent` at arity zero would have every claim of one apply to the other's
   * subjects, and nothing downstream could tell.
   */
  def compose(left: Domain, right: Domain): Either[Clash, Domain] =
    composeSharing(left, right, Set.empty)

  /**
   * The same, with the names the caller says the two domains genuinely share.
   *
   * A shared name still has to agree on its type, and that is checked rather than assumed: two
   * domains that both declare `Cost` and disagree about whether it takes a change or an agent are
   * not sharing a constant, they are colliding, and the caller saying otherwise does not make it
   * so.
   */
  def composeSharing(
    left: Domain,
    right: Domain,
    shared: Set[String]
  ): Either[Clash, Domain] = {
    val leftTypes = left.typeOperators.toMap
    val leftConstants = left.constants.toMap

    val collidingTypes = (left.introducedTypes & right.introducedTypes) -- shared
    val collidingConstants = (left.introduced & right.introduced) -- shared

    val disagreeing = right.constants.collect {
      case (name, schema) if shared.contains(name) && leftConstants.get(name).exists(_ != schema) =>
        name
    }
    val disagreeingTypes = right.typeOperators.collect {
      case (name, arity) if shared.contains(name) && leftTypes.get(name).exists(_ != arity) => name
    }

    if (collidingTypes.nonEmpty)
      Left(Clash(left.name, right.name, collidingTypes.toVector.sorted, Clash.Kind.TypeOperator))
    else if (collidingConstants.nonEmpty)
      Left(Clash(left.name, right.name, collidingConstants.toVector.sorted, Clash.Kind.Constant))
    else if (disagreeingTypes.nonEmpty)
      Left(Clash(left.name, right.name, disagreeingTypes.toVector.sorted, Clash.Kind.Arity))
    else if (disagreeing.nonEmpty)
      Left(Clash(left.name, right.name, disagreeing.toVector.sorted, Clash.Kind.Schema))
    else
      Right(
        Domain(
          s"${left.name} with ${right.name}",
          left.typeOperators ++ right.typeOperators.filterNot(entry => shared.contains(entry._1)),
          left.constants ++ right.constants.filterNot(entry => shared.contains(entry._1)),
          // An axiom of a shared vocabulary is kept from both sides: what is shared is the
          // constant, and each domain is still entitled to what it asserts about it.
          left.axioms ++ right.axioms
        )
      )
  }

  /**
   * Why composing has an error of its own rather than a `LogicError`.
   *
   * [[composeSharing]] never builds a term, never parses and never reaches the kernel: it compares
   * two lists of names. `LogicError` is sealed, lives in `modules/logic`, and every case of it
   * carries a `standing` saying whether the goal was decided, refused or never read. A clash
   * between two descriptions has no goal and no standing, so putting it there would mean inventing
   * an answer to a question nobody asked, in a module three developments sit above.
   *
   * [[build]] keeps `LogicError`, because it really does parse and really does call the kernel.
   */
  final case class Clash(
    left: String,
    right: String,
    names: Vector[String],
    kind: Clash.Kind
  ) {

    def message: String = kind match {
      case Clash.Kind.TypeOperator =>
        s"$left and $right both introduce the ${plural("type operator")} ${listed}; two theories " +
          s"that carve out one name carve out one type, so say so with `composeSharing` or rename"
      case Clash.Kind.Constant =>
        s"$left and $right both declare the ${plural("constant")} ${listed}; a declared constant " +
          s"has no origin, so these are ONE constant whatever each domain meant by it " +
          s"(docs/adr/0008, measured again in docs/adr/0019). Say so with `composeSharing`, or rename"
      case Clash.Kind.Arity =>
        s"$left and $right were said to share ${listed}, and disagree about arity"
      case Clash.Kind.Schema =>
        s"$left and $right were said to share ${listed}, and disagree about type"
    }

    private def listed: String = names.mkString(", ")
    private def plural(word: String): String = if (names.sizeIs == 1) word else word + "s"
  }

  object Clash {

    /** What the two domains disagreed about, which decides what the caller can do next. */
    enum Kind {

      /** Both carve out a type of one name: one type, and every claim of each reaches the other. */
      case TypeOperator

      /** Both declare a constant of one name: by `docs/adr/0008` that is one constant. */
      case Constant

      /** Declared shared, and the arities differ, so the sharing was not true. */
      case Arity

      /** Declared shared, and the types differ, so the sharing was not true. */
      case Schema
    }
  }

  /**
   * A domain built over a base, with its axioms asserted and held by name.
   *
   * The base is a theory the caller already has — `Classical.standard.theory` for a domain that
   * needs nothing of arithmetic, or the chain's widest for one that does. Nothing here extends the
   * chain: a domain theory sits **beside** it and must stay there, which is `docs/adr/0008`'s case
   * and the sentence `SoundnessAttackSpec` is the evidence for.
   */
  def build(
    base: Theory,
    notation: Notation,
    domain: Domain
  ): Either[LogicError, Built] = {
    val withTypes = domain.typeOperators.foldLeft[Either[LogicError, Theory]](Right(base)) {
      case (acc, (name, arity)) =>
        acc.flatMap(current => LogicError.lift(current.declareTypeOperator(name, arity)))
    }
    val withConstants = domain.constants.foldLeft(withTypes) { case (acc, (name, schema)) =>
      acc.flatMap(current => LogicError.lift(current.declareConstant(name, schema)))
    }

    domain.axioms
      .foldLeft(withConstants.map((_, Vector.empty[(String, Kernel.Thm)]))) {
        case (acc, (name, text)) =>
          for {
            reached <- acc
            (current, held) = reached
            proposition <- Parser.proposition(current, notation, text)
            asserted <- LogicError.lift(Kernel.assertAxiom(current, proposition))
          } yield (asserted._1, held :+ (name -> asserted._2))
      }
      .map { case (theory, held) => new Built(domain, base, theory, held.toMap) }
  }

  /**
   * A built domain, and the accounting a claim about it is worth making.
   *
   * The point of the whole exercise is not that a domain claim is a theorem. It is
   * [[spends]]: **which** of the assumptions the conclusion actually rests on, and which of them
   * are the domain's rather than the foundation's underneath it. `DomainTheorySpec` is the case
   * that shows why a reader cannot guess: four axioms asserted, one spent, and the three that state
   * when a change *is* admitted unused, because what the conclusion needed was the converse.
   */
  final class Built(
    val domain: Domain,
    val base: Theory,
    val theory: Theory,
    val axioms: Map[String, Kernel.Thm]
  ) {

    /** The axiom named, as asserted when the domain was built. */
    def axiom(name: String): Either[LogicError, Kernel.Thm] =
      axioms.get(name).toRight(MissingDefinition(name))

    /** This domain's own axioms, as propositions, which is what separates them from the base's. */
    def ours: Set[Term] = axioms.values.map(_.conclusion).toSet

    /**
     * What a theorem rests on, split into this domain's assumptions and the foundation's.
     *
     * The split is the reason the report is worth reading. A conclusion that spends one domain
     * axiom and no foundational one rests on something a reader of the domain can check; one that
     * spends choice has reached outside the domain to get there, and a reader should be told which
     * happened rather than shown a theorem.
     */
    def spends(theorem: Kernel.Thm): Spending = {
      val all = Derivation.axiomsOf(theorem)
      val mine = ours
      Spending(
        domain = domain.name,
        ofTheDomain = axioms.collect { case (name, asserted) if all.contains(asserted.conclusion) => name }.toSet,
        foundational = all -- mine,
        unspent = axioms.collect { case (name, asserted) if !all.contains(asserted.conclusion) => name }.toSet
      )
    }
  }

  /**
   * What a conclusion cost, by name where the name exists and by proposition where it does not.
   *
   * [[unspent]] is carried deliberately. A report that lists what was used invites the reading that
   * everything asserted was needed, and the finding in the one case anybody has measured is the
   * opposite: three of four axioms went unused and a reader would not have guessed which.
   */
  final case class Spending(
    domain: String,
    ofTheDomain: Set[String],
    foundational: Set[Term],
    unspent: Set[String]
  ) {

    /** The line a report prints: what it cost, and whether it reached outside the domain. */
    def summary: String = {
      val spent = if (ofTheDomain.isEmpty) "no axiom of the domain"
      else s"${ofTheDomain.size} of ${ofTheDomain.size + unspent.size}: ${ofTheDomain.toVector.sorted.mkString(", ")}"
      val outside =
        if (foundational.isEmpty) "and no foundational axiom at all"
        else s"and ${foundational.size} foundational"
      s"$domain: $spent, $outside"
    }
  }
}
