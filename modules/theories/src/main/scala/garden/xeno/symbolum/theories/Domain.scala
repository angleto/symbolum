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
 * == What automation reaches, and what it still does not ==
 *
 * `Ring` and `Linarith` decide fragments of the reals and have nothing to say about an arbitrary
 * axiom. What reaches a domain is the **propositional skeleton**, and since 2026-09-16
 * [[Built.settle]] is the one call that puts a claim to it: specialise this domain's axioms at the
 * subjects the claim names, decide the skeleton, keep only the axioms the decision needed, detach,
 * quantify again, and report what it spent.
 *
 * It costs no foundational axiom, which is the part that changed. `Intuitionistic` decides the
 * fragment a hand derivation about a domain works in, and `Propositional` is the fallback for a
 * claim that is classically valid and no more, at the choice axiom and reported as such.
 *
 * What it is still **not** is a search over the domain: nothing looks for a claim, nothing reasons
 * about what a constant means, and a claim reaching arithmetic is refused by name rather than
 * approximated. The promise is accounting, not search, and [[Built.spends]] is the accounting.
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
      .map { case (theory, held) => new Built(domain, base, theory, notation, held.toMap) }
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
    val notation: Notation,
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

    /* ------------------------------------------------------------- settling a claim about it */

    /**
     * A claim about this domain, settled against its axioms, with what it cost.
     *
     * The three steps are the ones a hand derivation takes and they are worth naming, because what
     * this does **not** do is the more important half. It specialises the domain's axioms at the
     * subjects the claim itself names; it asks a propositional procedure whether the claim follows
     * from those instances, with every constant of the domain an atom given no meaning at all; and
     * it detaches the instances and puts the quantifiers back. There is no search over the domain.
     *
     * == Why the intuitionistic calculus is asked first, which is the whole point of the method ==
     *
     * `Propositional` alone would answer more claims and would answer this one, and it closes with
     * `DOUBLE_NEGATION`, so every theorem it produces rests on the choice axiom. For a claim about
     * the world that is a bad trade made silently: the same claim derived by hand out of the
     * derived rules is intuitionistic throughout and rests on the domain's own assumptions and
     * nothing else, which is what a reader is being asked to check.
     *
     * So [[Intuitionistic]] is asked first and `Propositional` second, and what separates the two
     * answers is not a flag on the verdict but the [[Spending]] itself: a claim settled the first
     * way reports no foundational axiom, and one that needed the second reports choice. That is the
     * currency this whole file exists to report, and a route that moves it has to say so.
     *
     * == What it refuses, by name ==
     *
     * A claim that reaches a constant of the **foundation** rather than of the domain — arithmetic,
     * an order, an equation between numbers — is refused naming the constants. The procedures below
     * would give such a constant no meaning either, so what they would decide is a skeleton in which
     * "at most three attempts" is one opaque atom, and an approximation nobody asked for is worse
     * than a refusal. Composing this with `Linarith` is a different piece of work and it is not this
     * one.
     *
     * A claim needing more than [[Domain.Instances]] specialised axioms is refused for its size,
     * which is a bound on this method rather than on the domain: the instances are every assignment
     * of the subjects the claim names to the binders of each axiom, so a claim naming many subjects
     * over many axioms multiplies.
     */
    def settle(classical: Classical, goal: Term): Verdict =
      classical.logic.over(theory) match {
        case Left(error) => Verdict.Refused(error.message)
        case Right(reading) =>
          Logic.stripForall(goal) match {
            case Left(error) => Verdict.Refused(error.message)
            case Right((variables, body)) => settleBody(classical, reading, variables, body)
          }
      }

    /**
     * The same, for a claim written in the domain's own notation rather than assembled.
     *
     * Read against [[notation]], which is the one this domain was **built** with, and not against
     * the classical extension's. The two differ by everything the foundation added below the
     * domain: a domain over the chain's widest signature has numerals and an order to write with,
     * and parsing its claims against `Classical.standard.notation` refuses `3` by saying there is no
     * constant of that name. Found by a test whose axioms parsed and whose goal did not, which is
     * the same text through two notations.
     */
    def settle(classical: Classical, text: String): Verdict =
      Parser.proposition(theory, notation, text) match {
        case Left(error) => Verdict.Refused(error.message)
        case Right(goal) => settle(classical, goal)
      }

    private def settleBody(
      classical: Classical,
      reading: Logic,
      variables: Vector[FVar],
      body: Term
    ): Verdict = {
      val foreign = foundationConstantsIn(body)

      if (Term.typeOf(body) != Type.Bool) Verdict.Refused("a proposition")
      else if (foreign.nonEmpty)
        Verdict.Refused(
          s"a claim in ${domain.name}'s own vocabulary: ${foreign.toVector.sorted.mkString(", ")} " +
            "belongs to the foundation underneath it, and an atom with no meaning is not an " +
            "approximation of arithmetic"
        )
      else
        instancesFor(reading, body) match {
          case Left(why) => Verdict.Refused(why)
          case Right(instances) => close(classical, reading, instances, variables, body)
        }
    }

    /**
     * The tautology, detached against the axiom instances it actually needed, and quantified again.
     *
     * == Why the instances are cut down first, which is the whole value of the method ==
     *
     * The obvious version hands every specialised axiom to the procedure and detaches all of them.
     * It produces the same theorem and it **destroys the accounting**: `Derivation.axiomsOf` walks
     * the proof, every axiom that was detached is in the proof, and a report saying the conclusion
     * spent all four is worth nothing to the reader it is written for. Measured on the release gate
     * the first time this was run: four of four, where the hand derivation spends one.
     *
     * So the set is made irredundant before the theorem is built. Each instance is dropped in turn
     * and the bridge re-decided without it; where it still goes through, the instance is gone for
     * good. What comes out is a set no member of which can be removed, which is what an
     * unsatisfiable core is, obtained by deletion rather than read off a refutation — `Propositional`
     * does not publish the clauses its refutation read, and the intuitionistic calculus has no
     * clauses at all, so deletion is the one route that works for both.
     *
     * It costs `2n + 1` decisions for `n` instances, which is why [[Domain.Instances]] is bounded.
     * And it is **minimal rather than minimum**: a different deletion order can leave a different
     * irredundant set, and where two axioms would each do alone, the one tried later survives.
     *
     * == Why the route is fixed before the cutting down ==
     *
     * The intuitionistic calculus is asked first on the whole set, and whichever procedure answered
     * is the one every deletion step uses. Re-choosing per step would let a subset provable only
     * classically survive where the full set was intuitionistic, and the report would then name the
     * choice axiom because the search shrank the assumptions, which is a worse trade made silently.
     */
    private def close(
      classical: Classical,
      reading: Logic,
      instances: Vector[Kernel.Thm],
      variables: Vector[FVar],
      body: Term
    ): Verdict = {
      val rules = reading.rules
      val calculus = Intuitionistic(reading)
      val decision = Propositional.over(classical, reading)

      def bridgeOf(subset: Vector[Kernel.Thm]): Either[LogicError, Term] =
        subset.foldRight[Either[LogicError, Term]](Right(body)) { (instance, acc) =>
          acc.flatMap(reading.mkImp(instance.conclusion, _))
        }

      def intuitionistically(subset: Vector[Kernel.Thm]): Option[Kernel.Thm] =
        bridgeOf(subset).flatMap(calculus.prove).toOption

      def classically(subset: Vector[Kernel.Thm]): Option[Kernel.Thm] =
        bridgeOf(subset).toOption.flatMap(bridge =>
          decision.decide(bridge) match {
            case Propositional.Verdict.Proved(tautology) => Some(tautology)
            case _ => None
          }
        )

      val route: Option[Vector[Kernel.Thm] => Option[Kernel.Thm]] =
        if (intuitionistically(instances).isDefined) Some(intuitionistically)
        else if (classically(instances).isDefined) Some(classically)
        else None

      route match {
        case None =>
          bridgeOf(instances) match {
            case Left(error) => Verdict.Refused(error.message)
            case Right(bridge) =>
              decision.decide(bridge) match {
                case Propositional.Verdict.Countermodel(assignment) => Verdict.Countermodel(assignment)
                case Propositional.Verdict.Undecided(why) => Verdict.Refused(why)
                case Propositional.Verdict.Refused(why) => Verdict.Refused(why)
                case Propositional.Verdict.Proved(_) =>
                  Verdict.Refused("a decision that did not change between two identical questions")
              }
          }

        case Some(prove) =>
          val needed = instances.foldLeft(instances) { (kept, candidate) =>
            val trial = kept.filterNot(_.conclusion == candidate.conclusion)
            if (trial.length == kept.length || prove(trial).isEmpty) kept else trial
          }

          prove(needed) match {
            case None => Verdict.Refused("a decision that did not survive its own cutting down")
            case Some(tautology) =>
              needed
                .foldLeft[Either[LogicError, Kernel.Thm]](Right(tautology))((acc, instance) =>
                  acc.flatMap(rules.mp(_, instance))
                )
                .flatMap(rules.genAll(_, variables.toList)) match {
                case Left(error) => Verdict.Refused(error.message)
                case Right(theorem) => Verdict.Settled(theorem, spends(theorem))
              }
          }
      }
    }

    /**
     * Every axiom of the domain at every subject the claim names, and nothing else.
     *
     * The subjects are the claim's own: the variables its quantifiers bound, and the variables and
     * constants left free in its body. A claim about an arbitrary change and a claim about a named
     * one therefore both work, and a claim needing an instance at a term that appears nowhere in it
     * does not — which is the line between specialising a claim and searching for one, and this
     * method is on the first side of it deliberately.
     */
    private def instancesFor(reading: Logic, body: Term): Either[String, Vector[Kernel.Thm]] = {
      val rules = reading.rules
      val subjects = (Term.freeVariables(body).toVector: Vector[Term]) ++ constantsIn(body).toVector

      val prefixes = axioms.toVector
        .sortBy(_._1)
        .flatMap { case (_, asserted) =>
          Logic.stripForall(asserted.conclusion).toOption.toVector.map { case (binders, _) =>
            (asserted, binders.map(_.ty).toList)
          }
        }

      // Counted before the tuples are built rather than after, because the count is a PRODUCT: a
      // claim naming ten subjects over an axiom of eight binders is a hundred million tuples, and a
      // bound checked on the finished list is a bound checked after the machine has been asked for
      // the list. Each factor is how many of the subjects have the binder's type.
      val expected = prefixes.map { case (_, types) =>
        types.foldLeft(1L)((acc, ty) => acc * subjects.count(Term.typeOf(_) == ty))
      }.sum

      if (expected > Instances)
        Left(
          s"a claim of ${domain.name} needing at most $Instances specialised axioms, and this one " +
            s"needs $expected: the subjects it names, at every binder of every axiom that takes them"
        )
      else
        prefixes
          .flatMap { case (asserted, types) => tuples(types, subjects).map((asserted, _)) }
          .foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
            case (acc, (asserted, arguments)) =>
              for {
                held <- acc
                instance <- rules.specAll(asserted, arguments)
              } yield if (held.exists(_.conclusion == instance.conclusion)) held else held :+ instance
          }
          .left
          .map(_.message)
    }

    /** Every tuple of subjects matching a prefix of binder types, in the order they were found. */
    private def tuples(types: List[Type], subjects: Vector[Term]): Vector[List[Term]] =
      types match {
        case Nil => Vector(Nil)
        case head :: rest =>
          subjects.filter(Term.typeOf(_) == head).flatMap { subject =>
            tuples(rest, subjects).map(subject :: _)
          }
      }

    /** The constants of a term that this domain introduced, as terms, so they can be subjects. */
    private def constantsIn(term: Term): Set[Term] = term match {
      case constant @ Const(name, _) if domain.introduced.contains(name) => Set(constant)
      case App(fn, argument) => constantsIn(fn) ++ constantsIn(argument)
      case Abs(_, inner) => constantsIn(inner)
      case _ => Set.empty
    }

    /** The names a claim reaches that are neither the domain's nor a connective's. */
    private def foundationConstantsIn(term: Term): Set[String] = {
      def walk(current: Term): Set[String] = current match {
        case Const(name, _) if domain.introduced.contains(name) => Set.empty
        case Const(name, _) if Domain.Structural.contains(name) => Set.empty
        case Const(name, _) => Set(name)
        case App(fn, argument) => walk(fn) ++ walk(argument)
        case Abs(_, inner) => walk(inner)
        case _ => Set.empty
      }

      walk(term)
    }
  }

  /**
   * What a claim about a domain came back as, and the three are not one answer with a flag on it.
   *
   * [[Verdict.Countermodel]] is the weak one and carries `Propositional`'s own caveat: the atoms
   * are uninterpreted, so it refutes the claim **as a propositional schema over the domain's
   * constants** and never says that the claim is false. [[Verdict.Refused]] is the claim being
   * outside what this settles at all, and it names why.
   */
  enum Verdict {

    /** A theorem, with what it spent: the half a reader of a domain claim is really owed. */
    case Settled(theorem: Kernel.Thm, spending: Spending)

    /** An assignment to the domain's own atoms under which the claim's skeleton fails. */
    case Countermodel(assignment: Vector[(Term, Boolean)])

    /** Outside the fragment, named. */
    case Refused(why: String)
  }

  /**
   * How many specialised axioms one claim may carry.
   *
   * A bound on the method and not on the domain, and it is a product rather than a sum: every
   * subject the claim names is tried at every binder of every axiom. The release gate that this was
   * measured on is four axioms of one binder at one subject, which is four; a claim naming three
   * subjects over eight axioms of two binders each is seventy-two and is a different kind of
   * question, so it is refused rather than run.
   */
  val Instances: Int = 64

  /**
   * The names a claim may reach without leaving its own vocabulary.
   *
   * The eight connectives and equality: what a domain claim is built **with** rather than what it
   * is **about**. Everything else declared below the domain is the foundation's — an order, a sum,
   * a numeral — and a claim reaching one of those is refused by name, because the propositional
   * procedures would read it as an atom with no meaning and answer about a skeleton instead.
   */
  private val Structural: Set[String] = Set(
    Logic.Truth,
    Logic.Falsity,
    Logic.Conjunction,
    Logic.Disjunction,
    Logic.Implication,
    Logic.Negation,
    Logic.Universal,
    Logic.Existential,
    Term.EqualityName
  )

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
