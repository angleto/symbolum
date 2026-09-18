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
 * [[Domain.build]] runs it once against a base. `Real.Declarations` and `Natural.Statements`
 * already have this shape; this makes it a value a caller can hold.
 *
 * == Why composition refuses on a shared name ==
 *
 * `docs/adr/0019` measured the identity of a declared constant and left `docs/adr/0008`'s rule
 * standing: a declared constant has **no origin**, so two domains that each declare `Cost` produce
 * constants that are equal, whatever either of them meant by it. Composing them silently would
 * merge two vocabularies into one and say nothing.
 *
 * [[Domain.compose]] therefore refuses, naming the constant. That is the whole of what this file
 * does about `0019`'s residual risk: it does not remove it, it makes the one place a caller could
 * walk into it say so. A caller who really does mean one constant says so with
 * [[Domain.composeSharing]], and then the sharing is a line in their source rather than an accident
 * of two files agreeing on a word.
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
 * [[Domain.Built.settle]] is the one call that puts a claim to it: specialise this domain's
 * axioms at the subjects the claim names, decide the skeleton, keep only the axioms the decision
 * needed, detach, quantify again, and report what it spent.
 *
 * It costs no foundational axiom, which is the part that changed. `Intuitionistic` decides the
 * fragment a hand derivation about a domain works in, and `Propositional` is the fallback for a
 * claim that is classically valid and no more, at the choice axiom and reported as such.
 *
 * **Arithmetic arrives on a bridge the caller names**, which is `docs/adr/0024` and is the second
 * thing that changed. A claim may reach the foundation's constants; the terms of foundation type
 * in it stay opaque, and a theorem the caller hands over is specialised at them and joins the
 * axiom instances. Nothing is interpreted, because there is nothing to interpret: a constant like
 * `Attempts : job -> num` already returns a number, and what is unknown is which one. The cost
 * shows: the bridge carries its own axioms into [[Domain.Built.spends]]'s foundational column, so
 * arithmetic is visible rather than free.
 *
 * What it is still **not** is a search over the domain: nothing here looks for a claim, and a
 * domain **type** the foundation has never heard of has no bridge to be named, so a claim needing
 * arithmetic about one is still refused by name. The promise of this file is accounting, not
 * search, and [[Domain.Built.spends]] is what accounts.
 *
 * **The bridge itself is looked for since 2026-09-18, and it is looked for somewhere else.**
 * `Bridging` takes a library, puts the lemmas about the constants a claim names to this method one
 * at a time, and reports which of them carried it; `docs/adr/0027` is the decision, and the reason
 * it is a file above this one rather than a mode of [[Domain.Built.settle]] is the one stated at
 * the text overload below: resolving a name would put `Library` under this file and shut out the
 * caller whose bridge is a fact it never published. Nothing changes here: what that search hands
 * back was built by this method, and every refusal this method gives is still what a caller naming
 * its own bridge gets.
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

    /**
     * The foundation's constants a claim reaches, which is what a bridge has to be about.
     *
     * The same walk the refusal below is written from, published because the caller that has to
     * name a bridge is the one that needs the list, and until 2026-09-18 the only way to obtain it
     * was to read it back out of the refusal's sentence. `Bridging` is the first consumer: it is
     * what decides which of the library's lemmas are candidates, and a search over the library
     * rather than over these constants would be a different tool.
     *
     * A claim in the domain's own vocabulary answers with the empty set, and that is the answer
     * this is most often asked for: it says no bridge is wanted, rather than that none was found.
     */
    def reaches(goal: Term): Set[String] = foundationConstantsIn(opened(goal))

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
     * So `Intuitionistic` is asked first and `Propositional` second, and what separates the two
     * answers is not a flag on the verdict but the [[Domain.Spending]] itself: a claim settled the
     * first way reports no foundational axiom, and one that needed the second reports choice.
     * That is the currency this whole file exists to report, and a route that moves it has to say
     * so.
     *
     * == What it refuses, by name, and what it now asks for instead ==
     *
     * A claim that reaches a constant of the **foundation** rather than of the domain — arithmetic,
     * an order, an equation between numbers — is refused naming the constants **when the caller has
     * named no bridge**. The procedures below give such a constant no meaning, so what they would
     * decide alone is a skeleton in which "at most three attempts" is one opaque atom, and an
     * approximation nobody asked for is worse than a refusal.
     *
     * `docs/adr/0024` decides what carries a claim across that line, and it is not an
     * interpretation of the domain's constants. A caller hands over **theorems** — library lemmas,
     * or anything else it holds — and each is specialised at the claim's own foundation-typed
     * subterms and joins the axiom instances. `Attempts j` is never given a value: it is a term of
     * type `num` whose value nobody knows, so a fact used about it has to hold for all of them, and
     * that is what makes this safe where substituting a number would not be.
     *
     * Nothing **here** searches for the bridge. A caller that names a lemma which does not apply
     * has it dropped by the cutting-down below, at the cost of the decisions that takes; a caller
     * that names none gets the refusal, which is the same answer this method has always given.
     * Since 2026-09-18 a caller that wants the lemma found rather than named has `Bridging`, which
     * is a search over a library **above** this method and calls it once per candidate. What it
     * hands back is a theorem this method built, at a bridge this method was given, so it adds no
     * way of deciding anything; what it reaches that a caller naming nothing does not is exactly
     * the claims that were refused for wanting a bridge nobody had chosen.
     *
     * **What it costs is reported rather than hidden**, and that is the whole of why this is
     * allowed. A bridge carries whatever its own derivation spent, `Derivation.axiomsOf` walks it,
     * and a release-gate conclusion reaching `NUM_LT_NOT_LE` therefore reports the naturals' two
     * foundational axioms where a purely propositional one reports none. The promise is not that
     * arithmetic is free, it is that arithmetic is visible.
     *
     * A claim needing more than [[Domain.Instances]] specialised axioms is refused for its size,
     * which is a bound on this method rather than on the domain: the instances are every assignment
     * of the subjects the claim names to the binders of each axiom, so a claim naming many subjects
     * over many axioms multiplies.
     */
    def settle(classical: Classical, goal: Term): Verdict =
      settle(classical, goal, Vector.empty)

    /**
     * The same, carried across into the foundation's vocabulary by the facts the caller names.
     *
     * Theorems rather than names, which is a smaller decision than it looks. Resolving a name would
     * put `Library` under this file, and it would also shut out the caller whose bridge is a fact it
     * derived by hand rather than one the library publishes. What the record asks for is that the
     * bridge be the caller's choice and visible at the call site, and a theorem is that.
     */
    def settle(classical: Classical, goal: Term, bridges: Vector[Kernel.Thm]): Verdict =
      classical.logic.over(theory) match {
        case Left(error) => Verdict.Refused(error.message)
        case Right(reading) =>
          Logic.stripForall(goal) match {
            case Left(error) => Verdict.Refused(error.message)
            case Right((variables, body)) => settleBody(classical, reading, variables, body, bridges)
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
      settle(classical, text, Vector.empty)

    /** The same as the text overload, with the bridges `docs/adr/0024` decides are the caller's. */
    def settle(classical: Classical, text: String, bridges: Vector[Kernel.Thm]): Verdict =
      Parser.proposition(theory, notation, text) match {
        case Left(error) => Verdict.Refused(error.message)
        case Right(goal) => settle(classical, goal, bridges)
      }

    private def settleBody(
      classical: Classical,
      reading: Logic,
      variables: Vector[FVar],
      body: Term,
      bridges: Vector[Kernel.Thm]
    ): Verdict = {
      val foreign = foundationConstantsIn(body)

      if (Term.typeOf(body) != Type.Bool) Verdict.Refused("a proposition")
      else if (foreign.nonEmpty && bridges.isEmpty)
        Verdict.Refused(
          s"a claim in ${domain.name}'s own vocabulary, or a fact to carry it across: " +
            s"${foreign.toVector.sorted.mkString(", ")} belongs to the foundation underneath it, " +
            "and an atom with no meaning is not an approximation of arithmetic. Name the theorem " +
            "that relates them and it will be specialised at the terms this claim already names"
        )
      else
        instancesFor(reading, body, bridges) match {
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
     *
     * == The net under the first of the two, and why it is reported rather than hidden ==
     *
     * `Intuitionistic.Fuel` is a net under a termination argument rather than the argument, so the
     * calculus has two ways to refuse: `BoundReached`, carrying `Standing.Exhausted`, which means
     * **I stopped**, and everything else, which means **it is not so**. Until 2026-09-18 both were
     * read through `toOption` and both fell through to `classically` at the choice axiom, so a
     * claim whose free route was cut short came back at a price the logic never asked for, with
     * nothing in the answer saying which of the two had happened.
     *
     * **The measurement that decided it is not the one the paragraph here used to cite.** Over the
     * 1114 formulas `PropositionalRouteSpec` enumerates the deepest goal needs 7 of the 256, and
     * that population is formulas of at most six nodes; what this method builds is an implication
     * chain one link per instance, so the figure travels no further than the shape it was taken on.
     * Measured on the chains this method itself builds, the net **is** reached, by a claim that is
     * a chain of modus ponens and so intuitionistically valid at every length, and at a length
     * strictly inside [[Domain.Instances]] rather than at it. `docs/adr/0026` carries the table and
     * what it counted by; `DomainTheorySpec` finds the length where the free route is lost and
     * asserts the relation between it and the bound, which is the claim and is what this comment
     * would otherwise be a stale copy of.
     *
     * So the fall stays — refusing would lose a theorem the classical route really does have — and
     * what changes is that [[Domain.Verdict.CutShort]] is what comes back instead of
     * [[Domain.Verdict.Settled]]. A caller reading the price is told that the free route was
     * truncated rather than decided against, and a caller matching on `Settled` alone stops
     * compiling rather than quietly believing the price.
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

      def intuitionistically(subset: Vector[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
        bridgeOf(subset).flatMap(calculus.prove)

      def classically(subset: Vector[Kernel.Thm]): Option[Kernel.Thm] =
        bridgeOf(subset).toOption.flatMap(bridge =>
          decision.decide(bridge) match {
            case Propositional.Verdict.Proved(tautology) => Some(tautology)
            case _ => None
          }
        )

      val free = intuitionistically(instances)

      // The refusal kept rather than dropped, which is the whole of the repair. It is read once,
      // on the full set and before the route is fixed, because that is the decision it changes:
      // every later call is the route's own and answers a question about a subset.
      val cutShort: Option[String] =
        free.left.toOption.filter(_.standing.stoppedShort).map(_.message)

      val route: Option[Vector[Kernel.Thm] => Option[Kernel.Thm]] =
        if (free.isRight) Some(subset => intuitionistically(subset).toOption)
        else if (classically(instances).isDefined) Some(classically)
        else None

      route match {
        // Neither route answered, so what comes back is the classical decision's own answer about
        // the claim, and `cutShort` is deliberately not added to it: a countermodel refutes the
        // skeleton classically and therefore intuitionistically as well, so a free route that
        // stopped changes nothing about it, and the two refusals below already name the procedure
        // that stopped. What this case is for is a PRICE that carries a caveat, and there is none
        // here because nothing was settled.
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
                case Right(theorem) =>
                  cutShort match {
                    case None => Verdict.Settled(theorem, spends(theorem))
                    case Some(why) => Verdict.CutShort(theorem, spends(theorem), why)
                  }
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
    private def instancesFor(
      reading: Logic,
      body: Term,
      bridges: Vector[Kernel.Thm]
    ): Either[String, Vector[Kernel.Thm]] = {
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

      // **The bridges are counted here and were not until 2026-09-18**, which is the half of this
      // bound that was missing rather than a second bound. `docs/adr/0024` says the cut-down costs
      // `2n + 1` decisions and that `n` counts the bridges too; the check did not, so a caller
      // naming many of them walked past a guard that was reading the axioms alone. Found by
      // `BridgingSpec` putting a whole candidate set to this method and waiting minutes for an
      // answer it should have been refused in a step, which is what a bound is for.
      val expectedOfBridges = bridgeCounts(body, bridges).sum

      if (expected + expectedOfBridges > Instances)
        Left(
          s"a claim of ${domain.name} needing at most $Instances specialised axioms, and this one " +
            s"needs ${expected + expectedOfBridges}: the subjects it names, at every binder of " +
            s"every axiom that takes them, and $expectedOfBridges of them from the bridges it was " +
            "given"
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
          .flatMap(held => bridgeInstances(reading, body, bridges).map(held ++ _))
          .left
          .map(_.message)
    }

    /**
     * Each bridge specialised at the terms of its own binders' types that the claim already names.
     *
     * The subjects are **maximal** subterms of the wanted type rather than every subterm of it, and
     * that is the difference between four tuples and a hundred here. `NUM_LT (Attempts j) 3` holds
     * two terms of type `num` that a reader would point at, `Attempts j` and `3`; descending into
     * `3` finds the bit encoding under it, every level of which is also a `num` and none of which is
     * anything the claim is about. So the walk stops at the first subterm of the type it wants.
     *
     * A bridge with no binders is taken as it stands, which is the degenerate case and is right: a
     * closed fact needs no instance of itself.
     *
     * Nothing here refuses a bridge that does not fit. One whose binders have a type the claim names
     * no term of produces no instances and disappears, and one that produces instances the decision
     * does not need is removed by the cutting-down in [[Domain.Built.close]]. Both are the caller's
     * mistake costing decisions rather than this method's to diagnose, and a refusal here would have
     * to guess which of a caller's several bridges was the intended one.
     */
    /**
     * How many instances each bridge will produce, counted before any of them is built.
     *
     * The same walk [[bridgeInstances]] makes, as a product rather than as a list, because a bound
     * checked on the finished list is a bound checked after the machine has been asked for the
     * list. It has to agree with that method by construction, so the subjects are taken the same
     * way: the distinct binder types, the claim's maximal subterms of each, and one factor per
     * binder.
     */
    private def bridgeCounts(body: Term, bridges: Vector[Kernel.Thm]): Vector[Long] =
      bridges.map { bridge =>
        Logic.stripForall(bridge.conclusion) match {
          case Left(_) => 1L
          case Right((binders, _)) if binders.isEmpty => 1L
          case Right((binders, _)) =>
            val types = binders.map(_.ty).toList
            val subjects = types.distinct.flatMap(ty => maximalSubtermsOfType(body, ty)).distinct
            types.foldLeft(1L)((acc, ty) => acc * subjects.count(Term.typeOf(_) == ty))
        }
      }

    private def bridgeInstances(
      reading: Logic,
      body: Term,
      bridges: Vector[Kernel.Thm]
    ): Either[LogicError, Vector[Kernel.Thm]] = {
      val rules = reading.rules

      bridges.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, bridge) =>
        acc.flatMap { held =>
          Logic.stripForall(bridge.conclusion) match {
            case Left(_) => Right(if (held.exists(_.conclusion == bridge.conclusion)) held else held :+ bridge)
            case Right((binders, _)) if binders.isEmpty =>
              Right(if (held.exists(_.conclusion == bridge.conclusion)) held else held :+ bridge)
            case Right((binders, _)) =>
              val types = binders.map(_.ty).toList
              val subjects = types.distinct.flatMap(ty => maximalSubtermsOfType(body, ty)).distinct

              tuples(types, subjects.toVector)
                .foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(held)) { (inner, arguments) =>
                  inner.flatMap { kept =>
                    rules.specAll(bridge, arguments) match {
                      case Left(_) => Right(kept)
                      case Right(instance) =>
                        Right(if (kept.exists(_.conclusion == instance.conclusion)) kept else kept :+ instance)
                    }
                  }
                }
          }
        }
      }
    }

    /**
     * The terms of this type a claim names, which is what a bridge's binder can be specialised at.
     *
     * Published to `Bridging` and to nothing else, because a search over candidate bridges needs to
     * know which of them can produce an instance here at all: a bridge whose binders have a type
     * this claim names no term of produces none, and a bridge with no instances cannot change any
     * decision this method makes. Skipping such a candidate is therefore exact rather than a
     * heuristic, and skipping it is the difference between a search that runs and one that is
     * refused for its size.
     */
    private[theories] def subjectsOfType(goal: Term, ty: Type): Vector[Term] =
      maximalSubtermsOfType(opened(goal), ty)

    /**
     * A claim with its leading universals opened into free variables, which is what a walk needs.
     *
     * Binders here are locally nameless, so descending into `!j:job. P j` reaches an index with no
     * binder in hand and `Term.typeOf` throws rather than answering. [[settleBody]] never meets that
     * because [[settle]] strips the quantifiers before calling it; the two methods above are called
     * by somebody holding the claim as it was written, so they strip for themselves. Found by
     * `BridgingSpec` on the first run of the search, as a kernel invariant violation rather than a
     * wrong answer, which is the failure this representation is chosen to give.
     *
     * A claim that is not a universal is its own body, which is what the fall-through says.
     */
    private def opened(goal: Term): Term =
      Logic.stripForall(goal).map(_._2).getOrElse(goal)

    /** Every subterm of the given type, not descending into one once it has that type. */
    private def maximalSubtermsOfType(term: Term, ty: Type): Vector[Term] =
      if (Term.typeOf(term) == ty) Vector(term)
      else
        term match {
          case App(fn, argument) => maximalSubtermsOfType(fn, ty) ++ maximalSubtermsOfType(argument, ty)
          case Abs(_, inner) => maximalSubtermsOfType(inner, ty)
          case _ => Vector.empty
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
   * What a claim about a domain came back as, and the four are not one answer with a flag on it.
   *
   * [[Domain.Verdict.Countermodel]] is the weak one and carries `Propositional`'s own caveat: the atoms
   * are uninterpreted, so it refutes the claim **as a propositional schema over the domain's
   * constants** and never says that the claim is false. [[Domain.Verdict.Refused]] is the claim being
   * outside what this settles at all, and it names why.
   */
  enum Verdict {

    /** A theorem, with what it spent: the half a reader of a domain claim is really owed. */
    case Settled(theorem: Kernel.Thm, spending: Spending)

    /**
     * The same theorem and the same price, and the free route was cut short rather than decided.
     *
     * `Domain.Built.close` asks the intuitionistic calculus first because it costs no axiom, and
     * falls to the classical decision when that refuses. The calculus refuses in two ways: because
     * the claim is not intuitionistically valid, and because `Intuitionistic.Fuel` ran out. Only the
     * first is a fact about the claim. This case is the second, and what it says is that the
     * `SELECT` in [[Domain.Spending]] is the net's rather than the logic's: a larger net might have
     * reached the same theorem for nothing, and nothing here knows whether it would have.
     *
     * A case of its own rather than a field on [[Domain.Verdict.Settled]], because a price that
     * needs a caveat and a price that does not are two answers, and a caller that reads them as one
     * is being told that a claim about its domain needs choice when what it needed was patience.
     * The theorem is real and carries no hypothesis, so a caller that wants it whatever the route
     * took can take it from here; what it cannot do is read this as [[Domain.Verdict.Settled]] by
     * accident.
     *
     * `why` is the calculus's own refusal message, verbatim, naming the search and the depth it was
     * given. Rewriting it here would be this file inventing a sentence about somebody else's bound.
     */
    case CutShort(theorem: Kernel.Thm, spending: Spending, why: String)

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
   *
   * **The bridges are inside it since 2026-09-18 and were outside it before**, which was the one
   * way past this guard: a bridge is specialised the same way and its instances cost the cut-down
   * the same `2n + 1`, so a caller naming twenty of them paid twenty times what a bound of 64 is
   * for and nothing said so. `docs/adr/0027` records how it was found.
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
